/*
 * lean_stm.cpp — Multi-Protocol High-Performance STM Runtime for Lean 4
 *
 * Protocols supported:
 *   0 = TL2_LSA  : Transactional Locking II + GV4 Safe CAS Clock + Lazy Snapshot Extension (LSA)
 *                  + Polka exponential backoff + Adaptive Hybrid MVCC fallback on read-only contention
 *   1 = TL2_GV1  : Classic TL2 (fetch_add global clock, no LSA snapshot extension)
 *   2 = MVCC_RO  : Wait-Free Read-Only Snapshot via Inline 8-Version Ring (Lock-Before-Clock invariant)
 *   3 = NOREC    : Dalessandro-Spear-Scott NOrec (single global seqlock + Perceus ABA-free pointer validation)
 *
 * Memory & Reference-Counting Safety:
 *   - Every TVar external object and every Lean object stored inside a TVar is marked multi-threaded
 *     (`lean_mark_mt`) prior to publication, ensuring atomic RC updates (`m_rc < 0`).
 *   - Overwritten `lean_object*` pointers are retired via a 3-epoch Fraser Epoch-Based Reclamation (EBR)
 *     engine so concurrent lock-free readers never experience use-after-free prior to `lean_inc` and
 *     never dirty shared cache lines (eliminating Lean `IO.Ref.get`'s double `exchange(nullptr)` bottleneck).
 *   - Modular `retry` uses Dekker-synchronized (`seq_cst`) per-TVar wait queues for zero-spin blocking
 *     with mathematically zero lost wakeups.
 */

#include <lean/lean.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstring>
#include <memory>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <vector>

namespace lean_stm {

// ---------------------------------------------------------------------------
// Architecture-specific spin-pause hint
// ---------------------------------------------------------------------------
static inline void cpu_relax() noexcept {
#if defined(__aarch64__) || defined(_M_ARM64)
    asm volatile("yield" ::: "memory");
#elif defined(__x86_64__) || defined(_M_X64)
    __builtin_ia32_pause();
#else
    std::this_thread::yield();
#endif
}

// ---------------------------------------------------------------------------
// Protocol identifiers (must match `STM.Protocol` in Lean)
// ---------------------------------------------------------------------------
enum StmProtocol : uint8_t {
    PROTO_TL2_LSA = 0,
    PROTO_TL2_GV1 = 1,
    PROTO_MVCC_RO = 2,
    PROTO_NOREC   = 3,
};

static std::atomic<uint8_t> g_default_protocol{PROTO_TL2_LSA};

// ---------------------------------------------------------------------------
// Global Clocks & IDs (each isolated on its own 128-byte cache line pair
// for Apple Silicon M-series 128B L2 sector prefetchers!)
// ---------------------------------------------------------------------------
struct alignas(128) AlignedAtomicU64 {
    std::atomic<uint64_t> val;
    explicit constexpr AlignedAtomicU64(uint64_t init) : val(init) {}
};

static AlignedAtomicU64 g_next_tvar_id{1};
static AlignedAtomicU64 g_tl2_clock{1};   // Starts at version 1
static AlignedAtomicU64 g_norec_loc{0};   // Even = unlocked, Odd = committing writer

// ---------------------------------------------------------------------------
// Telemetry Counters (thread-local accumulation + global aggregation)
// ---------------------------------------------------------------------------
struct RawStats {
    uint64_t commits           = 0;
    uint64_t aborts_conflict   = 0;
    uint64_t aborts_validation = 0;
    uint64_t retries_parked    = 0;
    uint64_t lsa_extensions    = 0;
    uint64_t mvcc_snapshots    = 0;
    uint64_t gv4_elisions      = 0;
};

struct alignas(128) ThreadStatsNode {
    std::atomic<uint64_t> commits{0};
    std::atomic<uint64_t> aborts_conflict{0};
    std::atomic<uint64_t> aborts_validation{0};
    std::atomic<uint64_t> retries_parked{0};
    std::atomic<uint64_t> lsa_extensions{0};
    std::atomic<uint64_t> mvcc_snapshots{0};
    std::atomic<uint64_t> gv4_elisions{0};
    ThreadStatsNode* next = nullptr;
};

static std::mutex g_stats_mtx;
static ThreadStatsNode* g_stats_head = nullptr;
static RawStats g_exited_stats{};

struct ThreadStatsGuard {
    ThreadStatsNode* node;
    ThreadStatsGuard() : node(new ThreadStatsNode()) {
        std::lock_guard<std::mutex> lk(g_stats_mtx);
        node->next = g_stats_head;
        g_stats_head = node;
    }
    // Nodes remain in global list (bounded by OS threads created) so lock-free reads are always safe.
};

static thread_local ThreadStatsGuard tls_stats_guard;

static inline ThreadStatsNode* stats() noexcept {
    return tls_stats_guard.node;
}

// ---------------------------------------------------------------------------
// 3-Epoch Fraser Epoch-Based Reclamation (EBR) for Lean RC Objects
// ---------------------------------------------------------------------------
static constexpr uint64_t EBR_ACTIVE_BIT = 1ULL << 63;
static AlignedAtomicU64 g_ebr_epoch{1};

struct alignas(128) EbrThreadNode {
    std::atomic<uint64_t> local_epoch{0};
    std::atomic<bool> in_use{true};
    std::vector<lean_object*> bags[3];
    uint64_t retire_counter = 0;
    EbrThreadNode* next = nullptr;
};

static std::mutex g_ebr_mtx;
static EbrThreadNode* g_ebr_head = nullptr;
static std::vector<lean_object*> g_ebr_orphan_bags[3];

static void ebr_drain_bag(std::vector<lean_object*>& bag) noexcept {
    for (lean_object* o : bag) {
        lean_dec(o);
    }
    bag.clear();
}

struct EbrThreadGuard {
    EbrThreadNode* node;
    EbrThreadGuard() {
        std::lock_guard<std::mutex> lk(g_ebr_mtx);
        // Reuse an exited thread slot if available to keep registry compact
        for (EbrThreadNode* cur = g_ebr_head; cur != nullptr; cur = cur->next) {
            bool expected = false;
            if (!cur->in_use.load(std::memory_order_relaxed) &&
                cur->in_use.compare_exchange_strong(expected, true, std::memory_order_acq_rel)) {
                cur->local_epoch.store(0, std::memory_order_relaxed);
                cur->retire_counter = 0;
                node = cur;
                return;
            }
        }
        node = new EbrThreadNode();
        node->next = g_ebr_head;
        g_ebr_head = node;
    }
    ~EbrThreadGuard() {
        node->local_epoch.store(0, std::memory_order_release);
        {
            std::lock_guard<std::mutex> lk(g_ebr_mtx);
            for (int i = 0; i < 3; ++i) {
                if (!node->bags[i].empty()) {
                    g_ebr_orphan_bags[i].insert(
                        g_ebr_orphan_bags[i].end(),
                        node->bags[i].begin(),
                        node->bags[i].end());
                    node->bags[i].clear();
                }
            }
        }
        node->in_use.store(false, std::memory_order_release);
    }
};

static thread_local EbrThreadGuard tls_ebr;

static inline EbrThreadNode* ebr_enter() noexcept {
    EbrThreadNode* n = tls_ebr.node;
    uint64_t e = g_ebr_epoch.val.load(std::memory_order_relaxed);
    n->local_epoch.store(e | EBR_ACTIVE_BIT, std::memory_order_seq_cst);
    return n;
}

static inline void ebr_exit(EbrThreadNode* n) noexcept {
    n->local_epoch.store(0, std::memory_order_release);
}

static void ebr_try_advance(EbrThreadNode* self) noexcept {
    uint64_t cur_e = g_ebr_epoch.val.load(std::memory_order_seq_cst);
    {
        std::lock_guard<std::mutex> lk(g_ebr_mtx);
        for (EbrThreadNode* p = g_ebr_head; p != nullptr; p = p->next) {
            if (!p->in_use.load(std::memory_order_acquire)) continue;
            uint64_t le = p->local_epoch.load(std::memory_order_seq_cst);
            if ((le & EBR_ACTIVE_BIT) != 0 && (le & ~EBR_ACTIVE_BIT) != cur_e) {
                return; // Thread still pinned in an older epoch; cannot advance yet
            }
        }
        uint64_t expected = cur_e;
        if (g_ebr_epoch.val.compare_exchange_strong(expected, cur_e + 1, std::memory_order_seq_cst)) {
            uint64_t safe_idx = (cur_e + 2) % 3; // 2 epochs ago is now completely quiescent
            ebr_drain_bag(g_ebr_orphan_bags[safe_idx]);
            ebr_drain_bag(self->bags[safe_idx]);
        }
    }
}

static inline void ebr_retire(lean_object* obj) noexcept {
    if (obj == nullptr || lean_is_scalar(obj) || lean_is_persistent(obj)) {
        return; // Scalars & persistent constants never need heap reclamation!
    }
    EbrThreadNode* self = tls_ebr.node;
    uint64_t cur_e = g_ebr_epoch.val.load(std::memory_order_acquire);
    // Opportunistically drain our own safe bag from 2 epochs ago
    uint64_t safe_idx = (cur_e + 1) % 3; // cur_e - 2 mod 3 == cur_e + 1 mod 3
    if (!self->bags[safe_idx].empty()) {
        ebr_drain_bag(self->bags[safe_idx]);
    }
    self->bags[cur_e % 3].push_back(obj);
    if ((++self->retire_counter & 63) == 0) {
        ebr_try_advance(self);
    }
}

// ---------------------------------------------------------------------------
// WaitQueue Structures for Modular `retry` Blocking
// ---------------------------------------------------------------------------
struct ParkedThread {
    std::mutex mtx;
    std::condition_variable cv;
    std::atomic<bool> notified{false};
};

struct WaitNode {
    ParkedThread* waiter = nullptr;
    WaitNode* prev = nullptr;
    WaitNode* next = nullptr;
    bool linked = false;
};

// ---------------------------------------------------------------------------
// TVarCell — 128-byte aligned to avoid Apple Silicon cache-line false sharing
// ---------------------------------------------------------------------------
static constexpr size_t MVCC_RING_SIZE = 8;

struct VersionSlot {
    std::atomic<uint64_t> version{0};
    std::atomic<lean_object*> value{nullptr};
};

struct alignas(128) TVarCell {
    uint64_t id;

    // Hot Cache Line: TL2 Lock/Version + Current Value + Waiter Flag
    alignas(128) std::atomic<uint64_t> lock_ver; // bit 0: locked, bits 1..63: version
    std::atomic<lean_object*> latest_val;
    std::atomic<uint32_t> ring_head;
    std::atomic<uint32_t> has_waiters;

    // Inline 8-Version MVCC Ring Buffer
    VersionSlot ring[MVCC_RING_SIZE];

    // Cold WaitQueue State (touched ONLY when a thread calls `retry`)
    std::mutex wait_mtx;
    WaitNode* wait_head = nullptr;

    TVarCell(uint64_t id_, uint64_t init_ver, lean_object* init_val)
        : id(id_),
          lock_ver(init_ver << 1),
          latest_val(init_val),
          ring_head(1),
          has_waiters(0) {
        // init_val arrives with +1 RC owned for `latest_val`.
        // Take an additional +1 RC for `ring[0]`.
        lean_inc(init_val);
        ring[0].value.store(init_val, std::memory_order_relaxed);
        ring[0].version.store(init_ver, std::memory_order_relaxed);
    }

    ~TVarCell() {
        lean_object* cur = latest_val.load(std::memory_order_relaxed);
        if (cur != nullptr) {
            lean_dec(cur);
        }
        for (size_t i = 0; i < MVCC_RING_SIZE; ++i) {
            lean_object* rv = ring[i].value.load(std::memory_order_relaxed);
            if (rv != nullptr) {
                lean_dec(rv);
            }
        }
    }

    void notify_all_waiters() noexcept {
        std::lock_guard<std::mutex> lk(wait_mtx);
        for (WaitNode* w = wait_head; w != nullptr; w = w->next) {
            ParkedThread* pt = w->waiter;
            {
                std::lock_guard<std::mutex> plk(pt->mtx);
                pt->notified.store(true, std::memory_order_release);
            }
            pt->cv.notify_all();
        }
    }
};

static lean_external_class* g_tvar_class = nullptr;
static std::once_flag g_tvar_class_once;

static void tvar_finalizer(void* ptr) {
    delete static_cast<TVarCell*>(ptr);
}

static void tvar_foreach(void*, b_lean_obj_arg) {
    // All values stored in TVarCell are eagerly marked multi-threaded (`lean_mark_mt`)
    // prior to insertion, and the external TVar object itself is marked `mt` at creation.
}

static inline lean_external_class* get_tvar_class() {
    std::call_once(g_tvar_class_once, []() {
        g_tvar_class = lean_register_external_class(tvar_finalizer, tvar_foreach);
    });
    return g_tvar_class;
}

static inline TVarCell* get_cell(b_lean_obj_arg tvar_obj) noexcept {
    return static_cast<TVarCell*>(lean_get_external_data(tvar_obj));
}

// ---------------------------------------------------------------------------
// Thread-Local Transaction Context (`TxContext`)
// ---------------------------------------------------------------------------
struct ReadEntry {
    lean_object* tvar_obj; // +1 RC owned while in log
    TVarCell* cell;
    uint64_t ver;          // version observed (TL2/MVCC)
    lean_object* val;      // +1 RC owned (needed for ABA-free NOrec validation & idempotent re-reads)
};

struct WriteEntry {
    lean_object* tvar_obj; // +1 RC owned while in log
    TVarCell* cell;
    lean_object* val;      // +1 RC owned
};

struct UndoEntry {
    size_t write_idx;
    lean_object* prev_val; // +1 RC owned (previous buffered value before overwrite in nested branch)
};

struct Savepoint {
    size_t write_size;
    size_t undo_size;
};

static constexpr size_t SMALL_SET_THRESHOLD = 16;

struct TxContext {
    bool active              = false;
    StmProtocol proto        = PROTO_TL2_LSA;
    bool mvcc_fallback_mode  = false;
    bool current_wrote       = false;
    bool prev_attempt_wrote  = false;
    uint64_t rv              = 0;
    uint32_t attempt         = 0;
    uint32_t rng_state       = 0x9E3779B9u;

    std::vector<ReadEntry> read_log;
    std::vector<WriteEntry> write_set;
    std::vector<UndoEntry> undo_log;
    std::vector<Savepoint> savepoints;

    // Secondary hash indices activated automatically only for large transactions (> 16 TVars)
    std::unordered_map<TVarCell*, size_t> read_index;
    std::unordered_map<TVarCell*, size_t> write_index;

    // Reusable scratch vector for sorted lock acquisition (zero malloc on hot path)
    std::vector<size_t> lock_order;

    TxContext() {
        read_log.reserve(32);
        write_set.reserve(16);
        undo_log.reserve(8);
        savepoints.reserve(4);
        lock_order.reserve(16);
    }

    ~TxContext() {
        clear_all();
    }

    uint32_t next_rand() noexcept {
        uint32_t x = rng_state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        rng_state = x ? x : 0x9E3779B9u;
        return rng_state;
    }

    void clear_writes() noexcept {
        for (auto& u : undo_log) {
            if (u.prev_val != nullptr) lean_dec(u.prev_val);
        }
        undo_log.clear();
        for (auto& w : write_set) {
            lean_dec(w.val);
            lean_dec(w.tvar_obj);
        }
        write_set.clear();
        if (!write_index.empty()) write_index.clear();
        savepoints.clear();
    }

    void clear_reads() noexcept {
        for (auto& r : read_log) {
            lean_dec(r.val);
            lean_dec(r.tvar_obj);
        }
        read_log.clear();
        if (!read_index.empty()) read_index.clear();
    }

    void clear_all() noexcept {
        clear_writes();
        clear_reads();
        active = false;
    }

    // Lookup in write_set: returns index or SIZE_MAX
    size_t find_write(TVarCell* cell) const noexcept {
        const size_t n = write_set.size();
        if (n <= SMALL_SET_THRESHOLD) {
            for (size_t i = 0; i < n; ++i) {
                if (write_set[i].cell == cell) return i;
            }
            return SIZE_MAX;
        }
        auto it = write_index.find(cell);
        return (it != write_index.end()) ? it->second : SIZE_MAX;
    }

    // Lookup in read_log: returns index or SIZE_MAX
    size_t find_read(TVarCell* cell) const noexcept {
        const size_t n = read_log.size();
        if (n <= SMALL_SET_THRESHOLD) {
            for (size_t i = 0; i < n; ++i) {
                if (read_log[i].cell == cell) return i;
            }
            return SIZE_MAX;
        }
        auto it = read_index.find(cell);
        return (it != read_index.end()) ? it->second : SIZE_MAX;
    }

    void insert_read(b_lean_obj_arg tvar_obj, TVarCell* cell, uint64_t ver, lean_object* val) {
        size_t idx = read_log.size();
        lean_inc(tvar_obj);
        lean_inc(val);
        read_log.push_back(ReadEntry{tvar_obj, cell, ver, val});
        if (read_log.size() == SMALL_SET_THRESHOLD + 1) {
            read_index.reserve(64);
            for (size_t i = 0; i < read_log.size(); ++i) {
                read_index[read_log[i].cell] = i;
            }
        } else if (read_log.size() > SMALL_SET_THRESHOLD) {
            read_index[cell] = idx;
        }
    }

    void put_write(b_lean_obj_arg tvar_obj, TVarCell* cell, lean_object* new_val) {
        size_t idx = find_write(cell);
        if (idx != SIZE_MAX) {
            if (!savepoints.empty() && idx < savepoints.back().write_size) {
                // Record previous value for potential `orElse` / `tryCatch` rollback
                undo_log.push_back(UndoEntry{idx, write_set[idx].val}); // transfers ownership of old val to undo_log
            } else {
                lean_dec(write_set[idx].val);
            }
            lean_inc(new_val);
            write_set[idx].val = new_val;
            return;
        }
        size_t new_idx = write_set.size();
        lean_inc(tvar_obj);
        lean_inc(new_val);
        write_set.push_back(WriteEntry{tvar_obj, cell, new_val});
        if (write_set.size() == SMALL_SET_THRESHOLD + 1) {
            write_index.reserve(64);
            for (size_t i = 0; i < write_set.size(); ++i) {
                write_index[write_set[i].cell] = i;
            }
        } else if (write_set.size() > SMALL_SET_THRESHOLD) {
            write_index[cell] = new_idx;
        }
    }

    uint64_t push_savepoint() {
        uint64_t sp_id = savepoints.size();
        savepoints.push_back(Savepoint{write_set.size(), undo_log.size()});
        return sp_id;
    }

    void rollback_to_savepoint(uint64_t sp_id) noexcept {
        if (sp_id >= savepoints.size()) return;
        Savepoint target = savepoints[sp_id];

        // 1. Replay undo_log in reverse order to restore overwritten earlier entries
        while (undo_log.size() > target.undo_size) {
            UndoEntry u = undo_log.back();
            undo_log.pop_back();
            lean_dec(write_set[u.write_idx].val);
            write_set[u.write_idx].val = u.prev_val; // transfers ownership back
        }

        // 2. Pop write_set entries added after the savepoint
        while (write_set.size() > target.write_size) {
            WriteEntry w = write_set.back();
            write_set.pop_back();
            if (!write_index.empty()) {
                write_index.erase(w.cell);
            }
            lean_dec(w.val);
            lean_dec(w.tvar_obj);
        }
        if (write_set.size() <= SMALL_SET_THRESHOLD && !write_index.empty()) {
            write_index.clear();
        }

        savepoints.resize(sp_id);
        // Crucial Harris-Marlow invariant: `read_log` is INTENTIONALLY preserved!
    }

    void commit_savepoint(uint64_t sp_id) noexcept {
        if (sp_id >= savepoints.size()) return;
        // If popping the outermost savepoint, we can discard undo entries since no enclosing savepoint exists.
        // If an enclosing savepoint `sp_id - 1` exists, entries targeting `< savepoints[sp_id - 1].write_size`
        // must remain in `undo_log` so the outer savepoint can still roll them back!
        if (sp_id == 0) {
            for (auto& u : undo_log) {
                if (u.prev_val != nullptr) lean_dec(u.prev_val);
            }
            undo_log.clear();
        }
        savepoints.resize(sp_id);
    }
};

static thread_local TxContext tls_tx;

// ---------------------------------------------------------------------------
// TxOutcome Constructor Helpers (matches `STM.TxOutcome` in `STM/FFI.lean`)
//   0 = ok (val : α)
//   1 = retry          -> lean_box(1)
//   2 = conflict       -> lean_box(2)
//   3 = userError err
// ---------------------------------------------------------------------------
static inline lean_obj_res mk_outcome_ok(lean_obj_arg val) noexcept {
    lean_object* r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, val);
    return r;
}

static inline lean_obj_res mk_outcome_conflict() noexcept {
    return lean_box(2);
}

// ---------------------------------------------------------------------------
// LSA Snapshot Extension (Riegel, Felber, Fetzer, DISC 2006)
// ---------------------------------------------------------------------------
static bool tl2_try_extend_snapshot(TxContext& tx) noexcept {
    uint64_t new_rv = g_tl2_clock.val.load(std::memory_order_acquire);
    for (const auto& r : tx.read_log) {
        uint64_t lv = r.cell->lock_ver.load(std::memory_order_acquire);
        if ((lv & 1) != 0) {
            // Only okay if locked by us? During execution phase we hold NO locks!
            return false;
        }
        if ((lv >> 1) != r.ver) {
            return false;
        }
    }
    tx.rv = new_rv;
    stats()->lsa_extensions.fetch_add(1, std::memory_order_relaxed);
    return true;
}

// ---------------------------------------------------------------------------
// NOrec Snapshot Validation (Dalessandro, Spear, Scott, PPoPP 2010)
// ---------------------------------------------------------------------------
static uint64_t norec_validate(TxContext& tx) noexcept {
    while (true) {
        uint64_t time = g_norec_loc.val.load(std::memory_order_acquire);
        if ((time & 1) != 0) {
            cpu_relax();
            continue;
        }
        for (const auto& r : tx.read_log) {
            if (r.cell->latest_val.load(std::memory_order_acquire) != r.val) {
                return UINT64_MAX;
            }
        }
        if (time == g_norec_loc.val.load(std::memory_order_acquire)) {
            return time;
        }
    }
}

// ---------------------------------------------------------------------------
// MVCC Ring Snapshot Lookup (Lock-Before-Clock Soundness Theorem)
// ---------------------------------------------------------------------------
static lean_object* mvcc_read_at(TVarCell* cell, uint64_t rv, uint64_t& out_ver) noexcept {
    // 1. Wait if a writer is mid-commit on `cell`. Because writers acquire all write locks BEFORE
    //    incrementing `g_tl2_clock` (Lock-Before-Clock theorem), any writer with `wv <= rv` was
    //    already holding `cell`'s lock when `rv` was sampled, so waiting for unlock guarantees
    //    `(wv, val)` is present in `cell->ring`!
    uint32_t spins = 0;
    while ((cell->lock_ver.load(std::memory_order_acquire) & 1) != 0) {
        if (++spins < 64) cpu_relax();
        else std::this_thread::yield();
    }

    EbrThreadNode* ebr = ebr_enter();
    uint64_t best_ver = 0;
    lean_object* best_val = nullptr;

    // Fast check: if current latest version <= rv and unlocked, grab it directly!
    uint64_t lv1 = cell->lock_ver.load(std::memory_order_acquire);
    if ((lv1 & 1) == 0 && (lv1 >> 1) <= rv) {
        lean_object* v = cell->latest_val.load(std::memory_order_acquire);
        uint64_t lv2 = cell->lock_ver.load(std::memory_order_acquire);
        if (lv1 == lv2 && v != nullptr) {
            lean_inc(v);
            ebr_exit(ebr);
            out_ver = lv1 >> 1;
            return v;
        }
    }

    // Otherwise scan the 8-slot historical version ring for max version <= rv
    for (size_t i = 0; i < MVCC_RING_SIZE; ++i) {
        uint64_t sv1 = cell->ring[i].version.load(std::memory_order_acquire);
        if (sv1 > 0 && sv1 <= rv && sv1 >= best_ver) {
            lean_object* sv_val = cell->ring[i].value.load(std::memory_order_acquire);
            uint64_t sv2 = cell->ring[i].version.load(std::memory_order_acquire);
            if (sv1 == sv2 && sv_val != nullptr) {
                best_ver = sv1;
                best_val = sv_val;
            }
        }
    }

    if (best_val != nullptr) {
        lean_inc(best_val);
        ebr_exit(ebr);
        out_ver = best_ver;
        return best_val;
    }

    ebr_exit(ebr);
    return nullptr; // Ring wrapped (> 8 concurrent commits to this exact TVar during our scan)
}

// ---------------------------------------------------------------------------
// Polka Randomized Exponential Contention Backoff (Scherer & Scott, PODC 2005)
// ---------------------------------------------------------------------------
static void polka_backoff(TxContext& tx) noexcept {
    if (tx.attempt <= 1) return;
    uint32_t shift = std::min<uint32_t>(tx.attempt - 1, 10u);
    uint32_t max_spins = (1u << shift);
    uint32_t spins = (tx.next_rand() & (max_spins - 1u)) + 1u;
    if (spins <= 256) {
        for (uint32_t i = 0; i < spins; ++i) cpu_relax();
    } else {
        std::this_thread::yield();
    }
}

// ---------------------------------------------------------------------------
// Commit Engine
// ---------------------------------------------------------------------------
static void publish_cell_update(TVarCell* cell, uint64_t wv, lean_object* new_val) noexcept {
    lean_mark_mt(new_val);

    // 1. Update inline MVCC version ring while holding `cell`'s write lock
    uint32_t h = cell->ring_head.load(std::memory_order_relaxed);
    size_t slot_idx = h & (MVCC_RING_SIZE - 1);
    lean_object* old_ring_val = cell->ring[slot_idx].value.load(std::memory_order_relaxed);
    cell->ring[slot_idx].version.store(0, std::memory_order_release); // invalidate during write
    lean_inc(new_val);
    cell->ring[slot_idx].value.store(new_val, std::memory_order_release);
    cell->ring[slot_idx].version.store(wv, std::memory_order_release);
    cell->ring_head.store(h + 1, std::memory_order_release);
    if (old_ring_val != nullptr) {
        ebr_retire(old_ring_val);
    }

    // 2. Update `latest_val` (+1 RC for TVarCell, retire old `latest_val` via EBR)
    lean_object* old_latest = cell->latest_val.load(std::memory_order_relaxed);
    lean_inc(new_val);
    cell->latest_val.store(new_val, std::memory_order_release);
    if (old_latest != nullptr) {
        ebr_retire(old_latest);
    }
}

static bool commit_tl2(TxContext& tx) noexcept {
    // Fast Path 1: Read-Only Transaction (0 writes)!
    // Every read was already validated against `tx.rv` (extended consistently via LSA if needed),
    // so the transaction linearizes at `tx.rv` with ZERO locks and ZERO clock writes!
    if (tx.write_set.empty()) {
        if (tx.mvcc_fallback_mode || tx.proto == PROTO_MVCC_RO) {
            stats()->mvcc_snapshots.fetch_add(1, std::memory_order_relaxed);
        }
        stats()->commits.fetch_add(1, std::memory_order_relaxed);
        tx.clear_all();
        return true;
    }

    // If we speculated in MVCC read-only fallback mode and then encountered a write,
    // restart in full TL2_LSA mode unless read_log validates at current latest!
    const size_t nw = tx.write_set.size();
    tx.lock_order.resize(nw);
    for (size_t i = 0; i < nw; ++i) tx.lock_order[i] = i;
    if (nw > 1) {
        std::sort(tx.lock_order.begin(), tx.lock_order.end(), [&](size_t a, size_t b) {
            return tx.write_set[a].cell->id < tx.write_set[b].cell->id;
        });
    }

    // Step C1: Acquire write locks in strictly ascending `TVarCell::id` order (Deadlock-Free!)
    size_t locked_count = 0;
    for (size_t k = 0; k < nw; ++k) {
        TVarCell* cell = tx.write_set[tx.lock_order[k]].cell;
        uint64_t lv = cell->lock_ver.load(std::memory_order_relaxed);
        if ((lv & 1) != 0) {
            // Already locked by another writer -> abort & release acquired locks
            for (size_t j = 0; j < locked_count; ++j) {
                TVarCell* held = tx.write_set[tx.lock_order[j]].cell;
                uint64_t hlv = held->lock_ver.load(std::memory_order_relaxed);
                held->lock_ver.store(hlv & ~1ULL, std::memory_order_release);
            }
            stats()->aborts_conflict.fetch_add(1, std::memory_order_relaxed);
            return false;
        }
        // Note: if `cell` was ALSO read by us, verify its version matches `read_log` (or `<= tx.rv`)
        // right as we CAS the lock bit!
        size_t r_idx = tx.find_read(cell);
        if (r_idx != SIZE_MAX && (lv >> 1) != tx.read_log[r_idx].ver) {
            for (size_t j = 0; j < locked_count; ++j) {
                TVarCell* held = tx.write_set[tx.lock_order[j]].cell;
                uint64_t hlv = held->lock_ver.load(std::memory_order_relaxed);
                held->lock_ver.store(hlv & ~1ULL, std::memory_order_release);
            }
            stats()->aborts_validation.fetch_add(1, std::memory_order_relaxed);
            return false;
        }
        if (!cell->lock_ver.compare_exchange_strong(
                lv, lv | 1ULL, std::memory_order_acq_rel, std::memory_order_relaxed)) {
            for (size_t j = 0; j < locked_count; ++j) {
                TVarCell* held = tx.write_set[tx.lock_order[j]].cell;
                uint64_t hlv = held->lock_ver.load(std::memory_order_relaxed);
                held->lock_ver.store(hlv & ~1ULL, std::memory_order_release);
            }
            stats()->aborts_conflict.fetch_add(1, std::memory_order_relaxed);
            return false;
        }
        ++locked_count;
    }

    // Step C2: Acquire Write Version `wv` AFTER holding all write locks (Lock-Before-Clock Invariant!)
    uint64_t wv = 0;
    if (tx.proto == PROTO_TL2_GV1) {
        wv = g_tl2_clock.val.fetch_add(1, std::memory_order_acq_rel) + 1;
    } else {
        // Safe Post-Lock GV4 CAS Clock (Autoresearch Winner — see EXP-05 in RESEARCH.md):
        // Load `c = g_tl2_clock` AFTER all write locks are held. Try CAS(c, c + 1).
        // Elides up to 78.6% of global clock increments at 16 threads, preventing spurious
        // `rv` invalidations on concurrent readers and writers!
        uint64_t c = g_tl2_clock.val.load(std::memory_order_seq_cst);
        uint64_t expected = c;
        if (g_tl2_clock.val.compare_exchange_strong(expected, c + 1, std::memory_order_seq_cst)) {
            wv = c + 1;
        } else {
            wv = expected;
            stats()->gv4_elisions.fetch_add(1, std::memory_order_relaxed);
        }
    }

    // Step C3: Validate `read_log` (skip only if `tx.rv + 1 == wv` and not in fallback mode,
    // because NO other transaction committed since `tx.rv`!)
    bool need_validate = !(tx.proto != PROTO_MVCC_RO && !tx.mvcc_fallback_mode && (tx.rv + 1 == wv));
    if (need_validate) {
        for (const auto& r : tx.read_log) {
            uint64_t lv = r.cell->lock_ver.load(std::memory_order_acquire);
            if ((lv & 1) != 0) {
                // Must be locked by US; if locked by us, we already checked `(lv >> 1) == r.ver` in Step C1!
                if (tx.find_write(r.cell) == SIZE_MAX) {
                    for (size_t j = 0; j < nw; ++j) {
                        TVarCell* held = tx.write_set[tx.lock_order[j]].cell;
                        uint64_t hlv = held->lock_ver.load(std::memory_order_relaxed);
                        held->lock_ver.store(hlv & ~1ULL, std::memory_order_release);
                    }
                    stats()->aborts_validation.fetch_add(1, std::memory_order_relaxed);
                    return false;
                }
            } else if ((lv >> 1) != r.ver) {
                for (size_t j = 0; j < nw; ++j) {
                    TVarCell* held = tx.write_set[tx.lock_order[j]].cell;
                    uint64_t hlv = held->lock_ver.load(std::memory_order_relaxed);
                    held->lock_ver.store(hlv & ~1ULL, std::memory_order_release);
                }
                stats()->aborts_validation.fetch_add(1, std::memory_order_relaxed);
                return false;
            }
        }
    }

    // Step C4: Publish all updated values into MVCC rings + `latest_val`, then release write locks
    for (size_t k = 0; k < nw; ++k) {
        const WriteEntry& we = tx.write_set[tx.lock_order[k]];
        publish_cell_update(we.cell, wv, we.val);
        we.cell->lock_ver.store(wv << 1, std::memory_order_release);
    }

    // Step C5: Single `seq_cst` Dekker fence + wake any `retry` waiters
    std::atomic_thread_fence(std::memory_order_seq_cst);
    for (size_t k = 0; k < nw; ++k) {
        TVarCell* cell = tx.write_set[tx.lock_order[k]].cell;
        if (cell->has_waiters.load(std::memory_order_relaxed) != 0) {
            cell->notify_all_waiters();
        }
    }

    stats()->commits.fetch_add(1, std::memory_order_relaxed);
    tx.clear_all();
    return true;
}

static bool commit_norec(TxContext& tx) noexcept {
    if (tx.write_set.empty()) {
        stats()->commits.fetch_add(1, std::memory_order_relaxed);
        tx.clear_all();
        return true;
    }

    while (!g_norec_loc.val.compare_exchange_weak(
        tx.rv, tx.rv + 1, std::memory_order_acq_rel, std::memory_order_relaxed)) {
        uint64_t new_rv = norec_validate(tx);
        if (new_rv == UINT64_MAX) {
            stats()->aborts_validation.fetch_add(1, std::memory_order_relaxed);
            return false;
        }
        tx.rv = new_rv;
    }

    // Holding global odd seqlock `tx.rv + 1`.
    // Enforce the Lock-Before-Clock Invariant (`t_lock < t_clk < t_unlock`) on `cell->lock_ver`
    // so concurrent `atomicallyReadOnly` (MVCC) readers stay 100% cross-protocol opaque!
    for (const auto& we : tx.write_set) {
        we.cell->lock_ver.fetch_or(1ULL, std::memory_order_acq_rel);
    }
    uint64_t wv = g_tl2_clock.val.fetch_add(1, std::memory_order_acq_rel) + 1;
    for (const auto& we : tx.write_set) {
        publish_cell_update(we.cell, wv, we.val);
        we.cell->lock_ver.store(wv << 1, std::memory_order_release);
    }

    g_norec_loc.val.store(tx.rv + 2, std::memory_order_release);

    std::atomic_thread_fence(std::memory_order_seq_cst);
    for (const auto& we : tx.write_set) {
        if (we.cell->has_waiters.load(std::memory_order_relaxed) != 0) {
            we.cell->notify_all_waiters();
        }
    }

    stats()->commits.fetch_add(1, std::memory_order_relaxed);
    tx.clear_all();
    return true;
}

// ---------------------------------------------------------------------------
// Dekker-Synchronized Modular `retry` Parking
// ---------------------------------------------------------------------------
static void park_on_read_set(TxContext& tx) noexcept {
    // Discard any uncommitted writes; retain `read_log` to know what to wait on!
    tx.clear_writes();

    if (tx.read_log.empty()) {
        // Calling `retry` having read 0 TVars can never be woken by a TVar mutation; yield briefly.
        std::this_thread::yield();
        tx.clear_reads();
        return;
    }

    // Validate read_log consistency first! Under Harris-Marlow Opacity, a transaction may ONLY
    // block in `retry` if its reads formed a valid snapshot (otherwise an inconsistent view could
    // cause a spurious `retry`!).
    if (tx.proto == PROTO_NOREC) {
        if (norec_validate(tx) == UINT64_MAX) {
            tx.clear_reads();
            return; // Snapshot already changed -> retry immediately without sleeping!
        }
    } else {
        for (const auto& r : tx.read_log) {
            uint64_t lv = r.cell->lock_ver.load(std::memory_order_acquire);
            if ((lv & 1) != 0 || (lv >> 1) != r.ver) {
                tx.clear_reads();
                return; // A TVar in read_log ALREADY changed -> retry immediately!
            }
        }
    }

    // Deduplicate and sort `read_log` by `cell->id` so `wait_mtx` acquisition is deadlock-free
    struct ParkItem {
        TVarCell* cell;
        uint64_t ver;
        lean_object* val;
    };
    std::vector<ParkItem> items;
    items.reserve(tx.read_log.size());
    for (const auto& r : tx.read_log) {
        items.push_back(ParkItem{r.cell, r.ver, r.val});
    }
    std::sort(items.begin(), items.end(), [](const ParkItem& a, const ParkItem& b) {
        return a.cell->id < b.cell->id;
    });
    items.erase(
        std::unique(items.begin(), items.end(), [](const ParkItem& a, const ParkItem& b) {
            return a.cell == b.cell;
        }),
        items.end());

    ParkedThread waiter;
    std::vector<WaitNode> nodes(items.size());
    size_t registered = 0;
    bool changed = false;

    for (size_t i = 0; i < items.size(); ++i) {
        TVarCell* cell = items[i].cell;
        std::lock_guard<std::mutex> lk(cell->wait_mtx);

        nodes[i].waiter = &waiter;
        nodes[i].prev = nullptr;
        nodes[i].next = cell->wait_head;
        if (cell->wait_head != nullptr) {
            cell->wait_head->prev = &nodes[i];
        }
        cell->wait_head = &nodes[i];
        nodes[i].linked = true;
        ++registered;

        cell->has_waiters.fetch_add(1, std::memory_order_seq_cst);
        std::atomic_thread_fence(std::memory_order_seq_cst);

        // Double-check version / value AFTER publishing `has_waiters > 0`
        if (tx.proto == PROTO_NOREC) {
            if ((g_norec_loc.val.load(std::memory_order_acquire) & 1) != 0 ||
                cell->latest_val.load(std::memory_order_acquire) != items[i].val) {
                changed = true;
                break;
            }
        } else {
            uint64_t lv = cell->lock_ver.load(std::memory_order_acquire);
            if ((lv & 1) != 0 || (lv >> 1) != items[i].ver) {
                changed = true;
                break;
            }
        }
    }

    if (!changed) {
        stats()->retries_parked.fetch_add(1, std::memory_order_relaxed);
        std::unique_lock<std::mutex> wlk(waiter.mtx);
        waiter.cv.wait(wlk, [&]() { return waiter.notified.load(std::memory_order_acquire); });
    }

    // Unlink all registered nodes cleanly
    for (size_t i = 0; i < registered; ++i) {
        TVarCell* cell = items[i].cell;
        std::lock_guard<std::mutex> lk(cell->wait_mtx);
        if (nodes[i].linked) {
            if (nodes[i].prev != nullptr) nodes[i].prev->next = nodes[i].next;
            else cell->wait_head = nodes[i].next;
            if (nodes[i].next != nullptr) nodes[i].next->prev = nodes[i].prev;
            nodes[i].linked = false;
            cell->has_waiters.fetch_sub(1, std::memory_order_seq_cst);
        }
    }

    tx.clear_reads();
}

} // namespace lean_stm

// ===========================================================================
// Exported C ABI Symbols for Lean 4 (`STM/FFI.lean`)
// ===========================================================================
using namespace lean_stm;

extern "C" {

// Create a TVar in `BaseIO` (outside or inside a transaction)
LEAN_EXPORT lean_obj_res lean_stm_tvar_new_io(lean_obj_arg init_val) {
    lean_mark_mt(init_val);
    uint64_t id = g_next_tvar_id.val.fetch_add(1, std::memory_order_relaxed);
    uint64_t ver = g_tl2_clock.val.load(std::memory_order_acquire);
    TVarCell* cell = new TVarCell(id, ver, init_val);
    lean_object* ext = lean_alloc_external(get_tvar_class(), cell);
    lean_mark_mt(ext);
    return ext;
}

// Create a TVar inside an active `STM` transaction (version = `tx.rv` so immediate reads succeed!)
LEAN_EXPORT lean_obj_res lean_stm_tvar_new_tx(lean_obj_arg init_val) {
    lean_mark_mt(init_val);
    uint64_t id = g_next_tvar_id.val.fetch_add(1, std::memory_order_relaxed);
    uint64_t ver = tls_tx.active ? std::max<uint64_t>(1ULL, tls_tx.rv)
                                 : g_tl2_clock.val.load(std::memory_order_acquire);
    TVarCell* cell = new TVarCell(id, ver, init_val);
    lean_object* ext = lean_alloc_external(get_tvar_class(), cell);
    lean_mark_mt(ext);
    return mk_outcome_ok(ext);
}

// Non-transactional fast peek (`TVar.readIO` — consistent single-variable atomic snapshot via EBR!)
LEAN_EXPORT lean_obj_res lean_stm_tvar_read_io(b_lean_obj_arg tvar_obj) {
    TVarCell* cell = get_cell(tvar_obj);
    EbrThreadNode* ebr = ebr_enter();
    lean_object* val = cell->latest_val.load(std::memory_order_acquire);
    lean_inc(val);
    ebr_exit(ebr);
    return val;
}

// Pointer/ID equality and deterministic TVar ID retrieval
LEAN_EXPORT uint64_t lean_stm_tvar_id(b_lean_obj_arg tvar_obj) {
    return get_cell(tvar_obj)->id;
}

// Begin a transaction attempt on the current OS worker thread
LEAN_EXPORT lean_obj_res lean_stm_tx_begin(uint8_t proto_raw, uint32_t attempt) {
    TxContext& tx = tls_tx;
    if (tx.active) {
        tx.clear_all();
    }
    if (attempt > 0) {
        tx.prev_attempt_wrote = tx.current_wrote;
        tx.attempt = attempt;
        polka_backoff(tx);
    } else {
        tx.prev_attempt_wrote = false;
        tx.attempt = 0;
    }
    tx.current_wrote = false;

    StmProtocol proto = static_cast<StmProtocol>(proto_raw);
    tx.proto = proto;
    tx.active = true;

    // Adaptive Hybrid TL2-MVCC: if a TL2_LSA transaction has aborted >= 3 times without having
    // buffered any writes on the prior attempt, switch transparently to wait-free MVCC ring reads!
    tx.mvcc_fallback_mode =
        (proto == PROTO_MVCC_RO) || (proto == PROTO_TL2_LSA && attempt >= 3 && !tx.prev_attempt_wrote);

    if (proto == PROTO_NOREC) {
        uint64_t loc = g_norec_loc.val.load(std::memory_order_acquire);
        while ((loc & 1) != 0) {
            cpu_relax();
            loc = g_norec_loc.val.load(std::memory_order_acquire);
        }
        tx.rv = loc;
    } else {
        tx.rv = g_tl2_clock.val.load(std::memory_order_acquire);
    }
    return lean_box(0);
}

// Transactional Read: returns `TxOutcome α` (`ok val` or `conflict`)
LEAN_EXPORT lean_obj_res lean_stm_tvar_read(b_lean_obj_arg tvar_obj) {
    TxContext& tx = tls_tx;
    TVarCell* cell = get_cell(tvar_obj);

    // 1. Read-After-Write Forwarding (L1 local write buffer)
    size_t w_idx = tx.find_write(cell);
    if (w_idx != SIZE_MAX) {
        lean_object* v = tx.write_set[w_idx].val;
        lean_inc(v);
        return mk_outcome_ok(v);
    }

    // 2. Idempotent Re-Read Forwarding (if already read in this snapshot, return exact value in O(1)!)
    size_t r_idx = tx.find_read(cell);
    if (r_idx != SIZE_MAX) {
        lean_object* v = tx.read_log[r_idx].val;
        lean_inc(v);
        return mk_outcome_ok(v);
    }

    // 3. Protocol-specific read
    if (tx.proto == PROTO_NOREC) {
        EbrThreadNode* ebr = ebr_enter();
        lean_object* val = cell->latest_val.load(std::memory_order_acquire);
        while (tx.rv != g_norec_loc.val.load(std::memory_order_acquire)) {
            ebr_exit(ebr);
            uint64_t new_rv = norec_validate(tx);
            if (new_rv == UINT64_MAX) {
                stats()->aborts_validation.fetch_add(1, std::memory_order_relaxed);
                return mk_outcome_conflict();
            }
            tx.rv = new_rv;
            ebr = ebr_enter();
            val = cell->latest_val.load(std::memory_order_acquire);
        }
        lean_inc(val);
        ebr_exit(ebr);
        tx.insert_read(tvar_obj, cell, 0, val);
        return mk_outcome_ok(val);
    }

    if (tx.mvcc_fallback_mode) {
        uint64_t observed_ver = 0;
        lean_object* val = mvcc_read_at(cell, tx.rv, observed_ver);
        if (val == nullptr) {
            stats()->aborts_validation.fetch_add(1, std::memory_order_relaxed);
            return mk_outcome_conflict();
        }
        tx.insert_read(tvar_obj, cell, observed_ver, val);
        return mk_outcome_ok(val);
    }

    // Standard TL2 / TL2-LSA Read Path (Zero shared cache-line writes!)
    EbrThreadNode* ebr = ebr_enter();
    uint64_t lv1 = cell->lock_ver.load(std::memory_order_acquire);
    if ((lv1 & 1) != 0) {
        ebr_exit(ebr);
        stats()->aborts_conflict.fetch_add(1, std::memory_order_relaxed);
        return mk_outcome_conflict();
    }
    lean_object* val = cell->latest_val.load(std::memory_order_acquire);
    uint64_t lv2 = cell->lock_ver.load(std::memory_order_acquire);
    if (lv1 != lv2) {
        ebr_exit(ebr);
        stats()->aborts_conflict.fetch_add(1, std::memory_order_relaxed);
        return mk_outcome_conflict();
    }
    lean_inc(val);
    ebr_exit(ebr);

    uint64_t ver = lv1 >> 1;
    if (ver > tx.rv) {
        if (tx.proto == PROTO_TL2_LSA && tl2_try_extend_snapshot(tx) && ver <= tx.rv) {
            // Snapshot extended seamlessly!
        } else {
            lean_dec(val);
            stats()->aborts_validation.fetch_add(1, std::memory_order_relaxed);
            return mk_outcome_conflict();
        }
    }

    tx.insert_read(tvar_obj, cell, ver, val);
    return mk_outcome_ok(val);
}

// Transactional Write: returns `0` on ok, `2` on conflict (if MVCC read-only mode violated)
LEAN_EXPORT uint8_t lean_stm_tvar_write(b_lean_obj_arg tvar_obj, lean_obj_arg new_val) {
    TxContext& tx = tls_tx;
    if (tx.proto == PROTO_MVCC_RO) {
        // Explicit read-only snapshot transaction attempted a write -> upgrade/restart cleanly
        lean_dec(new_val);
        return 2;
    }
    if (tx.mvcc_fallback_mode) {
        // Adaptive fallback encountered a write: verify all MVCC reads still match current latest!
        for (const auto& r : tx.read_log) {
            uint64_t lv = r.cell->lock_ver.load(std::memory_order_acquire);
            if ((lv & 1) != 0 || (lv >> 1) != r.ver) {
                lean_dec(new_val);
                stats()->aborts_validation.fetch_add(1, std::memory_order_relaxed);
                return 2;
            }
        }
        tx.mvcc_fallback_mode = false;
    }
    TVarCell* cell = get_cell(tvar_obj);
    tx.current_wrote = true;
    tx.put_write(tvar_obj, cell, new_val);
    lean_dec(new_val); // `put_write` took its own `+1` RC
    return 0;
}

// Nested Savepoints for `orElse` (`<|>`) and `tryCatch`
LEAN_EXPORT uint64_t lean_stm_tx_savepoint() {
    return tls_tx.push_savepoint();
}

LEAN_EXPORT lean_obj_res lean_stm_tx_rollback_savepoint(uint64_t sp_id) {
    tls_tx.rollback_to_savepoint(sp_id);
    return lean_box(0);
}

LEAN_EXPORT lean_obj_res lean_stm_tx_commit_savepoint(uint64_t sp_id) {
    tls_tx.commit_savepoint(sp_id);
    return lean_box(0);
}

// Commit current transaction: returns `true` (1) if committed, `false` (0) if conflict/validation failed
LEAN_EXPORT uint8_t lean_stm_tx_commit() {
    TxContext& tx = tls_tx;
    bool ok = (tx.proto == PROTO_NOREC) ? commit_norec(tx) : commit_tl2(tx);
    if (!ok) {
        tx.clear_all();
    }
    return ok ? 1 : 0;
}

// Abort & clear current transaction (used on uncaught user error or conflict reset)
LEAN_EXPORT lean_obj_res lean_stm_tx_abort() {
    tls_tx.clear_all();
    return lean_box(0);
}

// Park on current `read_log` for modular `retry`
LEAN_EXPORT lean_obj_res lean_stm_tx_park_retry() {
    park_on_read_set(tls_tx);
    return lean_box(0);
}

// Global Default Protocol Configuration
LEAN_EXPORT uint8_t lean_stm_get_default_protocol() {
    return g_default_protocol.load(std::memory_order_acquire);
}

LEAN_EXPORT lean_obj_res lean_stm_set_default_protocol(uint8_t proto) {
    if (proto <= PROTO_NOREC) {
        g_default_protocol.store(proto, std::memory_order_release);
    }
    return lean_box(0);
}

// Telemetry Snapshot & Reset (`STM.Stats` in Lean: 7 UInt64 fields = 0 obj fields, 56 scalar bytes)
LEAN_EXPORT lean_obj_res lean_stm_get_stats() {
    RawStats agg{};
    {
        std::lock_guard<std::mutex> lk(g_stats_mtx);
        agg = g_exited_stats;
        for (ThreadStatsNode* p = g_stats_head; p != nullptr; p = p->next) {
            agg.commits           += p->commits.load(std::memory_order_relaxed);
            agg.aborts_conflict   += p->aborts_conflict.load(std::memory_order_relaxed);
            agg.aborts_validation += p->aborts_validation.load(std::memory_order_relaxed);
            agg.retries_parked    += p->retries_parked.load(std::memory_order_relaxed);
            agg.lsa_extensions    += p->lsa_extensions.load(std::memory_order_relaxed);
            agg.mvcc_snapshots    += p->mvcc_snapshots.load(std::memory_order_relaxed);
            agg.gv4_elisions      += p->gv4_elisions.load(std::memory_order_relaxed);
        }
    }
    lean_object* res = lean_alloc_ctor(0, 0, 7 * sizeof(uint64_t));
    uint64_t* payload = reinterpret_cast<uint64_t*>(lean_ctor_scalar_cptr(res));
    payload[0] = agg.commits;
    payload[1] = agg.aborts_conflict;
    payload[2] = agg.aborts_validation;
    payload[3] = agg.retries_parked;
    payload[4] = agg.lsa_extensions;
    payload[5] = agg.mvcc_snapshots;
    payload[6] = agg.gv4_elisions;
    return res;
}

LEAN_EXPORT lean_obj_res lean_stm_reset_stats() {
    std::lock_guard<std::mutex> lk(g_stats_mtx);
    g_exited_stats = RawStats{};
    for (ThreadStatsNode* p = g_stats_head; p != nullptr; p = p->next) {
        p->commits.store(0, std::memory_order_relaxed);
        p->aborts_conflict.store(0, std::memory_order_relaxed);
        p->aborts_validation.store(0, std::memory_order_relaxed);
        p->retries_parked.store(0, std::memory_order_relaxed);
        p->lsa_extensions.store(0, std::memory_order_relaxed);
        p->mvcc_snapshots.store(0, std::memory_order_relaxed);
        p->gv4_elisions.store(0, std::memory_order_relaxed);
    }
    return lean_box(0);
}

} // extern "C"

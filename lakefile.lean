import Lake
open System Lake DSL

package «lean-stm» where
  version := v!"0.1.0"

input_file lean_stm.cpp where
  path := "c" / "lean_stm.cpp"
  text := true

target lean_stm.o pkg : FilePath := do
  let srcJob ← lean_stm.cpp.fetch
  let oFile := pkg.buildDir / "c" / "lean_stm.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O3", "-std=c++20", "-Wall", "-Wextra", "-Wno-unused-parameter"] "c++" getLeanTrace

target libleanstm pkg : FilePath := do
  let ffiO ← lean_stm.o.fetch
  let name := nameToStaticLib "leanstm"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

@[default_target]
lean_lib STM where
  moreLinkObjs := #[libleanstm]

lean_exe «stm-test» where
  root := `Tests.Main
  moreLinkObjs := #[libleanstm]

lean_exe «stm-bench» where
  root := `Bench.Main
  moreLinkObjs := #[libleanstm]

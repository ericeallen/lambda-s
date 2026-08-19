import Lake
open Lake DSL

package lambdas where
  -- Accelerate supplies cblas on Apple platforms; elsewhere the C shim falls
  -- back to portable loops and no framework is needed.
  moreLinkArgs := if System.Platform.isOSX then
    #["-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib", "-lblas"] else #[]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.33.0"

target lambdas_blas.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "lambdas_blas.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "lambdas_blas.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2"]
  buildO oFile srcJob flags

extern_lib liblambdasblas pkg := do
  let ffiO ← fetch <| pkg.target ``lambdas_blas.o
  buildStaticLib (pkg.staticLibDir / "liblambdasblas.a") #[ffiO]

@[default_target]
lean_lib LambdaS

@[default_target]
lean_exe lambdas where
  root := `Main
  supportInterpreter := true

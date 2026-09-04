/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.QM
import LambdaS.Algorithms

/-!
The compiled entry point. `lake build lambdas` runs Lean's code generator over
`LambdaS.Dynamics.eval` at the `Float` instance, emits C, and links a native
binary, so the evaluator that `unit_soundness_total` and `erasure_correct` are
proved about is the one that executes. The exit status carries the run-time
verdict: a failed numeric check exits nonzero, so the binary can fail a CI
step, not merely print.
-/

def main : IO UInt32 := do
  IO.println LambdaS.QM.report
  IO.println LambdaS.Algorithms.report
  IO.println LambdaS.Algorithms.reportDecl
  IO.println LambdaS.QM.twoStateReport
  if LambdaS.QM.twoStateChecks then
    return 0
  else
    IO.eprintln "numeric checks FAILED"
    return 1

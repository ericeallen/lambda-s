import LambdaS.QM
import LambdaS.Algorithms

/-!
The compiled entry point. `lake build lambdas` runs Lean's code generator over
`LambdaS.Dynamics.eval` at the `Float` instance, emits C, and links a native
binary — so the evaluator that `unit_soundness_total` and `erasure_correct` are
proved about is the one that executes.
-/

def main : IO Unit := do
  IO.println LambdaS.QM.report
  IO.println LambdaS.Algorithms.report
  IO.println LambdaS.QM.twoStateReport

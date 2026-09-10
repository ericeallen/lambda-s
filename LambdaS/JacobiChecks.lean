/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Examples

/-!
# Numerical checks for the Jacobi example

These checks run the actual `sweep`, `stopRelative`, and `stopAbsolute` terms
through the Float evaluator in the native binary. Matrix composition reaches
the C dot-product implementation, so these are run-time checks, not `#guard`
assertions. The typing and parametricity checks remain in `Examples`.

The sweep checks cover 125 finite symmetric matrices with positive, negative,
and zero off-diagonals, and equal or unequal diagonals. They check the result,
not the formula used to construct the rotation: both off-diagonals must vanish,
symmetry must hold, and trace and determinant must be preserved. The tolerance
is `1e-12 * max(1, |expected|)` for these small test matrices. This is not an
error bound for arbitrary floating-point inputs.
-/

namespace LambdaS.JacobiChecks

open LambdaS.Examples

/-- The three independent entries of a symmetric two-by-two input. -/
structure SymmetricInput where
  a : Float
  b : Float
  d : Float

/-- A result with exactly two rows and two columns. -/
structure MatrixResult where
  a : Float
  b : Float
  c : Float
  d : Float

private def run (term : Term₀) (input : SymmetricInput) : Option MatrixResult :=
  match evalC (D := Dim) (fun _ _ => (1.0 : Float)) 0
      [.matrix [[input.a, input.b], [input.b, input.d]] U2 U2d] term with
  | some (.matrix [[a, b], [c, d]] _ _) => some ⟨a, b, c, d⟩
  | _ => none

private def finite (x : Float) : Bool := !x.isNaN && !x.isInf

private def close (actual expected : Float) : Bool :=
  finite actual && finite expected &&
    decide (Float.abs (actual - expected) ≤ 1e-12 * max 1.0 (Float.abs expected))

private def diagonalized (input : SymmetricInput) (output : MatrixResult) : Bool :=
  close output.b 0 && close output.c 0 && close output.b output.c &&
    close (output.a + output.d) (input.a + input.d) &&
    close (output.a * output.d - output.b * output.c)
      (input.a * input.d - input.b * input.b)

private def unchanged (input : SymmetricInput) (output : MatrixResult) : Bool :=
  output.a == input.a && output.b == input.b &&
    output.c == input.b && output.d == input.d

private def sweepInputs : List SymmetricInput :=
  ([-3.0, -1.0, 0.0, 1.0, 3.0] : List Float).flatMap fun a =>
    ([-2.0, -1.0, 0.0, 1.0, 2.0] : List Float).flatMap fun b =>
      ([-3.0, -1.0, 0.0, 1.0, 3.0] : List Float).map fun d => ⟨a, b, d⟩

private def sweepPasses (input : SymmetricInput) : Bool :=
  (run sweep input).any fun output =>
    diagonalized input output && (input.b != 0 || unchanged input output)

/-- Expected branch decisions are supplied independently of the stopping code. -/
structure StopCase where
  name : String
  input : SymmetricInput
  relativeStops : Bool
  absoluteStops : Bool

private def stopCases : List StopCase :=
  [⟨"positive residual", ⟨1, 1, 3⟩, false, false⟩,
   ⟨"negative residual", ⟨1, -1, 3⟩, false, false⟩,
   ⟨"negative diagonals", ⟨-1, -1, -3⟩, false, false⟩,
   ⟨"zero diagonal scale", ⟨0, -1, 0⟩, false, false⟩,
   ⟨"already diagonal", ⟨-1, 0, -3⟩, true, true⟩,
   ⟨"zero matrix", ⟨0, 0, 0⟩, true, true⟩,
   ⟨"small positive residual", ⟨-1, 5e-10, -3⟩, true, true⟩,
   ⟨"small negative residual", ⟨-1, -5e-10, -3⟩, true, true⟩,
   ⟨"relative scale, positive", ⟨-1, 2e-9, -3⟩, true, false⟩,
   ⟨"relative scale, negative", ⟨-1, -2e-9, -3⟩, true, false⟩,
   ⟨"absolute boundary", ⟨1, 1e-9, 3⟩, true, true⟩,
   ⟨"relative boundary", ⟨-1, -3e-9, -3⟩, true, false⟩]

private def stoppingPasses (term : Term₀) (input : SymmetricInput)
    (shouldStop : Bool) : Bool :=
  (run term input).any fun output =>
    if shouldStop then unchanged input output
    else !unchanged input output && diagonalized input output

private def stopPasses (test : StopCase) : Bool :=
  stoppingPasses stopRelative test.input test.relativeStops &&
    stoppingPasses stopAbsolute test.input test.absoluteStops

/-- All numerical Jacobi regressions; `main` exits nonzero on a failure. -/
def allChecks : Bool := sweepInputs.all sweepPasses && stopCases.all stopPasses

/-- Report failed inputs individually, so a failure can be reproduced. -/
def report : String :=
  let failedSweeps := sweepInputs.filter fun input => !sweepPasses input
  let failedStops := stopCases.filter fun test => !stopPasses test
  let sweepDetails := failedSweeps.map fun input =>
    s!"  FAILED sweep: a={input.a}, b={input.b}, d={input.d}\n"
  let stopDetails := failedStops.map fun test => s!"  FAILED stopping: {test.name}\n"
  s!"Jacobi: {sweepInputs.length} sweeps, {stopCases.length} stopping cases, all={allChecks}\n"
    ++ String.join (sweepDetails ++ stopDetails)

end LambdaS.JacobiChecks

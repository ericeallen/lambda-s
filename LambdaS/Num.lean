/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The numeric carrier

The evaluator in `LambdaS.Dynamics` is generic in its numbers, and one
definition serves both masters: the section below spells out the two
instances.

Everything about units is carrier-independent, which is why the proofs never
mention `Num` beyond threading it: unit soundness and erasure are statements
about which branch an evaluator takes, not about arithmetic.

## What the two instances demonstrate

`ℝ` and `Float` are the same definition read two ways. At `ℝ` the evaluator is
the object the soundness and erasure theorems are about, and necessarily
noncomputable since `Real.exp` is. At `Float` it is compiled to C. Nothing about
units differs between them, which is the point: the dimensional content of the
calculus is carrier-independent, and a carrier can be swapped (for complex
amplitudes, intervals, dual numbers for differentiation) without touching the
type system or a single theorem.

## Positivity

`nroot` and `nlog` assume a positive argument, which is the same assumption that
appears in `relQ_rpow` (where `rpow` needs `0 ≤ x`) and in Kennedy's Pi
theorem. Λs's `root` is applied to positive magnitudes in practice, but the
language does not enforce it.
-/

namespace LambdaS

/-! ## The native kernel

`LambdaS.Map` proves the units of a linear map are rank-one (entry `(j,i)`
carries `δ_W(j)/δ_V(i)`), so an `m×n` map needs `m+n` units rather than `mn`, and
those live in the *type*. By the time a numeric kernel runs, the checker has
discharged every dimensional obligation and the payload is a flat array of
doubles: no tagging, no strides, no per-entry metadata.

That is the substantive claim, and these two declarations test it. Both are
`@[extern]`, so the compiled binary calls C; the Lean bodies are the fallbacks
the interpreter uses and the definitions the theorems see. Swapping the C loops
for `cblas_ddot` and `cblas_dgemv` is a one-line change in `c/lambdas_blas.c`;
they are written out only so the build has no external dependency.

The trust boundary is the usual FFI one: the C is assumed to agree with the Lean
body, and the compiled checks in `LambdaS.QM` exercise it on real data. -/

/-- Inner product of two flat vectors. -/
@[extern "lambdas_ddot"]
def ddot (a x : @& FloatArray) : Float := Id.run do
  let mut s := 0.0
  for i in [0 : min a.size x.size] do
    s := s + a.get! i * x.get! i
  return s

/-- Matrix–vector product, `a` row-major `m×n`: **one** call per product, which
is the shape `cblas_dgemv` wants.

Written as a `map` over `Array.range` rather than a push loop so that the size of
the result is manifest: `dgemv_size` is what the soundness proof needs, and the
C is trusted to agree with this body. -/
@[extern "lambdas_dgemv"]
def dgemv (m n : @& Nat) (a x : @& FloatArray) : FloatArray :=
  ⟨(Array.range m).map fun i =>
    (List.range n).foldl (fun s j => s + a.get! (i * n + j) * x.get! j) 0.0⟩

@[simp] theorem dgemv_size (m n : Nat) (a x : FloatArray) :
    (dgemv m n a x).data.size = m := by simp [dgemv]

/-- Which numeric backend the binary was compiled against. -/
@[extern "lambdas_blas_backend"]
def blasBackend : Unit → String := fun _ => "Lean fallback"

/-- The numeric operations an evaluator needs. -/
class Num (R : Type) where
  ofRat : ℚ → R
  add : R → R → R
  mul : R → R → R
  div : R → R → R
  /-- The `n`-th root. Primitive because it is not definable from the field
  operations; see `LambdaS.NonDef.sqrt_not_definable`. -/
  nroot : ℕ → R → R
  nlog : R → R
  nexp : R → R
  /-- Inner product. Defaulted to a fold; carriers with a native kernel override
  it. -/
  dot : List R → List R → R := fun xs ys =>
    (List.zipWith mul xs ys).foldl add (ofRat 0)
  /-- **Batched** matrix–vector product, the operation `eval` performs when it
  applies a linear map. Defaulted to a row-at-a-time fold; carriers with a
  native kernel override it with a single call. -/
  matVec : List (List R) → List R → List R := fun M x => M.map fun r => dot r x
  /-- The result has one entry per row. A law rather than a theorem, because the
  overriding instance decides how the product is computed and the soundness
  proof needs the length regardless. -/
  matVec_length : ∀ M x, (matVec M x).length = M.length := by intro M x; simp

/-- The carrier the theorems are about. Noncomputable, as `Real.exp` forces. -/
noncomputable instance : Num ℝ where
  ofRat q := (q : ℝ)
  add := (· + ·)
  mul := (· * ·)
  div := (· / ·)
  nroot n x := x ^ ((1 : ℝ) / (n : ℝ))
  nlog := Real.log
  nexp := Real.exp

/-- Real double precision. -/
instance : Num Float where
  ofRat q := Float.ofInt q.num / Float.ofNat q.den
  add := (· + ·)
  mul := (· * ·)
  div := (· / ·)
  nroot n x := Float.pow x (1.0 / Float.ofNat n)
  nlog := Float.log
  nexp := Float.exp
  dot xs ys := ddot ⟨xs.toArray⟩ ⟨ys.toArray⟩
  matVec M x := (dgemv M.length x.length ⟨M.flatten.toArray⟩ ⟨x.toArray⟩).data.toList
  matVec_length := by intro M x; simp

end LambdaS

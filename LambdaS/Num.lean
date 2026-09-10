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

Typing is independent of the numeric carrier. Unit soundness, termination,
and erasure hold for every `Num` instance. Abstraction requires additional
arithmetic laws, and numerical adequacy is stated at the real instance.

## What the two instances demonstrate

`ℝ` and `Float` are the same definition read two ways. At `ℝ` the evaluator is
the object the soundness and erasure theorems are about, and necessarily
noncomputable since `Real.exp` is. At `Float` it is compiled to C. Changing the carrier preserves the type system and the carrier-generic
results above. A new carrier must separately supply the laws required by any
abstraction theorem; the real adequacy theorem does not establish its numerical
correspondence with that carrier.

## Positivity

`npow` and `nlog` are meaningful on positive arguments. Λs's `pow` is applied
to positive magnitudes in practice, but the language does not enforce it,
because enforcing it would exclude signed quantities from the calculus. For negative arguments, the two carriers use different conventions for
non-integer powers. `Real.rpow` is the real part of the principal complex
power, so `(-8) ^ (1/3 : ℝ)` denotes `1`, not the real cube root. `Float.pow`
returns `NaN` for a negative base and a non-integer floating-point exponent.
This is a choice of totalization, not a claim that real odd roots do not
exist. No theorem equates the compiled result with the real semantics.
The invariance theory
needs no positivity (`relQ_rpow` carries no sign hypothesis, because a
positive scale factor distributes over `rpow` at every real base); Kennedy's
Pi theorem still does.
-/

namespace LambdaS

/-! ## The native kernel

`LambdaS.Map` proves the units of a linear map are rank-one (entry `(j,i)`
carries `δ_W(j)/δ_V(i)`), so an `m×n` map needs `m+n` units rather than `mn`, and
those live in the *type*. By the time a numeric kernel runs, the checker has
discharged every dimensional obligation and the payload is a flat array of
doubles: no tagging, no strides, no per-entry metadata.

That is the substantive claim, and these two declarations test it. Both are
`@[extern]`, so the compiled binary calls C (`c/lambdas_blas.c`); the Lean
bodies are the fallbacks the interpreter uses and the definitions the theorems
see. On Apple platforms the C calls Accelerate's `cblas_ddot` and
`cblas_dgemv`; elsewhere it runs portable loops, so the build has no external
dependency. `blasBackend` reports which was compiled in.

The trust boundary is the usual FFI one: the C is assumed to agree with the Lean
body, and the compiled checks in `LambdaS.QM` exercise it on real data. The
agreement has one precondition, that the flat array holds `m × n` doubles; the
Lean body reads out of range through `get!` and the C checks the sizes and
aborts. `ddot` truncates to the shorter vector in both. -/

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
  /-- A constant rational power. Primitive because it is not definable from
  the field operations; see `LambdaS.NonDef.sqrt_not_definable`. -/
  npow : ℚ → R → R
  nlog : R → R
  nexp : R → R
  /-- **Comparison.** The one observation a conditional makes. Quantities are
  comparable only at a common unit (`T-IfLe`). Positive-rescaling invariance
  is an additional law supplied by `OrderedNum`, not a requirement of `Num`. -/
  le : R → R → Bool
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
  npow q x := x ^ ((q : ℚ) : ℝ)
  nlog := Real.log
  nexp := Real.exp
  le x y := decide (x ≤ y)

/-- **Carriers whose comparison survives a rescaling.**

Separate from `Num` on purpose: the evaluator needs `le` to run, but only the
abstraction theorems need it to be *invariant*, and `Float` cannot supply that.
Multiplication rounds, so `c * x` and `c * y` can compare differently from `x`
and `y` at subnormals and near overflow. Making this a field of `Num` would
therefore have forced either a false law or a `sorry`.

The split is the same one the development already draws elsewhere: theorems
over `ℝ`, binary over `Float`, with the places they part ways pinned rather
than papered over (`QM.boundaryChecks`). The
abstraction theorems live in the denotational semantics over `ℝ` and never
mention this class, so nothing here is newly unproved; `Float` has never
satisfied an arithmetic identity and was never asked to.

What differs is the *consequence* of rounding. In `add` and `mul` it perturbs a
number. In `le` it changes which branch runs, so a unit change can alter
control flow rather than the last bits, and that is the failure a user would
actually be ambushed by.

There is a useful sufficient condition, and it is narrower than "rescale by a
power of two". Multiplication by `2^k` shifts the exponent and leaves the
significand alone, so it is exact **provided both scaled results are finite
and normal**. Under that proviso the comparison is preserved. It is the case
that matters in practice: a compiler rescaling to keep magnitudes near 1 picks
binary powers because they are free and exact.

The proviso is not decoration. Both counterexamples below are rescalings by a
power of two, and both flip the comparison:

* Overflow. `1.7e308 ≤ 1e308` is `false`; after multiplying both by `2` each
  operand is `inf`, and `inf ≤ inf` is `true`.
* Underflow. `1e-323 ≤ 5e-324` is `false`; after multiplying both by `0.25`
  each operand is `0.0`, and `0.0 ≤ 0.0` is `true`.

Note what these refute besides the unconditional law: the operands differ by
seventy percent in the first case, so it is not true that a branch can flip
only when the two sides are within rounding of each other. Rounding to a
common `inf` or a common `0.0` destroys a wide separation in one step.

Positivity is not decoration. At `c = 0` both products collapse to zero and the
comparison is decided by reflexivity rather than by `x` and `y`, so the law is
false without it. Rescalings are positive by construction, `Scaling` living in
log space, so the hypothesis is discharged wherever this is used. -/
class OrderedNum (R : Type) extends Num R where
  le_scale : ∀ (c x y : R), le c (ofRat 0) = false →
    le (mul c x) (mul c y) = le x y

/-- `ℝ` is the carrier the abstraction theorems are stated over, so it is the
one that has to satisfy the law. -/
noncomputable instance : OrderedNum ℝ where
  le_scale := by
    intro c x y hc
    have hc' : (0 : ℝ) < c := by
      simp only [Num.le, Num.ofRat, Rat.cast_zero, decide_eq_false_iff_not,
        not_le] at hc
      exact hc
    simp only [Num.le, Num.mul, decide_eq_decide]
    exact ⟨fun h => le_of_mul_le_mul_left h hc',
           fun h => mul_le_mul_of_nonneg_left h hc'.le⟩


/-- Real double precision.

`npow` is bare `Float.pow`: even on positive bases its result is a
floating-point approximation, not an equality with `Real.rpow`. On a negative
base with a non-integer exponent it returns `NaN`, while `Real.rpow` uses
the real part of the principal complex power. Mathlib also has `0 ^ q = 0`
for nonzero `q` and `x / 0 = 0`, unlike floating-point infinities and NaNs.
`QM.boundaryChecks` tests selected conventions in the binary. -/
instance : Num Float where
  ofRat q := Float.ofInt q.num / Float.ofNat q.den
  add := (· + ·)
  mul := (· * ·)
  div := (· / ·)
  npow q x := Float.pow x (Float.ofInt q.num / Float.ofNat q.den)
  nlog := Float.log
  nexp := Float.exp
  le x y := x ≤ y
  dot xs ys := ddot ⟨xs.toArray⟩ ⟨ys.toArray⟩
  matVec M x := (dgemv M.length x.length ⟨M.flatten.toArray⟩ ⟨x.toArray⟩).data.toList
  matVec_length := by intro M x; simp

end LambdaS

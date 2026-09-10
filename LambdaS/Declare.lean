/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Conversion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Unit declarations, and why conflicting ones are rejected

`dimension Velocity = Length/Time` is an abbreviation: dimensions are exponent
vectors, so it expands and nothing is left to check. Unit declarations are the
interesting case, because

```
unit yard = 3 foot
```

declares a generator **and** an equation, and equations can conflict. This is
the bug that the Comp 311 assignment's one-unit-per-dimension restriction
(`LambdaS.Conversion`) exists to dodge: with units nameable in terms
of other units, two routes from `yard` to `meter` need not agree, and nothing in
a free abelian group of units forces them to.

## What the resolution is, and what it is not

It is *not* a consistency check on paths. `LambdaS.Conversion` already makes
conversion a ratio of one valuation, so `convChain_eq` says any chain of
intermediate conversions equals the direct factor: path independence is a
theorem there, not an obligation here.

What is left is the prior question: do the declarations determine a valuation at
all? That is a linear system, and this file gives its solvability criterion, in
both directions. `dependency_forces` is necessity: every ℚ-linear combination
of the declarations whose *unit* parts cancel forces the corresponding
*factors* to multiply to one. `dependency_sufficient` is sufficiency:
respect every dependency and a satisfying valuation exists, so
`consistent_iff_dependencies` (and its multiplicative form) characterizes
consistency outright. `factor_chain` is the two-step instance that is
literally the yard/foot/meter conflict. `not_satisfiable_of_chain` turns it
around: get the arithmetic wrong and **no** valuation exists, so the declaration
set is rejected rather than silently picking a route.

## Where exactness lives

The criterion is exact rational arithmetic even though valuations are real.
Declared factors are rationals; a dependency demands `∏ qᵢ^{cᵢ} = 1` with `cᵢ`
rational, which clearing denominators turns into an identity in ℚ. Rational
powers can require irrational magnitudes: if `V(c) = 2`, then
`V(c^(1/2)) = √2`. Valuations therefore range over ℝ. The checker manipulates
symbolic logarithmic expressions exactly; it evaluates no logarithms or roots.
Declarations live in ℚ⁺, and the consistency tests reduce to equality in ℚ⁺.

## What is not declared has no factor

A base unit with no declaration is a primitive, and its magnitude is free. So
`meter` and `foot` as bare generators are same-dimension units with **no**
determined conversion factor: `convert` between them typechecks, but its value
is whatever the valuation says. Declaring `unit foot = 0.3048 meter` is exactly
what pins it. `DeclSolver.check` in `LambdaS.DeclareSolver` now enforces the
execution obligation: declarations must be dimensionally sound, consistent,
and determine every same-dimension factor. `DeclSolver.conversionExact` also
supports individual lookup, returning none for an undetermined ratio. It
returns exact radicals for determined ratios; it does not silently supply an
arbitrary missing factor. The semantic criterion below is linked to those
executable checks by soundness and completeness proofs.
-/

/-!
## Unit Declarations

Conversion forces a question the parametric literature never faces: where do
the factors come from? The answer is unit declarations, in the style
scientists write them:

    unit yard = 3 foot;  unit foot = 0.3048 meter.

Declarations are not terms of Λs: they are the interface a surface
language hands to the calculus, and the artifact consumes them as data. Each
declaration constrains one unit against another by a factor; in
unit yard = 3 foot, the declared factor is
3.

Declarations can conflict. With units nameable in terms of other units, a
system that implements conversion by *walking the declared structure*
can offer more than one route between two units, with no guarantee the routes
agree: add the redundant declaration yard = 0.9 meter
and the direct route disagrees with the route through feet, since
3 × 0.3048 = 0.9144 ≠ 0.9 (see note 1). Any implementation that converts by chaining declared factors
ad hoc admits this defect, and nothing in the algebra of units forbids it: the units
form a free ℚ-vector space (“Units and Dimensions” (`Typing.lean`)), and the
declared factors are data the algebra does not constrain.

> **Note 1.** Redundant declarations are not
> a strawman: real unit databases can carry them deliberately, because lookup
> through a hub unit loses precision that a directly stored factor preserves.
> The design question is not whether redundancy occurs but what happens when it
> disagrees.

Dimension declarations, by contrast, carry no factor, and the only
check they need is scoping. A bare one,
dimension Length, introduces a base dimension;
freshness is its whole check, and the bare declarations jointly supply
the calculus's parameter D. One with a right-hand side is an
abbreviation: it introduces a fresh name for a vector
over the base dimensions, its right-hand side mentioning only base
dimensions and earlier abbreviations, and expands at once:
dimension Velocity = Length/Time
is the vector (Length ↦ 1, Time ↦ -1)
from then on. Cycles are consequently not detected but unrepresentable:
the incorrect pair Velocity = Length/Time,
Length = Velocity/Time is rejected at its
second line for rebinding a generator, before any question of
consistency can arise, and a forward reference is rejected because an
undefined name does not denote (`elabDimDefs`; the cyclic pair
is `dimCycle`). Base units are declared the same way, by a
dimension and no factor: unit meter : Length
makes meter *primary*, Fortress's
term [Allen et al. 2008], and the declaration is what determines the
unit's dimension. The primary declarations jointly supply the calculus's
parameters B and dim, and they too need only scoping
(`elabPrimary`): a fresh name, and a dimension that denotes.
This section is therefore about the declarations that carry a factor.

Λs does not implement conversion as a walk. Recall that a
valuation
V assigns each base unit a positive magnitude: an exchange-rate table
into an arbitrary fixed reference scale, not a measurement. For example,
V(meter) = 1, V(foot) = 0.3048,
V(yard) = 0.9144 is a valuation, and it satisfies both
declarations above. A valuation extends to a homomorphism from unit
expressions to (ℝ^(>0),×), and the conversion factor from u
to v is the ratio conv_V(u,v) = V(u)/V(v). Path independence is
then a theorem rather than a proof obligation (any chain of intermediate
conversions telescopes to the direct factor). Declarations constrain
valuations; we say a declaration set is *consistent* when some valuation
satisfies every declared equation. Note that declarations carry no order,
and no acyclicity condition is imposed or needed: each declaration is an
equation, the set is a simultaneous system, and a cycle is just a
dependency the criterion below decides. The benign cycle
yard = 3 foot,
foot = 1/3 yard is satisfiable
(`cycle_satisfiable`); close it wrongly, with
foot = yard, and the dependency forces 3 = 1, so no
valuation exists (`cycle_conflict`). Nor can a declaration
mention an undeclared generator: the base units are the calculus's
parameter B, so the reference is unrepresentable. What remains is the
prior question:
*do the declarations determine a valuation at all?*

A declaration unit b = q w constrains the ratio b/w to the
value q ∈ ℚ^(>0). In logarithmic coordinates each declaration is
one linear equation in the unknowns log V(b), so a valuation exists
exactly when that linear system is consistent: every linear dependency among
the constrained ratios must force the matching relation among the declared
factors. Both directions are theorems. Necessity holds
(`dependency_forces`; in product form,
`dependency_forces_mul`). Sufficiency invites a worry. The
unknowns log V(b) are real, and necessarily so: valuations are
real-valued, not merely their logarithms, since rational exponents can
force irrational magnitudes (declare c = 2 and
b = c^(1/2), and every satisfying valuation has
V(b) = √2), and rational magnitudes can have
irrational logarithms (though log 1 = 0). The dependencies, by contrast, are
rational, so we
might fear a real-coefficient dependency imposing a constraint the rational
ones miss. None does: ℝ is itself a vector space over
ℚ, its vectors the reals and its scalars the rationals, so
the rational coefficient matrix has the same dependencies over either
field, and the system is solved ℚ-linearly with real
values (`dependency_sufficient`).

**Theorem (Consistency; `consistent_iff_dependencies_mul`).** A declaration set with ratios r_i and factors q_i admits a satisfying
valuation if and only if, for every
ℚ-linear combination with ∑_i c_i r_i = 0 in the unit
group, ∏_i q_i^c_i = 1; equivalently, in logarithmic form,
∑_i c_i log q_i = 0 (`consistent_iff_dependencies`).

With the criterion in hand, we work the example in full. The three
declarations

    unit yard = 3 foot;  unit foot = 0.3048 meter;  unit yard = 0.9144 meter

constrain the ratios r₁ = yard/foot,
r₂ = foot/meter, and
r₃ = yard/meter. Writing y, f, m for
log V(yard), log V(foot), log V(meter),
they induce the linear system

    y - f = log 3,  f - m = log 0.3048,  y - m = log 0.9144.

The ratios are linearly dependent: with coefficients c = (1, 1, -1) in
the theorem “Consistency” (`consistent_iff_dependencies_mul`), r₁ + r₂ - r₃ = 0 in the unit group
(multiplicatively,
(yard/foot)(foot/meter)(meter/yard)
is the dimensionless 1), so consistency demands
q₁ q₂ q₃⁻¹ = 1, that is,
3 × 0.3048 = 0.9144 (see note 2). The equation
holds, and the artifact exhibits a satisfying valuation explicitly
(`yard_satisfiable`): the exchange-rate table V above. Now replace
the third declaration by yard = 0.9 meter. The same
dependency demands 3 × 0.3048 = 0.9, which is false; the artifact
refutes the set (`yard_conflict`): *no* valuation satisfies all
three, the set is rejected at declaration time, and there is never a choice
of route to get wrong. Because coefficients and factors are rational, the
test uses exact arithmetic. Symbolic logarithmic expressions are
manipulated without numerical evaluation; denominator clearing reduces their
zero tests to rational product equality. Note that a satisfied redundant declaration has no freedom in its
factor: any valuation satisfying all three declarations forces
3 × 0.3048 = 0.9144 (`yard_forced`), and the general lemma
(`factor_chain_consistent`) states this for an arbitrary third
declaration.

> **Note 2.** The yard has been exactly 0.9144
> meters only since 1959, when six English-speaking countries agreed to end a
> disagreement of roughly two parts per
> million [Astin et al. 1959]. The United States kept its
> earlier foot for surveying; that redundant declaration, inconsistent with
> the new one in the seventh decimal place, survived until the end of 2022; its
> retirement, effective December 31, 2022, was announced by a 2020 Federal
> Register notice [NIST and NOAA 2020].

Note that a base unit with no declaration is a primitive, and its magnitude
is free. Its dimension is not: the unit system assigns every base unit a
dimension (dim : B → ℚ^D is total, “Units and Dimensions” (`Typing.lean`)),
so declarations add magnitudes, never dimensions. Declarations, not the type
system, give conversion its numeric content; the type system contributes a
separate, decidable check that each declaration relates
units of one dimension: unit yard = 3 second
is rejected (`Sound`, orthogonal to
the theorem “Consistency” (`consistent_iff_dependencies_mul`)).

What the declared numbers are worth to running code is the subject of
“Adequacy and Erasure” (`Erasure.lean`), where the chain from declaration to real-valued
evaluation is closed: the evaluator instantiated with real arithmetic converts one yard into feet by
multiplying by the declared 3 and into meters by the forced
0.9144 (`one_yard_is_three_feet`; through the forced
factor, `one_yard_in_meters`).
-/

namespace LambdaS

open scoped BigOperators

variable {B D : Type} [Fintype B] [DecidableEq B]

/-! ## Declarations -/

/-- A **unit declaration**: `unit lhs = factor · rhs`.

The factor is a positive rational. That is not a convenience; it is what keeps
the consistency criterion exact, since a product of rational powers of rationals
is decidably one. -/
structure Decl (B : Type) where
  /-- The unit being declared. A generator: declaring is what gives it meaning,
  not what defines it away. -/
  lhs : B
  /-- The declared magnitude, against `rhs`. -/
  factor : ℚ
  /-- Positivity. A unit of negative magnitude is not a unit. -/
  pos : 0 < factor
  /-- What it is declared against: any unit expression, compound or not. -/
  rhs : UExp B 0

namespace Decl

/-- The **ratio** a declaration constrains: `lhs / rhs`, which the declaration
says has magnitude `factor`. Dimensionless when the declaration is sound. -/
def ratio (d : Decl B) : UExp B 0 := Term.div (Term.ofBase d.lhs) d.rhs

/-- A valuation **satisfies** a declaration when it assigns the declared
magnitude to the declared ratio. -/
def Satisfies (ψ : Scaling B 0) (d : Decl B) : Prop := ψ.scale d.ratio = (d.factor : ℝ)

/-- The multiplicative reading, which is how a declaration is written. -/
theorem satisfies_iff {ψ : Scaling B 0} {d : Decl B} :
    Satisfies ψ d ↔ ψ.scale (Term.ofBase d.lhs) = (d.factor : ℝ) * ψ.scale d.rhs := by
  have hr := ne_of_gt (ψ.scale_pos d.rhs)
  rw [Satisfies, ratio, Scaling.scale_div]
  constructor
  · intro h; field_simp at h ⊢; linarith [h]
  · intro h; rw [h]; field_simp

/-- The additive reading, in log coordinates. This is the form the linear
algebra runs on: a declaration is one linear equation in the unknowns `ψ.base`. -/
theorem satisfies_iff_log {ψ : Scaling B 0} {d : Decl B} :
    Satisfies ψ d ↔ ψ.logScale d.ratio = Real.log (d.factor : ℝ) := by
  have hq : (0 : ℝ) < (d.factor : ℝ) := by exact_mod_cast d.pos
  rw [Satisfies, Scaling.scale]
  constructor
  · intro h; rw [← h, Real.log_exp]
  · intro h; rw [h, Real.exp_log hq]

/-- **A declaration determines its conversion factor.** Whatever valuation
satisfies it, converting the declared unit into its right-hand side gives
exactly the declared number.

This is the link between declarations and `LambdaS.Conversion`: the declared
factor *is* the conversion factor, so path independence transfers wholesale. -/
theorem conv_eq_factor {ψ : Scaling B 0} {d : Decl B} (h : Satisfies ψ d) :
    conv ψ (Term.ofBase d.lhs) d.rhs = (d.factor : ℝ) := by
  rw [conv_eq_scale_div]; exact h

/-! ## Dimensional soundness -/

section Sound

variable [UnitSys B D]

/-- A declaration is **sound** when the declared unit has the dimension of its
right-hand side. Decidable, and it is what stops a declaration smuggling in a
conversion between dimensions: `unit yard = 3 second` is rejected here. -/
def Sound (d : Decl B) : Prop :=
  UnitSys.dim (D := D) d.lhs = dimOf (DCtx.nil D) d.rhs

instance [Fintype D] [DecidableEq D] (d : Decl B) : Decidable (Sound (D := D) d) := by
  unfold Sound; infer_instance

/-- The dimension of a bare generator is its declared dimension. -/
theorem dimOf_ofBase (b : B) :
    dimOf (D := D) (DCtx.nil D) (Term.ofBase b) = UnitSys.dim (D := D) b := by
  refine Term.ext' (funext fun d => ?_) (funext fun w => ?_)
  · simp only [dimOf, Term.ofBase]
    rw [Finset.sum_eq_single b] <;> simp_all
  · exact w.elim0

/-- **Sound declarations declare interchangeable units.** So the declared unit
and its right-hand side pass the `convert` check, and the declaration is
usable. -/
theorem sameDim_of_sound {d : Decl B} (h : Sound (D := D) d) :
    SameDim (DCtx.nil D) (Term.ofBase d.lhs) d.rhs := by
  rw [SameDim, dimOf_ofBase]; exact h

/-- **A sound declaration has a dimensionless ratio.** Which is why the factor is
a pure number, and why it can itself be named as a unit. -/
theorem ratio_dimensionless {d : Decl B} (h : Sound (D := D) d) :
    dimOf (D := D) (DCtx.nil D) d.ratio = 1 :=
  dimOf_ratio_one _ (sameDim_of_sound h)

end Sound

end Decl

/-! ## Consistency

A declaration set is a linear system in log coordinates. It is solvable exactly
when the factors respect every dependency among the unit parts, and that is the
criterion for the declarations to have a satisfying valuation. Uniqueness of
conversion factors is the separate determinacy question in `LambdaS.Determinacy`. -/

open Decl

/-- **The general criterion.** Any ℚ-linear combination of the declared ratios
that cancels in the unit group forces the same combination of log-factors to
vanish.

Contrapositively: exhibit a dependency whose factors do *not* multiply to one,
and no valuation exists; the declaration set is rejected. Since the
coefficients are
rational and the factors are rational, that test is exact arithmetic. -/
theorem dependency_forces {ψ : Scaling B 0} {n : ℕ} {ds : Fin n → Decl B}
    (h : ∀ i, Satisfies ψ (ds i)) (c : Fin n → ℚ)
    (hcancel : ∀ b : B, ∑ i, c i * (ds i).ratio.base b = 0) :
    ∑ i, (c i : ℝ) * Real.log ((ds i).factor : ℝ) = 0 := by
  have hlog : ∀ i, ψ.logScale (ds i).ratio = Real.log ((ds i).factor : ℝ) :=
    fun i => satisfies_iff_log.mp (h i)
  have hstep : ∀ i, (c i : ℝ) * Real.log ((ds i).factor : ℝ)
      = ∑ b, (c i : ℝ) * ((ds i).ratio.base b : ℝ) * ψ.base b := by
    intro i
    rw [← hlog i]
    simp only [Scaling.logScale, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : ∑ i, (c i : ℝ) * ((ds i).ratio.base b : ℝ) * ψ.base b
      = (∑ i, (c i : ℝ) * ((ds i).ratio.base b : ℝ)) * ψ.base b := by
    rw [Finset.sum_mul]
  rw [this]
  have hz : (∑ i, (c i : ℝ) * ((ds i).ratio.base b : ℝ)) = 0 := by
    have := hcancel b
    have hcast : ((∑ i, c i * (ds i).ratio.base b : ℚ) : ℝ) = 0 := by
      rw [this]; norm_num
    rw [Rat.cast_sum] at hcast
    simpa using hcast
  rw [hz, zero_mul]

/-- The multiplicative form of `dependency_forces`: the same rational
combination of declared factors, read as a product of real powers, equals `1`.
The two forms are equivalent because every factor is positive, so `Real.log`
and `Real.exp` translate between the product and the sum. -/
theorem dependency_forces_mul {ψ : Scaling B 0} {n : ℕ} {ds : Fin n → Decl B}
    (h : ∀ i, Satisfies ψ (ds i)) (c : Fin n → ℚ)
    (hcancel : ∀ b : B, ∑ i, c i * (ds i).ratio.base b = 0) :
    ∏ i, ((ds i).factor : ℝ) ^ (c i : ℝ) = 1 := by
  have hpos : ∀ i, (0 : ℝ) < ((ds i).factor : ℝ) := fun i => by exact_mod_cast (ds i).pos
  have hprodpos : (0 : ℝ) < ∏ i, ((ds i).factor : ℝ) ^ (c i : ℝ) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hpos i) _
  have hlog : Real.log (∏ i, ((ds i).factor : ℝ) ^ (c i : ℝ)) = 0 := by
    rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hpos i) _).ne')]
    calc ∑ i, Real.log (((ds i).factor : ℝ) ^ (c i : ℝ))
        = ∑ i, (c i : ℝ) * Real.log ((ds i).factor : ℝ) :=
          Finset.sum_congr rfl fun i _ => Real.log_rpow (hpos i) _
      _ = 0 := dependency_forces h c hcancel
  calc ∏ i, ((ds i).factor : ℝ) ^ (c i : ℝ)
      = Real.exp (Real.log (∏ i, ((ds i).factor : ℝ) ^ (c i : ℝ))) :=
        (Real.exp_log hprodpos).symm
    _ = 1 := by rw [hlog, Real.exp_zero]

/-! ## Sufficiency

The converse direction. `dependency_forces` says a satisfying valuation makes
every dependency respect the factors; here we show that respecting the
dependencies is all it takes, so the criterion decides consistency outright.

The proof needs no real linear algebra. The system asks for a function
`B → ℝ` in log coordinates, and ℝ is a vector space over ℚ, so the system can
be solved ℚ-linearly with values in ℝ: send each ratio's exponent vector to its
log-factor, check the assignment kills every rational dependency (the
hypothesis), factor it through the span of the exponent vectors, and extend to
all of `B → ℚ`. The question of whether real dependencies among rational
vectors exceed the rational ones never arises. -/

/-- **The criterion is sufficient.** If every ℚ-linear dependency among the
declared ratios forces the matching combination of log-factors to vanish, then
some valuation satisfies every declaration at once.

This is the converse of `dependency_forces` and the sufficiency half of the
paper's solvability theorem. In log coordinates each declaration is one linear
equation in the unknown base magnitudes; the hypothesis is exactly that the
right-hand sides respect the dependencies of the left-hand sides, and
`exists_linearMap_of_dependencies` turns that into a ℚ-linear map on `B → ℚ`
with values in ℝ. Reading that map on the standard basis gives the valuation. -/
theorem dependency_sufficient {n : ℕ} {ds : Fin n → Decl B}
    (h : ∀ c : Fin n → ℚ, (∀ b : B, ∑ i, c i * (ds i).ratio.base b = 0) →
      ∑ i, (c i : ℝ) * Real.log ((ds i).factor : ℝ) = 0) :
    ∃ ψ : Scaling B 0, ∀ i, Satisfies ψ (ds i) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_linearMap_of_dependencies (K := ℚ)
    (fun i => (ds i).ratio.base) (fun i => Real.log ((ds i).factor : ℝ))
    (fun c hc => by
      have hc' : ∀ b : B, ∑ i, c i * (ds i).ratio.base b = 0 := fun b => by
        simpa [Finset.sum_apply, smul_eq_mul] using congrFun hc b
      simpa [Rat.smul_def] using h c hc')
  refine ⟨⟨fun b => φ (Pi.single b 1), Fin.elim0⟩, fun i => ?_⟩
  rw [satisfies_iff_log]
  have hstep : ∀ b : B, ((ds i).ratio.base b : ℝ) * φ (Pi.single b 1)
      = φ (Pi.single b ((ds i).ratio.base b)) := by
    intro b
    rw [← Rat.smul_def, ← map_smul]
    congr 1
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [Scaling.logScale, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [Finset.sum_congr rfl fun b _ => hstep b, ← map_sum, Finset.univ_sum_single]
  exact hφ i

/-- **Consistency, characterized.** A declaration set has a satisfying
valuation exactly when every ℚ-linear dependency among its ratios forces the
matching combination of log-factors to vanish. Necessity is
`dependency_forces`; sufficiency is `dependency_sufficient`. This is the
solvability criterion in the form the linear algebra produces it. -/
theorem consistent_iff_dependencies {n : ℕ} {ds : Fin n → Decl B} :
    (∃ ψ : Scaling B 0, ∀ i, Satisfies ψ (ds i)) ↔
      ∀ c : Fin n → ℚ, (∀ b : B, ∑ i, c i * (ds i).ratio.base b = 0) →
        ∑ i, (c i : ℝ) * Real.log ((ds i).factor : ℝ) = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩ c hc
    exact dependency_forces hψ c hc
  · exact dependency_sufficient

/-- **Consistency, in the multiplicative form the paper states.** A declaration
set has a satisfying valuation exactly when every ℚ-linear dependency among its
ratios forces the corresponding product of declared factors to one. Since the
coefficients and factors are rational, the right-hand side is an exact
arithmetic test. -/
theorem consistent_iff_dependencies_mul {n : ℕ} {ds : Fin n → Decl B} :
    (∃ ψ : Scaling B 0, ∀ i, Satisfies ψ (ds i)) ↔
      ∀ c : Fin n → ℚ, (∀ b : B, ∑ i, c i * (ds i).ratio.base b = 0) →
        ∏ i, ((ds i).factor : ℝ) ^ (c i : ℝ) = 1 := by
  constructor
  · rintro ⟨ψ, hψ⟩ c hc
    exact dependency_forces_mul hψ c hc
  · intro h
    refine dependency_sufficient fun c hc => ?_
    have hpos : ∀ i, (0 : ℝ) < ((ds i).factor : ℝ) := fun i => by
      exact_mod_cast (ds i).pos
    have hm := congrArg Real.log (h c hc)
    rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hpos i) _).ne'),
      Real.log_one] at hm
    calc ∑ i, (c i : ℝ) * Real.log ((ds i).factor : ℝ)
        = ∑ i, Real.log (((ds i).factor : ℝ) ^ (c i : ℝ)) :=
          Finset.sum_congr rfl fun i _ => (Real.log_rpow (hpos i) _).symm
      _ = 0 := hm

/-! ## The conflict, exhibited

Three declarations, two routes from the first unit to the last. This is the
Comp 311 configuration exactly: `yard = 3 foot`, `foot = 0.3048 meter`, and a
redundant `yard = q meter`. -/

/-- **Chained declarations force the factor.** If `a` is declared against `b`'s
unit, `b` against some `w`, and `c` declares `a`'s unit directly against the same
`w`, then the factors are forced: `factor a · factor b = factor c`.

There is no freedom here and no route to choose. The redundant declaration is
either arithmetically correct or the system has no solution. -/
theorem factor_chain {ψ : Scaling B 0} {a b c : Decl B}
    (ha : Satisfies ψ a) (hb : Satisfies ψ b) (hc : Satisfies ψ c)
    (h1 : a.rhs = Term.ofBase b.lhs) (h2 : a.lhs = c.lhs) (h3 : b.rhs = c.rhs) :
    ((a.factor * b.factor : ℚ) : ℝ) = (c.factor : ℝ) := by
  rw [satisfies_iff] at ha hb hc
  rw [h1] at ha
  rw [h3] at hb
  rw [h2] at ha
  rw [hb] at ha
  have hw := ne_of_gt (ψ.scale_pos c.rhs)
  rw [hc] at ha
  push_cast
  field_simp at ha
  nlinarith [ha, ψ.scale_pos c.rhs]

/-- **Conflicting declarations are rejected.** Get the arithmetic wrong and no
valuation satisfies all three, so there is nothing for an implementation to pick
between: the declaration set fails to elaborate.

This is the Comp 311 bug, decided. The assignment's `convert` had to choose a
path and could choose wrongly; here the situation that would have forced a choice
is precisely the situation with no solution. -/
theorem not_satisfiable_of_chain {a b c : Decl B}
    (h1 : a.rhs = Term.ofBase b.lhs) (h2 : a.lhs = c.lhs) (h3 : b.rhs = c.rhs)
    (hbad : a.factor * b.factor ≠ c.factor) :
    ¬ ∃ ψ : Scaling B 0, Satisfies ψ a ∧ Satisfies ψ b ∧ Satisfies ψ c := by
  rintro ⟨ψ, ha, hb, hc⟩
  exact hbad (by exact_mod_cast factor_chain ha hb hc h1 h2 h3)

/-- **Joint satisfaction forces consistency**: `factor_chain` with the cast
removed, stated in ℚ for symmetry with `not_satisfiable_of_chain`: if one
valuation satisfies all three declarations, their factors obey the chain
equation exactly. -/
theorem factor_chain_consistent {ψ : Scaling B 0} {a b c : Decl B}
    (ha : Satisfies ψ a) (hb : Satisfies ψ b) (hc : Satisfies ψ c)
    (h1 : a.rhs = Term.ofBase b.lhs) (h2 : a.lhs = c.lhs) (h3 : b.rhs = c.rhs) :
    a.factor * b.factor = c.factor := by
  exact_mod_cast factor_chain ha hb hc h1 h2 h3


/-! ## Dimension abbreviations

Unit declarations constrain; dimension declarations abbreviate. A
dimension declaration introduces a fresh name for a vector over the base
dimensions, so the only check it needs is scoping: the name must be new,
and the right-hand side may mention only base dimensions and earlier
abbreviations. Under that discipline a cyclic pair such as
`Velocity = Length/Time; Length = Velocity/Time` is rejected at its second
line, for rebinding a generator, before any question of consistency can
arise; a forward reference is rejected because an undefined name does not
denote. Cycles are not detected but unrepresentable. -/

namespace DimAbbrev

variable {D : Type} [Fintype D] [DecidableEq D]

/-- One right-hand-side factor: a base dimension or an earlier
abbreviation, at a rational exponent. -/
abbrev Ref (D : Type) := (D ⊕ String) × ℚ

/-- Elaborate one abbreviation against the environment built so far.
Rejects a name that collides with a base dimension or an earlier
abbreviation, and a reference to a name not yet defined. -/
def elabOne (baseName : String → Option D)
    (env : List (String × DExp D 0)) (n : String) (rhs : List (Ref D)) :
    Option (List (String × DExp D 0)) :=
  if (baseName n).isSome || (env.lookup n).isSome then none else do
    let v ← rhs.foldlM (init := (1 : DExp D 0)) fun acc (r, q) => do
      let d ← match r with
        | .inl b => some (Term.ofBase b)
        | .inr s => env.lookup s
      pure (Term.mul acc (Term.rpow d q))
    some ((n, v) :: env)

/-- Elaborate a sequence of dimension abbreviations, in order. Every
name that survives maps to an exponent vector over the base dimensions;
nothing else survives. -/
def elabDimDefs (baseName : String → Option D) :
    List (String × List (Ref D)) → Option (List (String × DExp D 0)) :=
  List.foldlM (fun env (d : String × List (Ref D)) => elabOne baseName env d.1 d.2) []

/-- **Primary-unit declarations.** A base unit is introduced by naming it
and its dimension, with no factor: `unit meter : Length` makes `meter`
primary (Fortress's term), and the declaration is what determines the
unit's dimension. Elaboration is scoping again: a fresh unit name, and a
dimension that denotes (a base dimension or an abbreviation already
elaborated). The surviving table is the calculus's `dimOf`, restricted to
the declared generators. -/
def elabPrimary (baseName : String → Option D)
    (dims : List (String × DExp D 0)) :
    List (String × (D ⊕ String)) → Option (List (String × DExp D 0))
  | [] => some []
  | (n, dref) :: rest => do
      let table ← elabPrimary baseName dims rest
      if (table.lookup n).isSome then none else do
        let d ← match dref with
          | .inl b => some (Term.ofBase b)
          | .inr sname => dims.lookup sname
        some ((n, d) :: table)

end DimAbbrev

end LambdaS

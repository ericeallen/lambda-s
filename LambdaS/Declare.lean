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
of other units, two routes from `yard` to `metre` need not agree, and nothing in
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
literally the yard/foot/metre conflict. `not_satisfiable_of_chain` turns it
around: get the arithmetic wrong and **no** valuation exists, so the declaration
set is rejected rather than silently picking a route.

## Where exactness lives

The criterion is exact rational arithmetic even though valuations are real.
Declared factors are rationals; a dependency demands `∏ qᵢ^{cᵢ} = 1` with `cᵢ`
rational, which clearing denominators turns into an identity in ℚ. The
irrationality that ℚ exponents force (`val(m^(1/2))` is not rational) enters
only at `log`, which is *after* the check. Declarations live in ℚ⁺, valuations
in ℝ, and consistency is decided in ℚ⁺.

## What is not declared has no factor

A base unit with no declaration is a primitive, and its magnitude is free. So
`metre` and `foot` as bare generators are same-dimension units with **no**
determined conversion factor: `convert` between them typechecks, but its value
is whatever the valuation says. Declaring `unit foot = 0.3048 metre` is exactly
what pins it. That is the sense in which declarations, not the type system, give
conversion its content.
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
  · simp only [dimOf, Term.ofBase, add_zero, Finset.sum_const_zero]
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
whole content of "the declarations determine a valuation". -/

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
Comp 311 configuration exactly: `yard = 3 foot`, `foot = 0.3048 metre`, and a
redundant `yard = q metre`. -/

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

end LambdaS

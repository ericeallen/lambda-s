/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Syntax

/-!
# Scalings: the semantic foundation

Unit correctness is **not** type safety. Kennedy makes the point sharply
(WMM 2008): *"What 'goes wrong' if a program contains a unit error? Nothing!"* A
unit error does not get a program stuck; it gets you a wrong number. So progress
and preservation are vacuous here, and the semantic content of unit correctness
has to be something else: **invariance of program behavior under scaling**.

This file builds the object that invariance is stated against.

## Scalings are linear functionals

A scaling assigns a positive real factor to each base unit and each unit
variable, and extends to a homomorphism `UExp → (ℝ⁺, ×)`. Since `(ℝ⁺, ×) ≅ (ℝ, +)`
under `log`, and a unit expression *is* an exponent vector, the extension is a
**dot product**:

  `logScale ψ t = Σ_b t.base b · ψ.base b + Σ_i t.vars i · ψ.vars i`

Working in log space keeps everything linear, makes positivity free (the actual
factor is `exp` of this, so it is positive by construction), and turns the
homomorphism laws into linearity.

## Why the substitution lemma is easy here

Kennedy singled out the substitution lemma as the painful part of his Coq
development:

> *"First attempt in Coq: … This doesn't even type-check! Type-checker needs to
> know `usem τ = usem (subst ty s τ)`. Solution: explicit equality coercions."*

That pain comes from unit expressions being **syntax trees**, so substitution is
structural and the semantics has to be transported along it.

Here unit expressions are **exponent vectors** and substitution is a linear map
on them, so `logScale_subst` is an identity between two sums: pure arithmetic,
with no coercions and no transport. The representation choice made for
decidability in `LambdaS.Syntax` pays off again, in a place it was not chosen
for.
-/

namespace LambdaS

open scoped BigOperators

variable {B : Type} [Fintype B] {k k₀ : ℕ}

/-- A **scaling**: a positive factor for each base unit and each unit variable,
represented by its logarithm so that the group is `(ℝ, +)` and everything stays
linear. -/
structure Scaling (B : Type) (k : ℕ) where
  base : B → ℝ
  vars : Fin k → ℝ

namespace Scaling

/-- Extend a scaling to a unit expression. In log space this is the dot product
of the exponent vector with the scaling vector. -/
def logScale (ψ : Scaling B k) (t : UExp B k) : ℝ :=
  (∑ b, (t.base b : ℝ) * ψ.base b) + ∑ i, (t.vars i : ℝ) * ψ.vars i

/-- The actual scale factor. Positive by construction, which is the positivity
Kennedy's Pi theorem assumes. -/
noncomputable def scale (ψ : Scaling B k) (t : UExp B k) : ℝ :=
  Real.exp (ψ.logScale t)

theorem scale_pos (ψ : Scaling B k) (t : UExp B k) : 0 < ψ.scale t :=
  Real.exp_pos _

/-! ## The homomorphism laws -/

@[simp] theorem logScale_one (ψ : Scaling B k) : ψ.logScale (1 : UExp B k) = 0 := by
  simp [logScale]

theorem logScale_mul (ψ : Scaling B k) (u v : UExp B k) :
    ψ.logScale (Term.mul u v) = ψ.logScale u + ψ.logScale v := by
  simp only [logScale, Term.mul_base, Term.mul_vars, Rat.cast_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem logScale_inv (ψ : Scaling B k) (u : UExp B k) :
    ψ.logScale (Term.inv u) = -ψ.logScale u := by
  simp only [logScale, Term.inv_base, Term.inv_vars, Rat.cast_neg, neg_mul,
    Finset.sum_neg_distrib]
  ring

theorem logScale_div (ψ : Scaling B k) (u v : UExp B k) :
    ψ.logScale (Term.div u v) = ψ.logScale u - ψ.logScale v := by
  simp only [logScale, Term.div_base, Term.div_vars, Rat.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  ring

theorem logScale_rpow (ψ : Scaling B k) (u : UExp B k) (q : ℚ) :
    ψ.logScale (Term.rpow u q) = (q : ℝ) * ψ.logScale u := by
  simp only [logScale, Term.rpow_base, Term.rpow_vars, Rat.cast_mul, mul_assoc,
    ← Finset.mul_sum]
  ring

@[simp] theorem scale_one (ψ : Scaling B k) : ψ.scale (1 : UExp B k) = 1 := by
  simp [scale]

theorem scale_mul (ψ : Scaling B k) (u v : UExp B k) :
    ψ.scale (Term.mul u v) = ψ.scale u * ψ.scale v := by
  simp [scale, logScale_mul, Real.exp_add]

theorem scale_div (ψ : Scaling B k) (u v : UExp B k) :
    ψ.scale (Term.div u v) = ψ.scale u / ψ.scale v := by
  simp [scale, logScale_div, Real.exp_sub]

theorem scale_rpow (ψ : Scaling B k) (u : UExp B k) (q : ℚ) :
    ψ.scale (Term.rpow u q) = (ψ.scale u) ^ (q : ℝ) := by
  simp [scale, logScale_rpow, ← Real.exp_mul, mul_comm]

/-! ## Substitution

The lemma Kennedy called out as the awkward part of mechanizing this. -/

/-- Extend a scaling with a factor for a newly bound unit variable. -/
def cons (ψ : Scaling B k) (r : ℝ) : Scaling B (k + 1) :=
  ⟨ψ.base, Fin.cons r ψ.vars⟩

/-- **The substitution lemma.** Scaling a substituted expression is the same as
scaling the original under an environment extended by the scale of the
substituted expression.

Pure exponent arithmetic: no coercions, no transport. -/
theorem logScale_subst (ψ : Scaling B k) (t : UExp B (k + 1)) (σ : UExp B k) :
    ψ.logScale (t.subst σ) = (ψ.cons (ψ.logScale σ)).logScale t := by
  simp only [logScale, UExp.subst, cons, Rat.cast_add, Rat.cast_mul,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem scale_subst (ψ : Scaling B k) (t : UExp B (k + 1)) (σ : UExp B k) :
    ψ.scale (t.subst σ) = (ψ.cons (ψ.logScale σ)).scale t := by
  simp [scale, logScale_subst]

/-- Weakening is invisible to scaling: the fresh variable is unused, so whatever
factor it is given cannot matter. -/
@[simp] theorem logScale_weaken (ψ : Scaling B k) (r : ℝ) (t : UExp B k) :
    (ψ.cons r).logScale t.weaken = ψ.logScale t := by
  simp only [logScale, UExp.weaken, cons, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.cases_zero, Fin.cases_succ]
  ring

/-! ## Pulling a scaling back along a substitution

`logScale_subst` and `logScale_weaken` are both instances of one fact, and the
general form is what a denotation of unit-polymorphic terms needs: a scaling of
the *target* scope induces one on the source, by scaling what each variable was
substituted by. -/

/-- **Pulling a scaling back along a unit substitution.** Base units keep their
magnitudes; a variable gets the magnitude of whatever was substituted for it. -/
def pull (ψ : Scaling B k₀) (η : Fin k → UExp B k₀) : Scaling B k :=
  ⟨ψ.base, fun i => ψ.logScale (η i)⟩

/-- **The substitution lemma, in general.** Scaling a substituted expression is
scaling the original under the pulled-back scaling.

Pure exponent arithmetic, as before: substitution is a linear map and `logScale`
is a linear functional, so this is a change in summation order. -/
theorem logScale_pull (ψ : Scaling B k₀) (η : Fin k → UExp B k₀) (u : UExp B k) :
    (ψ.pull η).logScale u = ψ.logScale (substU η u) := by
  have hb : ∑ b, ((substU η u).base b : ℝ) * ψ.base b
      = (∑ b, (u.base b : ℝ) * ψ.base b)
        + ∑ i, (u.vars i : ℝ) * ∑ b, ((η i).base b : ℝ) * ψ.base b := by
    simp only [substU_base, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1
    exact Finset.sum_comm
  have hv : ∑ v, ((substU η u).vars v : ℝ) * ψ.vars v
      = ∑ i, (u.vars i : ℝ) * ∑ v, ((η i).vars v : ℝ) * ψ.vars v := by
    simp only [substU_vars, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    exact Finset.sum_comm
  simp only [logScale, pull, hb, hv, mul_add, Finset.sum_add_distrib]
  ring

theorem scale_pull (ψ : Scaling B k₀) (η : Fin k → UExp B k₀) (u : UExp B k) :
    (ψ.pull η).scale u = ψ.scale (substU η u) := by
  simp [scale, logScale_pull]

/-- A variable scales by exactly its own factor. -/
@[simp] theorem logScale_ofVar (ψ : Scaling B k) (i : Fin k) :
    ψ.logScale (Term.ofVar i) = ψ.vars i := by
  simp only [logScale, Term.ofVar, Rat.cast_zero, zero_mul, Finset.sum_const_zero,
    zero_add, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one, ite_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Pulling back along weakening drops the fresh variable.** Whatever factor
it was given cannot matter, because nothing in scope mentions it. -/
@[simp] theorem pull_weaken (ψ : Scaling B k) (s : ℝ) :
    (ψ.cons s).pull (fun i : Fin k => Term.ofVar i.succ) = ψ := by
  cases ψ; simp [pull, cons, logScale_ofVar]

/-- **Pulling back along an instantiation extends by the instantiated unit's
magnitude.** This is `logScale_subst` read as a statement about scalings. -/
@[simp] theorem pull_subst (ψ : Scaling B k) (σ : UExp B k) :
    ψ.pull (Fin.cons σ (idU B k)) = ψ.cons (ψ.logScale σ) := by
  cases ψ with | mk base vars =>
  simp only [pull, cons, Scaling.mk.injEq, true_and]
  refine funext fun i => ?_
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [idU]

/-- Pulling back along the identity substitution changes nothing. -/
@[simp] theorem pull_id (ψ : Scaling B k) : ψ.pull (idU B k) = ψ := by
  cases ψ; simp [pull, idU]

/-- Pulling back at the closed scope changes nothing. -/
@[simp] theorem pull_nil (ψ : Scaling B 0) : ψ.pull (nilU B) = ψ := by
  cases ψ; simp only [pull, Scaling.mk.injEq, true_and]
  exact funext fun i => i.elim0

/-- Pulling back along an instantiation of the outermost variable. -/
@[simp] theorem pull_cons (ψ : Scaling B k₀) (η : Fin k → UExp B k₀) (μ : UExp B k₀) :
    ψ.pull (Fin.cons μ η) = (ψ.pull η).cons (ψ.logScale μ) := by
  simp only [pull, cons, Scaling.mk.injEq, true_and]
  exact funext fun i => Fin.cases rfl (fun _ => rfl) i

/-- **Pulling back under a binder.** Lifting a substitution past a unit binder
and pulling back is the same as pulling back and then extending. -/
@[simp] theorem pull_liftU (ψ : Scaling B k₀) (η : Fin k → UExp B k₀) (s : ℝ) :
    (ψ.cons s).pull (liftU η) = (ψ.pull η).cons s := by
  have h : ∀ i : Fin (k + 1),
      (ψ.cons s).logScale (liftU η i)
        = (Fin.cons s (fun i => ψ.logScale (η i)) : Fin (k + 1) → ℝ) i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [liftU, cons]
    · simp [liftU]
  simp only [pull, cons, Scaling.mk.injEq, true_and]
  exact funext h

/-! ## The trivial scaling

Scaling everything by `1`: the identity, and the reference point the Pi theorem
collapses a polymorphic type down to. -/

/-- The scaling that changes nothing. -/
def id (B : Type) (k : ℕ) : Scaling B k := ⟨fun _ => 0, fun _ => 0⟩

@[simp] theorem logScale_id (t : UExp B k) : (Scaling.id B k).logScale t = 0 := by
  simp [logScale, Scaling.id]

@[simp] theorem scale_id (t : UExp B k) : (Scaling.id B k).scale t = 1 := by
  simp [scale]

end Scaling

end LambdaS

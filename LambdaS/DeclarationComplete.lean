/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Determinacy
import LambdaS.RationalSolver

/-!
# Executable completeness of unit declarations

Combine the declared ratio vectors with the dimension rows. Rational solving
against each standard basis vector decides whether these columns span the
unit space. For sound declarations this is exactly the condition that every
dimensionless ratio is constrained. Consistency is checked separately.
-/

namespace LambdaS.DeclarationComplete

open scoped BigOperators

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
  [UnitSys B D] {m d n k : ℕ}

/-- Check that the supplied vectors span by solving for every standard basis vector. -/
def checkSpan (enum : Fin m ≃ B) (vectors : Fin k → B → ℚ) : Bool :=
  (List.finRange m).all fun b =>
    (RationalSolver.solve (Matrix.of fun a i => vectors i (enum a))
      (fun a => if a = b then (1 : ℚ) else 0)).isSome

omit [Fintype B] [Fintype D] [DecidableEq D] [UnitSys B D] in
private theorem checkSpan_iff_coefficients (enum : Fin m ≃ B) (vectors : Fin k → B → ℚ) :
    checkSpan enum vectors = true ↔
      ∀ b : B, ∃ c : Fin k → ℚ,
        ∀ a : B, ∑ i, c i * vectors i a = (Pi.single b 1 : B → ℚ) a := by
  simp only [checkSpan, List.all_eq_true, List.mem_finRange, forall_const,
    RationalSolver.solve_isSome_iff, Matrix.of_apply, smul_eq_mul]
  constructor
  · intro h b
    obtain ⟨c, hc⟩ := h (enum.symm b)
    refine ⟨c, fun a => ?_⟩
    have heq : enum.symm a = enum.symm b ↔ a = b := enum.symm.injective.eq_iff
    simpa [mul_comm, Pi.single_apply, heq] using hc (enum.symm a)
  · intro h b
    obtain ⟨c, hc⟩ := h (enum b)
    refine ⟨c, fun a => ?_⟩
    simpa [mul_comm, Pi.single_apply, enum.injective.eq_iff] using hc (enum a)

omit [Fintype D] [DecidableEq D] [UnitSys B D] in
/-- The executable span check is sound and complete. -/
theorem checkSpan_iff (enum : Fin m ≃ B) (vectors : Fin k → B → ℚ) :
    checkSpan enum vectors = true ↔ Submodule.span ℚ (Set.range vectors) = ⊤ :=
  (checkSpan_iff_coefficients enum vectors).trans
    (Decl.span_eq_top_iff_basis_coefficients vectors).symm

/-- One row per dimension, over the base-unit coordinates. -/
def dimensionRows : D → B → ℚ := fun e b => (UnitSys.dim (D := D) b).base e

/-- Declaration vectors followed by dimension rows, explicitly enumerated. -/
def combined (dims : Fin d ≃ D) (ds : Fin n → Decl B) : Fin (n + d) → B → ℚ :=
  fun i => Sum.elim (fun j => (ds j).ratio.base) (fun e => dimensionRows (dims e))
    (finSumFinEquiv.symm i)

/-- True when the declaration vectors and dimension rows span all unit coordinates. -/
def check (enum : Fin m ≃ B) (dims : Fin d ≃ D) (ds : Fin n → Decl B) : Bool :=
  checkSpan enum (combined dims ds)

omit [Fintype B] [Fintype D] [DecidableEq D] in
private theorem combined_range (dims : Fin d ≃ D) (ds : Fin n → Decl B) :
    Set.range (combined dims ds) =
      Set.range (Sum.elim (fun i => (ds i).ratio.base) (dimensionRows (B := B) (D := D))) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    cases h : finSumFinEquiv.symm i with
    | inl j => exact ⟨Sum.inl j, by simp [combined, h]⟩
    | inr e => exact ⟨Sum.inr (dims e), by simp [combined, h]⟩
  · rintro ⟨i, rfl⟩
    cases i with
    | inl j => exact ⟨finSumFinEquiv (Sum.inl j), by simp [combined]⟩
    | inr e => exact ⟨finSumFinEquiv (Sum.inr (dims.symm e)), by simp [combined]⟩

omit [DecidableEq B] [Fintype D] [DecidableEq D] in
private theorem dimensionless_iff (r : UExp B 0) :
    dimOf (D := D) (DCtx.nil D) r = 1 ↔
      ∀ e : D, ∑ b, dimensionRows e b * r.base b = 0 := by
  constructor
  · intro h e
    have he := congrArg (fun z : DExp D 0 => z.base e) h
    simpa [dimOf, dimensionRows, mul_comm] using he
  · intro h
    apply Term.ext'
    · funext e
      simpa [dimOf, dimensionRows, mul_comm] using h e
    · funext e; exact e.elim0

omit [Fintype D] [DecidableEq D] in
/-- Sound declarations make the executable combined-span check equivalent to
covering the full kernel of the dimension map. -/
theorem check_iff_span_dimensionless (enum : Fin m ≃ B) (dims : Fin d ≃ D)
    (ds : Fin n → Decl B) (hsound : ∀ i, Decl.Sound (D := D) (ds i)) :
    check enum dims ds = true ↔
      ∀ r : UExp B 0, dimOf (D := D) (DCtx.nil D) r = 1 → r.base ∈ Decl.ratioSpan ds := by
  rw [check, checkSpan_iff, combined_range]
  have hs : ∀ i (e : D), ∑ b, dimensionRows e b * (ds i).ratio.base b = 0 :=
    fun i => (dimensionless_iff _).mp (Decl.ratio_dimensionless (hsound i))
  rw [Decl.combined_span_eq_top_iff _ _ hs]
  constructor
  · intro h r hr
    exact h r.base ((dimensionless_iff r).mp hr)
  · intro h x hx
    let r : UExp B 0 := ⟨x, Fin.elim0⟩
    exact h r ((dimensionless_iff r).mpr hx)

omit [Fintype D] [DecidableEq D] in
/-- For consistent sound declarations, completeness means every dimensionless
ratio has the same factor in every satisfying valuation. -/
theorem check_iff_determined (enum : Fin m ≃ B) (dims : Fin d ≃ D)
    (ds : Fin n → Decl B) (hsound : ∀ i, Decl.Sound (D := D) (ds i))
    (hconsistent : ∃ V : Scaling B 0, ∀ i, Decl.Satisfies V (ds i)) :
    check enum dims ds = true ↔
      ∀ r : UExp B 0, dimOf (D := D) (DCtx.nil D) r = 1 → Decl.Determined ds r := by
  rw [check_iff_span_dimensionless enum dims ds hsound]
  simp_rw [Decl.determined_iff_mem_span hconsistent]

omit [Fintype D] [DecidableEq D] in
/-- The user-facing completeness statement: every legal conversion has a factor
fixed by the declarations, provided the declaration set is consistent. -/
theorem check_iff_all_conversions_determined (enum : Fin m ≃ B) (dims : Fin d ≃ D)
    (ds : Fin n → Decl B) (hsound : ∀ i, Decl.Sound (D := D) (ds i))
    (hconsistent : ∃ V : Scaling B 0, ∀ i, Decl.Satisfies V (ds i)) :
    check enum dims ds = true ↔
      ∀ u v : UExp B 0, SameDim (DCtx.nil D) u v → Decl.Determined ds (Term.div u v) := by
  rw [check_iff_determined enum dims ds hsound hconsistent]
  constructor
  · intro h u v huv
    exact h _ (dimOf_ratio_one _ huv)
  · intro h r hr
    have hs : SameDim (DCtx.nil D) r 1 := by
      rw [SameDim, hr, dimOf_one]
    have hd := h r 1 hs
    have heq : Term.div r 1 = r := by
      apply Term.ext' <;> funext i <;> simp
    rwa [heq] at hd

/-! Executable boundary checks for the standard-basis solving loop. -/

#guard checkSpan (Equiv.refl (Fin 2)) ![![(1 : ℚ), -1], ![1, 1]]
#guard !(checkSpan (Equiv.refl (Fin 2)) ![![(1 : ℚ), -1]])
#guard checkSpan (Equiv.refl (Fin 0)) (fun _ : Fin 0 => Fin.elim0)

section Checks

local instance : UnitSys (Fin 2) (Fin 1) where
  dim _ := Term.ofBase 0

private def linkedUnits : Decl (Fin 2) :=
  ⟨0, 3, by norm_num, Term.ofBase 1⟩

-- Two units of one dimension need a declaration relating their magnitudes.
#guard !(check (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1)) (fun i : Fin 0 => i.elim0))
#guard check (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1)) ![linkedUnits]
-- Redundant declarations do not invalidate completeness.
#guard check (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1)) ![linkedUnits, linkedUnits]

end Checks

end LambdaS.DeclarationComplete

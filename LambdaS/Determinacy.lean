/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Declare
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Which conversion factors declarations determine

A consistent declaration family fixes precisely the rational span of its
ratios. Outside that span a rational separating functional perturbs a
satisfying valuation without changing any declared factor.
-/

namespace LambdaS.Decl

open scoped BigOperators

variable {B : Type} [Fintype B] [DecidableEq B] {n : ℕ}

/-- A ratio is determined when every satisfying valuation gives it the same factor. -/
def Determined (ds : Fin n → Decl B) (r : UExp B 0) : Prop :=
  ∀ V V' : Scaling B 0, (∀ i, Satisfies V (ds i)) →
    (∀ i, Satisfies V' (ds i)) → V.scale r = V'.scale r

/-- The rational vector space constrained by the declarations. -/
def ratioSpan (ds : Fin n → Decl B) : Submodule ℚ (B → ℚ) :=
  Submodule.span ℚ (Set.range fun i => (ds i).ratio.base)

private def logFunctional (V : Scaling B 0) : (B → ℚ) →ₗ[ℚ] ℝ where
  toFun x := ∑ b, (x b : ℝ) * V.base b
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Rat.smul_def, Finset.mul_sum, mul_assoc]

omit [DecidableEq B] in
private theorem logFunctional_apply (V : Scaling B 0) (r : UExp B 0) :
    logFunctional V r.base = V.logScale r := by
  simp [logFunctional, Scaling.logScale]

omit [Fintype B] in
/-- Membership in the declared span is a finite system of rational equations. -/
theorem mem_ratioSpan_iff_coefficients (ds : Fin n → Decl B) (r : UExp B 0) :
    r.base ∈ ratioSpan ds ↔
      ∃ c : Fin n → ℚ, ∀ b, ∑ i, c i * (ds i).ratio.base b = r.base b := by
  rw [ratioSpan, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun b => by simpa [Finset.sum_apply, smul_eq_mul] using congrFun hc b⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, funext fun b => by simpa [Finset.sum_apply, smul_eq_mul] using hc b⟩

theorem determined_of_mem_ratioSpan {ds : Fin n → Decl B} {r : UExp B 0}
    (hr : r.base ∈ ratioSpan ds) : Determined ds r := by
  intro V V' hV hV'
  have heq : ∀ x ∈ ratioSpan ds, logFunctional V x = logFunctional V' x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [logFunctional_apply, logFunctional_apply,
          (satisfies_iff_log.mp (hV i)), (satisfies_iff_log.mp (hV' i))]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  exact congrArg Real.exp (by simpa [logFunctional_apply] using heq r.base hr)

private noncomputable def separatingScaling (f : Module.Dual ℚ (B → ℚ)) : Scaling B 0 :=
  ⟨fun b => (f (Pi.single b 1) : ℝ), Fin.elim0⟩

private theorem separatingScaling_log (f : Module.Dual ℚ (B → ℚ)) (r : UExp B 0) :
    (separatingScaling f).logScale r = (f r.base : ℝ) := by
  have hrep := LinearMap.pi_apply_eq_sum_univ f r.base
  have hs : ∀ b : B, (fun a => if b = a then (1 : ℚ) else 0) = Pi.single b 1 := by
    intro b
    funext a
    simp [Pi.single_apply, eq_comm]
  simp only [hs, smul_eq_mul] at hrep
  simp only [Scaling.logScale, separatingScaling, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero]
  exact_mod_cast hrep.symm

/-- Necessity requires consistency: without a satisfying valuation every ratio
would satisfy the universal definition vacuously. -/
theorem determined_iff_mem_span {ds : Fin n → Decl B}
    (hconsistent : ∃ V : Scaling B 0, ∀ i, Satisfies V (ds i)) (r : UExp B 0) :
    Determined ds r ↔ r.base ∈ ratioSpan ds := by
  constructor
  · intro hd
    by_contra hr
    obtain ⟨V, hV⟩ := hconsistent
    obtain ⟨f, hfr, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hr inferInstance
    have hfzero : ∀ x ∈ ratioSpan ds, f x = 0 := by
      intro x hx
      have hm : f x ∈ (ratioSpan ds).map f := ⟨x, hx, rfl⟩
      simpa [hf] using hm
    have hrows : ∀ i, (separatingScaling f).logScale (ds i).ratio = 0 := by
      intro i
      rw [separatingScaling_log, hfzero _ (Submodule.subset_span ⟨i, rfl⟩)]
      simp
    have hV' : ∀ i, Satisfies (V.comp (separatingScaling f)) (ds i) := by
      intro i
      rw [satisfies_iff_log, Scaling.logScale_comp, hrows, add_zero]
      exact satisfies_iff_log.mp (hV i)
    have heq := Real.exp_injective (hd V (V.comp (separatingScaling f)) hV hV')
    rw [Scaling.logScale_comp, separatingScaling_log] at heq
    have hz : (f r.base : ℝ) = 0 := by linarith
    exact hfr (by exact_mod_cast hz)
  · exact determined_of_mem_ratioSpan

/-- Executable solvers may decide determinacy by solving this rational system. -/
theorem determined_iff_coefficients {ds : Fin n → Decl B}
    (hconsistent : ∃ V : Scaling B 0, ∀ i, Satisfies V (ds i)) (r : UExp B 0) :
    Determined ds r ↔
      ∃ c : Fin n → ℚ, ∀ b, ∑ i, c i * (ds i).ratio.base b = r.base b :=
  (determined_iff_mem_span hconsistent r).trans (mem_ratioSpan_iff_coefficients ds r)

section Completeness

variable {D : Type} [Fintype D]

private def dotFunctional (x : B → ℚ) : (B → ℚ) →ₗ[ℚ] ℚ where
  toFun y := ∑ b, y b * x b
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, mul_assoc]

private theorem dual_apply_eq_dot (f : Module.Dual ℚ (B → ℚ)) (x : B → ℚ) :
    f x = ∑ b, x b * f (Pi.single b 1) := by
  have h := LinearMap.pi_apply_eq_sum_univ f x
  have hs : ∀ b : B, (fun a => if b = a then (1 : ℚ) else 0) = Pi.single b 1 := by
    intro b
    funext a
    simp [Pi.single_apply, eq_comm]
  simpa only [hs, smul_eq_mul] using h

omit [Fintype D] in
/-- A kernel-basis-free completeness test. If declaration vectors `S` are
annihilated by all dimension rows, they span that kernel exactly when those
vectors together with the dimension rows span the whole unit space. -/
theorem span_sup_rows_eq_top_iff (S : Submodule ℚ (B → ℚ)) (rows : D → B → ℚ)
    (hsound : ∀ x ∈ S, ∀ d, ∑ b, rows d b * x b = 0) :
    S ⊔ Submodule.span ℚ (Set.range rows) = ⊤ ↔
      ∀ x : B → ℚ, (∀ d, ∑ b, rows d b * x b = 0) → x ∈ S := by
  constructor
  · intro htop x hx
    have hmem : x ∈ S ⊔ Submodule.span ℚ (Set.range rows) := by rw [htop]; trivial
    obtain ⟨s, hs, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
    have hyzero : ∀ d, ∑ b, rows d b * y b = 0 := by
      intro d
      have h := hx d
      rw [← hxy] at h
      simpa [mul_add, Finset.sum_add_distrib, hsound s hs d] using h
    have hann : ∀ z ∈ Submodule.span ℚ (Set.range rows), dotFunctional y z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨d, rfl⟩ := hz; exact hyzero d
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul a b _ hb => simp [hb]
    have hy0 : y = 0 := dotProduct_self_eq_zero.mp (hann y hy)
    rw [← hxy, hy0, add_zero]
    exact hs
  · intro hker
    by_contra htop
    have hne : S ⊔ Submodule.span ℚ (Set.range rows) < ⊤ := lt_top_iff_ne_top.mpr htop
    obtain ⟨x, hx⟩ := SetLike.exists_of_lt hne
    obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx.2 inferInstance
    have hfzero : ∀ z ∈ S ⊔ Submodule.span ℚ (Set.range rows), f z = 0 := by
      intro z hz
      have hm : f z ∈ (S ⊔ Submodule.span ℚ (Set.range rows)).map f := ⟨z, hz, rfl⟩
      simpa [hf] using hm
    let a : B → ℚ := fun b => f (Pi.single b 1)
    have ha : a ∈ S := hker a (fun d => by
      rw [← dual_apply_eq_dot]
      exact hfzero _ (Submodule.mem_sup_right (Submodule.subset_span ⟨d, rfl⟩)))
    have haa : ∑ b, a b * a b = 0 := by
      rw [← dual_apply_eq_dot]
      exact hfzero a (Submodule.mem_sup_left ha)
    have ha0 : a = 0 := dotProduct_self_eq_zero.mp haa
    apply hfx
    rw [dual_apply_eq_dot]
    change ∑ b, x b * a b = 0
    simp [ha0]

/-- Spanning the whole unit space is equivalent to solving for each standard
basis vector. This is a finite family of ordinary rational linear systems. -/
theorem span_eq_top_iff_basis_coefficients {ι : Type} [Fintype ι]
    (vectors : ι → B → ℚ) :
    Submodule.span ℚ (Set.range vectors) = ⊤ ↔
      ∀ b : B, ∃ c : ι → ℚ,
        ∀ a : B, ∑ i, c i * vectors i a = (Pi.single b 1 : B → ℚ) a := by
  constructor
  · intro h b
    have hb : Pi.single b (1 : ℚ) ∈ Submodule.span ℚ (Set.range vectors) := by
      rw [h]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hb
    obtain ⟨c, hc⟩ := hb
    exact ⟨c, fun a => by simpa [Finset.sum_apply, smul_eq_mul] using congrFun hc a⟩
  · intro h
    apply top_unique
    intro x _
    have hb : ∀ b : B, Pi.single b (1 : ℚ) ∈ Submodule.span ℚ (Set.range vectors) := by
      intro b
      obtain ⟨c, hc⟩ := h b
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, funext fun a => by simpa [Finset.sum_apply, smul_eq_mul] using hc a⟩
    have hx : (∑ b, x b • Pi.single b (1 : ℚ)) ∈
        Submodule.span ℚ (Set.range vectors) :=
      Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (hb b))
    have heq : (∑ b, x b • Pi.single b (1 : ℚ)) = x := by
      funext a
      simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
    rwa [heq] at hx

omit [Fintype D] in
/-- The concrete combined-column completeness criterion. Soundness says that
every declaration vector is annihilated by every dimension row. -/
theorem combined_span_eq_top_iff (vectors : Fin n → B → ℚ) (rows : D → B → ℚ)
    (hsound : ∀ i d, ∑ b, rows d b * vectors i b = 0) :
    Submodule.span ℚ (Set.range (Sum.elim vectors rows)) = ⊤ ↔
      ∀ x : B → ℚ, (∀ d, ∑ b, rows d b * x b = 0) →
        x ∈ Submodule.span ℚ (Set.range vectors) := by
  rw [Set.Sum.elim_range, Submodule.span_union]
  apply span_sup_rows_eq_top_iff
  intro x hx d
  have hz : dotFunctional (rows d) x = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        simpa [dotFunctional, mul_comm] using hsound i d
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hb]
  simpa [dotFunctional, mul_comm] using hz

end Completeness

end LambdaS.Decl

/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Declare
import LambdaS.RationalSolver
import LambdaS.LogFactor
import LambdaS.Determinacy
import LambdaS.DeclarationComplete

/-!
# Executable declaration solving

The solver uses an explicit enumeration of the finite base-unit universe.
This enumeration is input data, rather than a noncomputable choice of order.
-/

namespace LambdaS.DeclSolver

open scoped BigOperators

variable {B : Type} [Fintype B] [DecidableEq B] {m n : ℕ}

/-- The rational coefficient matrix of declaration equations. -/
def matrix (enum : Fin m ≃ B) (ds : Fin n → Decl B) : Matrix (Fin n) (Fin m) ℚ :=
  Matrix.of fun i j => (ds i).ratio.base (enum j)

/-- Real log-magnitudes in the supplied base-unit order. -/
def valuation (enum : Fin m ≃ B) (x : Fin m → ℝ) : Scaling B 0 :=
  ⟨fun b => x (enum.symm b), Fin.elim0⟩

omit [DecidableEq B] in
/-- Reindexing changes neither the unit nor its magnitude. -/
theorem logScale_valuation (enum : Fin m ≃ B) (x : Fin m → ℝ) (u : UExp B 0) :
    (valuation enum x).logScale u = ∑ j, (u.base (enum j) : ℝ) * x j := by
  simp only [Scaling.logScale, valuation, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  simpa using (Equiv.sum_comp enum (fun b => (u.base b : ℝ) * x (enum.symm b))).symm

/-- Declaration satisfaction is exactly the linear system in logarithms. -/
theorem satisfies_valuation_iff (enum : Fin m ≃ B) (ds : Fin n → Decl B)
    (x : Fin m → ℝ) :
    (∀ i, Decl.Satisfies (valuation enum x) (ds i)) ↔
      ∀ i, ∑ j, matrix enum ds i j • x j = Real.log ((ds i).factor : ℝ) := by
  simp only [Decl.satisfies_iff_log, logScale_valuation, matrix, Matrix.of_apply, Rat.smul_def]

omit [Fintype B] [DecidableEq B] in
/-- Every supplied valuation has coordinates in the explicit enumeration. -/
theorem valuation_coordinates (enum : Fin m ≃ B) (V : Scaling B 0) :
    valuation enum (fun j => V.base (enum j)) = V := by
  cases V
  simp only [valuation, Equiv.apply_symm_apply]
  congr
  funext i
  exact i.elim0

/-- Compute rational witnesses expressing a queried ratio through declarations.
Failure means that the declarations leave its factor undetermined. -/
def factorCoefficients (enum : Fin m ≃ B) (ds : Fin n → Decl B) (r : UExp B 0) :
    Option (Fin n → ℚ) :=
  RationalSolver.solve (Matrix.of fun j i => (ds i).ratio.base (enum j)) (fun j => r.base (enum j))

omit [Fintype B] in
/-- Successful factor lookup supplies an exact dependency witness. -/
theorem factorCoefficients_sound (enum : Fin m ≃ B) (ds : Fin n → Decl B)
    (r : UExp B 0) {c : Fin n → ℚ} (h : factorCoefficients enum ds r = some c) :
    ∀ b, ∑ i, c i * (ds i).ratio.base b = r.base b := by
  have hs := RationalSolver.solve_sound h
  intro b
  simpa [matrix, Matrix.of_apply, smul_eq_mul, mul_comm] using hs (enum.symm b)

omit [Fintype B] in
/-- Lookup decides span membership, including failure, using exact rationals. -/
theorem factorCoefficients_isSome_iff (enum : Fin m ≃ B) (ds : Fin n → Decl B)
    (r : UExp B 0) :
    (factorCoefficients enum ds r).isSome ↔
      ∃ c : Fin n → ℚ, ∀ b, ∑ i, c i * (ds i).ratio.base b = r.base b := by
  rw [factorCoefficients, RationalSolver.solve_isSome_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun b => by simpa [matrix, Matrix.of_apply, smul_eq_mul, mul_comm] using hc (enum.symm b)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun j => by simpa [matrix, Matrix.of_apply, smul_eq_mul, mul_comm] using hc (enum j)⟩

/-- Solve declaration equations in exact logarithmic numbers. A solution fixes
free log-magnitudes to zero, but its particular choices do not determine a
conversion unless the separate factor-witness check succeeds. -/
def solve (enum : Fin m ≃ B) (ds : Fin n → Decl B) : Option (Fin m → LogFactor) :=
  RationalSolver.solve (matrix enum ds) (fun i => LogFactor.ofRat (ds i).factor (ds i).pos)

/-- Every returned exact solution denotes a valuation satisfying every declaration. -/
theorem solve_sound (enum : Fin m ≃ B) (ds : Fin n → Decl B)
    {x : Fin m → LogFactor} (h : solve enum ds = some x) :
    ∀ i, Decl.Satisfies (valuation enum (fun j => LogFactor.interpret (x j))) (ds i) := by
  apply (satisfies_valuation_iff enum ds _).mpr
  have hs := RationalSolver.solve_sound h
  intro i
  have hr := congrArg LogFactor.interpret (hs i)
  simpa only [map_sum, map_smul, LogFactor.interpret_ofRat] using hr

/-- Executable solving decides existence of a real satisfying valuation.
No assumption that the magnitudes or their logarithms are rational is needed. -/
theorem solve_isSome_iff (enum : Fin m ≃ B) (ds : Fin n → Decl B) :
    (solve enum ds).isSome ↔ ∃ V : Scaling B 0, ∀ i, Decl.Satisfies V (ds i) := by
  rw [solve, RationalSolver.solve_isSome_iff,
    ← RationalSolver.solvable_map_iff LogFactor.interpret LogFactor.interpret_injective]
  simp only [LogFactor.interpret_ofRat]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨valuation enum x, (satisfies_valuation_iff enum ds x).mpr hx⟩
  · rintro ⟨V, hV⟩
    refine ⟨fun j => V.base (enum j), ?_⟩
    apply (satisfies_valuation_iff enum ds _).mp
    rwa [valuation_coordinates]

/-- Interpret the factor witness without choosing magnitudes for unconstrained units. -/
def factorLog (ds : Fin n → Decl B) (c : Fin n → ℚ) : LogFactor :=
  ∑ i, c i • LogFactor.ofRat (ds i).factor (ds i).pos

/-- A linear combination of declaration ratios fixes the same combination of log-factors. -/
theorem factorLog_correct (ds : Fin n → Decl B) (r : UExp B 0) (c : Fin n → ℚ)
    (hc : ∀ b, ∑ i, c i * (ds i).ratio.base b = r.base b)
    (V : Scaling B 0) (hV : ∀ i, Decl.Satisfies V (ds i)) :
    LogFactor.interpret (factorLog ds c) = V.logScale r := by
  simp only [factorLog, map_sum, map_smul, LogFactor.interpret_ofRat, Rat.smul_def]
  have hlog : ∀ i, Real.log ((ds i).factor : ℝ) = V.logScale (ds i).ratio :=
    fun i => (Decl.satisfies_iff_log.mp (hV i)).symm
  simp only [hlog, Scaling.logScale, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  have hcast := congrArg (fun q : ℚ => (q : ℝ)) (hc b)
  push_cast at hcast
  simpa [mul_assoc] using hcast

/-- Exact conversion lookup. An unresolved ratio returns none, even if an
arbitrary satisfying valuation could assign it a numerical value. -/
def conversion (enum : Fin m ≃ B) (ds : Fin n → Decl B) (u v : UExp B 0) :
    Option LogFactor := (factorCoefficients enum ds (Term.div u v)).map (factorLog ds)

/-- The returned exact logarithm gives the conversion factor in every satisfying valuation. -/
theorem conversion_correct (enum : Fin m ≃ B) (ds : Fin n → Decl B)
    (u v : UExp B 0) {q : LogFactor} (h : conversion enum ds u v = some q)
    (V : Scaling B 0) (hV : ∀ i, Decl.Satisfies V (ds i)) :
    Real.exp (LogFactor.interpret q) = conv V u v := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [factorLog_correct ds (Term.div u v) c (factorCoefficients_sound enum ds _ hc) V hV]
  exact (conv_eq_scale_div V u v).symm

/-- The executable factor test is exactly semantic determinacy on consistent declarations. -/
theorem factorCoefficients_iff_determined (enum : Fin m ≃ B) (ds : Fin n → Decl B)
    (hc : ∃ V : Scaling B 0, ∀ i, Decl.Satisfies V (ds i)) (r : UExp B 0) :
    (factorCoefficients enum ds r).isSome ↔ Decl.Determined ds r := by
  rw [factorCoefficients_isSome_iff, Decl.determined_iff_coefficients hc r]

/-- Success of conversion lookup decides determinacy, rather than merely producing a guess. -/
theorem conversion_isSome_iff (enum : Fin m ≃ B) (ds : Fin n → Decl B)
    (hc : ∃ V : Scaling B 0, ∀ i, Decl.Satisfies V (ds i)) (u v : UExp B 0) :
    (conversion enum ds u v).isSome ↔ Decl.Determined ds (Term.div u v) := by
  simp only [conversion, Option.isSome_map]
  exact factorCoefficients_iff_determined enum ds hc _

/-- An inspectable exact positive factor: the positive degree-th root of radicand. -/
structure ExactFactor where
  radicand : ℚ
  degree : ℕ
  radicand_pos : 0 < radicand
  degree_pos : 0 < degree
  deriving Repr

/-- Real interpretation only; constructing and comparing the output data is executable. -/
noncomputable def ExactFactor.value (q : ExactFactor) : ℝ :=
  Real.exp (Real.log (q.radicand : ℝ) / q.degree)

/-- Preserve a finite expression so its radical representation can be inspected. -/
def factorExpr (ds : Fin n → Decl B) (c : Fin n → ℚ) : LogFactor.Expr :=
  List.ofFn fun i => (c i, ⟨(ds i).factor, (ds i).pos⟩)

omit [Fintype B] [DecidableEq B] in
theorem factorExpr_eval (ds : Fin n → Decl B) (c : Fin n → ℚ) :
    LogFactor.eval (factorExpr ds c) = LogFactor.interpret (factorLog ds c) := by
  simp only [factorExpr, LogFactor.eval_ofFn, factorLog, map_sum, map_smul,
    LogFactor.interpret_ofRat, Rat.smul_def]

/-- Denominator clearing constructs a positive rational radicand and positive degree. -/
def exactFactor (ds : Fin n → Decl B) (c : Fin n → ℚ) : ExactFactor :=
  let xs := factorExpr ds c
  ⟨(LogFactor.radical xs).1, (LogFactor.radical xs).2,
    (LogFactor.radical_pos xs).1, (LogFactor.radical_pos xs).2⟩

omit [Fintype B] [DecidableEq B] in
theorem exactFactor_value (ds : Fin n → Decl B) (c : Fin n → ℚ) :
    (exactFactor ds c).value = Real.exp (LogFactor.interpret (factorLog ds c)) := by
  unfold ExactFactor.value exactFactor
  rw [LogFactor.radical_log, factorExpr_eval]
  congr 1
  have hn : ((LogFactor.radical (factorExpr ds c)).2 : ℝ) ≠ 0 := by
    exact_mod_cast (LogFactor.radical_pos (factorExpr ds c)).2.ne'
  exact mul_div_cancel_left₀ _ hn

/-- Return an inspectable exact radical for a determined conversion. -/
def conversionExact (enum : Fin m ≃ B) (ds : Fin n → Decl B) (u v : UExp B 0) :
    Option ExactFactor := (factorCoefficients enum ds (Term.div u v)).map (exactFactor ds)

/-- The extracted radical is the conversion factor in every satisfying valuation. -/
theorem conversionExact_correct (enum : Fin m ≃ B) (ds : Fin n → Decl B)
    (u v : UExp B 0) {q : ExactFactor} (h : conversionExact enum ds u v = some q)
    (V : Scaling B 0) (hV : ∀ i, Decl.Satisfies V (ds i)) : q.value = conv V u v := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [exactFactor_value,
    factorLog_correct ds (Term.div u v) c (factorCoefficients_sound enum ds _ hc) V hV]
  exact (conv_eq_scale_div V u v).symm

section Checked

variable {D : Type} [Fintype D] [DecidableEq D] [UnitSys B D] {d : ℕ}

/-- A checked unit system carries its computed solution and evidence that
its declarations are sound, consistent, and determine every legal conversion. -/
structure Checked (enum : Fin m ≃ B) (dims : Fin d ≃ D) (ds : Fin n → Decl B) where
  magnitudes : Fin m → LogFactor
  sound : ∀ i, Decl.Sound (D := D) (ds i)
  solution : solve enum ds = some magnitudes
  complete : DeclarationComplete.check enum dims ds = true

/-- The complete executable declaration checker. -/
def check (enum : Fin m ≃ B) (dims : Fin d ≃ D) (ds : Fin n → Decl B) :
    Option (Checked enum dims ds) :=
  if hs : ∀ i, Decl.Sound (D := D) (ds i) then
    match hx : solve enum ds with
    | none => none
    | some x =>
        if hc : DeclarationComplete.check enum dims ds = true then
          some ⟨x, hs, hx, hc⟩
        else none
  else none

omit [Fintype D] [DecidableEq D] in
/-- Every checked system supplies a genuine satisfying valuation. -/
theorem Checked.consistent {enum : Fin m ≃ B} {dims : Fin d ≃ D} {ds : Fin n → Decl B}
    (cert : Checked enum dims ds) : ∃ V : Scaling B 0, ∀ i, Decl.Satisfies V (ds i) :=
  ⟨valuation enum (fun j => LogFactor.interpret (cert.magnitudes j)),
    solve_sound enum ds cert.solution⟩

omit [Fintype D] [DecidableEq D] in
/-- Every same-dimension conversion in a checked system is determined. -/
theorem Checked.determined {enum : Fin m ≃ B} {dims : Fin d ≃ D} {ds : Fin n → Decl B}
    (cert : Checked enum dims ds) (u v : UExp B 0) (h : SameDim (DCtx.nil D) u v) :
    Decl.Determined ds (Term.div u v) :=
  (DeclarationComplete.check_iff_all_conversions_determined enum dims ds
    cert.sound cert.consistent).mp cert.complete u v h

/-- Acceptance is equivalent to dimensional soundness, consistency, and
factor determinacy for every same-dimension pair. Rejection is complete. -/
theorem check_isSome_iff (enum : Fin m ≃ B) (dims : Fin d ≃ D) (ds : Fin n → Decl B) :
    (check enum dims ds).isSome ↔
      (∀ i, Decl.Sound (D := D) (ds i)) ∧
      (∃ V : Scaling B 0, ∀ i, Decl.Satisfies V (ds i)) ∧
      (∀ u v : UExp B 0, SameDim (DCtx.nil D) u v → Decl.Determined ds (Term.div u v)) := by
  constructor
  · intro h
    obtain ⟨cert, _⟩ := Option.isSome_iff_exists.mp h
    exact ⟨cert.sound, cert.consistent, cert.determined⟩
  · rintro ⟨hs, hv, hd⟩
    have hc := (DeclarationComplete.check_iff_all_conversions_determined enum dims ds hs hv).mpr hd
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((solve_isSome_iff enum ds).mpr hv)
    simp only [check, dif_pos hs]
    split <;> simp_all

omit [Fintype D] [DecidableEq D] in
/-- Factor extraction cannot fail for a legal conversion in a checked system. -/
theorem Checked.conversionExact_isSome {enum : Fin m ≃ B} {dims : Fin d ≃ D}
    {ds : Fin n → Decl B} (cert : Checked enum dims ds) (u v : UExp B 0)
    (h : SameDim (DCtx.nil D) u v) : (conversionExact enum ds u v).isSome := by
  simp only [conversionExact, Option.isSome_map]
  exact (factorCoefficients_iff_determined enum ds cert.consistent _).mpr
    (cert.determined u v h)

end Checked

end LambdaS.DeclSolver

/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Tactic

/-! Exact, executable arithmetic for rational linear combinations of logarithms.

Expressions are finite lists. Denominator clearing reduces equality to an exact
rational product test. Quotienting by this decidable equality gives a rational
module; its real interpretation is injective. No real arithmetic is executed.
-/

namespace LambdaS
namespace LogFactor

abbrev PositiveRat := {q : ℚ // 0 < q}
abbrev Expr := List (ℚ × PositiveRat)

noncomputable def eval : Expr → ℝ
  | [] => 0
  | (c, q) :: xs => (c : ℝ) * Real.log (q.val : ℝ) + eval xs

/-- Evaluate an explicitly indexed finite family of logarithm coefficients. -/
theorem eval_ofFn {n : ℕ} (c : Fin n → ℚ) (q : Fin n → PositiveRat) :
    eval (List.ofFn fun i => (c i, q i)) =
      ∑ i, (c i : ℝ) * Real.log ((q i).val : ℝ) := by
  induction n with
  | zero => simp [eval]
  | succ n ih =>
    rw [List.ofFn_succ, eval, Fin.sum_univ_succ]
    rw [ih]

/-- Return `(q,D)` such that the expression denotes `log q / D`.
The integer powers clear denominators without factoring any integer. -/
def radical : Expr → ℚ × ℕ
  | [] => (1, 1)
  | (c, q) :: xs =>
    let r := radical xs
    (q.val ^ (c.num * (r.2 : ℤ)) * r.1 ^ c.den, c.den * r.2)

theorem radical_pos (xs : Expr) : 0 < (radical xs).1 ∧ 0 < (radical xs).2 := by
  induction xs with
  | nil => simp [radical]
  | cons a xs ih =>
    rcases a with ⟨c, q⟩
    exact ⟨mul_pos (zpow_pos q.property _) (pow_pos ih.1 _), Nat.mul_pos c.den_pos ih.2⟩

theorem radical_log (xs : Expr) :
    Real.log ((radical xs).1 : ℝ) = ((radical xs).2 : ℝ) * eval xs := by
  induction xs with
  | nil => simp [radical, eval]
  | cons a xs ih =>
    rcases a with ⟨c, q⟩
    have hq : (0 : ℝ) < (q.val : ℝ) := by exact_mod_cast q.property
    have hr : (0 : ℝ) < ((radical xs).1 : ℝ) := by
      exact_mod_cast (radical_pos xs).1
    have hc : (c.den : ℝ) * (c : ℝ) = (c.num : ℝ) := by
      rw [Rat.cast_def]
      field_simp
    simp only [radical, Rat.cast_mul, Rat.cast_zpow, Rat.cast_pow,
      Nat.cast_mul, eval]
    rw [Real.log_mul (zpow_pos hq _).ne' (pow_pos hr _).ne',
      Real.log_zpow, Real.log_pow, ih]
    push_cast
    rw [← hc]
    ring

/-- The returned rational and positive degree specify the positive real factor
without evaluating a logarithm or a root in the executable representation. -/
theorem radical_exp (xs : Expr) :
    Real.exp (eval xs) ^ (radical xs).2 = ((radical xs).1 : ℝ) := by
  rw [← Real.exp_nat_mul, ← radical_log]
  apply Real.exp_log
  exact_mod_cast (radical_pos xs).1

/-- The executable zero test; its decision takes place entirely in `ℚ`. -/
def isZero (xs : Expr) : Bool := (radical xs).1 == 1

theorem isZero_iff (xs : Expr) : isZero xs = true ↔ eval xs = 0 := by
  have hp := radical_pos xs
  have hr : (0 : ℝ) < ((radical xs).1 : ℝ) := by exact_mod_cast hp.1
  have hd : (((radical xs).2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hp.2.ne'
  rw [isZero, beq_iff_eq]
  constructor
  · intro h
    have he := radical_log xs
    rw [h, Rat.cast_one, Real.log_one] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hd
  · intro h
    have he := radical_log xs
    rw [h, mul_zero] at he
    have hh : ((radical xs).1 : ℝ) = 1 := by
      calc
        ((radical xs).1 : ℝ) = Real.exp (Real.log ((radical xs).1 : ℝ)) :=
          (Real.exp_log hr).symm
        _ = 1 := by rw [he, Real.exp_zero]
    exact_mod_cast hh

theorem eval_append (xs ys : Expr) : eval (xs ++ ys) = eval xs + eval ys := by
  induction xs with
  | nil => simp [eval]
  | cons a xs ih => simp only [List.cons_append, eval, ih]; ring

def scaleExpr (c : ℚ) (xs : Expr) : Expr := xs.map fun a => (c * a.1, a.2)

theorem eval_scaleExpr (c : ℚ) (xs : Expr) : eval (scaleExpr c xs) = (c : ℝ) * eval xs := by
  induction xs with
  | nil => simp [scaleExpr, eval]
  | cons a xs ih =>
    simp only [scaleExpr, List.map_cons, eval, Rat.cast_mul] at *
    rw [ih]
    ring

instance exprSetoid : Setoid Expr where
  r xs ys := eval xs = eval ys
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

instance exprRelDecidable : DecidableRel exprSetoid.r := fun xs ys =>
  decidable_of_iff (isZero (xs ++ scaleExpr (-1) ys) = true) (by
    rw [isZero_iff, eval_append, eval_scaleExpr]
    simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul]
    exact sub_eq_zero.trans Iff.rfl)

end LogFactor

/-- Exact logarithms of positive rational numbers, closed under rational linear combinations. -/
def LogFactor := Quotient LogFactor.exprSetoid

namespace LogFactor

instance : DecidableEq LogFactor := Quotient.decidableEq

def ofExpr (xs : Expr) : LogFactor := Quotient.mk _ xs

noncomputable def value : LogFactor → ℝ := Quotient.lift eval (fun _ _ h => h)

theorem value_injective : Function.Injective value := by
  intro x y
  induction x using Quotient.inductionOn with | h xs =>
    induction y using Quotient.inductionOn with | h ys =>
      intro h
      exact Quotient.sound (show eval xs = eval ys from h)

instance : Zero LogFactor := ⟨ofExpr []⟩
instance : Add LogFactor := ⟨fun x y => Quotient.liftOn₂ x y (fun xs ys => ofExpr (xs ++ ys)) (by
  intro a b c d hac hbd
  apply Quotient.sound
  change eval (a ++ b) = eval (c ++ d)
  rw [eval_append, eval_append, hac, hbd])⟩
instance : SMul ℚ LogFactor := ⟨fun c x => Quotient.liftOn x
  (fun xs => ofExpr (scaleExpr c xs)) (by
    intro a b hab
    apply Quotient.sound
    change eval (scaleExpr c a) = eval (scaleExpr c b)
    rw [eval_scaleExpr, eval_scaleExpr, hab])⟩
instance : Neg LogFactor := ⟨fun x => (-1 : ℚ) • x⟩
instance : Sub LogFactor := ⟨fun x y => x + -y⟩
instance : SMul ℕ LogFactor := ⟨fun n x => (n : ℚ) • x⟩
instance : SMul ℤ LogFactor := ⟨fun n x => (n : ℚ) • x⟩

@[simp] theorem value_zero : value 0 = 0 := rfl

@[simp] theorem value_add (x y : LogFactor) : value (x + y) = value x + value y := by
  induction x using Quotient.inductionOn with | h xs =>
    induction y using Quotient.inductionOn with | h ys =>
      exact eval_append xs ys

@[simp] theorem value_smul (c : ℚ) (x : LogFactor) : value (c • x) = c • value x := by
  induction x using Quotient.inductionOn with | h xs =>
    exact eval_scaleExpr c xs

@[simp] theorem value_neg (x : LogFactor) : value (-x) = - value x := by
  change value ((-1 : ℚ) • x) = _
  rw [value_smul, neg_one_smul]

@[simp] theorem value_sub (x y : LogFactor) : value (x - y) = value x - value y := by
  change value (x + -y) = _
  rw [value_add, value_neg, sub_eq_add_neg]

@[simp] theorem value_nsmul (n : ℕ) (x : LogFactor) : value (n • x) = n • value x := by
  change value ((n : ℚ) • x) = _
  rw [value_smul]
  simp [Rat.smul_def]

@[simp] theorem value_zsmul (n : ℤ) (x : LogFactor) : value (n • x) = n • value x := by
  change value ((n : ℚ) • x) = _
  rw [value_smul]
  simp [Rat.smul_def]

instance : AddCommGroup LogFactor := fast_instance% Function.Injective.addCommGroup value value_injective
  value_zero value_add value_neg value_sub (fun x n => value_nsmul n x) (fun x n => value_zsmul n x)

instance : Module ℚ LogFactor := fast_instance% Function.Injective.module ℚ
  ⟨⟨value, value_zero⟩, value_add⟩ value_injective value_smul

/-- The real interpretation is noncomputable; all operations on its domain are executable. -/
noncomputable def interpret : LogFactor →ₗ[ℚ] ℝ where
  toFun := value
  map_add' := value_add
  map_smul' := value_smul

theorem interpret_injective : Function.Injective interpret := value_injective

theorem eq_iff_interpret (x y : LogFactor) : x = y ↔ interpret x = interpret y :=
  interpret_injective.eq_iff.symm

@[simp] theorem interpret_ofExpr (xs : Expr) : interpret (ofExpr xs) = eval xs := rfl

/-- Construct the exact logarithm of a declared positive rational factor. -/
def ofRat (q : ℚ) (hq : 0 < q) : LogFactor := ofExpr [(1, ⟨q, hq⟩)]

@[simp] theorem interpret_ofRat (q : ℚ) (hq : 0 < q) :
    interpret (ofRat q hq) = Real.log (q : ℝ) := by
  change ((1 : ℚ) : ℝ) * Real.log (q : ℝ) + 0 = _
  simp

-- These checks execute only rational arithmetic and quotient operations.
#guard (ofRat 2 (by norm_num) + ofRat 3 (by norm_num) == ofRat 6 (by norm_num))
#guard ((1 / 2 : ℚ) • ofRat 4 (by norm_num) == ofRat 2 (by norm_num))
#guard !(ofRat 2 (by norm_num) == ofRat 3 (by norm_num))
#guard (ofRat (9144 / 10000) (by norm_num) ==
  ofRat 3 (by norm_num) + ofRat (3048 / 10000) (by norm_num))
#guard ((-2 / 3 : ℚ) • ofRat 8 (by norm_num) == -ofRat 4 (by norm_num))

end LogFactor
end LambdaS

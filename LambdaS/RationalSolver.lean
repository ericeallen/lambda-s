/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Executable rational linear solving with module-valued right-hand sides

One rational coefficient matrix can be eliminated against any decidable
ℚ-module. Pivot selection is finite search; back-substitution constructs a
solution. No basis choice, real equality test, or noncomputable data occurs.
-/

namespace LambdaS.RationalSolver

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- One row of a rational system with a module-valued right-hand side. -/
structure Row (n : ℕ) (M : Type*) where
  coeff : Fin n → ℚ
  rhs : M

/-- Evaluate a row's left-hand side. -/
def Row.eval (r : Row n M) (x : Fin n → M) : M := ∑ j, r.coeff j • x j

/-- The first nonzero coefficient, or no pivot for a zero row. -/
def Row.pivot (r : Row n M) : Option (Fin n) :=
  (List.finRange n).find? (fun j => decide (r.coeff j ≠ 0))

omit [AddCommGroup M] [Module ℚ M] in
theorem Row.pivot_none {r : Row n M} (h : r.pivot = none) : ∀ j, r.coeff j = 0 := by
  simpa [Row.pivot, List.find?_eq_none] using h

omit [AddCommGroup M] [Module ℚ M] in
theorem Row.pivot_some {r : Row n M} {j : Fin n} (h : r.pivot = some j) :
    r.coeff j ≠ 0 := by
  have hh := List.find?_some (p := fun i => decide (r.coeff i ≠ 0)) h
  exact of_decide_eq_true hh

/-- Row subtraction eliminates a chosen pivot coefficient. -/
def Row.reduce (r p : Row n M) (j : Fin n) : Row n M where
  coeff i := r.coeff i - (r.coeff j / p.coeff j) * p.coeff i
  rhs := r.rhs - (r.coeff j / p.coeff j) • p.rhs

theorem Row.reduce_pivot (r p : Row n M) (j : Fin n) (hp : p.coeff j ≠ 0) :
    (r.reduce p j).coeff j = 0 := by
  simp [Row.reduce, hp]

theorem Row.eval_reduce (r p : Row n M) (j : Fin n) (x : Fin n → M) :
    (r.reduce p j).eval x = r.eval x - (r.coeff j / p.coeff j) • p.eval x := by
  simp [Row.eval, Row.reduce, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]

theorem Row.reduce_satisfied_iff (r p : Row n M) (j : Fin n) (x : Fin n → M)
    (hp : p.eval x = p.rhs) :
    (r.reduce p j).eval x = (r.reduce p j).rhs ↔ r.eval x = r.rhs := by
  rw [Row.eval_reduce, hp]
  simp [Row.reduce]

/-- Solve one pivot variable with the remaining coordinates held fixed. -/
def Row.backsub (p : Row n M) (j : Fin n) (x : Fin n → M) : Fin n → M :=
  Function.update x j ((p.coeff j)⁻¹ •
    (p.rhs - ∑ i ∈ Finset.univ.erase j, p.coeff i • x i))

private theorem Row.eval_split (r : Row n M) (j : Fin n) (x : Fin n → M) :
    r.eval x = r.coeff j • x j + ∑ i ∈ Finset.univ.erase j, r.coeff i • x i := by
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm

theorem Row.backsub_satisfies (p : Row n M) (j : Fin n) (hp : p.coeff j ≠ 0)
    (x : Fin n → M) : p.eval (p.backsub j x) = p.rhs := by
  rw [Row.eval_split p j]
  have hrest : (∑ i ∈ Finset.univ.erase j, p.coeff i • p.backsub j x i) =
      ∑ i ∈ Finset.univ.erase j, p.coeff i • x i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Row.backsub, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest]
  simp only [Row.backsub, Function.update_self, smul_smul, mul_inv_cancel₀ hp, one_smul]
  exact sub_add_cancel _ _

theorem Row.eval_backsub_of_zero (r p : Row n M) (j : Fin n)
    (hj : r.coeff j = 0) (x : Fin n → M) : r.eval (p.backsub j x) = r.eval x := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = j
  · subst i
    simp [hj]
  · rw [Row.backsub, Function.update_of_ne hi]

/-- A concrete assignment satisfies every equation in a row list. -/
def Solves (rows : List (Row n M)) (x : Fin n → M) : Prop :=
  ∀ r ∈ rows, r.eval x = r.rhs

@[simp] theorem solves_nil (x : Fin n → M) : Solves [] x := by
  simp [Solves]

@[simp] theorem solves_cons (r : Row n M) (rows : List (Row n M)) (x : Fin n → M) :
    Solves (r :: rows) x ↔ r.eval x = r.rhs ∧ Solves rows x := by
  simp [Solves]

/-- Reduce all remaining rows against one pivot. -/
def reduceRows (rows : List (Row n M)) (p : Row n M) (j : Fin n) : List (Row n M) :=
  rows.map (fun r => r.reduce p j)

@[simp] theorem length_reduceRows (rows : List (Row n M)) (p : Row n M) (j : Fin n) :
    (reduceRows rows p j).length = rows.length := List.length_map ..

theorem solves_reduceRows_iff (rows : List (Row n M)) (p : Row n M) (j : Fin n)
    (x : Fin n → M) (hp : p.eval x = p.rhs) :
    Solves (reduceRows rows p j) x ↔ Solves rows x := by
  simp only [Solves, reduceRows, List.forall_mem_map]
  exact forall_congr' fun r => forall_congr' fun _ => r.reduce_satisfied_iff p j x hp

theorem backsub_solves (rows : List (Row n M)) (p : Row n M) (j : Fin n)
    (hp : p.coeff j ≠ 0) (x : Fin n → M) (hx : Solves (reduceRows rows p j) x) :
    Solves (p :: rows) (p.backsub j x) := by
  have hhead := p.backsub_satisfies j hp x
  rw [solves_cons]
  refine ⟨hhead, (solves_reduceRows_iff rows p j _ hhead).mp ?_⟩
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  rw [Row.eval_backsub_of_zero _ p j (q.reduce_pivot p j hp)]
  exact hx _ (List.mem_map.mpr ⟨q, hq, rfl⟩)

variable [DecidableEq M]

/-- Gaussian elimination with executable pivot search and back-substitution.
Recursion removes one row, including when no variables remain. -/
def solveRows : List (Row n M) → Option (Fin n → M)
  | [] => some (fun _ => 0)
  | p :: rows =>
      match p.pivot with
      | none => if p.rhs = 0 then solveRows rows else none
      | some j => (solveRows (reduceRows rows p j)).map (p.backsub j)
  termination_by rows => rows.length
  decreasing_by all_goals simp

/-- Every assignment the executable solver returns satisfies the system. -/
theorem solveRows_sound : ∀ (rows : List (Row n M)) (x : Fin n → M),
    solveRows rows = some x → Solves rows x
  | [], x, _ => solves_nil x
  | p :: rows, x, h => by
    rw [solveRows] at h
    cases hp : p.pivot with
    | none =>
      simp only [hp] at h
      by_cases hz : p.rhs = 0
      · simp only [hz, ↓reduceIte] at h
        rw [solves_cons]
        exact ⟨by simp [Row.eval, p.pivot_none hp, hz], solveRows_sound rows x h⟩
      · simp [hz] at h
    | some j =>
      rw [hp] at h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      exact backsub_solves rows p j (p.pivot_some hp) y
        (solveRows_sound (reduceRows rows p j) y hy)
  termination_by rows => rows.length
  decreasing_by all_goals simp

/-- A satisfying assignment guarantees that executable solving succeeds. -/
theorem solveRows_complete : ∀ (rows : List (Row n M)) (x : Fin n → M),
    Solves rows x → (solveRows rows).isSome
  | [], _, _ => by simp [solveRows]
  | p :: rows, x, h => by
    obtain ⟨hhead, htail⟩ := (solves_cons p rows x).mp h
    rw [solveRows]
    cases hp : p.pivot with
    | none =>
      have hz : p.rhs = 0 := by
        rw [← hhead]
        simp [Row.eval, p.pivot_none hp]
      simp only [hz, ↓reduceIte]
      exact solveRows_complete rows x htail
    | some j =>
      simp only [Option.isSome_map]
      exact solveRows_complete (reduceRows rows p j) x
        ((solves_reduceRows_iff rows p j x hhead).mpr htail)
  termination_by rows => rows.length
  decreasing_by all_goals simp

theorem solveRows_isSome_iff (rows : List (Row n M)) :
    (solveRows rows).isSome ↔ ∃ x, Solves rows x := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact ⟨x, solveRows_sound rows x hx⟩
  · rintro ⟨x, hx⟩
    exact solveRows_complete rows x hx

/-- Turn a matrix and right-hand side into executable rows. -/
def matrixRows {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → M) : List (Row n M) :=
  List.ofFn fun i => ⟨A i, b i⟩

/-- Solve `A x = b`, where coefficients are rational and values lie in `M`. -/
def solve {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → M) : Option (Fin n → M) :=
  solveRows (matrixRows A b)

omit [DecidableEq M] in
theorem solves_matrixRows_iff {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → M)
    (x : Fin n → M) : Solves (matrixRows A b) x ↔ ∀ i, ∑ j, A i j • x j = b i := by
  simp [Solves, matrixRows, Row.eval, List.mem_ofFn]

/-- Soundness of the matrix interface. -/
theorem solve_sound {m : ℕ} {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → M}
    {x : Fin n → M} (h : solve A b = some x) : ∀ i, ∑ j, A i j • x j = b i :=
  (solves_matrixRows_iff A b x).mp (solveRows_sound _ x h)

/-- Success decides solvability over the supplied decidable ℚ-module. -/
theorem solve_isSome_iff {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → M) :
    (solve A b).isSome ↔ ∃ x : Fin n → M, ∀ i, ∑ j, A i j • x j = b i := by
  rw [solve, solveRows_isSome_iff]
  simp only [solves_matrixRows_iff]

section Naturality

variable {N : Type*} [AddCommGroup N] [Module ℚ N]

/-- Apply a linear map to the right-hand side, leaving coefficients untouched. -/
def Row.map (L : M →ₗ[ℚ] N) (r : Row n M) : Row n N := ⟨r.coeff, L r.rhs⟩

omit [DecidableEq M] in
@[simp] theorem Row.pivot_map (L : M →ₗ[ℚ] N) (r : Row n M) :
    (r.map L).pivot = r.pivot := rfl

omit [DecidableEq M] in
@[simp] theorem Row.map_reduce (L : M →ₗ[ℚ] N) (r p : Row n M) (j : Fin n) :
    (r.reduce p j).map L = (r.map L).reduce (p.map L) j := by
  simp [Row.map, Row.reduce]

omit [DecidableEq M] in
theorem Row.map_backsub (L : M →ₗ[ℚ] N) (p : Row n M) (j : Fin n) (x : Fin n → M) :
    (fun i => L (p.backsub j x i)) = (p.map L).backsub j (fun i => L (x i)) := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [Row.backsub, Row.map, map_sub, map_sum]
  · simp [Row.backsub, Row.map, hi]

variable [DecidableEq N]

/-- Executable solving commutes with an injective linear change of value
carrier. Injectivity ensures the same rigid-residual zero tests in both. -/
theorem solveRows_map (L : M →ₗ[ℚ] N) (hL : Function.Injective L) :
    ∀ rows : List (Row n M),
      solveRows (rows.map (Row.map L)) = (solveRows rows).map (fun x i => L (x i))
  | [] => by simp [solveRows]
  | p :: rows => by
    rw [List.map_cons, solveRows, solveRows, Row.pivot_map]
    cases hp : p.pivot with
    | none =>
      have hz : L p.rhs = 0 ↔ p.rhs = 0 := by
        constructor
        · intro h
          apply hL
          simpa using h
        · rintro h
          simp [h]
      simp only [Row.map, hz]
      split
      · exact solveRows_map L hL rows
      · rfl
    | some j =>
      simp only []
      have hred : reduceRows (rows.map (Row.map L)) (p.map L) j =
          (reduceRows rows p j).map (Row.map L) := by
        simp [reduceRows, List.map_map, Function.comp_def, Row.map_reduce]
      rw [hred, solveRows_map L hL (reduceRows rows p j)]
      simp only [Option.map_map]
      congr 1
      funext x
      exact (p.map_backsub L j x).symm
  termination_by rows => rows.length
  decreasing_by all_goals simp

/-- The matrix solver commutes with an injective linear embedding. -/
theorem solve_map {m : ℕ} (L : M →ₗ[ℚ] N) (hL : Function.Injective L)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → M) :
    solve A (fun i => L (b i)) = (solve A b).map (fun x i => L (x i)) := by
  have hr : matrixRows A (fun i => L (b i)) = (matrixRows A b).map (Row.map L) := by
    simp [matrixRows, Row.map, List.map_ofFn, Function.comp_def]
  rw [solve, hr, solveRows_map L hL]
  rfl

end Naturality

/-- Solvability reflects along an injective linear embedding, even if equality
in the larger carrier is not executable. Classical equality is used only in
this proof, never in the solver that computes over the smaller carrier. -/
theorem solvable_map_iff {N : Type*} [AddCommGroup N] [Module ℚ N] {m : ℕ}
    (L : M →ₗ[ℚ] N) (hL : Function.Injective L)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → M) :
    (∃ x : Fin n → N, ∀ i, ∑ j, A i j • x j = L (b i)) ↔
      ∃ x : Fin n → M, ∀ i, ∑ j, A i j • x j = b i := by
  classical
  rw [← solve_isSome_iff, ← solve_isSome_iff, solve_map L hL, Option.isSome_map]

/-- Failure decides absence of any solution, rather than an algorithmic
inability to select pivots. -/
theorem solve_eq_none_iff {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → M) :
    solve A b = none ↔ ¬ ∃ x : Fin n → M, ∀ i, ∑ j, A i j • x j = b i := by
  rw [← solve_isSome_iff]
  simp

/-! Executable boundary checks. Soundness and completeness above are kernel
proofs; these guards also exercise the actual finite-search implementation. -/

-- The first row's leading coefficient is zero: pivot selection must search.
#guard (solve (!![0, 1; 1, 1]) ![(2 : ℚ), 3]).map (fun x => [x 0, x 1]) == some [1, 2]

-- Inconsistent dependent rows leave a nonzero rigid residual.
#guard (solve (!![1, 1; 2, 2]) ![(1 : ℚ), 3]).isNone

-- A free coordinate is assigned zero, and back-substitution fixes the pivot.
#guard (solve (!![1, 1]) ![(3 : ℚ)]).map (fun x => [x 0, x 1]) == some [3, 0]

-- No equations still returns an executable all-zero assignment.
#guard (solve (fun i : Fin 0 => i.elim0 : Matrix (Fin 0) (Fin 2) ℚ)
  (fun i : Fin 0 => i.elim0 : Fin 0 → ℚ)).map (fun x => [x 0, x 1]) == some [0, 0]

-- No variables cannot satisfy a nonzero right-hand side.
#guard (solve (fun (_ : Fin 1) (j : Fin 0) => j.elim0 : Matrix (Fin 1) (Fin 0) ℚ)
  ![(1 : ℚ)]).isNone

-- The value carrier need not be a field: the same elimination handles pairs.
#guard (solve (!![0, 1; 1, 1]) ![((2, 4) : ℚ × ℚ), (3, 5)]).map
  (fun x => [x 0, x 1]) == some [(1, 1), (2, 4)]

end LambdaS.RationalSolver

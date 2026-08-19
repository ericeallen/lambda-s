import LambdaS.Syntax
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The Pi theorem: linear-algebra core

Kennedy's Pi Theorem for programming (POPL 1997; restated in the 2009 lecture
notes as Theorem 4) says that a first-order unit-polymorphic type

  `∀α₁…αₘ. float<u₁> → ⋯ → float<uₙ> → float<u₀>`

is *isomorphic* to one with `n − r` dimensionless arguments, where `r` is the
rank of the matrix of unit-variable exponents.

He mechanized the extensional semantics in Coq (WMM 2008) but listed the Pi
theorem's proof as **work in progress**, along with the non-definability results
and the higher-order generalization. No completion appears in the eighteen years
since. This file is progress on that, and it is important to be precise about
how much.

## What is proved here

The **linear-algebra core**: the dimensionless power-products of the arguments
form the kernel of the exponent matrix, its dimension is `n − r` by
rank-nullity, and — the pedagogically important part — a unit variable occurring
in exactly one argument forces that argument out of every dimensionless group
*and* out of the answer.

That last theorem is the pendulum, mechanized. Mass appears only in the mass, so
it has nothing to cancel against.

## What is not proved here

Kennedy's **syntactic** route to the isomorphism — applying primitive
isomorphisms corresponding to row and column operations until the matrix is in
normal form — is not taken, because its witnesses need a term-level rational
power of a value, which Λs does not have, and positivity to make it meaningful.
`LambdaS.PiTheorem` proves the isomorphism (`piEquiv`) by the *semantic* route
instead: the scaling law plus the exponent-matrix linear algebra of this file.
So the computational content is mechanized here, and the isomorphism there.

## Why ℚ helps

Kennedy's proof reduces the exponent matrix to **Smith Normal Form**, which is
what ℤ forces. Over ℚ the matrix is over a field, so the same reduction is
Gaussian elimination and the rank theory is Mathlib's off the shelf. The
rational-exponent decision, taken in `LambdaS.Uom` for volatility and
wavefunctions, pays off again here for reasons unrelated to either.
-/

namespace LambdaS.Pi

open Matrix

variable {m n : ℕ}

/-- The **exponent matrix** of a first-order unit-polymorphic signature: `A i j`
is the exponent of unit variable `i` in the unit of argument `j`. -/
abbrev ExpMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℚ

/-- A **dimensionless power-product** of the arguments: exponents `x` such that
`x₁·u₁ + ⋯ + xₙ·uₙ` cancels every unit variable.

These are the Π groups of Buckingham's theorem. -/
def Dimensionless (A : ExpMatrix m n) : Submodule ℚ (Fin n → ℚ) :=
  LinearMap.ker (Matrix.mulVecLin A)

@[simp] theorem mem_dimensionless {A : ExpMatrix m n} {x : Fin n → ℚ} :
    x ∈ Dimensionless A ↔ A.mulVec x = 0 := Iff.rfl

/-- **The Pi count.** The dimensionless groups form a space of dimension
`n − r`, where `r` is the rank of the exponent matrix.

Stated as an addition to avoid truncated subtraction. This is Buckingham's
theorem's arithmetic, and it is exactly what a `:pi` command would report. -/
theorem finrank_dimensionless_add_rank (A : ExpMatrix m n) :
    Module.finrank ℚ (Dimensionless A) + Matrix.rank A = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
  have hn : Module.finrank ℚ (Fin n → ℚ) = n := by simp
  rw [hn] at h
  rw [Dimensionless, Matrix.rank]
  omega

/-- **A unit variable occurring in exactly one argument forces that argument
out of every dimensionless group.**

This is the pendulum. The mass dimension `M` appears only in the mass, so it has
nothing to cancel against, and the `M` row of the exponent matrix reduces to the
single equation `x_mass = 0` — with no physics involved.

It is also the precise sense in which the Pi theorem does *not* claim mass is
irrelevant to pendulums. It claims that **given this list of variables**, mass
cannot appear. Add a second mass-carrying quantity, such as a fluid density, and
the hypothesis `hrow` fails, the mass ratio becomes a legitimate group, and the
conclusion evaporates. -/
theorem eq_zero_of_appears_once (A : ExpMatrix m n) (v : Fin m) (j : Fin n)
    (hne : A v j ≠ 0) (hrow : ∀ j', j' ≠ j → A v j' = 0)
    {x : Fin n → ℚ} (hx : x ∈ Dimensionless A) : x j = 0 := by
  rw [mem_dimensionless] at hx
  have hv : A.mulVec x v = 0 := by rw [hx]; rfl
  rw [Matrix.mulVec, dotProduct] at hv
  rw [Finset.sum_eq_single j] at hv
  · exact (mul_eq_zero.mp hv).resolve_left hne
  · intro j' _ hj'; rw [hrow j' hj', zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The same argument applied to the *solution*, not just the kernel.

If unit variable `v` occurs only in argument `j`, and the **result** unit does
not mention `v`, then every solution of `A X = B` has `X j = 0`. So argument `j`
does not appear in the answer at all — which is the pendulum's conclusion, that
the period is independent of the mass. -/
theorem solution_eq_zero_of_appears_once (A : ExpMatrix m n) (Bv : Fin m → ℚ)
    (v : Fin m) (j : Fin n) (hne : A v j ≠ 0) (hrow : ∀ j', j' ≠ j → A v j' = 0)
    (hB : Bv v = 0) {X : Fin n → ℚ} (hX : A.mulVec X = Bv) : X j = 0 := by
  have hv : A.mulVec X v = 0 := by rw [hX, hB]
  rw [Matrix.mulVec, dotProduct] at hv
  rw [Finset.sum_eq_single j] at hv
  · exact (mul_eq_zero.mp hv).resolve_left hne
  · intro j' _ hj'; rw [hrow j' hj', zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## The pendulum, concretely

Variables `M`, `L`, `T`; arguments `m`, `l`, `g`, `θ`. -/

/-- Exponents of `M, L, T` in the units of `m`, `l`, `g = L/T²`, `θ = 1`. -/
def pendulum : ExpMatrix 3 4 :=
  !![1, 0,  0, 0;
     0, 1,  1, 0;
     0, 0, -2, 0]

/-- The mass row is nonzero exactly at the mass column. -/
theorem pendulum_mass_only : pendulum 0 0 ≠ 0 ∧ ∀ j, j ≠ 0 → pendulum 0 j = 0 := by
  refine ⟨by decide, ?_⟩
  decide

/-- **Mass cannot appear in any dimensionless group of the pendulum**, derived
rather than observed. -/
theorem pendulum_mass_drops_out {x : Fin 4 → ℚ} (hx : x ∈ Dimensionless pendulum) :
    x 0 = 0 :=
  eq_zero_of_appears_once pendulum 0 0 pendulum_mass_only.1 pendulum_mass_only.2 hx

/-- And mass does not appear in the answer either: the period, whose unit is
`T²`, has no `M` exponent. -/
theorem pendulum_period_independent_of_mass
    {X : Fin 4 → ℚ} (hX : pendulum.mulVec X = ![0, 0, 2]) : X 0 = 0 :=
  solution_eq_zero_of_appears_once pendulum ![0, 0, 2] 0 0
    pendulum_mass_only.1 pendulum_mass_only.2 rfl hX

end LambdaS.Pi

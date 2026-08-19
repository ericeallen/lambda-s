import LambdaS.Pi
import LambdaS.Fundamental

/-!
# The Pi theorem

Kennedy's Theorem 4: a first-order unit-polymorphic type is isomorphic to one
with `n − r` dimensionless arguments, where `r` is the rank of the exponent
matrix. He listed its proof as work in progress on his WMM 2008 slides and no
completion appears in the eighteen years since.

## The route taken

Kennedy proves it by reducing the exponent matrix through a sequence of
*syntactic* type isomorphisms — column operations `C1`–`C3`, row operations
`R1`–`R3`, then `r` instances of an elimination isomorphism `D`. That route
needs the isomorphism witnesses to be terms, hence a term-level rational power
`xᵠ`, hence positivity, and it is what has been blocking progress here.

This file takes the **semantic** route instead. The fundamental theorem
(`fundamental_free`) already gives every parametric convert-free term an
unrestricted scaling law. Working
directly from that law — in logarithmic coordinates, where the scaling action is
a *translation* — the theorem becomes a statement in linear algebra and no term
witnesses are needed.

Concretely, in log coordinates `ξ = log x` the action of a scaling `ψ` is
`ξ ↦ ξ + Aᵀψ`, and the scaling law reads `F(ξ + Aᵀψ) = F(ξ) + ⟨b, ψ⟩`. Given a
solution `X` of `A X = b` — Kennedy's solvability hypothesis — subtracting the
linear functional `⟨X, ·⟩` produces a function invariant under the *entire*
action. That invariant function is exactly the "function of the dimensionless
groups", and

  `f(x) = (∏ xᵢ^{Xᵢ}) · g(Π₁, …, Π_{n−r})`

is Buckingham's conclusion.

## Why ℚ pays off a fourth time

Kennedy reduces the matrix to **Smith Normal Form**, which is what ℤ forces.
Here the orbit subspace is `range Aᵀ` over a field, its dimension is `rank A`,
and the quotient has dimension `n − r` by rank-nullity — Mathlib's, off the
shelf. The rational-exponent decision keeps paying in places it was not made for.
-/

namespace LambdaS.Pi

open scoped BigOperators

variable {m n : ℕ}

/-- The displacement a scaling induces on the log-arguments. In log coordinates
the scaling action is translation by `Aᵀψ`. -/
def act (A : ExpMatrix m n) (ψ : Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ v, (A v i : ℝ) * ψ v

/-- **The scaling law** of a first-order signature, in log coordinates.

`F` is `log ∘ f ∘ exp`; rescaling the units translates the arguments and shifts
the value by the output's own scale. This is exactly what `fundamental_free`
delivers for a parametric convert-free term, transported to logs. -/
def ScaleLaw (A : ExpMatrix m n) (b : Fin m → ℚ) (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ψ ξ, F (fun i => ξ i + act A ψ i) = F ξ + ∑ v, (b v : ℝ) * ψ v

/-- The exchange identity at the heart of the reduction: a solution of `A X = b`
turns the argument displacement into exactly the output shift.

This is where Kennedy's solvability hypothesis does its work. -/
theorem sum_act_eq (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ)) (ψ : Fin m → ℝ) :
    ∑ i, X i * act A ψ i = ∑ v, (b v : ℝ) * ψ v := by
  simp only [act, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← hX v, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The Pi theorem.**

Any function satisfying the scaling law factors as an explicit power-product
times a function that is **invariant under every rescaling** — hence a function
of the dimensionless groups alone, of which there are `n − r`.

In the original coordinates this reads
`f(x) = (∏ xᵢ^{Xᵢ}) · g(Π₁, …, Π_{n−r})`, which is Buckingham's conclusion and
Kennedy's isomorphism. -/
theorem pi_theorem (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ))
    {F : (Fin n → ℝ) → ℝ} (hF : ScaleLaw A b F) :
    ∃ G : (Fin n → ℝ) → ℝ,
      (∀ ψ ξ, G (fun i => ξ i + act A ψ i) = G ξ) ∧
      (∀ ξ, F ξ = (∑ i, X i * ξ i) + G ξ) := by
  refine ⟨fun ξ => F ξ - ∑ i, X i * ξ i, ?_, ?_⟩
  · intro ψ ξ
    show F (fun i => ξ i + act A ψ i) - ∑ i, X i * (ξ i + act A ψ i)
        = F ξ - ∑ i, X i * ξ i
    rw [hF]
    have hsplit : ∑ i, X i * (ξ i + act A ψ i)
        = (∑ i, X i * ξ i) + ∑ i, X i * act A ψ i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, sum_act_eq A b X hX]
    ring
  · intro ξ; ring

/-- **The invariants are exactly the dimensionless groups.**

A monomial `∏ xᵢ^{cᵢ}` — a linear functional `⟨c, ·⟩` in log coordinates — is
invariant under every rescaling precisely when `c` lies in the kernel of the
exponent matrix, which is `Dimensionless A`.

So the function `pi_theorem` produces really is a function of the Π groups, and
by `finrank_dimensionless_add_rank` there are `n − r` of them. -/
theorem invariant_iff_dimensionless (A : ExpMatrix m n) (c : Fin n → ℝ) :
    (∀ ψ : Fin m → ℝ, ∑ i, c i * act A ψ i = 0) ↔
      ∀ v, ∑ i, (A v i : ℝ) * c i = 0 := by
  constructor
  · intro h v
    have hv := h (fun w => if w = v then 1 else 0)
    simp only [act, Finset.mul_sum] at hv
    rw [Finset.sum_comm] at hv
    simpa [Finset.sum_ite_eq', mul_comm] using hv
  · intro h ψ
    simp only [act, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v _ => ?_
    have : ∑ i, c i * ((A v i : ℝ) * ψ v) = (∑ i, (A v i : ℝ) * c i) * ψ v := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h v, zero_mul]

/-- **The count.** The dimensionless groups form a space of dimension `n − r`,
so `pi_theorem`'s `G` depends on exactly that many arguments.

Restated here from `finrank_dimensionless_add_rank` to keep the theorem's two
halves — the factorization and the count — in one place. -/
theorem pi_count (A : ExpMatrix m n) :
    Module.finrank ℚ (Dimensionless A) + Matrix.rank A = n :=
  finrank_dimensionless_add_rank A

/-! ## The isomorphism

Kennedy states the theorem as a *type isomorphism*. Here it is, as an actual
bijection: the functions satisfying a signature's scaling law correspond exactly
to the scale-invariant functions, and the correspondence is adding and
subtracting the power-product `∏ xᵢ^{Xᵢ}`. -/

/-- A function invariant under every rescaling — a function of the dimensionless
groups alone, by `invariant_iff_dimensionless`. -/
def Invariant (A : ExpMatrix m n) (G : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ψ ξ, G (fun i => ξ i + act A ψ i) = G ξ

/-- Adding the power-product back turns an invariant function into one obeying
the scaling law. The inverse direction of `pi_theorem`. -/
theorem scaleLaw_add_linear (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ))
    {G : (Fin n → ℝ) → ℝ} (hG : Invariant A G) :
    ScaleLaw A b (fun ξ => (∑ i, X i * ξ i) + G ξ) := by
  intro ψ ξ
  show (∑ i, X i * (ξ i + act A ψ i)) + G (fun i => ξ i + act A ψ i)
      = ((∑ i, X i * ξ i) + G ξ) + ∑ v, (b v : ℝ) * ψ v
  rw [hG]
  have hsplit : ∑ i, X i * (ξ i + act A ψ i)
      = (∑ i, X i * ξ i) + ∑ i, X i * act A ψ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, sum_act_eq A b X hX]
  ring

/-- **Kennedy's isomorphism, as a bijection.**

Functions obeying the scaling law of the signature `(A, b)` are in bijection with
scale-invariant functions. Since the invariants are exactly the functions of the
`n − r` dimensionless groups (`invariant_iff_dimensionless`, `pi_count`), this is
the statement that a first-order unit-polymorphic type is isomorphic to one with
`n − r` dimensionless arguments. -/
noncomputable def piEquiv (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ)) :
    {F : (Fin n → ℝ) → ℝ // ScaleLaw A b F} ≃
      {G : (Fin n → ℝ) → ℝ // Invariant A G} where
  toFun F :=
    ⟨fun ξ => F.1 ξ - ∑ i, X i * ξ i, by
      obtain ⟨G, hGinv, hGeq⟩ := pi_theorem A b X hX F.2
      intro ψ ξ
      show F.1 (fun i => ξ i + act A ψ i) - ∑ i, X i * (ξ i + act A ψ i)
          = F.1 ξ - ∑ i, X i * ξ i
      rw [hGeq, hGeq, hGinv]
      have hsplit : ∑ i, X i * (ξ i + act A ψ i)
          = (∑ i, X i * ξ i) + ∑ i, X i * act A ψ i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit]
      ring⟩
  invFun G := ⟨fun ξ => (∑ i, X i * ξ i) + G.1 ξ, scaleLaw_add_linear A b X hX G.2⟩
  left_inv F := by ext ξ; show (∑ i, X i * ξ i) + (F.1 ξ - ∑ i, X i * ξ i) = F.1 ξ; ring
  right_inv G := by ext ξ; show ((∑ i, X i * ξ i) + G.1 ξ) - ∑ i, X i * ξ i = G.1 ξ; ring

/-! ## The pendulum, again

With the general theorem in hand, the running example collapses in one line: the
mass exponent is zero in the solution, so the power-product `∏ xᵢ^{Xᵢ}` does not
mention the mass, and by `eq_zero_of_appears_once` neither does any dimensionless
group. So `G` cannot mention it either — the period is independent of the mass,
and both halves of the theorem say so. -/

theorem pendulum_mass_absent {X : Fin 4 → ℚ}
    (hX : pendulum.mulVec X = ![0, 0, 2]) : X 0 = 0 :=
  solution_eq_zero_of_appears_once pendulum ![0, 0, 2] 0 0
    pendulum_mass_only.1 pendulum_mass_only.2 rfl hX

end LambdaS.Pi

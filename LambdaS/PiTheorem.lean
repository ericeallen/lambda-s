/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Pi
import LambdaS.Fundamental
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Pi theorem

Kennedy's Theorem 4: a first-order unit-polymorphic type is isomorphic to one
with `n − r` dimensionless arguments, where `r` is the rank of the exponent
matrix. He listed its proof as work in progress on his WMM 2008 slides and no
completion appears in the eighteen years since.

## The route taken

Kennedy proves it by reducing the exponent matrix through a sequence of
*syntactic* type isomorphisms: column operations `C1`–`C3`, row operations
`R1`–`R3`, then `r` instances of an elimination isomorphism `D`. That route
needs the isomorphism witnesses to be terms, hence a term-level rational power
`xᵠ`, hence positivity, and it is what has been blocking progress here.

This file takes the **semantic** route instead. The fundamental theorem
(`fundamental_free`) already gives every parametric convert-free term an
unrestricted scaling law. Working
directly from that law (in logarithmic coordinates, where the scaling action is
a *translation*), the theorem becomes a statement in linear algebra and no term
witnesses are needed.

Concretely, in log coordinates `ξ = log x` the action of a scaling `ψ` is
`ξ ↦ ξ + Aᵀψ`, and the scaling law reads `F(ξ + Aᵀψ) = F(ξ) + ⟨b, ψ⟩`. Given a
solution `X` of `A X = b` (Kennedy's solvability hypothesis), subtracting the
linear functional `⟨X, ·⟩` produces a function invariant under the *entire*
action. That invariant function is exactly the "function of the dimensionless
groups", and

  `f(x) = (∏ xᵢ^{Xᵢ}) · g(Π₁, …, Π_{n−r})`

is Buckingham's conclusion.

## Why ℚ pays off a fourth time

Kennedy reduces the matrix to **Smith Normal Form**, which is what ℤ forces.
Here the orbit subspace is `range Aᵀ` over a field, its dimension is `rank A`,
and the quotient has dimension `n − r` by rank-nullity (Mathlib's, off the
shelf). The rational-exponent decision keeps paying in places it was not made for.
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
times a function that is **invariant under every rescaling**, hence a function
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

A monomial `∏ xᵢ^{cᵢ}` (a linear functional `⟨c, ·⟩` in log coordinates) is
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
halves (the factorization and the count) in one place. -/
theorem pi_count (A : ExpMatrix m n) :
    Module.finrank ℚ (Dimensionless A) + Matrix.rank A = n :=
  finrank_dimensionless_add_rank A

/-! ## The isomorphism

Kennedy states the theorem as a *type isomorphism*. Here it is, as an actual
bijection: the functions satisfying a signature's scaling law correspond exactly
to the scale-invariant functions, and the correspondence is adding and
subtracting the power-product `∏ xᵢ^{Xᵢ}`. -/

/-- A function invariant under every rescaling: a function of the dimensionless
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

/-! ## The multiplicative bridge

`ScaleLaw` lives in log coordinates. The law the calculus itself delivers
(`scaleLaw` in `LambdaS.Fundamental`) is multiplicative: rescaling each
argument by the scale factor of its unit multiplies the result by the scale
factor of the result unit. This section states that multiplicative law as a
predicate on functions and factors any function satisfying it, on the
positive orthant, as the power product `∏ xᵢ^{Xᵢ}` times an invariant
function of the log magnitudes.

No positivity of the function is assumed anywhere in the factorization: only
the *arguments* pass through `exp` and `log`, and the invariant factor
carries whatever sign the function has (the zero function is carried by the
zero invariant). Positivity enters only in `scaleLaw_of_mulScaleLaw` below,
which additionally takes the logarithm of the *output* to present the law
additively; that is a presentation choice, not a hypothesis of the
theorem. -/

/-- **The multiplicative scale law.** Scaling each base unit `v` by a positive
factor `κ v` scales argument `i` by `∏ v, κ v ^ A v i` and the result by
`∏ v, κ v ^ b v`. This is the form of the scaling law a Λs term actually
satisfies (`den_mulScaleLaw` below); `ScaleLaw` is its image in log
coordinates. Exponents are rational, so the powers are `Real.rpow` under a
cast. -/
def MulScaleLaw (A : ExpMatrix m n) (b : Fin m → ℚ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ κ : Fin m → ℝ, (∀ v, 0 < κ v) → ∀ x : Fin n → ℝ,
    f (fun i => (∏ v, κ v ^ ((A v i : ℚ) : ℝ)) * x i)
      = (∏ v, κ v ^ ((b v : ℚ) : ℝ)) * f x

/-- The log conjugate `log ∘ f ∘ exp` of a function on magnitudes. This is the
`F` that `ScaleLaw` and `pi_theorem` speak about, produced from the
multiplicative function the calculus provides. -/
noncomputable def logConj (f : (Fin n → ℝ) → ℝ) (ξ : Fin n → ℝ) : ℝ :=
  Real.log (f fun i => Real.exp (ξ i))

/-- A product of real powers of exponentials is the exponential of a dot
product. The computation that carries the multiplicative law into log
coordinates and back. -/
theorem prod_exp_rpow (ψ : Fin m → ℝ) (c : Fin m → ℚ) :
    ∏ v, Real.exp (ψ v) ^ ((c v : ℚ) : ℝ) = Real.exp (∑ v, (c v : ℝ) * ψ v) := by
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun v _ => by
    rw [mul_comm ((c v : ℚ) : ℝ) (ψ v), Real.exp_mul]

/-- **The scale law in exponential coordinates.** The multiplicative law
transported to log coordinates on the arguments only: the output is scaled,
not logged, so the predicate makes sense for functions of any sign. This is
the signed carrier of the Pi reduction; `ScaleLaw` is its image under a
further logarithm on the values, available only for positive functions. -/
def ExpScaleLaw (A : ExpMatrix m n) (b : Fin m → ℚ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ψ ξ, g (fun i => ξ i + act A ψ i) = Real.exp (∑ v, (b v : ℝ) * ψ v) * g ξ

/-- The displacement of the linear functional `⟨X, ·⟩` along the scaling
action is exactly the output shift: `sum_act_eq` packaged with the splitting
of the sum, since every use below needs the two together. -/
theorem sum_act_shift (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ)) (ψ : Fin m → ℝ) (ξ : Fin n → ℝ) :
    ∑ i, X i * (ξ i + act A ψ i) = (∑ i, X i * ξ i) + ∑ v, (b v : ℝ) * ψ v := by
  rw [← sum_act_eq A b X hX ψ, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A function satisfying the multiplicative law, precomposed with `exp`,
satisfies the exponential-coordinates law. No hypothesis on the function
beyond the law itself: the exponentials are all on the argument side. -/
theorem expScaleLaw_of_mulScaleLaw (A : ExpMatrix m n) (b : Fin m → ℚ)
    {f : (Fin n → ℝ) → ℝ} (hmul : MulScaleLaw A b f) :
    ExpScaleLaw A b fun ξ => f fun i => Real.exp (ξ i) := by
  intro ψ ξ
  show f (fun i => Real.exp (ξ i + act A ψ i))
      = Real.exp (∑ v, (b v : ℝ) * ψ v) * f fun i => Real.exp (ξ i)
  have harg : ∀ i, Real.exp (ξ i + act A ψ i)
      = (∏ v, Real.exp (ψ v) ^ ((A v i : ℚ) : ℝ)) * Real.exp (ξ i) := by
    intro i
    rw [prod_exp_rpow, ← Real.exp_add, add_comm (ξ i) (act A ψ i)]
    rfl
  simp only [harg]
  rw [hmul (fun v => Real.exp (ψ v)) (fun v => Real.exp_pos _) fun i => Real.exp (ξ i),
    prod_exp_rpow]

/-- **Kennedy's isomorphism at the multiplicative level.** Functions obeying
the exponential-coordinates scale law of the signature `(A, b)` are in
bijection with the scale-invariant functions, of any sign: the correspondence
multiplies and divides by the exponential of the linear functional `⟨X, ·⟩`,
which is the power product `∏ xᵢ^{Xᵢ}` in the original coordinates. The
additive `piEquiv` is the same bijection read after a further logarithm on
the values, which is where positivity would enter and why it is not needed
here. -/
noncomputable def piEquivSigned (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ)) :
    {g : (Fin n → ℝ) → ℝ // ExpScaleLaw A b g} ≃
      {H : (Fin n → ℝ) → ℝ // Invariant A H} where
  toFun g :=
    ⟨fun ξ => g.1 ξ * Real.exp (-(∑ i, X i * ξ i)), by
      intro ψ ξ
      show g.1 (fun i => ξ i + act A ψ i)
            * Real.exp (-(∑ i, X i * (ξ i + act A ψ i)))
          = g.1 ξ * Real.exp (-(∑ i, X i * ξ i))
      rw [g.2 ψ ξ, sum_act_shift A b X hX ψ ξ, neg_add, Real.exp_add]
      have hc : Real.exp (∑ v, (b v : ℝ) * ψ v)
          * Real.exp (-(∑ v, (b v : ℝ) * ψ v)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linear_combination g.1 ξ * Real.exp (-(∑ i, X i * ξ i)) * hc⟩
  invFun H :=
    ⟨fun ξ => Real.exp (∑ i, X i * ξ i) * H.1 ξ, by
      intro ψ ξ
      show Real.exp (∑ i, X i * (ξ i + act A ψ i)) * H.1 (fun i => ξ i + act A ψ i)
          = Real.exp (∑ v, (b v : ℝ) * ψ v) * (Real.exp (∑ i, X i * ξ i) * H.1 ξ)
      rw [H.2 ψ ξ, sum_act_shift A b X hX ψ ξ, Real.exp_add]
      ring⟩
  left_inv g := by
    ext ξ
    show Real.exp (∑ i, X i * ξ i) * (g.1 ξ * Real.exp (-(∑ i, X i * ξ i))) = g.1 ξ
    have hc : Real.exp (∑ i, X i * ξ i) * Real.exp (-(∑ i, X i * ξ i)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linear_combination g.1 ξ * hc
  right_inv H := by
    ext ξ
    show Real.exp (∑ i, X i * ξ i) * H.1 ξ * Real.exp (-(∑ i, X i * ξ i)) = H.1 ξ
    have hc : Real.exp (∑ i, X i * ξ i) * Real.exp (-(∑ i, X i * ξ i)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linear_combination H.1 ξ * hc

/-- **Buckingham's factorization for multiplicative data, signed.** A function
satisfying the multiplicative scale law factors, on the positive orthant, as
the power product `∏ i, x i ^ X i` times a function of the log magnitudes
that is invariant under every rescaling, hence a function of the
dimensionless groups alone (`invariant_iff_dimensionless`, `pi_count`).

No positivity of `f` is assumed and none survives in the conclusion: `H` is
real-valued of whatever sign `f` takes, and the zero function is carried by
`H = 0`. The factorization needs only the solvability witness `X`; when the
system is unsolvable there is nothing to factor, because `f` is forced to
vanish (`mulScaleLaw_eq_zero_of_unsolvable`). -/
theorem mulScaleLaw_factorization (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ))
    {f : (Fin n → ℝ) → ℝ} (hmul : MulScaleLaw A b f) :
    ∃ H : (Fin n → ℝ) → ℝ, Invariant A H ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
        f x = (∏ i, x i ^ X i) * H (fun i => Real.log (x i)) := by
  refine ⟨fun ξ => f (fun i => Real.exp (ξ i)) * Real.exp (-(∑ i, X i * ξ i)),
    (piEquivSigned A b X hX ⟨_, expScaleLaw_of_mulScaleLaw A b hmul⟩).2, fun x hx => ?_⟩
  show f x = (∏ i, x i ^ X i)
      * (f (fun i => Real.exp (Real.log (x i)))
          * Real.exp (-(∑ i, X i * Real.log (x i))))
  have hxfun : (fun i => Real.exp (Real.log (x i))) = x :=
    funext fun i => Real.exp_log (hx i)
  have hprod : (∏ i, x i ^ X i) = Real.exp (∑ i, X i * Real.log (x i)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Real.rpow_def_of_pos (hx i), mul_comm (Real.log (x i)) (X i)]
  rw [hxfun, hprod]
  have hc : Real.exp (∑ i, X i * Real.log (x i))
      * Real.exp (-(∑ i, X i * Real.log (x i))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination (-(f x)) * hc

/-! ## The solvability dichotomy

Kennedy's hypothesis that `A X = b` be solvable is not bookkeeping either,
but its failure mode is total collapse rather than a missing factorization:
an unsolvable signature admits only the zero function. Unsolvability over `ℝ`
means `b` is separated from the column space of `A` by a linear functional;
instantiating the multiplicative law along the one-parameter family of
scalings in that functional's direction leaves every argument fixed while
multiplying the output by a nonconstant factor, which forces the value to
zero. Everywhere, not just on the positive orthant: the law itself
quantifies over all argument vectors. -/

/-- **Unsolvability is witnessed by an annihilator.** If `A X = b` has no
real solution, some direction `ψ` annihilates every column of `A` (so the
induced scaling moves no argument) while pairing nontrivially with `b` (so
it moves the output). The linear geometry behind the dichotomy: `b` outside
the column space of `A` is separated from it by a dual functional, and a
functional on `Fin m → ℝ` is again a vector. -/
theorem exists_act_annihilator_of_unsolvable (A : ExpMatrix m n) (b : Fin m → ℚ)
    (hb : ¬ ∃ X : Fin n → ℝ, ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ)) :
    ∃ ψ : Fin m → ℝ, (∀ i, act A ψ i = 0) ∧ ∑ v, (b v : ℝ) * ψ v ≠ 0 := by
  classical
  set Ar : Matrix (Fin m) (Fin n) ℝ := A.map ((↑) : ℚ → ℝ) with hAr
  have hmv : ∀ (X : Fin n → ℝ) (v : Fin m), Ar.mulVec X v = ∑ i, (A v i : ℝ) * X i := by
    intro X v
    simp [hAr, Matrix.mulVec, dotProduct, Matrix.map_apply]
  set W : Submodule ℝ (Fin m → ℝ) := LinearMap.range Ar.mulVecLin
  have hbW : (fun v => (b v : ℝ)) ∉ W := by
    intro hmem
    obtain ⟨X, hXeq⟩ := LinearMap.mem_range.mp hmem
    refine hb ⟨X, fun v => ?_⟩
    have h := congrFun hXeq v
    rwa [Matrix.mulVecLin_apply, hmv] at h
  have hq : W.mkQ (fun v => (b v : ℝ)) ≠ 0 := by
    rw [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hbW
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℝ hq
  have hrep : ∀ x : Fin m → ℝ,
      φ (W.mkQ x) = ∑ v, x v * φ (W.mkQ fun w => if v = w then 1 else 0) := by
    intro x
    simpa [smul_eq_mul] using LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ W.mkQ) x
  refine ⟨fun v => φ (W.mkQ fun w => if v = w then 1 else 0), fun i => ?_, ?_⟩
  · have hcol : (fun v => (A v i : ℝ)) ∈ W := by
      refine LinearMap.mem_range.mpr ⟨fun i' => if i' = i then 1 else 0, funext fun v => ?_⟩
      rw [Matrix.mulVecLin_apply, hmv, Finset.sum_eq_single i]
      · simp
      · intro i' _ hne
        simp [hne]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have h0 : φ (W.mkQ fun v => (A v i : ℝ)) = 0 := by
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hcol, map_zero]
    show ∑ v, (A v i : ℝ) * φ (W.mkQ fun w => if v = w then 1 else 0) = 0
    rw [← hrep fun v => (A v i : ℝ)]
    exact h0
  · show (∑ v, (b v : ℝ) * φ (W.mkQ fun w => if v = w then 1 else 0)) ≠ 0
    rw [← hrep fun v => (b v : ℝ)]
    exact hφ

/-- **Unsolvable signatures force zero.** When `A X = b` has no real
solution, the only function satisfying the multiplicative scale law is the
zero function, on the whole space. The scaling built from the annihilator
fixes every argument pointwise while scaling the output by a factor other
than `1`, and the only value that survives is `0`.

`scaleLaw_forces_zero` in `LambdaS.Definability` is the one-variable special
case of this collapse, stated for terms: there the result unit mentions a
base unit no argument mentions, so the row of that base unit is zero in the
matrix while its entry in `b` is not, and the annihilator is the coordinate
direction itself. -/
theorem mulScaleLaw_eq_zero_of_unsolvable (A : ExpMatrix m n) (b : Fin m → ℚ)
    (hb : ¬ ∃ X : Fin n → ℝ, ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ))
    {f : (Fin n → ℝ) → ℝ} (hmul : MulScaleLaw A b f) (x : Fin n → ℝ) : f x = 0 := by
  obtain ⟨ψ, hker, hbψ⟩ := exists_act_annihilator_of_unsolvable A b hb
  have harg : ∀ i, (∏ v, Real.exp (ψ v) ^ ((A v i : ℚ) : ℝ)) = 1 := by
    intro i
    rw [prod_exp_rpow]
    show Real.exp (act A ψ i) = 1
    rw [hker i, Real.exp_zero]
  have h := hmul (fun v => Real.exp (ψ v)) (fun v => Real.exp_pos _) x
  rw [prod_exp_rpow] at h
  simp only [harg, one_mul] at h
  have h' : f x = Real.exp (∑ v, (b v : ℝ) * ψ v) * f x := h
  have hne : Real.exp (∑ v, (b v : ℝ) * ψ v) ≠ 1 := fun hone => by
    have h0 := congrArg Real.log hone
    rw [Real.log_exp, Real.log_one] at h0
    exact hbψ h0
  have hz : (1 - Real.exp (∑ v, (b v : ℝ) * ψ v)) * f x = 0 := by linarith
  rcases mul_eq_zero.mp hz with hc | hfx
  · exact absurd (by linarith : Real.exp (∑ v, (b v : ℝ) * ψ v) = 1) hne
  · exact hfx

/-- **The dichotomy.** A signature either admits a solution of `A X = b`, and
then every function satisfying its multiplicative law factors through the
dimensionless groups with the solution as exponent vector, or it admits
none, and then the zero function is the only one satisfying the law. There
is no third case: Kennedy's solvability hypothesis is not a gap in the
theorem but the boundary between factorization and collapse. -/
theorem mulScaleLaw_dichotomy (A : ExpMatrix m n) (b : Fin m → ℚ)
    {f : (Fin n → ℝ) → ℝ} (hmul : MulScaleLaw A b f) :
    (∃ X : Fin n → ℝ, (∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ)) ∧
        ∃ H : (Fin n → ℝ) → ℝ, Invariant A H ∧
          ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
            f x = (∏ i, x i ^ X i) * H (fun i => Real.log (x i))) ∨
      ∀ x, f x = 0 := by
  by_cases hs : ∃ X : Fin n → ℝ, ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ)
  · obtain ⟨X, hX⟩ := hs
    exact Or.inl ⟨X, hX, mulScaleLaw_factorization A b X hX hmul⟩
  · exact Or.inr (mulScaleLaw_eq_zero_of_unsolvable A b hs hmul)

/-! ## The additive presentation -/

/-- **The additive presentation of the bridge.** A function satisfying the
multiplicative scale law and positive on positive inputs has a log conjugate
satisfying the additive `ScaleLaw` with the same exponent matrix and result
vector, which is the form `pi_theorem` and `piEquiv` consume.

Positivity is a presentation choice, not a hypothesis of the factorization:
`mulScaleLaw_factorization` needs no sign information, because it
exponentiates only the arguments. Only this statement, which also takes the
logarithm of the *output*, must know the output is in the logarithm's
domain. The zero function shows the hypothesis cannot be dropped from this
presentation: it satisfies every multiplicative law, and its log conjugate is
the constant `log 0 = 0`, which satisfies `ScaleLaw A b` only when
`b = 0`. -/
theorem scaleLaw_of_mulScaleLaw (A : ExpMatrix m n) (b : Fin m → ℚ)
    {f : (Fin n → ℝ) → ℝ} (hmul : MulScaleLaw A b f)
    (hpos : ∀ x : Fin n → ℝ, (∀ i, 0 < x i) → 0 < f x) :
    ScaleLaw A b (logConj f) := by
  intro ψ ξ
  have hfpos : 0 < f fun i => Real.exp (ξ i) :=
    hpos _ fun i => Real.exp_pos _
  have harg : ∀ i, Real.exp (ξ i + act A ψ i)
      = (∏ v, Real.exp (ψ v) ^ ((A v i : ℚ) : ℝ)) * Real.exp (ξ i) := by
    intro i
    rw [prod_exp_rpow, ← Real.exp_add, add_comm (ξ i) (act A ψ i)]
    rfl
  simp only [logConj, harg]
  rw [hmul (fun v => Real.exp (ψ v)) (fun v => Real.exp_pos _) (fun i => Real.exp (ξ i)),
    Real.log_mul (by positivity) (ne_of_gt hfpos), prod_exp_rpow, Real.log_exp]
  exact add_comm _ _

/-- The positive corollary of `mulScaleLaw_factorization`: when `f` is
positive on positive inputs, the invariant factor is positive everywhere and
can be written as an exponential, recovering the classical form
`f(x) = (∏ xᵢ^{Xᵢ}) · exp(G(log x))`. Derived from the signed factorization
rather than proved separately: positivity only repackages `H` as
`Real.exp ∘ G`. -/
theorem mulScaleLaw_factorization_pos (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ))
    {f : (Fin n → ℝ) → ℝ} (hmul : MulScaleLaw A b f)
    (hpos : ∀ x : Fin n → ℝ, (∀ i, 0 < x i) → 0 < f x) :
    ∃ G : (Fin n → ℝ) → ℝ, Invariant A G ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
        f x = (∏ i, x i ^ X i) * Real.exp (G fun i => Real.log (x i)) := by
  obtain ⟨H, hHinv, hHeq⟩ := mulScaleLaw_factorization A b X hX hmul
  have hHpos : ∀ ξ : Fin n → ℝ, 0 < H ξ := by
    intro ξ
    have hx : ∀ i, (0 : ℝ) < Real.exp (ξ i) := fun i => Real.exp_pos _
    have h := hHeq (fun i => Real.exp (ξ i)) hx
    have hlog : (fun i => Real.log (Real.exp (ξ i))) = ξ :=
      funext fun i => Real.log_exp _
    rw [hlog] at h
    have hf : 0 < f fun i => Real.exp (ξ i) := hpos _ hx
    rw [h] at hf
    rcases mul_pos_iff.mp hf with ⟨_, hH⟩ | ⟨hp', _⟩
    · exact hH
    · exact absurd (Finset.prod_pos fun i _ =>
        Real.rpow_pos_of_pos (Real.exp_pos _) (X i)) (lt_asymm hp')
  refine ⟨fun ξ => Real.log (H ξ), ?_, fun x hx => ?_⟩
  · intro ψ ξ
    show Real.log (H fun i => ξ i + act A ψ i) = Real.log (H ξ)
    rw [hHinv ψ ξ]
  · rw [hHeq x hx]
    congr 1
    exact (Real.exp_log (hHpos _)).symm

/-! ## From terms to the multiplicative law

The last gap: `scaleLaw` in `LambdaS.Fundamental` speaks about environments
and `Scaling`s, while `MulScaleLaw` speaks about vectors of magnitudes and a
matrix of exponents. This section closes it. For a first-order term over `n`
scalar arguments, the denotation as a function of the argument magnitudes
satisfies `MulScaleLaw` with the matrix whose column `i` collects the
exponents of argument `i`'s unit and the vector of the result unit's
exponents. The row index runs over **every rescalable symbol in scope**,
base units and unit variables alike, enumerated by an equivalence
`Fin m ≃ B ⊕ Fin k`: a `Scaling B k` carries an independent factor for each,
and `scaleLaw` quantifies over all of them, so the exponent matrix must have
a row for each or the bridge would silently restrict the scaling group. -/

section TermBridge

variable {B D : Type} [Fintype B] [Fintype D] [UnitSys B D] {j k : ℕ}

/-- The environment of a first-order scalar signature, assembled from a vector
of argument magnitudes. Inverse to reading the magnitudes off the
environment. -/
def envOf : (us : List (UExp B k)) → (Fin us.length → ℝ) →
    Env (scalarCtx (B := B) (D := D) (j := j) us)
  | [], _ => PUnit.unit
  | _ :: us, x => (x 0, envOf us fun i => x i.succ)

omit [Fintype D] [UnitSys B D] in
/-- Rescaling the environment of a scalar signature is rescaling each
magnitude by the scale factor of its unit. Connects `scaleEnv`, which walks
the context, to the componentwise scaling `MulScaleLaw` quantifies over. -/
theorem scaleEnv_envOf (ψ : Scaling B k) :
    ∀ (us : List (UExp B k)) (x : Fin us.length → ℝ),
      scaleEnv (D := D) (j := j) ψ us (envOf us x)
        = envOf us fun i => ψ.scale (us.get i) * x i
  | [], _ => rfl
  | u :: us, x => by
      simp only [scaleEnv, envOf, scaleEnv_envOf ψ us]
      rfl

/-- The scaling whose factors are a given vector of positive reals, read
through an enumeration of the base units *and* the unit variables in scope.
The witness that instantiates `scaleLaw` at the scalings `MulScaleLaw`
quantifies over: one independent factor for every symbol a scaling can
move. -/
noncomputable def scalingOfFactors (e : Fin m ≃ B ⊕ Fin k) (κ : Fin m → ℝ) : Scaling B k :=
  ⟨fun b => Real.log (κ (e.symm (Sum.inl b))), fun i => Real.log (κ (e.symm (Sum.inr i)))⟩

/-- The scale factor of `scalingOfFactors e κ` on a unit is the power product
of the factors against the unit's full exponent vector, base and variable
exponents both. Positivity of the factors is required: `scale` exponentiates
the logs of `κ`, and `log` collapses nonpositive inputs. -/
theorem scale_scalingOfFactors (e : Fin m ≃ B ⊕ Fin k) (κ : Fin m → ℝ)
    (hκ : ∀ v, 0 < κ v) (u : UExp B k) :
    (scalingOfFactors e κ).scale u
      = ∏ v, κ v ^ ((Sum.elim u.base u.vars (e v) : ℚ) : ℝ) := by
  have h1 : (∏ v, κ v ^ ((Sum.elim u.base u.vars (e v) : ℚ) : ℝ))
      = ∏ s : B ⊕ Fin k, κ (e.symm s) ^ ((Sum.elim u.base u.vars s : ℚ) : ℝ) := by
    rw [← Equiv.prod_comp e fun s => κ (e.symm s) ^ ((Sum.elim u.base u.vars s : ℚ) : ℝ)]
    exact Finset.prod_congr rfl fun v _ => by rw [Equiv.symm_apply_apply]
  have h2 : ∀ s : B ⊕ Fin k, κ (e.symm s) ^ ((Sum.elim u.base u.vars s : ℚ) : ℝ)
      = Real.exp (((Sum.elim u.base u.vars s : ℚ) : ℝ) * Real.log (κ (e.symm s))) :=
    fun s => by rw [Real.rpow_def_of_pos (hκ _), mul_comm]
  rw [h1, Finset.prod_congr rfl fun s _ => h2 s, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  simp only [Scaling.scale, Scaling.logScale, scalingOfFactors]

omit [Fintype D] in
/-- **The term-level multiplicative scale law.** The denotation of a
first-order parametric convert-free term, as a function of its argument
magnitudes, satisfies `MulScaleLaw` for the matrix of its arguments'
exponents and the vector of its result unit's exponents, with one row for
every rescalable symbol in scope: base units and unit variables alike,
enumerated by `Fin m ≃ B ⊕ Fin k`.

Together with `mulScaleLaw_factorization` this closes the chain from a
well-typed Λs term to Buckingham's factorization, with no positivity
assumption anywhere: the term supplies the multiplicative law, and the
factorization is signed. `mulScaleLaw_dichotomy` adds the other half: a
signature whose system is unsolvable forces the denotation to vanish.

The law quantifies over the **full scaling group** of the signature: a
rescaling may move base units and unit variables independently, which is
exactly the freedom `scaleLaw` itself provides. For a closed program
(`k = 0`) the `Fin k` summand is empty and the matrix is the base-unit
matrix, so the concrete examples are unchanged. -/
theorem den_mulScaleLaw {m : ℕ} {Δ : DCtx D j k} {e : Tm B D j k}
    {us : List (UExp B k)} {u₀ : UExp B k}
    (d : HasTy Δ (scalarCtx us) e (.Q u₀)) (hp : e.Parametric)
    (hf : e.ConvertFree) (V : Scaling B k) (eqv : Fin m ≃ B ⊕ Fin k) :
    MulScaleLaw
      (Matrix.of fun v i => Sum.elim (us.get i).base (us.get i).vars (eqv v))
      (fun v => Sum.elim u₀.base u₀.vars (eqv v))
      (fun x => den V d (envOf us x)) := by
  intro κ hκ x
  have h := scaleLaw d hp hf V (scalingOfFactors eqv κ) (envOf us x)
  rw [scaleEnv_envOf] at h
  simp only [scale_scalingOfFactors eqv κ hκ] at h
  simpa [Matrix.of_apply] using h

end TermBridge

/-! ## The pendulum, again

The mass conclusion, restated here so the full pipeline can see it: the
statement and proof are those of `Pi.pendulum_period_independent_of_mass`,
verbatim. The mass exponent is zero in the solution, so the power-product
`∏ xᵢ^{Xᵢ}` does not
mention the mass, and by `eq_zero_of_appears_once` neither does any dimensionless
group. So `G` cannot mention it either: the period is independent of the mass,
and both halves of the theorem say so. -/

theorem pendulum_mass_absent {X : Fin 4 → ℚ}
    (hX : pendulum.mulVec X = ![0, 0, 2]) : X 0 = 0 :=
  solution_eq_zero_of_appears_once pendulum ![0, 0, 2] 0 0
    pendulum_mass_only.1 pendulum_mass_only.2 rfl hX

end LambdaS.Pi

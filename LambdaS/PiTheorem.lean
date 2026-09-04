/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
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
predicate on functions and proves the transport into log coordinates, so that
`pi_theorem` applies. The transport requires the function to be positive on
positive inputs. That is a genuine hypothesis, not bookkeeping: denotations
can be zero or negative, and the log transport is unavailable there. -/

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

/-- **The bridge theorem.** A function satisfying the multiplicative scale law
and positive on positive inputs has a log conjugate satisfying the additive
`ScaleLaw` with the same exponent matrix and result vector. This is the
missing link between the term-level law `scaleLaw` and the hypotheses of
`pi_theorem`: before this theorem the two were connected only in prose.

Positivity cannot be dropped. The zero function satisfies every multiplicative
law, and its log conjugate is the constant `log 0 = 0`, which satisfies
`ScaleLaw A b` only when `b = 0`. -/
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

/-- **Buckingham's factorization for multiplicative data.** The composition of
the bridge theorem with `pi_theorem`, stated back in the original coordinates:
a function satisfying the multiplicative scale law and positive on positive
inputs factors, on the positive orthant, as the power product `∏ i, x i ^ X i`
times a positive function of the log magnitudes that is invariant under every
rescaling, hence a function of the dimensionless groups alone
(`invariant_iff_dimensionless`, `pi_count`). -/
theorem mulScaleLaw_factorization (A : ExpMatrix m n) (b : Fin m → ℚ) (X : Fin n → ℝ)
    (hX : ∀ v, ∑ i, (A v i : ℝ) * X i = (b v : ℝ))
    {f : (Fin n → ℝ) → ℝ} (hmul : MulScaleLaw A b f)
    (hpos : ∀ x : Fin n → ℝ, (∀ i, 0 < x i) → 0 < f x) :
    ∃ G : (Fin n → ℝ) → ℝ, Invariant A G ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
        f x = (∏ i, x i ^ X i) * Real.exp (G fun i => Real.log (x i)) := by
  obtain ⟨G, hGinv, hGeq⟩ := pi_theorem A b X hX (scaleLaw_of_mulScaleLaw A b hmul hpos)
  refine ⟨G, hGinv, fun x hx => ?_⟩
  have hxfun : (fun i => Real.exp (Real.log (x i))) = x :=
    funext fun i => Real.exp_log (hx i)
  have hfx : 0 < f x := hpos x hx
  have hlog : Real.log (f x)
      = (∑ i, X i * Real.log (x i)) + G fun i => Real.log (x i) := by
    have h := hGeq fun i => Real.log (x i)
    simp only [logConj] at h
    rwa [hxfun] at h
  calc f x = Real.exp (Real.log (f x)) := (Real.exp_log hfx).symm
    _ = Real.exp ((∑ i, X i * Real.log (x i)) + G fun i => Real.log (x i)) := by
        rw [hlog]
    _ = (∏ i, x i ^ X i) * Real.exp (G fun i => Real.log (x i)) := by
        rw [Real.exp_add]
        congr 1
        rw [Real.exp_sum]
        exact Finset.prod_congr rfl fun i _ => by
          rw [Real.rpow_def_of_pos (hx i), mul_comm (Real.log (x i)) (X i)]

/-! ## From terms to the multiplicative law

The last gap: `scaleLaw` in `LambdaS.Fundamental` speaks about environments
and `Scaling`s, while `MulScaleLaw` speaks about vectors of magnitudes and a
matrix of exponents. This section closes it. For a first-order term over `n`
scalar arguments, the denotation as a function of the argument magnitudes
satisfies `MulScaleLaw` with the matrix whose column `i` is the base exponent
vector of argument `i`'s unit and the vector of the result unit's base
exponents. Base units are enumerated by an equivalence `Fin m ≃ B` so the
matrix has the index types `ScaleLaw` expects. -/

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

/-- The scaling whose base factors are a given vector of positive reals, read
through an enumeration of the base units, and whose unit-variable factors are
all `1`. The witness that instantiates `scaleLaw` at the scalings
`MulScaleLaw` quantifies over. -/
noncomputable def scalingOfFactors (e : Fin m ≃ B) (κ : Fin m → ℝ) : Scaling B k :=
  ⟨fun b => Real.log (κ (e.symm b)), fun _ => 0⟩

/-- The scale factor of `scalingOfFactors e κ` on a unit is the power product
of the factors against the unit's base exponents. Positivity of the factors is
required: `scale` exponentiates the logs of `κ`, and `log` collapses
nonpositive inputs. -/
theorem scale_scalingOfFactors (e : Fin m ≃ B) (κ : Fin m → ℝ)
    (hκ : ∀ v, 0 < κ v) (u : UExp B k) :
    (scalingOfFactors (k := k) e κ).scale u
      = ∏ v, κ v ^ ((u.base (e v) : ℚ) : ℝ) := by
  simp only [Scaling.scale, Scaling.logScale, scalingOfFactors, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [← Equiv.sum_comp e fun b => (u.base b : ℝ) * Real.log (κ (e.symm b))]
  simp only [Equiv.symm_apply_apply]
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun v _ => by
    rw [Real.rpow_def_of_pos (hκ v), mul_comm (Real.log (κ v)) ((u.base (e v) : ℚ) : ℝ)]

omit [Fintype D] in
/-- **The term-level multiplicative scale law.** The denotation of a
first-order parametric convert-free term, as a function of its argument
magnitudes, satisfies `MulScaleLaw` for the matrix of its arguments' base
exponents and the vector of its result unit's base exponents.

Together with `scaleLaw_of_mulScaleLaw` and `pi_theorem` this closes the chain
from a well-typed Λs term to Buckingham's factorization: the term supplies the
multiplicative law with no positivity assumption, and positivity of the
denotation on positive inputs is exactly what remains to be assumed before the
logarithmic transport applies.

The law quantifies over base-unit rescalings only; the unit-variable factors
of the underlying scaling are held at `1`. For a signature whose units also
mention unit variables this is the restriction of the full scaling law, not
its entirety. -/
theorem den_mulScaleLaw {m : ℕ} {Δ : DCtx D j k} {e : Tm B D j k}
    {us : List (UExp B k)} {u₀ : UExp B k}
    (d : HasTy Δ (scalarCtx us) e (.Q u₀)) (hp : e.Parametric)
    (hf : e.ConvertFree) (V : Scaling B k) (eqv : Fin m ≃ B) :
    MulScaleLaw (Matrix.of fun v i => (us.get i).base (eqv v))
      (fun v => u₀.base (eqv v)) (fun x => den V d (envOf us x)) := by
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

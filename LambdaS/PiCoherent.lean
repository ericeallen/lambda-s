/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.PiTheorem
import LambdaS.Adequacy

/-!
# Dimension-level Buckingham factorization for converting programs

`PiTheorem.den_mulScaleLaw` uses independent rescaling of every unit symbol,
which requires conversion freedom or a drift-free diagnosis. Physics instead
rescales dimensions. The coherent abstraction theorem supplies this weaker
law even for converting programs, but compares denotations at `V` and
`V.comp ψ`; a fixed-valuation scaling law needs one further argument.

The instrumented evaluator consults its oracle only after checking that source
and target have the same dimension. Oracles agreeing on those pairs therefore
produce identical evaluations, at every fuel and without a typing hypothesis.
Normalization and adequacy carry that equality to a scalar denotation with
scalar inputs. Coherent rescaling preserves precisely those oracle entries.

The resulting `den_pi_coherent` factors arbitrary signed outputs on positive
inputs through a rational basis of the dimension matrix's kernel. Its external
unit and dimension scope is closed (`j = k = 0`); the program may use all term
constructors, including unit and dimension binders internally. Extending this
bridge to ungrounded external unit/dimension variables is not claimed here.
-/

namespace LambdaS

variable {B D R : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
  [UnitSys B D] [Num R]

/-- Conversion oracles that agree on same-dimension pairs produce identical
instrumented evaluations, because the evaluator checks that condition before
consulting either oracle. No typing assumption is needed. -/
theorem eval_congr_sameDim (cf cf' : UExp B 0 → UExp B 0 → R)
    (hcf : ∀ u v, SameDim (DCtx.nil D) u v → cf u v = cf' u v)
    (n j k : ℕ) (η : UEnv B k) (δ : DEnv D j) (ρ : List (Val R B D))
    (e : Tm B D j k) : eval cf n j k η δ ρ e = eval cf' n j k η δ ρ e := by
  fun_induction eval cf n j k η δ ρ e <;> simp_all [eval]
  all_goals split <;> simp_all
  all_goals
    exfalso
    apply_assumption <;> rfl

/-- Scalar denotational environments as instrumented runtime values. -/
def scalarVals : (us : List (UExp B 0)) →
    Env (scalarCtx (D := D) (j := 0) us) → List (Val ℝ B D)
  | [], _ => []
  | u :: us, ρ => .scalar ⟨ρ.1, u⟩ :: scalarVals us ρ.2

private theorem scalarVals_red (cf : UExp B 0 → UExp B 0 → ℝ) :
    ∀ (us : List (UExp B 0)) (ρ : Env (scalarCtx (D := D) (j := 0) us)),
      RedEnv cf (scalarVals us ρ) (scalarCtx us)
  | [], _ => .nil
  | _ :: us, ρ => .cons (by simp [Red]) (scalarVals_red cf us ρ.2)

private theorem scalarVals_adeq (V : Scaling B 0) :
    ∀ (us : List (UExp B 0)) (ρ : Env (scalarCtx (D := D) (j := 0) us)),
      EnvAdeq V (nilU B) (nilU D) (scalarCtx us) (scalarVals us ρ) ρ
  | [], _ => .nil
  | _ :: us, ρ => .cons (by simp [Adeq]) (scalarVals_adeq V us ρ.2)

/-- A first-order scalar denotation depends only on conversion factors between
same-dimension units. Unit and dimension binders inside the term are allowed;
the external unit/dimension scope is closed. -/
theorem den_eq_of_sameDim_conv {e : Tm B D 0 0} {us : List (UExp B 0)} {u : UExp B 0}
    (d : HasTy (DCtx.nil D) (scalarCtx us) e (.Q u)) (V V' : Scaling B 0)
    (hconv : ∀ u v, SameDim (DCtx.nil D) u v → conv V u v = conv V' u v)
    (ρ : Env (scalarCtx us)) : den V d ρ = den V' d ρ := by
  have hred : RedEnv (conv V) (scalarVals us ρ)
      (groundCtx (nilU B) (nilU D) (scalarCtx us)) := by
    simpa [groundCtx, scalarCtx, List.map_map, Function.comp_def, Ty.ground]
      using scalarVals_red (conv V) us ρ
  obtain ⟨n, v, hv, _⟩ := red_eval (conv V) e (nilU B) (nilU D) (scalarVals us ρ)
    (DCtx.nil D) (scalarCtx us) (.Q u) hred (fun i => i.elim0) d
  have hv' : eval (conv V') n 0 0 (nilU B) (nilU D) (scalarVals us ρ) e = some v := by
    rw [← eval_congr_sameDim (conv V) (conv V') hconv]
    exact hv
  have h₁ := eval_adeq V e (nilU B) (nilU D) (scalarVals us ρ) (DCtx.nil D)
    (scalarCtx us) (.Q u) ρ d (scalarVals_adeq V us ρ) (fun i => i.elim0) n v hv
  have h₂ := eval_adeq V' e (nilU B) (nilU D) (scalarVals us ρ) (DCtx.nil D)
    (scalarCtx us) (.Q u) ρ d (scalarVals_adeq V' us ρ) (fun i => i.elim0) n v hv'
  simp only [Adeq, Scaling.pull_nil, substU_nil] at h₁ h₂
  simpa using h₁.symm.trans h₂

/-- Coherent rescaling leaves the valuation dependence of any first-order
scalar program unchanged, even when the program contains conversion. -/
theorem den_eq_of_coherent {e : Tm B D 0 0} {us : List (UExp B 0)} {u : UExp B 0}
    (d : HasTy (DCtx.nil D) (scalarCtx us) e (.Q u)) (V ψ : Scaling B 0)
    (hψ : ψ.Coherent (DCtx.nil D)) (ρ : Env (scalarCtx us)) :
    den (V.comp ψ) d ρ = den V d ρ :=
  den_eq_of_sameDim_conv d (V.comp ψ) V (fun _ _ h => conv_invariant_of_coherent V hψ h) ρ

omit [DecidableEq B] [DecidableEq D] [UnitSys B D] in
private theorem relEnvCo_scaleEnv (ψ : Scaling B 0) (Φ : Scaling D 0) :
    ∀ (us : List (UExp B 0)) (ρ : Env (scalarCtx (D := D) (j := 0) us)),
      RelEnvCo (scalarCtx us) (DCtx.nil D) Φ ψ ρ (scaleEnv ψ us ρ)
  | [], _ => trivial
  | _ :: us, ρ => ⟨rfl, relEnvCo_scaleEnv ψ Φ us ρ.2⟩

/-- The fixed-valuation coherent scaling law, for first-order programs that may
convert and may contain internal unit/dimension polymorphism. -/
theorem scaleLaw_coherent {e : Tm B D 0 0} {us : List (UExp B 0)} {u : UExp B 0}
    (d : HasTy (DCtx.nil D) (scalarCtx us) e (.Q u)) (hp : e.Parametric)
    (V ψ : Scaling B 0) (Φ : Scaling D 0) (hψ : ψ.Factors (DCtx.nil D) Φ)
    (ρ : Env (scalarCtx us)) :
    den V d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ := by
  have henv := relEnvCo_scaleEnv ψ Φ us ρ
  have h := fundamental d hp V ψ Φ hψ henv
  change den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ at h
  rwa [den_eq_of_coherent d V ψ hψ.coherent] at h

namespace Pi

/-- Exponents of a unit's dimension, in an enumerated dimension basis. The
empty summand is retained to reuse the general scaling enumeration. -/
def dimensionExponents {m : ℕ} (eqv : Fin m ≃ D ⊕ Fin 0) (u : UExp B 0) :
    Fin m → ℚ :=
  fun v => Sum.elim (dimOf (D := D) (DCtx.nil D) u).base
    (dimOf (D := D) (DCtx.nil D) u).vars (eqv v)

/-- The dimension matrix: different units of one dimension have identical
columns, unlike the stronger unit-level matrix used by `den_mulScaleLaw`. -/
def dimensionMatrix {m : ℕ} (eqv : Fin m ≃ D ⊕ Fin 0) (us : List (UExp B 0)) :
    ExpMatrix m us.length := Matrix.of fun v i => dimensionExponents eqv (us.get i) v

/-- **The classical dimension-level scaling law for converting programs.**
Any parametric first-order program in closed external unit/dimension scope
obeys the multiplicative law over dimensions, for a fixed valuation. The
program may contain internal polymorphism and conversion. -/
theorem den_mulScaleLaw_coherent {m : ℕ} {e : Tm B D 0 0}
    {us : List (UExp B 0)} {u : UExp B 0}
    (d : HasTy (DCtx.nil D) (scalarCtx us) e (.Q u)) (hp : e.Parametric)
    (V : Scaling B 0) (eqv : Fin m ≃ D ⊕ Fin 0) :
    MulScaleLaw (dimensionMatrix eqv us) (dimensionExponents eqv u)
      (fun x => den V d (envOf us x)) := by
  intro κ hκ x
  let Φ : Scaling D 0 := scalingOfFactors eqv κ
  let ψ : Scaling B 0 :=
    ⟨fun b => ∑ d, ((UnitSys.dim (D := D) b).base d : ℝ) * Φ.base d, Fin.elim0⟩
  have hψ : ψ.Factors (DCtx.nil D) Φ := ⟨fun _ => rfl, fun i => i.elim0⟩
  have hs : ∀ w : UExp B 0, ψ.scale w =
      ∏ v, κ v ^ (dimensionExponents eqv w v : ℝ) := by
    intro w
    change Real.exp (ψ.logScale w) = _
    rw [hψ.logScale]
    exact scale_scalingOfFactors eqv κ hκ (dimOf (D := D) (DCtx.nil D) w)
  have h := scaleLaw_coherent d hp V ψ Φ hψ (envOf us x)
  rw [scaleEnv_envOf] at h
  simpa only [hs, dimensionMatrix, Matrix.of_apply] using h

/-- **Buckingham's reduced-arity factorization for converting programs.**
The matrix is over dimensions; positive arguments and arbitrary signed output
are exactly the domain of `mulScaleLaw_factorization_reduced`. -/
theorem den_pi_coherent {m : ℕ} {e : Tm B D 0 0}
    {us : List (UExp B 0)} {u : UExp B 0}
    (d : HasTy (DCtx.nil D) (scalarCtx us) e (.Q u)) (hp : e.Parametric)
    (V : Scaling B 0) (eqv : Fin m ≃ D ⊕ Fin 0)
    (X : Fin us.length → ℝ)
    (hX : ∀ v, ∑ i, (dimensionMatrix eqv us v i : ℝ) * X i =
      (dimensionExponents eqv u v : ℝ)) :
    ∃ G : (Fin (us.length - Matrix.rank (dimensionMatrix eqv us)) → ℝ) → ℝ,
      ∀ x : Fin us.length → ℝ, (∀ i, 0 < x i) →
        den V d (envOf us x) = (∏ i, x i ^ X i) *
          G (piCoordinates (dimensionMatrix eqv us) (fun i => Real.log (x i))) :=
  mulScaleLaw_factorization_reduced (dimensionMatrix eqv us) (dimensionExponents eqv u)
    X hX (den_mulScaleLaw_coherent d hp V eqv)

end Pi
end LambdaS

/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.PiCoherent
import LambdaS.Examples

/-!
# Boundary checks for the strengthened Pi theorem

These kernel-checked examples test three predictions recorded before running:
coherent factorization covers `addMixed` despite its diagnostic decline;
internal dimension/unit abstraction is accepted by the coherent bridge; and
rank-zero/full-rank matrices require no extra nonempty hypotheses. The caster's
derivation is constructed from typing rules and substitution lemmas, without
compiler-evaluated decision procedures.
-/

namespace LambdaS.Examples
open LambdaS.Pi

/-- Coherent scaling covers a program the drift diagnostic declines. -/
theorem addMixed_coherent (V : Scaling Base 0) {m' : ℕ}
    (eqv : Fin m' ≃ Dim ⊕ Fin 0) :
    MulScaleLaw (dimensionMatrix eqv [m, ft]) (dimensionExponents eqv ft)
      (fun x => den V addMixedDeriv (envOf [m, ft] x)) :=
  den_mulScaleLaw_coherent addMixedDeriv (by trivial) V eqv

/-- Internal dimension and unit abstraction, instantiated at meter and foot. -/
def instantiatedCaster : Term₀ :=
  .app (.uapp (.uapp (.dapp caster (Term.ofBase Dim.length)) m) ft) (.var 0)

private def casterTyped : HasTy Δ₀ (scalarCtx [m]) caster
    (.allDim (.all (Term.ofVar 0) (.all (Term.ofVar 0)
      (.arrow (.Q (Term.ofVar 1)) (.Q (Term.ofVar 0)))))) :=
  .dlam (.ulam (.ulam (.lam (.convert (.var rfl) (by simp only [SameDim, dimOf_ofVar]; rfl)))))

private def casterDimTyped : HasTy Δ₀ (scalarCtx [m])
    (.dapp caster (Term.ofBase Dim.length))
    (.all (Term.ofBase Dim.length) (.all (Term.ofBase Dim.length)
      (.arrow (.Q (Term.ofVar 1)) (.Q (Term.ofVar 0))))) := by
  simpa [Ty.substDim, Ty.ground, liftU, idU] using
    (HasTy.dapp (d := Term.ofBase Dim.length) casterTyped)

private def casterMeterTyped : HasTy Δ₀ (scalarCtx [m])
    (.uapp (.dapp caster (Term.ofBase Dim.length)) m)
    (.all (Term.ofBase Dim.length) (.arrow (.Q (UExp.weaken m)) (.Q (Term.ofVar 0)))) := by
  have h := HasTy.uapp casterDimTyped (σ := m) (by
    change dimOf (DCtx.nil Dim) (Term.ofBase Base.meter) = UnitSys.dim Base.meter
    exact Decl.dimOf_ofBase Base.meter)
  convert h using 1
  simp [Ty.subst, Ty.ground, liftU]
  rfl

def instantiatedCasterDeriv : HasTy Δ₀ (scalarCtx [m]) instantiatedCaster (.Q ft) := by
  have h : HasTy Δ₀ (scalarCtx [m])
      (.uapp (.uapp (.dapp caster (Term.ofBase Dim.length)) m) ft)
      (.arrow (.Q m) (.Q ft)) := by
    simpa [Ty.subst, Ty.ground, liftU, idU, substU_weaken_cons] using (HasTy.uapp casterMeterTyped (σ := ft) (by
      change dimOf (DCtx.nil Dim) (Term.ofBase Base.foot) = UnitSys.dim Base.foot
      exact Decl.dimOf_ofBase Base.foot))
  exact .app h (.var rfl)

theorem instantiatedCaster_coherent (V : Scaling Base 0) {m' : ℕ}
    (eqv : Fin m' ≃ Dim ⊕ Fin 0) :
    MulScaleLaw (dimensionMatrix eqv [m]) (dimensionExponents eqv ft)
      (fun x => den V instantiatedCasterDeriv (envOf [m] x)) :=
  den_mulScaleLaw_coherent instantiatedCasterDeriv (by trivial) V eqv

end LambdaS.Examples

namespace LambdaS.Pi

/-- Full rank really produces a function of zero arguments. -/
theorem fullRank_descends {H : (Fin 1 → ℝ) → ℝ} (hH : Invariant (1 : ExpMatrix 1 1) H) :
    ∃ G : (Fin 0 → ℝ) → ℝ, ∀ ξ, H ξ = G (fun i => i.elim0) := by
  obtain ⟨G, hG⟩ := invariant_descends (1 : ExpMatrix 1 1) hH
  have hr : Matrix.rank (1 : ExpMatrix 1 1) = 1 := by simp
  refine ⟨fun _ => G (piCoordinates (1 : ExpMatrix 1 1) (fun _ => 0)), fun ξ => ?_⟩
  rw [hG]
  congr 1
  funext i
  have hi := i.isLt
  omega

/-- Zero rank retains all coordinates, with no nonempty-row assumption. -/
theorem zeroRank_descends {n : ℕ} {H : (Fin n → ℝ) → ℝ} :
    Matrix.rank (0 : ExpMatrix 0 n) = 0 ∧
    ∃ G : (Fin (n - Matrix.rank (0 : ExpMatrix 0 n)) → ℝ) → ℝ,
      ∀ ξ, H ξ = G (piCoordinates (0 : ExpMatrix 0 n) ξ) := by
  have hH : Invariant (0 : ExpMatrix 0 n) H := by
    intro ψ ξ
    simp [act]
  exact ⟨by simp, invariant_descends (0 : ExpMatrix 0 n) hH⟩

end LambdaS.Pi

/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Ratio
import LambdaS.Definability

/-!
# Fuel-free comparison of open first-order ratios

Every scalar component of a first-order context receives its own fresh unit
variable. `Tw.nf` evaluates in that symbolic environment by structural recursion:
internal functions, higher-order applications, and unit binders impose no fuel
bound. Unknown function and unit-family inputs are outside this interface.
The correctness and exactness statements quantify over arbitrary positive input
drifts, not an all-ones environment.
-/

namespace LambdaS

/-- Shapes whose unknown values have finitely many independent scalar components. -/
def Shape.firstOrder : Shape → Bool
  | .scalar | .vec _ | .mat _ _ => true
  | .arrow _ _ | .bind _ => false

/-- Number of independent scalar components. Higher-order inputs are excluded. -/
@[reducible] def Shape.cells : Shape → Nat
  | .scalar => 1
  | .vec n => n
  | .mat n m => m * n
  | .arrow _ _ | .bind _ => 0

/-- Reconstruct a value from its scalar components. -/
def Shape.decode : (s : Shape) → (Fin s.cells → SemScalar) → SemTw s
  | .scalar, f => f 0
  | .vec _, f => f
  | .mat _ _, f => fun j i => f (finProdFinEquiv (j, i))
  | .arrow _ t, _ => oneSem (.arrow _ t)
  | .bind t, _ => oneSem (.bind t)

/-- Read scalar components out of a value. -/
def Shape.encode : (s : Shape) → SemTw s → Fin s.cells → SemScalar
  | .scalar, v, _ => v
  | .vec _, v, i => v i
  | .mat _ _, v, i => v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  | .arrow _ _, _, i => i.elim0
  | .bind _, _, i => i.elim0

/-- Component reconstruction preserves every first-order value. -/
theorem Shape.decode_encode (s : Shape) (h : s.firstOrder = true) (v : SemTw s) :
    s.decode (s.encode v) = v := by
  cases s with
  | scalar => rfl
  | vec n => rfl
  | mat n m => funext j i; simp [Shape.decode, Shape.encode]
  | arrow s t => cases h
  | bind s => cases h

/-- Reflect symbolic scalar components at their shape. -/
def Shape.reflect {B : Type} {k : Nat} : (s : Shape) →
    (Fin s.cells → UExp B k) → SynTw B k s
  | .scalar, f => f 0
  | .vec _, f => f
  | .mat _ _, f => fun j i => f (finProdFinEquiv (j, i))
  | .arrow s t, _ => SynTw.one (.arrow s t)
  | .bind t, _ => SynTw.one (.bind t)

/-- Reflection respects the symbolic logical relation. -/
theorem Shape.reflect_correct {B : Type} [Fintype B] {k : Nat}
    (ψ : Scaling B k) (s : Shape) (f : Fin s.cells → UExp B k) :
    SRel ψ s (s.reflect f) (s.decode fun i => ⟨ψ.scale (f i), ψ.scale_pos _⟩) := by
  cases s with
  | scalar => rfl
  | vec n => intro i; rfl
  | mat n m => intro j i; rfl
  | arrow s t => exact srel_one ψ (.arrow s t)
  | bind t => exact srel_one ψ (.bind t)

/-- Total number of independent context components. -/
@[reducible] def ratioCells : List Shape → Nat
  | [] => 0
  | s :: Θ => s.cells + ratioCells Θ

/-- A first-order context may contain vectors and matrices, but no unknown functions. -/
def ratioFirstOrder (Θ : List Shape) : Bool := Θ.all Shape.firstOrder

/-- Reconstruct an environment from independent scalar components. -/
def decodeRatioEnv : (Θ : List Shape) → (Fin (ratioCells Θ) → SemScalar) → TwEnv Θ
  | [], _ => PUnit.unit
  | s :: Θ, f => (s.decode (fun i => f (Fin.castAdd _ i)),
      decodeRatioEnv Θ (fun i => f (Fin.natAdd s.cells i)))

/-- Read all scalar components of a context. -/
def encodeRatioEnv : (Θ : List Shape) → TwEnv Θ → Fin (ratioCells Θ) → SemScalar
  | [], _, i => i.elim0
  | s :: Θ, ρ, i => Fin.addCases (s.encode ρ.1) (encodeRatioEnv Θ ρ.2) i

/-- No information is lost for first-order contexts. -/
theorem decode_encode_ratioEnv (Θ : List Shape) (h : ratioFirstOrder Θ = true)
    (ρ : TwEnv Θ) : decodeRatioEnv Θ (encodeRatioEnv Θ ρ) = ρ := by
  induction Θ with
  | nil => cases ρ; rfl
  | cons s Θ ih =>
    simp only [ratioFirstOrder, List.all_cons, Bool.and_eq_true] at h
    simp only [decodeRatioEnv, encodeRatioEnv, Fin.addCases_left, Fin.addCases_right]
    rw [Shape.decode_encode s h.1, ih h.2]

/-- Reflect a context using distinct symbolic scalar components. -/
def reflectRatioEnv {B : Type} {k : Nat} : (Θ : List Shape) →
    (Fin (ratioCells Θ) → UExp B k) → SynEnv B k Θ
  | [], _ => PUnit.unit
  | s :: Θ, f => (s.reflect (fun i => f (Fin.castAdd _ i)),
      reflectRatioEnv Θ (fun i => f (Fin.natAdd s.cells i)))

/-- Context reflection is related to its componentwise interpretation. -/
theorem reflectRatioEnv_correct {B : Type} [Fintype B] {k : Nat}
    (ψ : Scaling B k) (Θ : List Shape) (f : Fin (ratioCells Θ) → UExp B k) :
    SRelEnv ψ Θ (reflectRatioEnv Θ f)
      (decodeRatioEnv Θ fun i => ⟨ψ.scale (f i), ψ.scale_pos _⟩) := by
  induction Θ with
  | nil => trivial
  | cons s Θ ih => exact ⟨s.reflect_correct ψ _, ih _⟩

/-- Fuel-free scalar normal form, with fresh coordinates for every input component.
Exactness for arbitrary environments requires `ratioFirstOrder Θ = true`. -/
def Tw.openNF {B : Type} {k : Nat} {Θ : List Shape} (t : Tw B k Θ .scalar) :
    UExp B (k + ratioCells Θ) :=
  Tw.nf (fun i => Term.ofVar (Fin.castAdd _ i)) t
    (reflectRatioEnv Θ fun i => Term.ofVar (Fin.natAdd k i))

/-- Split the enlarged scaling into the original unit scope. -/
def ratioUnitScaling {B : Type} {k : Nat} {Θ : List Shape}
    (χ : Scaling B (k + ratioCells Θ)) : Scaling B k :=
  ⟨χ.base, fun i => χ.vars (Fin.castAdd _ i)⟩

/-- Interpret the fresh coordinates as independent positive input drifts. -/
noncomputable def ratioInputEnv {B : Type} {k : Nat} (Θ : List Shape)
    (χ : Scaling B (k + ratioCells Θ)) : TwEnv Θ :=
  decodeRatioEnv Θ fun i => ⟨Real.exp (χ.vars (Fin.natAdd k i)), Real.exp_pos _⟩

/-- Correctness under every assignment of original and fresh coordinates. -/
theorem Tw.openNF_correct {B : Type} [Fintype B] {k : Nat} {Θ : List Shape}
    (t : Tw B k Θ .scalar) (χ : Scaling B (k + ratioCells Θ)) :
    (Tw.eval (ratioUnitScaling χ) t (ratioInputEnv Θ χ) : ℝ) = χ.scale t.openNF := by
  have h := Tw.nf_correct χ (fun i => Term.ofVar (Fin.castAdd (ratioCells Θ) i)) t
    _ _ (reflectRatioEnv_correct χ Θ (fun i => Term.ofVar (Fin.natAdd k i)))
  simpa [SRel, Tw.openNF, ratioUnitScaling, ratioInputEnv, Scaling.pull,
    Scaling.scale] using h

/-- Extend any original scaling with the logarithms of the actual input drifts. -/
noncomputable def extendRatioScaling {B : Type} {k : Nat} {Θ : List Shape}
    (ψ : Scaling B k) (ρ : TwEnv Θ) : Scaling B (k + ratioCells Θ) :=
  ⟨ψ.base, Fin.addCases ψ.vars (fun i => Real.log (encodeRatioEnv Θ ρ i : ℝ))⟩

/-- Restriction recovers the original unit scaling. -/
@[simp] theorem ratioUnitScaling_extend {B : Type} {k : Nat} {Θ : List Shape}
    (ψ : Scaling B k) (ρ : TwEnv Θ) : ratioUnitScaling (extendRatioScaling ψ ρ) = ψ := by
  cases ψ
  simp [ratioUnitScaling, extendRatioScaling]

/-- Every first-order environment is represented by fresh coordinates. -/
@[simp] theorem ratioInputEnv_extend {B : Type} {k : Nat} {Θ : List Shape}
    (h : ratioFirstOrder Θ = true) (ψ : Scaling B k) (ρ : TwEnv Θ) :
    ratioInputEnv Θ (extendRatioScaling ψ ρ) = ρ := by
  simp only [ratioInputEnv, extendRatioScaling, Fin.addCases_right]
  have he : (fun i => (⟨Real.exp (Real.log (encodeRatioEnv Θ ρ i : ℝ)),
      Real.exp_pos _⟩ : SemScalar)) = encodeRatioEnv Θ ρ := by
    funext i
    exact Subtype.ext (Real.exp_log (encodeRatioEnv Θ ρ i).property)
  rw [he, decode_encode_ratioEnv Θ h]

/-- Equal open normal forms agree at arbitrary positive first-order inputs. -/
theorem Tw.openNF_sound {B : Type} [Fintype B] {k : Nat} {Θ : List Shape}
    (a b : Tw B k Θ .scalar) (hΘ : ratioFirstOrder Θ = true) (h : a.openNF = b.openNF)
    (ψ : Scaling B k) (ρ : TwEnv Θ) : Tw.eval ψ a ρ = Tw.eval ψ b ρ := by
  have ha := a.openNF_correct (extendRatioScaling ψ ρ)
  have hb := b.openNF_correct (extendRatioScaling ψ ρ)
  simp only [ratioUnitScaling_extend, ratioInputEnv_extend hΘ] at ha hb
  exact Subtype.ext (ha.trans ((congrArg _ h).trans hb.symm))

/-- Exactness includes all internal higher-order applications and unit binders;
only the unknown input context must be first-order. -/
theorem Tw.openNF_eq_iff {B : Type} [Fintype B] {k : Nat} {Θ : List Shape}
    (a b : Tw B k Θ .scalar) (hΘ : ratioFirstOrder Θ = true) :
    a.openNF = b.openNF ↔
      ∀ (ψ : Scaling B k) (ρ : TwEnv Θ), Tw.eval ψ a ρ = Tw.eval ψ b ρ := by
  constructor
  · exact a.openNF_sound b hΘ
  · intro h
    classical
    apply scale_eq_iff.mp
    intro χ
    rw [← a.openNF_correct χ, ← b.openNF_correct χ, h]

end LambdaS

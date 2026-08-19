import LambdaS.Uom

/-!
# Dimensioned spaces

A **space** is an index type `I` together with a unit assignment `δ : I → Uom B`.
A vector over it is a dependent function `(i : I) → Q[F, δ i]`; a linear map is
handled in `LambdaS.Map`.

## Spaces are structural

`Space B I` is a *reducible abbreviation* for `I → Uom B`. A space therefore
**is** its unit assignment: two spaces with equal `δ` are equal, definitionally,
with no coercion in between.

This is a decision, not an accident. It is what makes a uniform space *equal* to
`triv ⊗ u` rather than merely isomorphic to it, and so what lets the signature of
SVD be a type error rather than a side condition. Making spaces nominal would
silently invalidate `Space.uniform_iff_scale_triv` and, with it, the claim
that Hart's taxonomy is derived rather than checked.
-/

namespace LambdaS

/-- A space: an index type together with a unit assignment. Structural in `δ`. -/
abbrev Space (B I : Type*) := I → Uom B

namespace Space

variable {B I J : Type*}

/-- The dimensionless space on `I`, written `I₁` on paper. Every component
carries the trivial unit. -/
def triv (B I : Type*) : Space B I := fun _ => 1

/-- The dual space carries **reciprocal** units.

This one definition is why `⟨φ|ψ⟩` is dimensionless and why `⟨φ|H|ψ⟩` carries
the unit of `H`: neither needs a rule. -/
def dual (V : Space B I) : Space B I := fun i => (V i)⁻¹

/-- Scaling a space by a scalar unit, written `V ⊗ d`. -/
def scale (V : Space B I) (d : Uom B) : Space B I := fun i => V i * d

@[inherit_doc] infixl:70 " ⊗ " => Space.scale

/-- A space is *uniform* when every component carries the same unit. -/
def Uniform (V : Space B I) : Prop := ∃ u, ∀ i, V i = u

/-- The tensor product of spaces: index types multiply, units multiply.
This is what composite quantum systems need. -/
def tensor (V : Space B I) (W : Space B J) : Space B (I × J) := fun p => V p.1 * W p.2

/-- The one-dimensional space carrying unit `d`. -/
def ofUom (d : Uom B) : Space B PUnit := fun _ => d

/-- **Scaling is tensoring.** `V ⊗ d` is the tensor product of `V` with the
one-dimensional space carrying `d`, transported along `I × PUnit ≅ I`.

So `⊗` is a single operator, not two that happen to share notation — the
scalar case is the one-point case. It holds definitionally. -/
theorem scale_eq_tensor (V : Space B I) (d : Uom B) (i : I) :
    (V ⊗ d) i = tensor V (ofUom d) (i, PUnit.unit) := rfl

@[simp] theorem triv_apply (i : I) : triv B I i = 1 := rfl

@[simp] theorem dual_apply (V : Space B I) (i : I) : V.dual i = (V i)⁻¹ := rfl

@[simp] theorem scale_apply (V : Space B I) (d : Uom B) (i : I) : (V ⊗ d) i = V i * d := rfl

@[simp] theorem dual_dual (V : Space B I) : V.dual.dual = V := by funext i; simp

@[simp] theorem scale_one (V : Space B I) : V ⊗ (1 : Uom B) = V := by funext i; simp

/-- Scaling composes: `(V ⊗ d) ⊗ e = V ⊗ (d * e)`. Half of the functoriality of
`⊗`; the other half is `LambdaS.Map.entry_scale_scale`. -/
@[simp] theorem scale_scale (V : Space B I) (d e : Uom B) : (V ⊗ d) ⊗ e = V ⊗ (d * e) := by
  funext i; simp [mul_assoc]

theorem dual_scale (V : Space B I) (d : Uom B) : (V ⊗ d).dual = V.dual ⊗ d⁻¹ := by
  funext i; simp [mul_comm]

/-- A uniform space is *equal* to a scaled dimensionless space — not merely
isomorphic to one. This equality is what structurality buys, and it is what
makes `LambdaS.Map.svd_entry_const` a statement about types. -/
theorem uniform_iff_scale_triv (V : Space B I) :
    V.Uniform ↔ ∃ u, V = triv B I ⊗ u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, funext fun i => by simp [hu i]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, fun i => by simp⟩

theorem triv_uniform : (triv B I).Uniform := ⟨1, fun _ => rfl⟩

end Space

end LambdaS

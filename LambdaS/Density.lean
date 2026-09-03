/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Map

/-!
# Densities of weight `w`, and why one construction covers three domains

A space with measure unit `μ` induces, for each rational weight `w`, a space of
**densities of weight `w`** carrying unit `μ^(-w)`. Fixing `w` recovers, one at
a time, three things usually treated as unrelated:

| `w` | what it is | domain |
|-----|------------|--------|
| `0`   | ordinary scalar functions | – |
| `1/2` | half-densities: `L2` amplitudes, wavefunctions | quantum mechanics |
| `1`   | probability densities | statistics |
| `-1`  | the measure itself | – |

The half-density case is a pleasing convergence: the design's L² space was
derived purely from the normalization condition `∫|ψ|² dx = 1`, and it turns
out to be the half-density bundle that geometric quantization arrives at from
entirely different motives.

## What this buys in statistics

Because `log` requires a dimensionless argument, `log p` for a probability
density `p` **fails to typecheck**. That is the base-measure problem: a density
only means something relative to the measure it was taken against, and
representing a distribution by its density silently discards that measure.
Radul and Alexeev (arXiv:2010.09647) identify exactly this failure in
probabilistic programming systems, and solve it by library convention:
standardizing on Hausdorff measure and tracking corrections in a `Bijector`
architecture. Here it is a *type error* instead, and the tracking is inferred.

The classical consequence falls straight out: differential entropy `-∫ p log p`
is ill-typed, while KL divergence `∫ p log(p/q)` is fine, because a ratio of
equal-weight densities has weight `0`. The well-known fact that differential
entropy is not invariant under a change of units while relative entropy is
becomes a distinction the checker enforces rather than one you are expected to
remember.

## What this buys in general relativity

A metric is a map `V ⊸ dual V ⊗ d`, so its entries carry `d/(δᵢδⱼ)` and lowering
an index shifts a unit by `d`. The invariant volume element then works out to
`d^(n/2)`, independent of the coordinate units, as it must be.

Note the exponent. Rational weights are not a convenience here: `w = 1/2` for
wavefunctions and `n/2` for volume elements in odd dimension both require them.
That is now the *third* independent forcing of ℚ over ℤ, after volatility at
`Time^(-1/2)` and normalized wavefunctions at `m^(-3/2)`.
-/

namespace LambdaS

variable {B I : Type*}

/-- The space of densities of weight `w` over an index type `I` whose measure
carries unit `μ`. Uniform, as densities are. -/
def Density (μ : Uom B) (w : ℚ) (I : Type*) : Space B I := fun _ => μ ^ (-w)

@[simp] theorem density_apply (μ : Uom B) (w : ℚ) (i : I) :
    Density μ w I i = μ ^ (-w) := rfl

/-- Weight `0` is the dimensionless space. This is why `log` typechecks on
weight-`0` quantities and on nothing else. -/
theorem density_zero (μ : Uom B) : Density μ 0 I = Space.triv B I := by
  funext i; simp [Density, Space.triv]

/-- **Weights add under multiplication of densities.** -/
theorem density_mul (μ : Uom B) (w₁ w₂ : ℚ) (i : I) :
    Density μ w₁ I i * Density μ w₂ I i = Density μ (w₁ + w₂) I i := by
  simp only [density_apply, ← Uom.rpow_add]
  ring_nf

/-- **`|ψ|²` of a half-density is a weight-1 density**: that is, exactly the
thing that can be integrated. The normalization condition of quantum mechanics
and the defining property of a probability density are the same statement at
two different weights. -/
theorem modulus_sq_of_half (μ : Uom B) (i : I) :
    Density μ (1/2) I i * Density μ (1/2) I i = Density μ 1 I i := by
  rw [density_mul]; norm_num

/-- **Integration is well-typed exactly at weight 1.** A weight-1 density paired
with the measure is dimensionless. -/
theorem integrate_weight_one (μ : Uom B) (i : I) :
    Density μ 1 I i * μ = 1 := by
  simp only [density_apply]
  ext b
  simp

/-- **The ratio of two densities of equal weight is dimensionless**, whatever
that weight is.

This is the whole KL-versus-entropy distinction: `log (p/q)` typechecks because
the ratio lands at weight `0`, while `log p` does not, because `p` does not. -/
theorem ratio_weight_zero (μ : Uom B) (w : ℚ) (i : I) :
    Density μ w I i / Density μ w I i = Density μ 0 I i := by
  simp

/-- A density of nonzero weight is *not* dimensionless, unless the measure
itself is. This is the statement that `log p` genuinely fails: the failure is
not an artifact of how the weight is written. -/
theorem density_ne_triv (μ : Uom B) {w : ℚ} (hw : w ≠ 0) (i : I) {b : B}
    (hμ : Uom.exp μ b ≠ 0) : Density μ w I i ≠ Space.triv B I i := by
  simp only [density_apply, Space.triv]
  intro h
  have : (-w) * Uom.exp μ b = 0 := by
    have := congrArg (fun u => Uom.exp u b) h
    simpa using this
  rcases mul_eq_zero.mp this with h1 | h2
  · exact hw (neg_eq_zero.mp h1)
  · exact hμ h2

/-! ## General relativity, on the same machinery -/

/-- A **metric** is a map `V ⊸ dual V ⊗ d`, where `d` is the unit of the
invariant interval. Its entries carry `d / (δⱼ δᵢ)`, symmetric in the two
indices, as a metric must be, and dimensionally consistent with `gᵢⱼxⁱxʲ`
having unit `d`. -/
theorem metric_entry (V : Space B I) (d : Uom B) (j i : I) :
    entry V (V.dual ⊗ d) j i = d / (V j * V i) := by
  ext b; simp; ring

/-- **Lowering an index shifts the unit by `d`.** In coordinates, `xⁱ` and `xᵢ`
are dimensionally different objects, and this is by how much. -/
theorem lower_index (V : Space B I) (d : Uom B) (i : I) :
    (V.dual ⊗ d) i = d / V i := by
  ext b; simp; ring

/-- **The interval is invariant.** Contracting a vector twice against the metric
lands at `d`, whatever units the coordinates carry, which is the statement that
the metric determines a coordinate-independent scale. -/
theorem interval_unit (V : Space B I) (d : Uom B) (j i : I) :
    V j * entry V (V.dual ⊗ d) j i * V i = d := by
  ext b; simp; ring

end LambdaS

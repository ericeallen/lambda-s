import LambdaS.Space

/-!
# Linear maps between dimensioned spaces, and the collapse of Hart's taxonomy

George Hart's *Multidimensional Analysis* (1995) is the only serious theory of
dimensioned matrices. Its central observation is that an array of dimensioned
entries is only well-behaved when its exponent structure is **rank one**
(entry `(j,i)` must carry `aⱼ · bᵢ`), and from there Hart derives a taxonomy of
five classes, each licensing a different set of operations:

| Hart's class        | operations licensed                    |
|---------------------|----------------------------------------|
| multipliable        | compose, transpose, solve              |
| endomorphic         | powers, `exp`, `det`, `trace`          |
| squarable           | eigendecomposition                     |
| dimensionally symm. | Cholesky, weighted norms               |
| uniform             | SVD, pseudo-inverse                    |

Hart needed the rank-one condition because he worked with raw arrays.

**This file is the claim that if you type the space, all of it is free.** A
linear map `V ⊸ W` has entry `(j,i)` at `δ_W(j) / δ_V(i)`, which is rank one by
construction. Each of Hart's five classes then corresponds to a *type*, and the
operations it licenses are exactly the ones well-typed at that type. Nothing is
checked; the taxonomy is derived.

The theorems below are that argument, one class at a time.
-/

namespace LambdaS

variable {B I J K : Type*}

/-- The unit carried by entry `(j,i)` of a linear map `V ⊸ W`.

Forced by requiring `(Ax)ⱼ = Σᵢ A[j,i] · xᵢ` to be well-typed: `xᵢ` carries
`δ_V(i)` and the result must carry `δ_W(j)`. -/
def entry (V : Space B I) (W : Space B J) (j : J) (i : I) : Uom B := W j / V i

@[simp] theorem entry_def (V : Space B I) (W : Space B J) (j : J) (i : I) :
    entry V W j i = W j / V i := rfl

/-! ## Rank one, by construction

Hart's precondition, recovered as a triviality: the entry unit factors as a
function of `j` times a function of `i`, always. -/

/-- Hart's rank-one form `A ~ a·b̃`, with `a = δ_W` and `b = δ_V⁻¹`. There is no
hypothesis: every well-typed map has it. -/
theorem entry_rank_one (V : Space B I) (W : Space B J) (j : J) (i : I) :
    entry V W j i = W j * (V i)⁻¹ := by
  simp [div_eq_mul_inv]

/-! ## 1. Multipliable -/

/-- **Composition.** The summand `entry V W k j * entry U V j i` does not depend
on the summation index `j`, so the sum is dimensionally legal, and its value is
exactly the entry of the composite `U ⊸ W`.

Hart's "multipliable" is not a class one checks. It is the only thing writable. -/
theorem entry_comp (U : Space B I) (V : Space B J) (W : Space B K)
    (k : K) (j : J) (i : I) :
    entry V W k j * entry U V j i = entry U W k i := by
  ext b; simp

/-! ## 2. Endomorphic: `V ⊸ V` -/

/-- Diagonal entries of an endomorphism are dimensionless, so **trace is
dimensionless** without a side condition. -/
@[simp] theorem entry_diag (V : Space B I) (i : I) : entry V V i i = 1 := by
  ext b; simp

/-- Each permutation term of a determinant is dimensionless, because `σ` is a
bijection and so the numerator and denominator products agree. Hence
**determinant is dimensionless** for any endomorphism. -/
theorem entry_perm_prod [Fintype I] (V : Space B I) (σ : Equiv.Perm I) :
    ∏ i, entry V V (σ i) i = 1 := by
  simp only [entry_def, Finset.prod_div_distrib]
  rw [Equiv.prod_comp σ V]
  simp

/-- The identity map is dimensionless on the diagonal, and its off-diagonal
entries are `0`, which inhabits *every* unit.

That zero is unit-polymorphic is not a convenience here but a structural
requirement: without it neither the identity matrix nor the `n = 0` term of
`exp` would be well-typed. It is the parametricity fact doing load-bearing work. -/
theorem entry_id_diag (V : Space B I) (i : I) : entry V V i i = 1 := entry_diag V i

/-! ## 3. Squarable: `V ⊸ V ⊗ d` -/

/-- **Squaring.** `A ∘ A` does *not* typecheck for `A : V ⊸ V ⊗ d`: the inner
codomain is `V ⊗ d` and the outer domain is `V`. What typechecks is
`(A ⊗ d) ∘ A : V ⊸ V ⊗ d²`, and this is the identity that makes it work.

The requirement it exposes (that `⊗` be functorial on spaces) is recorded as
`entry_scale_scale` below. -/
theorem entry_square (V : Space B I) (d : Uom B) (k j i : I) :
    entry (V ⊗ d) (V ⊗ (d * d)) k j * entry V (V ⊗ d) j i
      = entry V (V ⊗ (d * d)) k i := by
  ext b; simp

/-- **Functoriality of `⊗`.** Scaling domain and codomain by the same unit
leaves every entry unchanged, so `(V ⊗ d) ⊸ (W ⊗ d) ≅ V ⊸ W`.

Squarability depends on this, and it was not stated anywhere in the design until
the paper test surfaced it. -/
@[simp] theorem entry_scale_scale (V : Space B I) (W : Space B J) (d : Uom B) (j : J) (i : I) :
    entry (V ⊗ d) (W ⊗ d) j i = entry V W j i := by
  ext b; simp

/-- **Eigenvalues.** For `A : V ⊸ V ⊗ d`, the equation `A v = λ v` forces `λ` to
carry exactly `d`: the unit by which the map fails to be an endomorphism.

"Only squarable matrices have eigenstructure" becomes: a map has eigenvalues
exactly when it is an endomorphism up to a scalar unit, and that scalar *is* the
unit of the eigenvalues. Read off the type; nothing declared. -/
theorem eigenvalue_uom (V : Space B I) (d : Uom B) (i : I) : (V ⊗ d) i / V i = d := by
  ext b; simp

/-! ## 4. Dimensionally symmetric: `V ⊸ dual V` -/

/-- Entries of a map into the dual are **symmetric in their two indices**:
Hart's "symmetric about the main diagonal", derived. -/
theorem entry_dual_symm (V : Space B I) (j i : I) :
    entry V V.dual j i = ((V j) * (V i))⁻¹ := by
  ext b; simp; ring

/-- A weighted norm `x† M x` with `M : V ⊸ dual V` is dimensionless. -/
theorem weighted_norm_dimensionless (V : Space B I) (j i : I) :
    V j * entry V V.dual j i * V i = 1 := by
  ext b; simp; ring

/-- **Cholesky.** If `M : V ⊸ dual V` factors as `Rᵀ ∘ R` with `R : V ⊸ Y`, then
composability forces `Y = dual Y`, and torsion-freeness of the unit group forces
`Y` to be the *dimensionless* space.

So the Cholesky factor lands in `triv`: it is the whitening transform, and the
type derives that rather than the programmer asserting it. -/
theorem cholesky_factor_dimensionless {Y : Space B I} (h : Y = Y.dual) :
    Y = Space.triv B I := by
  funext i
  exact Uom.eq_inv_iff_one.mp (congrFun h i)

/-! ## 5. Uniform: `triv ⊗ u` -/

/-- **SVD.** Every entry of a map between uniform spaces carries the *same*
unit `w / u`.

That is exactly what SVD needs and what it needs it for: singular values are
sorted and truncated, which is meaningful only when they are comparable, which
requires them to share a unit. Because a uniform space is *equal* to `triv ⊗ u`
(see `Space.uniform_iff_scale_triv`, which needs structurality), this is an
ordinary signature and a non-uniform argument is a **type error**, not a failed
side condition. -/
theorem svd_entry_const (u w : Uom B) (j : J) (i : I) :
    entry (Space.triv B I ⊗ u) (Space.triv B J ⊗ w) j i = w / u := by
  ext b; simp

/-! ## 6. Beyond Hart: the pseudo-inverse needs a metric

Hart lists "left uniform" as a separate precondition for the Moore–Penrose
pseudo-inverse. It is not separate. -/

/-- `Aᵀ ∘ A` for `A : V ⊸ W` requires the codomain of `A` to be the domain of
`Aᵀ`, i.e. `W = dual W`, which happens only when `W` is dimensionless.

In general the composition needs a **metric** `g : W ⊸ dual W`, giving the
normal-equations map `Aᵀ ∘ g ∘ A : V ⊸ dual V`. -/
theorem transpose_comp_direct_iff (W : Space B J) :
    W = W.dual ↔ W = Space.triv B J := by
  constructor
  · exact cholesky_factor_dimensionless
  · rintro rfl; funext j; simp

/-- A **uniform** space carries a canonical metric, with constant entry `u⁻²`.

This is where Hart's "left uniform" condition comes from: it is the case in
which the metric the pseudo-inverse needs exists canonically. For a non-uniform
space no canonical metric exists and one must be supplied, which is exactly
right, since least squares on components of differing units *is* weighted least
squares, and the weighting is a modeling choice rather than a default. -/
theorem uniform_canonical_metric (u : Uom B) (j i : J) :
    entry (Space.triv B J ⊗ u) (Space.triv B J ⊗ u).dual j i = (u * u)⁻¹ := by
  ext b; simp; ring

end LambdaS

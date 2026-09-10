/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Space

/-!
# Unit identities for linear maps between dimensioned spaces

George Hart's *Multidimensional Analysis* (1995) is the standard reference on
dimensioned matrices, and this file follows it. Its central observation is that
an array of dimensioned entries is only well-behaved when the array of **entry
units** is multiplicatively separable: entry `(j,i)` must carry `aⱼ · bᵢ`, so
that two vectors of units determine every entry. Hart calls this rank one, and
so do we; it is a statement about the entry units and says nothing about the
numerical rank of the matrix. From there Hart derives a taxonomy of five
classes, each licensing a different set of operations:

| Hart's class        | operations licensed                    |
|---------------------|----------------------------------------|
| multipliable        | compose, transpose, solve              |
| endomorphic         | powers, `exp`, `det`, `trace`          |
| squarable           | eigendecomposition                     |
| dimensionally symm. | Cholesky, weighted norms               |
| uniform             | singular value decomposition, pseudo-inverse |

Hart needed the rank-one condition because he worked with raw arrays.

This module proves identities of entry-unit assignments for Hart's classes.
A linear map `V ⊸ W` has entry `(j,i)` at `δ_W(j) / δ_V(i)`, which is rank one
by construction. These identities determine the compatible unit shapes.
Numerical decomposition algorithms require additional definitions, hypotheses,
and correctness proofs; the identities below do not implement them.
-/

/-!
## Dimensioned Linear Algebra

In this section we present the unit algebra the artifact proves for the
Vec and Lin types of “The Calculus” (`Typing.lean`),
following Hart [1995], and the typing rule that carries it into the
calculus. Hart observed that a matrix of dimensioned entries cannot
carry arbitrary units: for (Ax)_j = ∑_i A_ji x_i to be dimensionally
legal when x_i carries u_i and the result component carries w_j, entry
(j,i) must carry w_j/u_i, so the array of entry units has rank one. From
this condition he derived a taxonomy of dimensioned matrices; five of its
classes
(multipliable, endomorphic, squarable, dimensionally symmetric, uniform)
each license different operations. Hart worked with raw arrays, so rank
one is a precondition his reader must verify. The artifact makes it the
definition, and the calculus makes it a typing invariant. At the types,
Lin u⃗ w⃗ carries its two
spaces, and the unit of the (j,i) entry is
defined to be w_j/u_i (`entry`). At the terms, the introduction
rule T-MCons of Figure 2 of the paper (the constructors of `HasTy`) accepts a row only at the
space w/u⃗, so no term constructs a matrix outside Hart's form;
the artifact checks one-row maps (`toTime` accepted, the same
map with a mistyped row rejected at build time). The operations the taxonomy governs
(trace, determinant, factorization) belong to a numerical library above
the calculus; what the calculus contributes is that every matrix reaching
them, written as a literal or received as an argument, is in Hart's form.

**Theorem (Rank-one units; `entry_rank_one`).** The unit of entry (j,i) of a map of type Lin u⃗ w⃗
factors as w_j · u_i⁻¹. There is no hypothesis: every well-typed
map is in Hart's rank-one form.

The classes correspond to unit shapes, and the following identities explain
their compatibility conditions. For composition, the summand
A_kj B_ji carries (w_k/v_j)(v_j/u_i) = w_k/u_i, independent of the
summation index and equal to the composite's entry unit
(`entry_comp`); “multipliable” is not a condition to check but the
only composition writable. In an endomorphism type
Lin u⃗ u⃗, every diagonal entry is dimensionless
(`entry_id_diag`) and every permutation product
∏_i A_(σ(i) i) is dimensionless (`entry_perm_prod`), so
trace and determinant have unit 1. This statement concerns their units, not
an implementation of either operation. For example, on the artifact's
state space u⃗ = [m, kg·m/s]
of position and momentum, an endomorphism has entry units
with rows (1, s/kg) and (kg/s, 1), and both permutation
products, 1 · 1 and (s/kg)(kg/s),
equal the dimensionless 1: the determinant is a number.

Hart's “squarable” matrices are the types
Lin u⃗ (u⃗· w), where u⃗· w scales
every component unit by w: endomorphisms up to a scalar unit. In the
eigenvalue equation Av = λ v the two sides carry u_i · w and
λ · u_i, so every eigenvalue carries w; the artifact records
the unit identity this reading rests on, (u_i · w)/u_i = w uniformly
in the component (`eigenvalue_uom`): a continuous-time dynamics matrix in
ẋ = Ax has type Lin u⃗ (u⃗·s⁻¹),
so eigenvalues, when they exist, would carry frequency units. This identity
does not prove eigenvalue existence or provide an eigenvalue algorithm.

The fourth class is maps into the *dual*, the space that pairs with
Vec u⃗ to give plain numbers. Write u⃗⁻¹ for the
space with componentwise reciprocal units; its components carry reciprocal
units exactly so that the pairing xᵀ y is dimensionless. A map M : Lin u⃗ u⃗⁻¹ has entry unit (u_j u_i)⁻¹,
symmetric in its indices (`entry_dual_symm`), and the weighted norm
xᵀ M x is dimensionless, since
u_j · (u_j u_i)⁻¹ · u_i = 1
(`weighted_norm_dimensionless`). If such an M factors as
Rᵀ ∘ R with R : Lin u⃗ y⃗, composability
forces y⃗ = y⃗⁻¹. The unit group is torsion-free, so y_i² = 1 forces
y_i = 1: a self-dual space has unit 1 in every component
(`cholesky_factor_dimensionless`). Torsion-freeness suffices; this argument also
holds with integer exponents. Such a Cholesky factor would therefore map
dimensioned data into dimensionless coordinates, the unit shape needed by a
whitening transform.

The fifth class is maps between *uniform* spaces, in
which every component carries one unit. A uniform space is equal, not merely
isomorphic, to the dimensionless space scaled by its unit
(`Space.uniform_iff_scale_triv`), and every entry of a map between
uniform spaces carries the same unit w/u (`svd_entry_const`).
The singular value decomposition factors a matrix through a diagonal of
nonnegative scale factors; sorting and truncating those factors requires
that they share a unit. These identities identify the applicable unit
shapes; they do not constitute a typed SVD implementation. The concrete
Jacobi kernel in `Examples` is accepted on its uniform space and rejected
under the non-uniform context `ΓN`, as executable checker guards record.

Hart lists “left uniform” as a separate requirement for the Moore–Penrose
pseudo-inverse (the least-squares inverse of a rectangular matrix); it is
not. Forming Aᵀ ∘ A, for
A : Lin u⃗ w⃗, asks the codomain space to be its own
dual, and a self-dual space is dimensionless
(`transpose_comp_direct_iff`). In general the normal
equations, the equations AᵀA x = Aᵀb that least squares
solves, need a metric g : Lin w⃗ w⃗⁻¹: an inner
product on the codomain, which is to say a choice of weights. A
uniform space determines the *entry unit* such a metric must have, constantly
u⁻² (`uniform_canonical_metric`): residuals all measured in meters admit a
metric with entries at m⁻², under which the weighted norm of a residual
vector is a plain number. That is an identity of unit assignments. It does not
construct the numerical matrix, nor prove it positive definite, nor single one
out; choosing the numbers is additional structure the caller supplies. A non-uniform space carries no canonical
metric, and
rightly so: least squares over components of differing units *is*
weighted least squares, and the weighting is a modeling choice.

Note that the theorem “Rank-one units” (`entry_rank_one`) is also a compilation
observation: the two spaces determine every entry unit, so a run-time array
of bare magnitudes loses nothing, and the compiled evaluator hands vectors
and matrices to BLAS as unboxed arrays. The formal license for the flat
representation is the erasure theorem of “Adequacy and Erasure” (`Erasure.lean`), whose
run-time matrix values carry magnitudes and a space tag only; the rank-one
structure is why the tag suffices. Type soundness covers the literals:
evaluating a well-typed matrix literal yields a matrix value at the
declared spaces (`lin_soundness_total`).
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

This identifies the unit eigenvalues would carry. It proves neither their
existence nor the correctness of an eigenvalue algorithm. -/
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

/-- On a **uniform** space, a metric has constant entry unit `u⁻²`.

The statement is about entry units only: it fixes the unit every entry of such
a metric carries, and says nothing about which numbers fill it, whether they
are positive definite, or whether one choice is canonical. This is where
Hart's "left uniform" condition applies: all metric entries share one unit.
The space determines metric entry units in the non-uniform case too, but those
units differ across components. Numerical weights must be supplied in either
case; the unit assignment alone chooses no metric. -/
theorem uniform_canonical_metric (u : Uom B) (j i : J) :
    entry (Space.triv B J ⊗ u) (Space.triv B J ⊗ u).dual j i = (u * u)⁻¹ := by
  ext b; simp; ring

end LambdaS

/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
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

/-!
## From the paper's long form: Dimensioned Linear Algebra

The paper's tag `long-form` carries this section in full; preserved here,
lightly de-TeXed, so the documentation develops what the paper now
summarizes.

 sectionDimensioned Linear Algebra]


In this section we present the unit algebra the artifact proves for the
Vec] and Lin] types of Section [ref: sec:calculus],
following [cite: hart1995], and the typing rule that carries it into the
calculus. Hart observed that a matrix of dimensioned entries cannot
carry arbitrary units: for (Ax)_j =  sum_i A_ji] x_i to be dimensionally
legal when x_i carries u_i and the result component carries w_j, entry
(j,i) must carry w_j/u_i, so the array of entry units has rank one. From
this condition he derived a taxonomy of dimensioned matrices; five of its
classes
(multipliable, endomorphic, squarable, dimensionally symmetric, uniform)
each license different operations. Hart worked with raw arrays, so rank
one is a precondition his reader must verify. The artifact makes it the
definition, and the calculus makes it a typing invariant. At the types,
Lin]  vecu]  vecw] carries its two
spaces, and the unit of the (j,i) entry is
defined to be w_j/u_i (`entry]). At the terms, the introduction
rule  ftruleT-MCons] of Figure [ref: fig:typing] accepts a row only at the
space w/ vecu], so no term constructs a matrix outside Hart's form;
the artifact checks one-row maps (`toTime] accepted, the same
map with a mistyped row rejected at build time). The operations the taxonomy governs
(trace, determinant, factorization) belong to a numerical library above
the calculus; what the calculus contributes is that every matrix reaching
them, written as a literal or received as an argument, is in Hart's form.



The unit of entry (j,i) of a map of type Lin]  vecu]  vecw]
factors as w_j  cdot u_i^-1]. There is no hypothesis: every well-typed
map is in Hart's rank-one form.


Each class is then a type, and the operations it licenses are the operations
well-typed at that type. Composition is the first class entire: the summand
A_kj] B_ji] carries (w_k/v_j)(v_j/u_i) = w_k/u_i, independent of the
summation index and equal to the composite's entry unit
(`entry_comp]); ``multipliable'' is not a condition to check but the
only composition writable. In an endomorphism type
Lin]  vecu]  vecu], every diagonal entry is dimensionless
(`entry_id_diag]) and every permutation product
 prod_i A_ sigma(i) i] is dimensionless (`entry_perm_prod]), so
trace and determinant need no side condition. For example, on the artifact's
state space  vecu] = [m],  kg] cdotm]/s]]
of position and momentum, an endomorphism has entry units
 left(1 & s]/kg]  
kg]/s] & 1 right), and both permutation
products, 1  cdot 1 and (s]/kg])(kg]/s]),
equal the dimensionless 1: the determinant is a number.

Hart's ``squarable'' matrices are the types
Lin]  vecu] ( vecu] cdot w), where  vecu] cdot w scales
every component unit by w: endomorphisms up to a scalar unit. In the
eigenvalue equation Av =  lambda v the two sides carry u_i  cdot w and
 lambda  cdot u_i, so every eigenvalue carries w; the artifact records
the unit identity this reading rests on, (u_i  cdot w)/u_i = w uniformly
in the component (`eigenvalue_uom]): a continuous-time dynamics matrix in
 dotx] = Ax has type Lin]  vecu] ( vecu] cdots]^-1]),
and the modes of a linear system are frequencies, by typing alone.

The fourth class is maps into the **dual], the space that pairs with
Vec]  vecu] to give plain numbers. Write  vecu]^-1] for the
space with componentwise reciprocal units; its components carry reciprocal
units exactly so that the pairing x^ top] y is dimensionless. A map M :
Lin]  vecu]  vecu]^-1] has entry unit (u_j u_i)^-1],
symmetric in its indices (`entry_dual_symm]), and the weighted norm
x^ top] M x is dimensionless, since
u_j  cdot (u_j u_i)^-1]  cdot u_i = 1
(`weighted_norm_dimensionless]). If such an M factors as
R^ top]  circ R with R : Lin]  vecu]  vecy], composability
forces  vecy] =  vecy]^-1], and a self-dual space is
dimensionless (`cholesky_factor_dimensionless]: the unit group is
a ℚ-vector space,
Section [ref: sec:units], hence torsion-free, so y_i^2 = 1 forces
y_i = 1). The Cholesky factor is therefore a whitening transform, a map
carrying
dimensioned data into dimensionless coordinates, derived rather
than asserted.

The fifth class is maps between **uniform] spaces, in
which every component carries one unit. A uniform space is equal, not merely
isomorphic, to the dimensionless space scaled by its unit
(`Space.uniform_iff_scale_triv]), and every entry of a map between
uniform spaces carries the same unit w/u (`svd_entry_const]).
The singular value decomposition factors a matrix through a diagonal of
nonnegative scale factors; sorting and truncating those factors requires
that they share a unit, so a
non-uniform argument to SVD is a type error, not a failed side condition.

Hart lists ``left uniform'' as a separate requirement for the Moore--Penrose
pseudo-inverse (the least-squares inverse of a rectangular matrix); it is
not. Forming A^ top]  circ A, for
A : Lin]  vecu]  vecw], asks the codomain space to be its own
dual, and a self-dual space is dimensionless
(`transpose_comp_direct_iff]). In general the normal
equations, the equations A^ top] !A x = A^ top]b that least squares
solves, need a metric g : Lin]  vecw]  vecw]^-1]: an inner
product on the codomain, which is to say a choice of weights. A
uniform space carries a canonical one, with constant entry u^-2]
(`uniform_canonical_metric]): residuals all measured in meters get
the metric with entries m]^-2], and the weighted norm of a
residual vector is a plain number. A non-uniform space carries no canonical
metric, and
rightly so: least squares over components of differing units **is]
weighted least squares, and the weighting is a modeling choice.

Note that Theorem [ref: thm:hart-rank-one] is also a compilation
observation: the two spaces determine every entry unit, so a run-time array
of bare magnitudes loses nothing, and the compiled evaluator hands vectors
and matrices to BLAS as unboxed arrays. The formal license for the flat
representation is the erasure theorem of Section [ref: sec:erasure], whose
run-time matrix values carry magnitudes and a space tag only; the rank-one
structure is why the tag suffices. Type soundness covers the literals:
evaluating a well-typed matrix literal yields a matrix value at the
declared spaces (`lin_soundness_total]).

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

import LambdaS.Scaling
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Conversion, and why paths cannot disagree

Λs has a conversion operator (`convert`, a core term constructor), and
conversion is the right place to be
careful: with units nameable and definable in terms of combinations of other
units, a system that defines conversion by *walking a declared structure* can
offer more than one route between two units, with no guarantee the routes
agree.

This file answers that. Conversion is not a path at all; it is a **ratio of
valuations**, and the object that supplies the valuations already exists:
`Scaling`. A scaling assigns a positive magnitude to every base unit and extends
to a homomorphism, which is exactly what "reduce every unit to a canonical
value" means in the specification of Fortress, a language whose standard
library carried units of measure.

Once conversion is a ratio, path independence is not a condition to check but a
theorem: `convChain_eq` says any chain of intermediate conversions collapses to
the direct one, because the intermediate factors telescope. The multiple-paths
problem does not arise, and there is nothing an implementation could get wrong.

## The contrast worth recording

There is a real alternative, and it is the one a unit-conversion programming
assignment (Rice's Comp 311, Fall 2016)
adopts: restrict compound units to *at most one named unit per dimension*, so
that lining up two compounds has a unique pairing. That works, and it kills the
ambiguity, but it buys uniqueness by shrinking the algebra. Under it
`meter / foot` is illegal, because both are units of Length; yet that is exactly
a conversion factor, dimensionless, and worth naming.

The exponent-vector representation needs no such restriction. `meter` and `foot`
are distinct generators that happen to share a dimension, `meter * foot` is a
perfectly good vector, and no pairing question ever arises because a vector's
components are already indexed.
-/

namespace LambdaS

variable {B D : Type} [Fintype B] {k : ℕ}

/-- The **conversion factor** from `u` to `v`, relative to a valuation.

A valuation is a `Scaling`: it fixes what each base unit is worth, and extends
to a homomorphism on all units. The factor is then just the ratio. -/
noncomputable def conv (ψ : Scaling B k) (u v : UExp B k) : ℝ :=
  ψ.scale u / ψ.scale v

@[simp] theorem conv_pos (ψ : Scaling B k) (u v : UExp B k) : 0 < conv ψ u v :=
  div_pos (ψ.scale_pos u) (ψ.scale_pos v)

theorem conv_ne_zero (ψ : Scaling B k) (u v : UExp B k) : conv ψ u v ≠ 0 :=
  ne_of_gt (conv_pos ψ u v)

/-- Converting a unit to itself does nothing. -/
@[simp] theorem conv_self (ψ : Scaling B k) (u : UExp B k) : conv ψ u u = 1 :=
  div_self (ne_of_gt (ψ.scale_pos u))

/-- The conversion factor is the scale of the *ratio*, so it is itself the
valuation of a dimensionless unit, which is what makes conversion factors
nameable as units. -/
theorem conv_eq_scale_div (ψ : Scaling B k) (u v : UExp B k) :
    conv ψ u v = ψ.scale (Term.div u v) := by
  rw [conv, Scaling.scale_div]

/-- **Transitivity.** Converting through an intermediate unit gives the same
factor as converting directly. -/
theorem conv_trans (ψ : Scaling B k) (u v w : UExp B k) :
    conv ψ u v * conv ψ v w = conv ψ u w := by
  have hv := ne_of_gt (ψ.scale_pos v)
  have hw := ne_of_gt (ψ.scale_pos w)
  simp only [conv]
  field_simp

/-- Converting back undoes converting forward. -/
theorem conv_symm (ψ : Scaling B k) (u v : UExp B k) :
    conv ψ u v * conv ψ v u = 1 := by
  rw [conv_trans, conv_self]

/-- The factor along a chain of intermediate units. -/
noncomputable def convChain (ψ : Scaling B k) :
    UExp B k → List (UExp B k) → UExp B k → ℝ
  | u, [], v => conv ψ u v
  | u, w :: ws, v => conv ψ u w * convChain ψ w ws v

/-- **Path independence.** *Any* chain of intermediate conversions from `u` to
`v` gives exactly the direct factor.

This is the theorem the multiple-paths problem asks for. It holds because the
factors are ratios of a single valuation, so intermediates telescope, not
because anyone checked the declarations for consistency. There is no route by
which two paths could disagree. -/
theorem convChain_eq (ψ : Scaling B k) :
    ∀ (u : UExp B k) (ws : List (UExp B k)) (v : UExp B k),
      convChain ψ u ws v = conv ψ u v
  | _, [], _ => rfl
  | u, w :: ws, v => by
      rw [convChain, convChain_eq ψ w ws v, conv_trans]

/-- **Conversion preserves the quantity.** A measurement `⟨m, u⟩` converted into
unit `v` denotes the same physical quantity: its interpretation under the
valuation is unchanged.

This is the correctness statement for an `in` operator, and it is what the
Comp 311 assignment needs of its `def in(v: PhysicalUnit)` and never states. -/
theorem conv_preserves (ψ : Scaling B k) (u v : UExp B k) (m : ℝ) :
    ψ.scale v * (m * conv ψ u v) = ψ.scale u * m := by
  have hv := ne_of_gt (ψ.scale_pos v)
  simp only [conv]
  field_simp

/-- Composing two scalings: in log space, pointwise addition. -/
def Scaling.comp (V ψ : Scaling B k) : Scaling B k :=
  ⟨fun b => V.base b + ψ.base b, fun i => V.vars i + ψ.vars i⟩

/-- Composing scalings commutes with extending them: a new variable's factors
add, like everything else. -/
@[simp] theorem Scaling.comp_cons (V ψ : Scaling B k) (r s : ℝ) :
    (V.cons r).comp (ψ.cons s) = (V.comp ψ).cons (r + s) := by
  simp only [comp, cons, Scaling.mk.injEq, true_and]
  exact funext fun i => Fin.cases rfl (fun _ => rfl) i

theorem Scaling.logScale_comp (V ψ : Scaling B k) (u : UExp B k) :
    (V.comp ψ).logScale u = V.logScale u + ψ.logScale u := by
  have h1 : ∀ b : B, (u.base b : ℝ) * (V.base b + ψ.base b)
      = (u.base b : ℝ) * V.base b + (u.base b : ℝ) * ψ.base b := fun _ => by ring
  have h2 : ∀ i : Fin k, (u.vars i : ℝ) * (V.vars i + ψ.vars i)
      = (u.vars i : ℝ) * V.vars i + (u.vars i : ℝ) * ψ.vars i := fun _ => by ring
  simp only [logScale, comp, h1, h2, Finset.sum_add_distrib]
  ring

theorem Scaling.scale_comp (V ψ : Scaling B k) (u : UExp B k) :
    (V.comp ψ).scale u = V.scale u * ψ.scale u := by
  simp [scale, logScale_comp, Real.exp_add]

/-- Rescaling the valuation multiplies a conversion factor by the ratio of the
two units' scale factors. The engine of every coherence result: the factor is
*almost* invariant, off by exactly the amount coherence sets to one. -/
theorem conv_comp (V ψ : Scaling B k) (u v : UExp B k) :
    conv (V.comp ψ) u v = conv V u v * (ψ.scale u / ψ.scale v) := by
  have h1 := ne_of_gt (V.scale_pos v)
  have h2 := ne_of_gt (ψ.scale_pos v)
  simp only [conv, Scaling.scale_comp]
  field_simp

/-! ## Dimensions

`dimOf` lives in `LambdaS.Syntax`, since the typing rule for `convert` needs it.
These are the homomorphism laws the design requires of it: dimension is a group
homomorphism from units to dimensions, which is what makes "same dimension" an
equivalence compatible with the algebra. -/

section Dimensions

variable [UnitSys B D] {j : ℕ} (Δ : DCtx D j k)

theorem dimOf_mul (u v : UExp B k) :
    dimOf (D := D) Δ (Term.mul u v) = Term.mul (dimOf Δ u) (dimOf Δ v) := by
  refine Term.ext' (funext fun d => ?_) (funext fun w => ?_) <;>
    (simp only [dimOf, Term.mul_base, Term.mul_vars, add_mul, Finset.sum_add_distrib]
     try ring)

@[simp] theorem dimOf_one : dimOf (D := D) Δ (1 : UExp B k) = 1 := by
  refine Term.ext' (funext fun d => ?_) (funext fun w => ?_) <;> simp [dimOf]

theorem dimOf_div (u v : UExp B k) :
    dimOf (D := D) Δ (Term.div u v) = Term.div (dimOf Δ u) (dimOf Δ v) := by
  refine Term.ext' (funext fun d => ?_) (funext fun w => ?_) <;>
    (simp only [dimOf, Term.div_base, Term.div_vars, sub_mul, Finset.sum_sub_distrib]
     try ring)

theorem dimOf_rpow (u : UExp B k) (q : ℚ) :
    dimOf (D := D) Δ (Term.rpow u q) = Term.rpow (dimOf Δ u) q := by
  refine Term.ext' (funext fun d => ?_) (funext fun w => ?_)
  · simp only [dimOf, Term.rpow_base, Term.rpow_vars, mul_add, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => by ring)
      (Finset.sum_congr rfl fun _ _ => by ring)
  · simp only [dimOf, Term.rpow_base, Term.rpow_vars, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Interchangeable units have a **dimensionless ratio**, which is why their
conversion factor is a pure number and can itself be named as a unit.

Under the "one named unit per dimension" restriction this ratio is not even
expressible, since `u` and `v` would be two units of one dimension in a single
compound. -/
theorem dimOf_ratio_one {u v : UExp B k} (h : SameDim Δ u v) :
    dimOf (D := D) Δ (Term.div u v) = 1 := by
  rw [dimOf_div, h]
  refine Term.ext' (funext fun d => ?_) (funext fun w => ?_) <;> simp

end Dimensions

/-! ## A linear extension lemma

The classical fact both this file and `LambdaS.Declare` consume: a value
assignment on a finite family extends to a linear map exactly when it respects
the family's linear dependencies. -/

/-- **Prescribed values extend to a linear map when dependencies are
respected.** Given finite families `r` in `M` and `v` in `V` over a field `K`,
a single linear map sends each `r i` to `v i` exactly when every `K`-linear
dependency among the `r i` also annihilates the corresponding combination of
the `v i`. This is the extension step behind `Scaling.Coherent.factors` in this
file and `dependency_sufficient` in `LambdaS.Declare`: the value assignment
factors through the span of the family and then extends to the whole space. -/
theorem exists_linearMap_of_dependencies {K M V : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → M) (v : ι → V)
    (h : ∀ c : ι → K, ∑ i, c i • r i = 0 → ∑ i, c i • v i = 0) :
    ∃ φ : M →ₗ[K] V, ∀ i, φ (r i) = v i := by
  -- The hypothesis says the value map kills the kernel of the combination map.
  have hker : LinearMap.ker (Fintype.linearCombination K r)
      ≤ LinearMap.ker (Fintype.linearCombination K v) := by
    intro c hc
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hc ⊢
    exact h c hc
  -- Factor the value map through the range of the combination map, then
  -- extend from that subspace to all of `M`.
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend
    (((LinearMap.ker (Fintype.linearCombination K r)).liftQ
        (Fintype.linearCombination K v) hker).comp
      (Fintype.linearCombination K r).quotKerEquivRange.symm.toLinearMap)
  refine ⟨φ, fun i => ?_⟩
  have hri : Fintype.linearCombination K r (Pi.single i 1) = r i := by
    rw [Fintype.linearCombination_apply_single, one_smul]
  have hmem : r i ∈ LinearMap.range (Fintype.linearCombination K r) :=
    ⟨Pi.single i 1, hri⟩
  have h1 := LinearMap.congr_fun hφ ⟨r i, hmem⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    LinearEquiv.coe_toLinearMap] at h1
  have h3 : (⟨r i, hmem⟩ : LinearMap.range (Fintype.linearCombination K r))
      = ⟨Fintype.linearCombination K r (Pi.single i 1),
          LinearMap.mem_range_self _ _⟩ :=
    Subtype.ext hri.symm
  rw [h1, h3, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
    Submodule.liftQ_apply, Fintype.linearCombination_apply_single, one_smul]

/-! ## Coherence: which scalings are physically meaningful

Parametricity quantifies over **all** scalings, including ones that scale
`metre` and `foot` independently. That is physical nonsense (rescale the metre
and the foot must follow), but it is exactly the freedom that lets Λs treat
same-dimension units as independent generators, and so avoid restricting
compound units to one named unit per dimension.

The physically meaningful scalings are those that **factor through dimension**,
and they are precisely the ones that leave conversion factors alone. This is the
bridge between the two roles a `Scaling` plays: fixed declared data on the one
hand, quantified-over transformation on the other.

It is also the exact price of `convert`. A parametric term without `convert` is
scale-invariant for *every* scaling: that is `fundamental_free`, and it is what
the Pi theorem consumes. A term *with* `convert` is scale-invariant for the
coherent ones, and `conv_invariant_of_coherent` is the lemma that discharges its
case. Nothing else in Λs can observe a unit, so nothing else pays. -/

section Coherence

variable [UnitSys B D] {j : ℕ}

/-- A scaling is **coherent** for `Δ` when interchangeable units scale alike;
that is, when it factors through `dim`. -/
def Scaling.Coherent (Δ : DCtx D j k) (ψ : Scaling B k) : Prop :=
  ∀ u v : UExp B k, SameDim Δ u v → ψ.scale u = ψ.scale v

/-- **Conversion factors are invariant under coherent rescaling.**

Change the unit system by any scaling that respects dimensions and every
conversion factor is unchanged: `1 m = 3.28 ft` whatever reference you measure
against. -/
theorem conv_invariant_of_coherent (V : Scaling B k) {Δ : DCtx D j k} {ψ : Scaling B k}
    (hψ : ψ.Coherent Δ) {u v : UExp B k} (h : SameDim Δ u v) :
    conv (V.comp ψ) u v = conv V u v := by
  simp only [conv, Scaling.scale_comp, hψ u v h]
  have hv := ne_of_gt (V.scale_pos v)
  have hp := ne_of_gt (ψ.scale_pos v)
  field_simp

/-- ψ **factors through dimension** via the dimension scaling `Φ`.

This is `Coherent` with its witness named, and split into the two facts that
determine it: what each base unit is worth, and what each unit variable is worth.
Coherence says interchangeable units scale alike, which is precisely the
statement that the scaling is pulled back from one on *dimensions*.

Naming the dimension scaling is what makes unit abstraction tractable. Under
`Λu:δ` the factor the bound unit must receive is then not merely constrained to
some coherent value; it is **determined**, namely `Φ δ`. A coherent rescaling is
a rescaling of dimensions, and unit abstraction has no freedom left. -/
structure Scaling.Factors [Fintype D] (ψ : Scaling B k) (Δ : DCtx D j k)
    (Φ : Scaling D j) : Prop where
  /-- A base unit scales by its dimension's factor. -/
  base : ∀ b : B, ψ.base b = ∑ d, ((UnitSys.dim (D := D) b).base d : ℝ) * Φ.base d
  /-- A unit variable scales by its declared dimension's factor. -/
  vars : ∀ i, ψ.vars i = Φ.logScale (Δ i)

/-- **Factoring is pointwise, so it extends to every unit expression.** The
content is that `logScale` and `dimOf` are both linear, so this is a change in
summation order rather than an induction. -/
theorem Scaling.Factors.logScale [Fintype D] {ψ : Scaling B k} {Δ : DCtx D j k}
    {Φ : Scaling D j} (h : ψ.Factors Δ Φ) (u : UExp B k) :
    ψ.logScale u = Φ.logScale (dimOf (D := D) Δ u) := by
  have hb : ∑ b, (u.base b : ℝ) * ψ.base b
      = ∑ d, (∑ b, (u.base b : ℝ) * ((UnitSys.dim (D := D) b).base d : ℝ)) * Φ.base d := by
    simp only [h.base, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hv : ∑ i, (u.vars i : ℝ) * ψ.vars i
      = (∑ d, (∑ i, (u.vars i : ℝ) * ((Δ i).base d : ℝ)) * Φ.base d)
        + ∑ v, (∑ i, (u.vars i : ℝ) * ((Δ i).vars v : ℝ)) * Φ.vars v := by
    simp only [h.vars, Scaling.logScale, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
    congr 1 <;> exact Finset.sum_comm
  simp only [Scaling.logScale, dimOf, hb, hv, Rat.cast_add, Rat.cast_sum, Rat.cast_mul,
    add_mul, Finset.sum_add_distrib]
  ring

/-- Factoring through dimension is coherence. -/
theorem Scaling.Factors.coherent [Fintype D] {ψ : Scaling B k} {Δ : DCtx D j k}
    {Φ : Scaling D j} (h : ψ.Factors Δ Φ) : ψ.Coherent Δ := by
  intro u v huv
  simp only [Scaling.scale, h.logScale u, h.logScale v]
  rw [show dimOf (D := D) Δ u = dimOf (D := D) Δ v from huv]

/-- **Factoring survives a unit binder**, at the factor the bound dimension
dictates. There is no choice to make, which is the whole point. -/
theorem Scaling.Factors.cons [Fintype D] {ψ : Scaling B k} {Δ : DCtx D j k}
    {Φ : Scaling D j} (h : ψ.Factors Δ Φ) (d : DExp D j) :
    (ψ.cons (Φ.logScale d)).Factors (Δ.cons d) Φ where
  base b := h.base b
  vars i := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Scaling.cons, DCtx.cons]
    · simpa [Scaling.cons, DCtx.cons] using h.vars i

/-- **Factoring survives a dimension binder**, at whatever the new dimension is
worth: dimension abstraction is unconstrained, which is what makes `∀δ. ∀u:δ`
genuinely unbounded. -/
theorem Scaling.Factors.weakenDim [Fintype D] {ψ : Scaling B k} {Δ : DCtx D j k}
    {Φ : Scaling D j} (h : ψ.Factors Δ Φ) (t : ℝ) :
    ψ.Factors Δ.weakenDim (Φ.cons t) where
  base b := by simpa [Scaling.cons] using h.base b
  vars i := by simpa [DCtx.weakenDim] using h.vars i

/-- **Every coherent scaling factors through dimension.** This is the converse
of `Scaling.Factors.coherent`, and together they give the equivalence the
paper's introduction asserts when it defines coherence as inheriting factors
from dimensions.

The proof is ℚ-linear algebra with values in ℝ. Each generator (base unit or
unit variable) has a dimension exponent vector and a log factor. A rational
dependency among the vectors assembles a dimensionless unit expression, which
coherence sends to the scale of `1`, so the corresponding combination of log
factors vanishes. `exists_linearMap_of_dependencies` then extends the
assignment to a ℚ-linear functional on the whole dimension space, and reading
that functional on the standard basis gives the dimension scaling. -/
theorem Scaling.Coherent.factors [Fintype D] {ψ : Scaling B k} {Δ : DCtx D j k}
    (hcoh : ψ.Coherent Δ) : ∃ Φ : Scaling D j, ψ.Factors Δ Φ := by
  classical
  -- Every rational dependency among the generators' dimension vectors kills
  -- the matching combination of log factors.
  have hdep : ∀ c : B ⊕ Fin k → ℚ,
      ∑ x, c x • Sum.elim (fun b => Sum.elim (UnitSys.dim (D := D) b).base (0 : Fin j → ℚ))
        (fun i => Sum.elim (Δ i).base (Δ i).vars) x = (0 : (D ⊕ Fin j) → ℚ) →
      ∑ x, c x • Sum.elim ψ.base ψ.vars x = (0 : ℝ) := by
    intro c hc
    -- The coefficients assemble a unit expression, and the dependency says it
    -- is dimensionless.
    have hdim : dimOf (D := D) Δ
        (⟨fun b => c (Sum.inl b), fun i => c (Sum.inr i)⟩ : UExp B k) = 1 := by
      refine Term.ext' (funext fun d => ?_) (funext fun w => ?_)
      · have hd := congrFun hc (Sum.inl d)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
          Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hd
        simpa [dimOf] using hd
      · have hw := congrFun hc (Sum.inr w)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
          Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hw
        simpa [dimOf] using hw
    -- Coherence gives the dimensionless expression the scale of `1`, so its
    -- log scale is zero.
    have hsame : SameDim Δ
        (⟨fun b => c (Sum.inl b), fun i => c (Sum.inr i)⟩ : UExp B k) (1 : UExp B k) :=
      hdim.trans (dimOf_one (D := D) Δ).symm
    have hscale := hcoh _ _ hsame
    rw [Scaling.scale_one] at hscale
    have hlog : ψ.logScale
        (⟨fun b => c (Sum.inl b), fun i => c (Sum.inr i)⟩ : UExp B k) = 0 :=
      (Real.exp_eq_one_iff _).mp hscale
    calc ∑ x, c x • Sum.elim ψ.base ψ.vars x
        = ψ.logScale (⟨fun b => c (Sum.inl b), fun i => c (Sum.inr i)⟩ : UExp B k) := by
          simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Rat.smul_def,
            Scaling.logScale]
      _ = 0 := hlog
  obtain ⟨φ, hφ⟩ := exists_linearMap_of_dependencies (K := ℚ)
    (Sum.elim (fun b => Sum.elim (UnitSys.dim (D := D) b).base (0 : Fin j → ℚ))
      (fun i => Sum.elim (Δ i).base (Δ i).vars))
    (Sum.elim ψ.base ψ.vars) hdep
  -- Read the functional on the standard basis of the dimension space.
  have hstep : ∀ (x : D ⊕ Fin j) (q : ℚ),
      (q : ℝ) * φ (Pi.single x 1) = φ (Pi.single x q) := by
    intro x q
    rw [← Rat.smul_def, ← map_smul]
    congr 1
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hexpand : ∀ m : (D ⊕ Fin j) → ℚ,
      φ m = (∑ d, (m (Sum.inl d) : ℝ) * φ (Pi.single (Sum.inl d) 1))
        + ∑ w, (m (Sum.inr w) : ℝ) * φ (Pi.single (Sum.inr w) 1) := by
    intro m
    conv_lhs => rw [← Finset.univ_sum_single m]
    rw [map_sum, Fintype.sum_sum_type]
    exact congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun d _ => (hstep _ _).symm)
      (Finset.sum_congr rfl fun w _ => (hstep _ _).symm)
  refine ⟨⟨fun d => φ (Pi.single (Sum.inl d) 1), fun w => φ (Pi.single (Sum.inr w) 1)⟩,
    ?_, ?_⟩
  · intro b
    have h1 := hφ (Sum.inl b)
    simp only [Sum.elim_inl] at h1
    rw [hexpand] at h1
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Rat.cast_zero, zero_mul,
      Finset.sum_const_zero, add_zero] at h1
    exact h1.symm
  · intro i
    have h1 := hφ (Sum.inr i)
    simp only [Sum.elim_inr] at h1
    rw [hexpand] at h1
    simp only [Sum.elim_inl, Sum.elim_inr] at h1
    exact h1.symm

/-- **Coherence is factoring through dimension.** A scaling respects
interchangeability exactly when it is pulled back from some scaling of
dimensions. The paper defines coherence by the right-hand side; this
equivalence shows the two readings agree. -/
theorem Scaling.coherent_iff_factors [Fintype D] {ψ : Scaling B k} {Δ : DCtx D j k} :
    ψ.Coherent Δ ↔ ∃ Φ : Scaling D j, ψ.Factors Δ Φ :=
  ⟨Scaling.Coherent.factors, fun ⟨_, hΦ⟩ => hΦ.coherent⟩

/-- The trivial scaling is coherent, so the coherent theorems are never vacuous. -/
theorem Scaling.coherent_id (Δ : DCtx D j k) : (Scaling.id B k).Coherent Δ := by
  intro u v _
  simp [Scaling.id, scale, logScale]

end Coherence

end LambdaS

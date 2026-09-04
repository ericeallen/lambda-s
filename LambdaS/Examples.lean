/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Typing
import LambdaS.Declare
import LambdaS.Twist
import LambdaS.NonDefinability

/-!
# Λs, running

Every line below **runs the checker** at build time via `#guard`. If any result
were different, this file would not compile.

A note on what that does and does not establish. `#guard` executes the compiled
`infer`, so these are *tests*, not kernel-checked proofs: kernel reduction gets
stuck on the `Rat` instance chain that Mathlib's algebraic hierarchy is built
from, which is a known cost of building on it. The correctness guarantee does
not come from here: it comes from `LambdaS.Typing`, where `check` returns the
derivation (so soundness holds by construction) and `check_eq` is proved in
the kernel, saying nothing well-typed is rejected. These examples show the
verified checker *running*.
-/

namespace LambdaS.Examples

/-- Four base units; note **two** of them measure Length. That is deliberate:
it is the configuration a "one named unit per dimension" restriction forbids,
and the one conversion factors live in. -/
inductive Base | metre | foot | yard | kilogram | second
  deriving DecidableEq

instance : Fintype Base where
  elems := {Base.metre, Base.foot, Base.yard, Base.kilogram, Base.second}
  complete := by intro x; cases x <;> decide

/-- The dimensions those units measure. -/
inductive Dim | length | mass | time
  deriving DecidableEq

instance : Fintype Dim where
  elems := {Dim.length, Dim.mass, Dim.time}
  complete := by intro x; cases x <;> decide

/-- The declared dimension of each base unit. Metre and foot collapse to the
same dimension; nothing else does.

Note that `dim` lands in `DExp Dim 0`, a dimension *expression*, not a single
base dimension. That is what lets a derived unit be declared directly at a
compound dimension. -/
instance : UnitSys Base Dim where
  dim
    | .metre => Term.ofBase .length
    | .foot => Term.ofBase .length
    | .yard => Term.ofBase .length
    | .kilogram => Term.ofBase .mass
    | .second => Term.ofBase .time

/-- The empty dimension context: a closed term has no unit variables in scope. -/
abbrev Δ₀ : DCtx Dim 0 0 := fun i => i.elim0

/-- Terms and types of the running example, at the closed scope. -/
abbrev Term₀ := Tm Base Dim 0 0
abbrev Type₀ := Ty Base Dim 0 0

/-- The type a closed term is assigned. -/
abbrev typeOf (e : Term₀) : Option Type₀ := infer Δ₀ [] e

/-- The type a term is assigned in a non-empty value context. -/
abbrev typeOfIn (Γ : Ctx Base Dim 0 0) (e : Term₀) : Option Type₀ := infer Δ₀ Γ e

/-- A base unit as a unit expression, at any scope. -/
abbrev bu {k} (b : Base) : UExp Base k := Term.ofBase b

abbrev m : UExp Base 0 := bu .metre
abbrev ft : UExp Base 0 := bu .foot
abbrev yd : UExp Base 0 := bu .yard
abbrev kg : UExp Base 0 := bu .kilogram
abbrev sec : UExp Base 0 := bu .second

/- Because unit expressions are exponent vectors, `m·s/m` and `s` are literally
the same object: there is no normalization step, and none to get wrong. -/
#guard (Term.div (Term.mul m sec) m) == sec

/-! ## Scalars -/

/-- `1.3 m`: a literal times a unit constant. -/
def length : Term₀ := .mul (.lit 1.3) (.ucon m)

/-- `5 s`. -/
def duration : Term₀ := .mul (.lit 5) (.ucon sec)

/-- `1.3 m / 5 s`. -/
def velocity : Term₀ := .div length duration

#guard typeOf length == some (.Q m)
#guard typeOf velocity == some (.Q (Term.div m sec))

/- Literals are dimensionless: there is no unitless *type*, only the unit `1`. -/
#guard typeOf (.lit 42 : Term₀) == some (.Q 1)

/-! ## The error that motivates the whole exercise -/

/-- Adding a length to a duration: the Mars Climate Orbiter failure, in one line. -/
def mismatch : Term₀ := .add length duration

#guard (typeOf mismatch).isNone

/- Adding two lengths is fine. -/
#guard typeOf (.add length length) == some (.Q m)

/-! ## Roots, where ℚ exponents pay for themselves

Kennedy's Λu and F# both type `sqrt : float<'u^2> -> float<'u>`, which to apply
at a volume requires solving `2·vec(u) = 3` over ℤ. There is no solution, so
**F# rejects the square root of a volume.** Over ℚ the root is total, and this
lands at `m^(3/2)`. -/

def volume : Term₀ := .mul (.mul (.ucon m) (.ucon m)) (.ucon m)

#guard typeOf (.root 2 volume) == some (.Q (Term.rpow (Term.mul (Term.mul m m) m) (1/2)))

/- And `m^(3/2)` really is a half-integer exponent, not an artifact. -/
#guard (Term.rpow (Term.mul (Term.mul m m) m) (1/2)).base .metre == (3/2 : ℚ)

/- The zeroth root is rejected: the side condition is real. -/
#guard (typeOf (.root 0 volume)).isNone

/-! ## Spaces

A **state space** whose components carry *different* units: position in metres,
momentum in `kg·m/s`. This is the non-uniform case F# cannot express at all,
since it parameterizes a type by a single unit. -/

def State : Sp Base 0 := [m, Term.div (Term.mul kg m) sec]

/- Indexing reads the unit out of the space: the operational content of
"units live on spaces". -/
#guard typeOfIn [.vec State] (.idx (.var 0) 0) == some (.Q m)
#guard typeOfIn [.vec State] (.idx (.var 0) 1) == some (.Q (Term.div (Term.mul kg m) sec))

/- Out-of-range indexing is rejected. -/
#guard (typeOfIn [.vec State] (.idx (.var 0) 2)).isNone

/-! ## Linear maps -/

def W : Sp Base 0 := [sec]

#guard typeOfIn [.lin State W, .vec State] (.mapp (.var 0) (.var 1)) == some (.vec W)

/- Applying a map to a vector over the wrong space fails. -/
#guard (typeOfIn [.lin State W, .vec W] (.mapp (.var 0) (.var 1))).isNone

/- Composition requires the middle spaces to agree. -/
#guard typeOfIn [.lin State W, .lin W State] (.comp (.var 0) (.var 1)) == some (.lin W W)
#guard (typeOfIn [.lin State W, .lin State W] (.comp (.var 0) (.var 1))).isNone

/-! ## Unit polymorphism

The reason Kennedy's calculus exists, now over spaces, with the dimension
bound that lets a polymorphic function still convert.

`∀u. τ` is not primitive. It is `∀δ. ∀u:δ. τ`: a unit variable bounded by a
*dimension* variable. That is what makes it genuinely unbounded, and the guards
below check both halves: that `δ` matches any concrete dimension on
instantiation, and that nothing concrete matches `δ` inside the binder. -/

/-- The bound unit variable, inside one unit binder. -/
abbrev uvar : UExp Base 1 := Term.ofVar 0

/-- The bound dimension variable, inside one dimension binder. -/
abbrev dvar : DExp Dim 1 := Term.ofVar 0

/-- `Λδ. Λu:δ. λ(x : Q u). x * x`: squaring, at *any* unit. -/
def sqr : Term₀ := .dlam (.ulam dvar (.lam (.Q uvar) (.mul (.var 0) (.var 0))))

#guard typeOf sqr
    == some (.allDim (.all dvar (.arrow (.Q uvar) (.Q (Term.mul uvar uvar)))))

/- Using it takes two applications: supply the dimension, then the unit. -/
abbrev sqrAt (d : DExp Dim 0) (μ : UExp Base 0) : Term₀ := .uapp (.dapp sqr d) μ

/- Instantiating at metres gives `Q m → Q m²`. The unit variable really is
substituted, not merely erased. -/
#guard typeOf (sqrAt (Term.ofBase .length) m) == some (.arrow (.Q m) (.Q (Term.mul m m)))

/- Instantiating at a *compound* unit works the same way: `m/s ↦ m²/s²`, and the
dimension supplied has to be the compound one. -/
abbrev velDim : DExp Dim 0 := Term.div (Term.ofBase .length) (Term.ofBase .time)

#guard typeOf (sqrAt velDim (Term.div m sec))
    == some (.arrow (.Q (Term.div m sec))
                    (.Q (Term.mul (Term.div m sec) (Term.div m sec))))

/- **The dimension bound is checked.** Instantiating the velocity-dimensioned
copy at a length is rejected: `uapp` verifies that the unit really has the
declared dimension. Bounded quantification would be decoration otherwise. -/
#guard (typeOf (sqrAt velDim m)).isNone
#guard (typeOf (sqrAt (Term.ofBase .length) (Term.div m sec))).isNone

/- Metre and foot both satisfy the Length bound: the point of bounding by
dimension rather than by unit. -/
#guard typeOf (sqrAt (Term.ofBase .length) ft) == some (.arrow (.Q ft) (.Q (Term.mul ft ft)))

/-- Addition at any unit, but the *same* unit on both sides. -/
def addPoly : Term₀ :=
  .dlam (.ulam dvar (.lam (.Q uvar) (.lam (.Q uvar) (.add (.var 0) (.var 1)))))

#guard typeOf addPoly
    == some (.allDim (.all dvar (.arrow (.Q uvar) (.arrow (.Q uvar) (.Q uvar)))))

/-- Polymorphism does not weaken the check. `Λδ. Λu:δ. λ(x : Q u). x + 1` is
rejected, because `u` is rigid inside the binder and cannot be `1`. -/
def badPoly : Term₀ := .dlam (.ulam dvar (.lam (.Q uvar) (.add (.var 0) (.lit 1))))

#guard (typeOf badPoly).isNone

/-- Two *distinct* unit variables cannot be added either: nested binders really
introduce fresh variables rather than shadowing. -/
def twoVars : Term₀ :=
  .dlam (.ulam dvar (.ulam dvar
    (.lam (.Q (Term.ofVar 0)) (.lam (.Q (Term.ofVar 1)) (.add (.var 0) (.var 1))))))

#guard (typeOf twoVars).isNone

/-! ### Conversion under a binder

This is what the dimension bound buys, and what an unbounded quantifier cannot
express: a polymorphic function that converts its argument. -/

/-- `Λu:Length. λ(x : Q u). convert x u metre`: take a length in any unit,
return it in metres. -/
def inMetres : Term₀ :=
  .ulam (Term.ofBase .length) (.lam (.Q uvar) (.convert (.var 0) uvar m.weaken))

#guard typeOf inMetres
    == some (.all (Term.ofBase .length) (.arrow (.Q uvar) (.Q m.weaken)))

/- It applies at any Length unit; that is the whole point. -/
#guard typeOf (.uapp inMetres ft) == some (.arrow (.Q ft) (.Q m))
#guard typeOf (.uapp inMetres m) == some (.arrow (.Q m) (.Q m))

/- And not at a duration. -/
#guard (typeOf (.uapp inMetres sec)).isNone

/-- **The unbounded quantifier cannot convert.** The same body under `∀δ. ∀u:δ.`
is rejected: `dimOf` reports the dimension *variable* `δ`, which is not the
dimension of the metre, so `SameDim` fails. This is the rejection an unbounded
quantifier ought to give, and it is why the bound is a dimension variable rather
than the trivial dimension: under the trivial dimension `u` would be claimed
dimensionless and the conversion would wrongly be accepted. -/
def inMetresFree : Term₀ :=
  .dlam (.ulam dvar (.lam (.Q uvar) (.convert (.var 0) uvar m.weaken)))

#guard (typeOf inMetresFree).isNone

/-! ## Physics: where the exponents come from -/

namespace Physics

/-- ħ = kg·m²/s -/
abbrev hbar : UExp Base 0 := Term.div (Term.mul kg (Term.mul m m)) sec

/-- G = m³/(kg·s²) -/
abbrev G : UExp Base 0 :=
  Term.div (Term.mul m (Term.mul m m)) (Term.mul kg (Term.mul sec sec))

/-- c = m/s -/
abbrev c : UExp Base 0 := Term.div m sec

/- **The Planck length**, √(ħG/c³). Three constants, three base dimensions, an
exponent matrix of rank 3, so by the Pi theorem the combination with dimension
Length is *unique*. The checker confirms the standard formula lands on metres. -/
def planckLength : Term₀ :=
  .root 2 (.div (.mul (.ucon hbar) (.ucon G))
                (.mul (.ucon c) (.mul (.ucon c) (.ucon c))))

#guard typeOf planckLength == some (.Q m)

/- Getting the power of c wrong is caught. -/
def planckWrong : Term₀ :=
  .root 2 (.div (.mul (.ucon hbar) (.ucon G))
                (.mul (.mul (.ucon c) (.ucon c)) (.mul (.ucon c) (.ucon c))))

#guard typeOf planckWrong != some (.Q m)

/- **Fermion fields have mass dimension 3/2.** The Lagrangian carries mass
dimension 4 and the kinetic term contributes `2[ψ] + 1`, forcing `[ψ] = 3/2`.

This is the case that matters, and it is *not* like the Planck length. There the
half-powers cancel inside the root: `ħG/c³` is already `m²`, so every
intermediate has integer exponents and F# types it fine after grouping. A
fermion field carries `3/2` **standing alone**, appearing by itself in every
interaction term with nothing to group against. No integer-exponent units system
can write its type. -/
def fermionField : Term₀ := .root 2 (.mul (.ucon kg) (.mul (.ucon kg) (.ucon kg)))

#guard typeOf fermionField == some (.Q (Term.rpow (Term.mul kg (Term.mul kg kg)) (1/2)))

/- The exponent really is 3/2. -/
#guard (Term.rpow (Term.mul kg (Term.mul kg kg)) (1/2)).base .kilogram == (3/2 : ℚ)

/- A fermion field cannot be added to a mass or to a mass squared: the
half-integer is not an integer in disguise. -/
#guard (typeOf (.add fermionField (.ucon kg))).isNone
#guard (typeOf (.add fermionField (.ucon (Term.mul kg kg)))).isNone

/- In d dimensions `[ψ] = (d-1)/2`, so in the ten dimensions of superstring
theory a fermion carries `9/2`. -/
#guard (Term.rpow (Term.mul kg (Term.mul kg (Term.mul kg (Term.mul kg
          (Term.mul kg (Term.mul kg (Term.mul kg (Term.mul kg kg))))))))
        (1/2)).base .kilogram == (9/2 : ℚ)

end Physics

/-! ## The base-measure problem, as a type error

A probability density over a space whose measure carries `μ` itself carries
`μ⁻¹`; that is what makes `∫ p dμ` dimensionless. So `log p` is **not**
well-typed, which is the base-measure problem: a density means nothing except
relative to the measure it was taken against, and representing a distribution by
its density silently discards that measure.

Radul and Alexeev (arXiv:2010.09647) identify exactly this failure in
probabilistic programming systems and fix it by library convention. Here the
checker rejects it. -/

namespace Measure

/-- A probability density over a length-parameterized space: `m⁻¹`. -/
abbrev density : UExp Base 0 := Term.inv m

/-- A wavefunction is a *half*-density, at `m^(-1/2)`. Squaring it gives a
weight-1 density, which is the normalization condition. -/
abbrev halfDensity : UExp Base 0 := Term.rpow (Term.inv m) (1/2)

#guard halfDensity.base .metre == (-1/2 : ℚ)
#guard (Term.mul halfDensity halfDensity) == density

/- **Differential entropy is ill-typed.** `log p` is rejected. -/
#guard (typeOf (.log (.ucon density))).isNone

/- **KL divergence is fine.** A ratio of equal-weight densities lands at `1`, so
`log (p/q)` typechecks. The classical fact that relative entropy is invariant
under a change of units while differential entropy is not, as a distinction the
checker enforces rather than one the reader must remember. -/
#guard typeOf (.log (.div (.ucon density) (.ucon density)))
    == some (.Q (1 : UExp Base 0))

/- `exp` is equally strict: you cannot exponentiate a length. -/
#guard (typeOf (.exp (.ucon m))).isNone
#guard typeOf (.exp (.lit 1) : Term₀) == some (.Q (1 : UExp Base 0))

/- A Boltzmann factor `exp(-E/kT)` is well-typed exactly because the exponent is
an energy over an energy. -/
abbrev joule : UExp Base 0 := Term.div (Term.mul kg (Term.mul m m)) (Term.mul sec sec)

#guard typeOf (.exp (.div (.ucon joule) (.ucon joule)))
    == some (.Q (1 : UExp Base 0))
#guard (typeOf (.exp (.div (.ucon joule) (.ucon sec)))).isNone

end Measure

/-! ## Conversion, and the ambiguity that never arises

Comp 311's unit-conversion assignment has a latent bug: with units nameable in
terms of other units, `convert` walks a declared structure, and two routes from
`u` to `v` need not agree. Λs cannot exhibit it. Conversion is a *ratio of one
valuation* (`LambdaS.Conversion`), so `convChain_eq` makes path independence a
theorem rather than a proof obligation on declarations.

What the checker enforces is the side condition (that the two units measure the
same thing), and that is `SameDim`. -/

section Conversion

/- Metre and foot share a dimension, so `m → ft` converts. -/
#guard decide (SameDim Δ₀ (m : UExp Base 0) ft)

/- Metre and second do not. -/
#guard !decide (SameDim Δ₀ (m : UExp Base 0) sec)

/- `m/ft` is a perfectly good unit, and it is **dimensionless**, which is
exactly what a conversion factor is, and why it can itself be named. Under the
"at most one named unit per dimension" restriction this expression is illegal. -/
#guard decide (SameDim Δ₀ (Term.div m ft) (1 : UExp Base 0))

/- Dimension is what is shared; the *unit* is not. `m` and `ft` are distinct
exponent vectors, so nothing has been identified. -/
#guard (m : UExp Base 0) != ft

/- Converting `1.3 m` into feet: well-typed, at unit `ft`. -/
#guard typeOf (.convert length m ft) == some (.Q ft)

/- Converting a length into seconds is rejected statically, by `SameDim`. -/
#guard (typeOf (.convert length m sec)).isNone

/- The annotation must match: `convert` states the unit it is converting *from*,
so the erased evaluator can recover the factor without consulting a type. Get it
wrong and the term does not typecheck. -/
#guard (typeOf (.convert length sec ft)).isNone

/- Compound units convert componentwise, because dimension is a homomorphism:
`m/s → ft/s` is legal, `m/s → ft` is not. -/
#guard typeOf (.convert velocity (Term.div m sec) (Term.div ft sec))
    == some (.Q (Term.div ft sec))
#guard (typeOf (.convert velocity (Term.div m sec) ft)).isNone

/- Speed of light in metres per second converted to feet per second: the shape
of every real unit conversion, and the round trip is the identity because
`conv_symm` says the factors are inverse. -/
#guard typeOf (.convert (.convert velocity (Term.div m sec) (Term.div ft sec))
    (Term.div ft sec) (Term.div m sec)) == some (.Q (Term.div m sec))

end Conversion

/-! ## Declarations, and the conflict that cannot be declared away

`unit yard = 3 foot` declares a generator **and** an equation. Three such
declarations give two routes from yard to metre, which is the Comp 311 bug. Here
the redundant declaration is either arithmetically right or the system has no
solution: there is never a choice of route to get wrong. -/

section Declarations

/-- Base units of equal declared dimension are interchangeable, via
`dimOf_ofBase` rather than `decide`, since kernel reduction sticks on `ℚ`'s
instance chain. The dimension equation is `rfl` for any two Length units. -/
theorem sameDim_bu {b c : Base}
    (h : UnitSys.dim (D := Dim) b = UnitSys.dim (D := Dim) c) :
    SameDim Δ₀ (bu b : UExp Base 0) (bu c) := by
  unfold SameDim
  rw [show Δ₀ = DCtx.nil Dim from rfl, Decl.dimOf_ofBase, Decl.dimOf_ofBase, h]

theorem sameDim_m_ft : SameDim Δ₀ (m : UExp Base 0) ft := sameDim_bu rfl

theorem sameDim_ft_m : SameDim Δ₀ (ft : UExp Base 0) m := sameDim_m_ft.symm

/-- `unit yard = 3 foot` -/
def dYardFoot : Decl Base := ⟨.yard, 3, by norm_num, ft⟩

/-- `unit foot = 0.3048 metre` -/
def dFootMetre : Decl Base := ⟨.foot, 3048 / 10000, by norm_num, m⟩

/-- `unit yard = 0.9144 metre`: the redundant declaration, stated correctly. -/
def dYardMetre : Decl Base := ⟨.yard, 9144 / 10000, by norm_num, m⟩

/-- `unit yard = 0.9 metre`: the same declaration, stated wrongly. This is the
one that would have made `convert` route-dependent. -/
def dYardMetreBad : Decl Base := ⟨.yard, 9 / 10, by norm_num, m⟩

/- Every declaration is dimensionally sound: each declares a Length against a
Length. `unit yard = 3 second` would fail here. -/
#guard decide (Decl.Sound (D := Dim) dYardFoot)
#guard decide (Decl.Sound (D := Dim) dFootMetre)
#guard decide (Decl.Sound (D := Dim) dYardMetre)

/- The consistency test is exact rational arithmetic: no reals, no rounding. -/
#guard dYardFoot.factor * dFootMetre.factor == dYardMetre.factor
#guard dYardFoot.factor * dFootMetre.factor != dYardMetreBad.factor

/-- **The consistent set forces the redundant factor.** Any valuation satisfying
the first two determines the third, so the second route cannot disagree with the
first; it is not free to. -/
theorem yard_forced (ψ : Scaling Base 0)
    (h1 : Decl.Satisfies ψ dYardFoot) (h2 : Decl.Satisfies ψ dFootMetre)
    (h3 : Decl.Satisfies ψ dYardMetre) :
    dYardFoot.factor * dFootMetre.factor = dYardMetre.factor :=
  factor_chain_consistent h1 h2 h3 rfl rfl rfl

/-- **The conflicting set has no valuation at all.**

This is the Comp 311 bug, decided rather than papered over. The assignment's
`convert` had to walk a declared structure and could walk the wrong way; here the
configuration that would force a choice is exactly the configuration with no
solution, so it is rejected at declaration time. -/
theorem yard_conflict :
    ¬ ∃ ψ : Scaling Base 0, Decl.Satisfies ψ dYardFoot ∧ Decl.Satisfies ψ dFootMetre
        ∧ Decl.Satisfies ψ dYardMetreBad :=
  not_satisfiable_of_chain rfl rfl rfl (by norm_num [dYardFoot, dFootMetre, dYardMetreBad])

/-! ### The valuation the declarations determine, and the compiled evaluator using it

`yard_conflict` says the bad set has no valuation; this is the other half,
exhibited rather than asserted: the consistent set has one, written down. Its
factors then reach the compiled evaluator through `evalC_convert_declared`: the number the
evaluator multiplies by is the number the declaration names, with no route
through an informal reading of "3". -/

/-- The valuation `metre = 1, foot = 0.3048, yard = 0.9144` (in log space). -/
noncomputable def ψyd : Scaling Base 0 where
  base
    | .metre => 0
    | .foot => Real.log (3048 / 10000)
    | .yard => Real.log (9144 / 10000)
    | .kilogram => 0
    | .second => 0
  vars i := i.elim0

theorem ψyd_yardFoot : Decl.Satisfies ψyd dYardFoot := by
  show ψyd.scale (Term.div (Term.ofBase Base.yard) ft) = ((3 : ℚ) : ℝ)
  rw [Scaling.scale_div, NonDef.scale_ofBase, NonDef.scale_ofBase]
  show Real.exp (Real.log (9144 / 10000)) / Real.exp (Real.log (3048 / 10000)) = _
  rw [Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  norm_num

theorem ψyd_footMetre : Decl.Satisfies ψyd dFootMetre := by
  show ψyd.scale (Term.div (Term.ofBase Base.foot) m) = ((3048 / 10000 : ℚ) : ℝ)
  rw [Scaling.scale_div, NonDef.scale_ofBase, NonDef.scale_ofBase]
  show Real.exp (Real.log (3048 / 10000)) / Real.exp 0 = _
  rw [Real.exp_log (by norm_num), Real.exp_zero]
  norm_num

theorem ψyd_yardMetre : Decl.Satisfies ψyd dYardMetre := by
  show ψyd.scale (Term.div (Term.ofBase Base.yard) m) = ((9144 / 10000 : ℚ) : ℝ)
  rw [Scaling.scale_div, NonDef.scale_ofBase, NonDef.scale_ofBase]
  show Real.exp (Real.log (9144 / 10000)) / Real.exp 0 = _
  rw [Real.exp_log (by norm_num), Real.exp_zero]
  norm_num

/-- **The consistent set is satisfiable**: the counterpart to `yard_conflict`,
with the witness constructed rather than assumed. -/
theorem yard_satisfiable :
    ∃ ψ : Scaling Base 0, Decl.Satisfies ψ dYardFoot ∧ Decl.Satisfies ψ dFootMetre
      ∧ Decl.Satisfies ψ dYardMetre :=
  ⟨ψyd, ψyd_yardFoot, ψyd_footMetre, ψyd_yardMetre⟩

/-- **One yard is three feet, on the compiled evaluator.** Evaluating `(1 yd) in ft` with
the conversion oracle the declarations determine multiplies by exactly the
declared `3` and lands at `ft`: `evalC_convert_declared`, instantiated. -/
theorem one_yard_is_three_feet :
    ∃ n, evalC (conv ψyd) n [] ((.convert (.ucon yd) yd ft : Term₀))
      = some (.scalar ⟨3, ft⟩) := by
  obtain ⟨n, hn⟩ := evalC_convert_declared (D := Dim) ψyd_yardFoot
    (HasTy.ucon (u := yd)) (sameDim_bu rfl)
  refine ⟨n, hn.trans ?_⟩
  show some (Val.scalar ⟨(1 : ℝ) * ((3 : ℚ) : ℝ), ft⟩) = some (Val.scalar ⟨(3 : ℝ), ft⟩)
  norm_num

/-- And directly to metres, by the redundant declaration: the same number the
chain through feet produces, which is `yard_forced` made numeric. -/
theorem one_yard_in_metres :
    ∃ n, evalC (conv ψyd) n [] ((.convert (.ucon yd) yd m : Term₀))
      = some (.scalar ⟨((9144 / 10000 : ℚ) : ℝ), m⟩) := by
  obtain ⟨n, hn⟩ := evalC_convert_declared (D := Dim) ψyd_yardMetre
    (HasTy.ucon (u := yd)) (sameDim_bu rfl)
  refine ⟨n, hn.trans ?_⟩
  show some (Val.scalar ⟨(1 : ℝ) * ((9144 / 10000 : ℚ) : ℝ), m⟩)
    = some (Val.scalar ⟨((9144 / 10000 : ℚ) : ℝ), m⟩)
  norm_num

end Declarations

/-! ## Regression: substitution under nested binders

Attempting the type-soundness proof turned up a genuine defect in `Ty.subst`.

Inside `∀u. τ`, de Bruijn index 0 is the **bound** variable and 1 is the outer
one, so substituting for the outer variable must leave the binder alone. The
original definition recursed as `τ.subst σ.weaken`, which substitutes index 0
(the bound variable) and shifts the outer one down into its place. `Ty.weaken`
had the matching defect, inserting the fresh variable at index 0 rather than past
the binder.

Nothing here reached it. Every single-binder use is unaffected, and the one test
with nested unit binders (`twoVars`) is *rejected* by the checker before
substitution runs. The two definitions were also wrong in a way that cancelled,
so `subst_weaken` (the only theorem about them) held regardless.

It took writing the soundness proof to surface it: the composition lemma for
substitution refused to hold, and the reason was that `liftU` had no counterpart
in the quantifier case. The fix was to define `subst` and `weaken` as instances
of a simultaneous substitution that lifts properly. These guards pin the
corrected behavior.

That is the argument for mechanizing a calculus rather than describing one. The
defect is invisible to inspection, invisible to the examples, and invisible to
the one property anybody would have thought to state about it. -/

section SubstRegression

abbrev dLen : DExp Dim 0 := Term.ofBase Dim.length

/-- `∀u. Q v₁`: the body mentions the *outer* variable, not the bound one. -/
abbrev polyOuter : Ty Base Dim 0 1 := .all dLen (.Q (Term.ofVar 1))

/- Substituting for the outer variable leaves the binder untouched. -/
#guard Ty.subst polyOuter m == Ty.all dLen (.Q (bu Base.metre : UExp Base 1))

/- And does not capture the bound variable, which is precisely what the original
definition did. -/
#guard Ty.subst polyOuter m != Ty.all dLen (.Q (Term.ofVar 0))

/-- `∀u. Q v₀`: the body mentions the bound variable. -/
abbrev polyBound : Ty Base Dim 0 0 := .all dLen (.Q (Term.ofVar 0))

/- Weakening shifts the outer variables past the binder and leaves the bound one
where it is. -/
#guard Ty.weaken polyBound == Ty.all dLen (.Q (Term.ofVar 0))

/- Substituting into a weakened type is the identity. This held under the old
definitions too: both were wrong in a way that cancelled, which is why the only
theorem about them never noticed. -/
#guard Ty.subst (Ty.weaken polyBound) m == polyBound

end SubstRegression


/-! ## Algebraic units, in types and in measurements

Two expressibility checks worth keeping visible, because a reader of the
grammar can miss both. Unit expressions are the free abelian group: a type may
be indexed by an algebraic combination of *bound* unit variables, and a
measurement is a literal times a unit constant at any compound unit. -/

/-- `Λu:Length. Λv:Time. λx : Q (u·v). x`: a polymorphic identity at a
compound unit built from two distinct bound variables. Inside the two binders,
de Bruijn variable 1 is `u` and 0 is `v`. -/
def compoundPoly : Term₀ :=
  .ulam (Term.ofBase Dim.length) (.ulam (Term.ofBase Dim.time)
    (.lam (.Q (Term.mul (Term.ofVar 1) (Term.ofVar 0))) (.var 0)))

#guard typeOf compoundPoly ==
  some (.all (Term.ofBase Dim.length) (.all (Term.ofBase Dim.time)
    (.arrow (.Q (Term.mul (Term.ofVar 1) (Term.ofVar 0)))
            (.Q (Term.mul (Term.ofVar 1) (Term.ofVar 0))))))

/-- `5 m/s`: a literal times the unit constant at a compound unit. The type is
`Q (1 · m/s)`, and the exponent-vector representation makes that the *same*
index as `Q (m/s)`; the `#guard` compares the vectors. -/
def fiveMps : Term₀ := .mul (.lit 5) (.ucon (Term.div m sec))

#guard typeOf fiveMps == some (.Q (Term.div m sec))

/-! ## The drift diagnostic, exercised

Three programs, three answers. Converting metres to feet and back cancels:
`unitDrift` answers `1`, and the result is unit-system independent. Converting
one way does not: the drift is `m/ft`, and the diagnostic names it. And a sum
whose branches share a variable carries the branches' shared drift. -/

/-- `x : Q m ⊢ (x in ft) in m`: a round trip. -/
def roundTrip : Term₀ := .convert (.convert (.var 0) m ft) ft m

/-- `x : Q m ⊢ x in ft`, left in feet: drifted. -/
def oneWay : Term₀ := .convert (.var 0) m ft

def roundTripDeriv : HasTy Δ₀ (scalarCtx [m]) roundTrip (.Q m) :=
  .convert (.convert (.var rfl) sameDim_m_ft) sameDim_ft_m

def oneWayDeriv : HasTy Δ₀ (scalarCtx [m]) oneWay (.Q ft) :=
  .convert (.var rfl) sameDim_m_ft

/- The round trip's conversions cancel: drift `1`. -/
#guard (unitDrift roundTripDeriv).map (· == (1 : UExp Base 0)) == some true

/- The one-way conversion drifts by `m/ft`, and the diagnostic names it. -/
#guard (unitDrift oneWayDeriv).map (· == Term.div m ft) == some true

/-- Addition demands agreeing branch ratios, and `x in ft + x in ft` has them:
both branches carry the same variable's ratio times `m/ft`. Note that
`x in ft + y in ft` for *distinct* variables is rightly outside the relation:
its branches' ratios differ at some environments, and indeed that program is
not scale-invariant. -/
def addSame : Term₀ := .add (.convert (.var 0) m ft) (.convert (.var 0) m ft)

def addSameDeriv : HasTy Δ₀ (scalarCtx [m]) addSame (.Q ft) :=
  .add (.convert (.var rfl) sameDim_m_ft) (.convert (.var rfl) sameDim_m_ft)

/- The shared drift is reported. -/
#guard (unitDrift addSameDeriv).map (· == Term.div m ft) == some true

/-- Branch ratios compare up to the unit algebra, not up to spelling. The two
branches below convert the same product of meters to feet, placed differently:
the first converts the product once at `m·m`, the second converts each factor
at `m`. Their ratio terms differ syntactically (the syntactic check `Tw.beq`
rejects exactly
this pair), but `Tw.scalarEq` flattens both to the unit vector `m²/ft²` and
the atom bag `{x, y}`, so the analysis answers, and the answer is the drift
the branches share. -/
def addAssoc : Term₀ :=
  .add (.convert (.mul (.var 0) (.var 1)) (Term.mul m m) (Term.mul ft ft))
       (.mul (.convert (.var 0) m ft) (.convert (.var 1) m ft))

theorem sameDim_mm_ftft : SameDim Δ₀ (Term.mul m m) (Term.mul ft ft) := by
  have h := sameDim_m_ft
  unfold SameDim at h ⊢
  rw [dimOf_mul, dimOf_mul, h]

def addAssocDeriv : HasTy Δ₀ (scalarCtx [m, m]) addAssoc (.Q (Term.mul ft ft)) :=
  .add (.convert (.mul (.var rfl) (.var rfl)) sameDim_mm_ftft)
       (.mul (.convert (.var rfl) sameDim_m_ft) (.convert (.var rfl) sameDim_m_ft))

/- Differently placed but equal conversions are accepted; the shared drift is
reported. -/
#guard (unitDrift addAssocDeriv).map (· == Term.div (Term.mul m m) (Term.mul ft ft))
  == some true

/-! ## The generic caster

Under `∀δ. ∀u:δ`, conversion out of `u` is not blocked wholesale: it can
target any expression of dimension `δ`, and in particular another variable
bounded by the same `δ`. The generic caster

`Λδ. Λu:δ. Λv:δ. λx:Q u. convert x u v`

typechecks, at the polymorphic cast type, and instantiating both unit
quantifiers at same-dimension ground units yields an ordinary cast. What
remains rejected is conversion from `u` to a *concrete* unit, since no
concrete unit has dimension `δ`. The caster is a term the two abstraction
theorems separate: coherent rescalings give `u` and `v` one shared factor
and leave it invariant; independent factors move it. -/

section Caster

/-- The single dimension variable, seen under one dimension binder. -/
private abbrev δVar : DExp Dim 1 := Term.ofVar 0
/-- The outer unit variable `u`, seen under two unit binders. -/
private abbrev castU : UExp Base 2 := Term.ofVar 1
/-- The inner unit variable `v`. -/
private abbrev castV : UExp Base 2 := Term.ofVar 0

/-- `Λδ. Λu:δ. Λv:δ. λx:Q u. convert x u v`. -/
def caster : Term₀ :=
  .dlam (.ulam δVar (.ulam δVar
    (.lam (.Q castU) (.convert (.var 0) castU castV))))

/- The caster typechecks, at exactly the polymorphic cast type. -/
#guard typeOf caster ==
  some (.allDim (.all δVar (.all δVar (.arrow (.Q castU) (.Q castV)))))

/- Instantiated at Length, meter, and foot it is a meter-to-foot cast. -/
#guard typeOf (.uapp (.uapp (.dapp caster (Term.ofBase Dim.length)) m) ft) ==
  some (.arrow (.Q m) (.Q ft))

/-- One δ-bounded variable, converting to a concrete unit. -/
private abbrev castU1 : UExp Base 1 := Term.ofVar 0

/- Conversion from `u` to a concrete unit is rejected: `metre` has dimension
Length, not `δ`. -/
#guard (typeOf (.dlam (.ulam δVar (.lam (.Q castU1)
  (.convert (.var 0) castU1 (Term.ofBase Base.metre)))))).isNone

/- The self-cast `u` to `u` is the one conversion a single δ-bounded
variable admits, and it typechecks. -/
#guard (typeOf (.dlam (.ulam δVar (.lam (.Q castU1)
  (.convert (.var 0) castU1 castU1))))).isSome

end Caster

/-! ## The coherent fundamental theorem, at a rescaling that moves a dimension

`fundamental` quantifies over dimension rescalings `Φ`. This section
instantiates it at a `Φ` that is not the identity: it multiplies every Length
by 2 and fixes Mass and Time. The term is a conversion from meters to feet, so
the instantiation exercises the `convert` case of the theorem, the case that
requires coherence. -/

section MovingRescale

/-- A dimension rescaling that doubles Length and fixes Mass and Time. In log
coordinates the Length entry is `log 2`, which is nonzero, so this rescaling
moves a dimension. -/
noncomputable def ΦDouble : Scaling Dim 0 where
  base
    | .length => Real.log 2
    | .mass => 0
    | .time => 0
  vars i := i.elim0

/-- `ΦDouble` is not the trivial rescaling: it moves the Length dimension. -/
theorem ΦDouble_moves_length : ΦDouble.base Dim.length ≠ 0 :=
  ne_of_gt (Real.log_pos (by norm_num))

/-- The unit rescaling `ΦDouble` pulls back to: each base unit scales by the
factor of its dimension, so meter, foot, and yard all scale by 2 while
kilogram and second are fixed. -/
noncomputable def ψDouble : Scaling Base 0 where
  base b := ∑ d, ((UnitSys.dim (D := Dim) b).base d : ℝ) * ΦDouble.base d
  vars i := i.elim0

/-- `ψDouble` factors through dimension via `ΦDouble`, by construction: its
`base` field is definitionally the sum `Scaling.Factors` requires. -/
theorem ψDouble_factors : ψDouble.Factors Δ₀ ΦDouble where
  base _ := rfl
  vars i := i.elim0

/-- `λ(x : Q m). convert x m ft`, closed and parametric: the conversion is the
only non-variable subterm, and `Tm.Parametric` admits `convert`. -/
def cvtMFDeriv : HasTy Δ₀ ([] : Ctx Base Dim 0 0)
    (.lam (.Q m) (cvtTm m ft)) (.arrow (.Q m) (.Q ft)) :=
  .lam (cvtDeriv sameDim_m_ft)

/-- **`fundamental`, instantiated at a rescaling that moves a dimension.** The
conversion program is related to itself under `ΦDouble`, which rescales Length
by 2. Unfolding `RelCo` at the arrow type: for inputs related by
`ψDouble.scale m`, the outputs are related by `ψDouble.scale ft`. The `convert`
case of `fundamental` carries the content here, since the conversion factor
`conv V m ft` must be invariant under the rescaling, and coherence of
`ψDouble` (every Length unit scales by the same factor 2) is exactly what
makes it so. -/
theorem fundamental_at_moving_rescale (V : Scaling Base 0) :
    RelCo Δ₀ ΦDouble (.arrow (.Q m) (.Q ft)) ψDouble
      (den V cvtMFDeriv PUnit.unit) (den (V.comp ψDouble) cvtMFDeriv PUnit.unit) :=
  fundamental cvtMFDeriv trivial V ψDouble ΦDouble ψDouble_factors trivial

end MovingRescale

/-! ## Vector and matrix literals

Until the introduction forms existed, vectors and matrices entered only as free
variables: the calculus could consume its data but not construct it. These
guards exercise the forms that close the gap: a `State` vector built one
component at a time, matrices built one row at a time, the rejections the rules
impose, and the zero-row width story that `mnil`'s annotation exists to tell. -/

section Literals

/-- The momentum unit of `State`, `kg·m/s`. -/
abbrev pmom : UExp Base 0 := Term.div (Term.mul kg m) sec

/-- The `State` vector as a literal: position `1.3 m` consed onto momentum
`21 kg·m/s`. -/
def stateVec : Term₀ :=
  .vcons (.mul (.lit 1.3) (.ucon m))
    (.vcons (.mul (.lit 21) (.ucon pmom)) .vnil)

/- The literal lands at exactly the space the elimination forms consume. -/
#guard typeOf stateVec == some (.vec State)

/- The empty vector lives at the empty space. -/
#guard typeOf (.vnil : Term₀) == some (.vec [])

/- Consing a duration where the momentum slot expects `kg·m/s` builds a vector
over a *different* space, and the eliminations reject it: a `State`-consuming
map applies to the literal above and not to this one. -/
def wrongVec : Term₀ :=
  .vcons (.mul (.lit 1.3) (.ucon m)) (.vcons duration .vnil)

#guard typeOfIn [.lin State W] (.mapp (.var 0) stateVec) == some (.vec W)
#guard (typeOfIn [.lin State W] (.mapp (.var 0) wrongVec)).isNone

/-- A map from `State` to `W = [sec]` as a literal: one row whose entry `i`
carries `sec / δ_State(i)`, which is the rank-one condition the `mcons` rule
checks. -/
def toTime : Term₀ :=
  .mcons sec
    (.vcons (.mul (.lit 2) (.ucon (Term.div sec m)))
      (.vcons (.mul (.lit 3) (.ucon (Term.div sec pmom))) .vnil))
    (.mnil State)

#guard typeOf toTime == some (.lin State W)

/-- A two-row map the other way, one row per component of `State`. -/
def fromTime : Term₀ :=
  .mcons m (.vcons (.mul (.lit 4) (.ucon (Term.div m sec))) .vnil)
    (.mcons pmom (.vcons (.mul (.lit 5) (.ucon (Term.div pmom sec))) .vnil)
      (.mnil W))

#guard typeOf fromTime == some (.lin W State)

/- A row at the wrong space is rejected by the introduction rule itself: a
`toTime` row must carry `sec/m` in its first slot, not `sec`. -/
#guard (typeOf (.mcons sec
    (.vcons (.mul (.lit 2) (.ucon sec))
      (.vcons (.mul (.lit 3) (.ucon (Term.div sec pmom))) .vnil))
    (.mnil State))).isNone

/- **The zero-row width story.** `mnil State : Lin State []` composes on the
left of any map into `State`, and the composite still has a well-defined
column count: the width survives because `mnil` carries its space. -/
#guard typeOf (.comp (.mnil State) fromTime) == some (.lin W [])
#guard typeOfIn [.lin W State] (.comp (.mnil State) (.var 0)) == some (.lin W [])

/- The evaluator round trip: indexing the literal vector returns exactly the
value of its consed component, magnitude and unit both. -/
#guard (match evalC (D := Dim) (fun _ _ => (1.0 : Float)) 10 [] (.idx stateVec 0),
              evalC (D := Dim) (fun _ _ => (1.0 : Float)) 10 [] length with
        | some (.scalar x), some (.scalar y) => x.mag == y.mag && x.unit == y.unit
        | _, _ => false)

end Literals

/-! ## Case study: a mixed-unit ballistics kernel

The drift diagnostic has so far run on one-line programs. This section runs it
on a small straight-line kernel with the shape real conversion bugs have:
field data arrives in imperial units, the physics is metric, and the report
goes back out in imperial units.

Inputs: a distance in feet (variable 0) and a time in seconds (variable 1).
The shared pipeline converts the distance to meters, forms the velocity in
`m/s`, and computes the kinetic energy per unit mass `v²/2` in `m²/s²`. Four
reporting variants, four verdicts, all decided at build time:

* `kernelConsistent` converts the metric energy back to `ft²/s²` for the
  report. The input conversion cancels against the output conversion through
  the arithmetic, and `unitDrift` certifies the whole multi-step routine
  drift-free: by `den_indep_of_driftFree`, the reported number does not
  depend on the declared unit magnitudes.
* `kernelOneWay` reports in metric, so the input conversion is never undone.
  The diagnostic names the exact ratio, `ft²/m²`: the drift `ft/m` of one
  foot-to-meter conversion, squared through `v²`.
* `kernelMixedPaths` computes `v²` twice in one sum: once by converting the
  input and squaring the metric velocity, once by squaring the imperial
  velocity and converting the square at `ft²/s²`. The branch ratios differ
  syntactically (`Tw.beq` rejects the pair), but `Tw.scalarEq` flattens both
  to the exponent vector `ft²/m²` over the atom bags `{x, x}/{t, t}`, so the
  sum is accepted and carries the branches' shared drift.
* `kernelDeclined` takes the speed back out of the energy with a square
  root, and there the analysis declines: `twistOf` has no rule at `root`.
  The invariance *theory* covers roots (`Tm.Parametric` admits them, and
  `fundamental` handles them through `relQ_rpow`), but the root's scale
  factor is a rational power `ψ(u)^(1/n)` and the ratio grammar `Tw` has no
  rational-power former, so declining is a limitation of the analysis, not
  an exclusion by the theory. `unitDrift` answers `none` rather than
  guessing.

Every routine typechecks by a `#guard` on the inferred type, and every drift
claim is a `#guard` on `unitDrift`, so a wrong claim fails the build. -/

namespace Ballistics

/-- The kernel's input context: a distance in feet and a time in seconds. -/
abbrev Γb : Ctx Base Dim 0 0 := scalarCtx [ft, sec]

/-- Metric velocity, `m/s`. -/
abbrev mps : UExp Base 0 := Term.div m sec
/-- Imperial velocity, `ft/s`. -/
abbrev fps : UExp Base 0 := Term.div ft sec
/-- Metric energy per unit mass, `m²/s²`. -/
abbrev mps2 : UExp Base 0 := Term.mul mps mps
/-- Imperial energy per unit mass, `ft²/s²`. -/
abbrev fps2 : UExp Base 0 := Term.mul fps fps

/-- Meter and foot share a dimension, so velocity squared does too: the side
condition the energy conversions below discharge, proved by the homomorphism
laws for `dimOf` rather than by `decide`. -/
theorem sameDim_mps2_fps2 : SameDim Δ₀ mps2 fps2 := by
  have h := sameDim_m_ft
  unfold SameDim at h ⊢
  rw [dimOf_mul, dimOf_mul, dimOf_div, dimOf_div, h]

theorem sameDim_fps2_mps2 : SameDim Δ₀ fps2 mps2 := sameDim_mps2_fps2.symm

/-! ### The shared pipeline

Real code shares subterms, so the variants do too: one converted distance,
one metric velocity, one imperial velocity, each with its derivation. -/

/-- The distance input, converted to meters: `x in m`. -/
def distM : Term₀ := .convert (.var 0) ft m

/-- Metric velocity: the converted distance over the raw time input. -/
def velM : Term₀ := .div distM (.var 1)

/-- Imperial velocity: the raw inputs, no conversion. -/
def velF : Term₀ := .div (.var 0) (.var 1)

def distMDeriv : HasTy Δ₀ Γb distM (.Q m) := .convert (.var rfl) sameDim_ft_m

def velMDeriv : HasTy Δ₀ Γb velM (.Q mps) := .div distMDeriv (.var rfl)

def velFDeriv : HasTy Δ₀ Γb velF (.Q fps) := .div (.var rfl) (.var rfl)

#guard typeOfIn Γb distM == some (.Q m)
#guard typeOfIn Γb velM == some (.Q mps)
#guard typeOfIn Γb velF == some (.Q fps)

/-- The one-way drift both drifted variants share: one foot-to-meter
conversion, squared through `v²`. -/
abbrev driftSq : UExp Base 0 := Term.div (Term.mul ft ft) (Term.mul m m)

/-! ### Variant 1: convert in, compute, convert out -/

/-- `(1/2) · ((velM · velM) in ft²/s²)`: metric energy, reported imperial.
The `ft → m` conversion inside `velM` enters the ratio twice through the
square; the output conversion contributes `m²/ft²` and cancels it exactly. -/
def kernelConsistent : Term₀ :=
  .mul (.lit (1/2)) (.convert (.mul velM velM) mps2 fps2)

def kernelConsistentDeriv : HasTy Δ₀ Γb kernelConsistent (.Q (Term.mul 1 fps2)) :=
  .mul .lit (.convert (.mul velMDeriv velMDeriv) sameDim_mps2_fps2)

#guard typeOfIn Γb kernelConsistent == some (.Q fps2)

/- Certified drift-free: a genuinely multi-step mixed-unit routine whose
result is independent of the declared unit magnitudes. -/
#guard (unitDrift kernelConsistentDeriv).map (· == (1 : UExp Base 0)) == some true

/-! ### Variant 2: convert in, report metric -/

/-- `(1/2) · (velM · velM)`: the same computation, left in `m²/s²`. -/
def kernelOneWay : Term₀ := .mul (.lit (1/2)) (.mul velM velM)

def kernelOneWayDeriv : HasTy Δ₀ Γb kernelOneWay (.Q (Term.mul 1 mps2)) :=
  .mul .lit (.mul velMDeriv velMDeriv)

#guard typeOfIn Γb kernelOneWay == some (.Q mps2)

/- The drift is exactly `ft²/m²`, named by the diagnostic: the input
conversion's `ft/m`, squared, undone by nothing. -/
#guard (unitDrift kernelOneWayDeriv).map (· == driftSq) == some true

/-! ### Variant 3: the same quantity, two ways, in one sum -/

/-- `(1/2) · (velM·velM + ((velF·velF) in m²/s²))`: the left branch converts
the input then squares, the right squares the raw imperial velocity then
converts once at `ft²/s²`. Averaging the two would divide by a further
literal; adding them keeps the branch comparison the interesting step. -/
def kernelMixedPaths : Term₀ :=
  .mul (.lit (1/2))
    (.add (.mul velM velM)
          (.convert (.mul velF velF) fps2 mps2))

def kernelMixedPathsDeriv : HasTy Δ₀ Γb kernelMixedPaths (.Q (Term.mul 1 mps2)) :=
  .mul .lit
    (.add (.mul velMDeriv velMDeriv)
          (.convert (.mul velFDeriv velFDeriv) sameDim_fps2_mps2))

#guard typeOfIn Γb kernelMixedPaths == some (.Q mps2)

/- Differently placed conversions across the sum are accepted, and the shared
drift is the same `ft²/m²` the one-way variant carries. -/
#guard (unitDrift kernelMixedPathsDeriv).map (· == driftSq) == some true

/-! ### Variant 4: the rooted variant, declined -/

/-- `√(2 · kernelOneWay)`: the speed recovered from the energy. Well-typed at
`m/s` (roots are total over ℚ exponents), but outside the analysis: `Tw` has
no rational-power former, so `twistOf` has no rule at `root`. -/
def kernelDeclined : Term₀ := .root 2 (.mul (.lit 2) kernelOneWay)

def kernelDeclinedDeriv :
    HasTy Δ₀ Γb kernelDeclined
      (.Q (Term.rpow (Term.mul 1 (Term.mul 1 mps2)) (1 / ((2 : ℕ) : ℚ)))) :=
  .root (by decide) (.mul .lit kernelOneWayDeriv)

/- The exponent vectors identify `1·(1·v²)` with `v²`, so the root lands at
`m/s`, the unit a speed should have. -/
#guard typeOfIn Γb kernelDeclined == some (.Q (Term.rpow mps2 (1/2)))

/- The analysis declines rather than answers: theory covers the root, the
ratio grammar does not. -/
#guard (unitDrift kernelDeclinedDeriv).isNone

end Ballistics

end LambdaS.Examples

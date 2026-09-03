/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Scaling
import LambdaS.Dynamics

/-!
# Relational parametricity for units

Kennedy's POPL 1997 insight: the semantic content of unit correctness is
**invariance of program behavior under rescaling**. This file builds the
relation that says so at scalar type, and proves that every operation of the
arithmetic fragment preserves it.

## Why the *erased* semantics

The relation is stated on bare magnitudes: a quantity is a real number, and the
unit lives only in the relation. That is deliberate, and it is the half of
Kennedy's "instrumentation is cheating" objection that survives. An instrumented
semantics carries units on values, so there is nothing left to be invariant
*about*; parametricity has content only once units are erased and something else
has to carry them.

`LambdaS.Erasure` does the other half, where instrumentation is exactly right:
`eeval_erase` proves the units can be dropped without moving the numbers. Neither
file can state the other's theorem, and both are needed.

## What is proved here

`RelQ`, the relation at scalar type, and (the substance) that **every
arithmetic operation preserves it**. These are the inductive steps of the
fundamental theorem, and each is an instance of a homomorphism law from
`LambdaS.Scaling`.

Three read as design justifications rather than lemmas:

* `relQ_add` requires **both operands at the same unit**. State it at different
  units and it is false: the summands would scale by different factors and the
  sum by neither. The typing rule is forced by the semantics, not chosen.
* `relQ_rpow` requires the value to be **non-negative**: precisely Kennedy's
  standing assumption that floats are positive. Here it appears as a hypothesis
  that cannot be dropped, since `(k·x)^p = k^p · x^p` fails without it. Note
  that only the *value* needs it: the scale factor is positive by construction
  (`Scaling.scale_pos`).
* `relQ_log` holds **only at the trivial unit**, which is the semantic content of
  the base-measure problem. A dimensioned quantity has no scale-invariant
  logarithm, so `log p` for a density cannot mean anything that survives a
  change of units.

And `eq_zero_of_relQ_self` proves Kennedy's observation about zero: it is the
*unique* scale-invariant magnitude, which is why `0.0 : ∀u. float<u>` while every
other literal is `float<1>`.

## The relation at higher type

`Ty.den` and the full `Rel` are here, including the `∀u` case, and
`free_theorem_sqr` is the first result that uses them: any `f` related to itself
at `∀u. Q u → Q (u·u)` satisfies `f (r + log k) (k·x) = k²·f r x` for every
positive `k`. That is the familiar `f (k·x) = k²·f x`, with the family index
moved along by the rescaling, and it is Kennedy's "theorems for free",
mechanized.

Two notes on getting `Ty.den` to work, since both looked like obstacles and
neither was. Its type must generalize both scope indices (`{j k : ℕ} →
Ty B D j k → Type`, not `Ty B D j k → Type`) because `all` recurses at `k + 1`
and `allDim` at `j + 1`.
And it must be `@[reducible]`, because instance synthesis runs at reducible
transparency and otherwise `HMul ℝ (Ty.Q u).den` fails to resolve even though
the two types are definitionally equal.

## Where this leads

The **fundamental theorem** (every well-typed term related to itself) needs a
denotation of *terms*, hence recursion over typing **derivations**. `HasTy` is
`Type`-valued for exactly that reason, and `LambdaS.Fundamental` does the work:
`den` interprets derivations, and `fundamental` and `fundamental_free` are the
theorems. The Pi theorem is assembled in `LambdaS.PiTheorem`.
-/

namespace LambdaS

variable {B D : Type} [Fintype B] {j k : ℕ}

/-- The **erased denotation** of a type. Units contribute nothing: a quantity is
a real number whatever unit it carries, and a dimension abstraction denotes what its
body does, because dimensions have no magnitudes to carry.

A **unit** abstraction is different, and this is where `convert` shows its cost.
`Λu:δ. e` denotes a *family* `ℝ → Ty.den τ`, indexed by the log-magnitude the
instantiating unit is declared to have. It has to: `Λu:Length. convert x u metre`
means something different depending on how big `u` is, and `conv` is what reads
that. For convert-free terms the family is constant, which is Kennedy's theorem
rather than our definition, and is the better place for it to live.

`@[reducible]` is load-bearing: instance synthesis runs at reducible
transparency, so without it `HMul ℝ (Ty.Q u).den` fails to resolve. -/
@[reducible] def Ty.den : {j k : ℕ} → Ty B D j k → Type
  | _, _, .Q _ => ℝ
  | _, _, .arrow a b => Ty.den a → Ty.den b
  | _, _, .vec V => Fin V.length → ℝ
  | _, _, .lin V W => Fin W.length → Fin V.length → ℝ
  | _, _, .all _ τ => ℝ → Ty.den τ
  | _, _, .allDim τ => Ty.den τ

/-- **Units carry no data.** Grounding a type through unit and dimension
environments leaves its denotation unchanged.

This is unit erasure, stated at the level of types, and it is what makes the
denotation of polymorphic terms typeable at instantiation: `Λu:δ. e` denotes a
family, `e[μ]` samples it at `μ`'s log-magnitude, and the result must land in
`Ty.den (τ.subst μ)`; this equation says that is the same type as `Ty.den τ`,
because instantiating a unit variable moves no magnitudes.
The equation is propositional rather than definitional (`Ty.ground` maps over a
space's unit list, and `(V.map f).length = V.length` is a theorem), so the
denotation of a unit application transports along it. That transport is not an
artifact of the encoding; it is exactly the place where "units are erasable"
does its work. -/
theorem Ty.den_ground : ∀ {j k : ℕ} (τ : Ty B D j k) {j₀ k₀ : ℕ}
    (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀),
    Ty.den (Ty.ground η δ τ) = Ty.den τ := by
  intro j k τ
  induction τ with
  | Q u => intro _ _ _ _; rfl
  | arrow a b iha ihb => intro _ _ η δ; simp only [Ty.ground, Ty.den, iha, ihb]
  | vec V => intro _ _ η _; simp [Ty.ground, Ty.den]
  | lin V W => intro _ _ η _; simp [Ty.ground, Ty.den]
  | all d τ ih => intro _ _ η δ; simp only [Ty.ground, Ty.den, ih]
  | allDim τ ih => intro _ _ η δ; simp only [Ty.ground, Ty.den, ih]

/-- Instantiating a unit variable does not change the denotation. -/
theorem Ty.den_subst {j k : ℕ} (τ : Ty B D j (k + 1)) (μ : UExp B k) :
    Ty.den (τ.subst μ) = Ty.den τ := Ty.den_ground _ _ _

/-- Nor does instantiating a dimension variable. -/
theorem Ty.den_substDim {j k : ℕ} (τ : Ty B D (j + 1) k) (d : DExp D j) :
    Ty.den (τ.substDim d) = Ty.den τ := Ty.den_ground _ _ _

/-- Nor does weakening. -/
theorem Ty.den_weaken {j k : ℕ} (τ : Ty B D j k) :
    Ty.den (Ty.weaken τ) = Ty.den τ := Ty.den_ground _ _ _

/-- Nor does dimension weakening. -/
theorem Ty.den_weakenDim {j k : ℕ} (τ : Ty B D j k) :
    Ty.den (Ty.weakenDim τ) = Ty.den τ := Ty.den_ground _ _ _

/-- The **logical relation**: "behaves the same when units are rescaled by `ψ`".

At a scalar the two readings differ by exactly the scale factor. At a function,
related arguments must give related results. At `∀u:d. τ` the two families must agree at
every instantiation `r` and under every scaling `s` of the bound variable, with
the rescaled reading taken at `r + s` because rescaling moves the instantiating
unit too. The dimension bound restricts which *units* may instantiate, not which
*scalings* are considered, so the free theorems keep their full strength and the
Pi theorem keeps its hypothesis. At `∀δ. τ` nothing changes, because dimension
abstraction does not touch units. -/
def Rel : {j k : ℕ} → (τ : Ty B D j k) → Scaling B k → Ty.den τ → Ty.den τ → Prop
  | _, _, .Q u, ψ, x, y => y = ψ.scale u * x
  | _, _, .arrow a b, ψ, f, g => ∀ x y, Rel a ψ x y → Rel b ψ (f x) (g y)
  | _, _, .vec V, ψ, v, w => ∀ i, w i = ψ.scale (V.get i) * v i
  | _, _, .lin V W, ψ, A, C =>
      ∀ a i, C a i = (ψ.scale (W.get a) / ψ.scale (V.get i)) * A a i
  | _, _, .all _ τ, ψ, F, G => ∀ r s : ℝ, Rel τ (ψ.cons s) (F r) (G (r + s))
  | _, _, .allDim τ, ψ, F, G => Rel τ ψ F G

/-! ## Transporting the relation along a substitution

The relation must survive instantiation, or unit abstraction has no semantics.
`rel_ground` is that statement, and it is the semantic counterpart of
`Scaling.logScale_pull`: relatedness under `ψ` at a grounded type is relatedness
under the pulled-back scaling at the original.

The denotations are compared with `HEq` because `Ty.den (Ty.ground η δ τ)` and
`Ty.den τ` are equal but not definitionally so: the same transport that appears
in `den` at `uapp` and `dapp`. -/

/-- Applying heterogeneously equal functions to heterogeneously equal arguments. -/
theorem heq_app {α α' β β' : Sort _} {f : α → β} {g : α' → β'} {x : α} {y : α'}
    (hα : α = α') (hβ : β = β') (hf : HEq f g) (hx : HEq x y) : HEq (f x) (g y) := by
  subst hα; subst hβ; cases hf; cases hx; rfl

/-- **The relation transports along grounding.** -/
theorem rel_ground : ∀ {j k : ℕ} (τ : Ty B D j k) {j₀ k₀ : ℕ}
    (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀) (ψ : Scaling B k₀)
    {x y : Ty.den τ} {x' y' : Ty.den (Ty.ground η δ τ)}, HEq x x' → HEq y y' →
    (Rel (Ty.ground η δ τ) ψ x' y' ↔ Rel τ (ψ.pull η) x y) := by
  intro j k τ
  induction τ with
  | Q u =>
    intro _ _ η δ ψ x y x' y' hx hy
    obtain rfl := eq_of_heq hx
    obtain rfl := eq_of_heq hy
    simp [Ty.ground, Rel, Scaling.scale_pull]
  | arrow a b iha ihb =>
    intro _ _ η δ ψ x y x' y' hx hy
    have ha := Ty.den_ground a η δ
    have hb := Ty.den_ground b η δ
    constructor
    · intro h p q hpq
      exact (ihb η δ ψ (heq_app ha.symm hb.symm hx (cast_heq ha.symm p).symm)
          (heq_app ha.symm hb.symm hy (cast_heq ha.symm q).symm)).mp
        (h _ _ ((iha η δ ψ (cast_heq ha.symm p).symm (cast_heq ha.symm q).symm).mpr hpq))
    · intro h p' q' hpq'
      exact (ihb η δ ψ (heq_app ha.symm hb.symm hx (cast_heq ha p'))
          (heq_app ha.symm hb.symm hy (cast_heq ha q'))).mpr
        (h _ _ ((iha η δ ψ (cast_heq ha p') (cast_heq ha q')).mp hpq'))
  | vec V =>
    intro _ _ η δ ψ x y x' y' hx hy
    have hlen : V.length = (V.map (substU η)).length := by simp
    have hx : HEq (show Fin V.length → ℝ from x)
        (show Fin (V.map (substU η)).length → ℝ from x') := hx
    have hy : HEq (show Fin V.length → ℝ from y)
        (show Fin (V.map (substU η)).length → ℝ from y') := hy
    rw [Fin.heq_fun_iff hlen] at hx hy
    show (∀ i, y' i = ψ.scale ((V.map (substU η)).get i) * x' i)
      ↔ ∀ i, y i = (ψ.pull η).scale (V.get i) * x i
    constructor
    · intro h i
      have := h ⟨(i : ℕ), hlen ▸ i.2⟩
      rw [← hx i, ← hy i] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
    · intro h i
      have := h ⟨(i : ℕ), hlen.symm ▸ i.2⟩
      rw [hx ⟨(i : ℕ), hlen.symm ▸ i.2⟩, hy ⟨(i : ℕ), hlen.symm ▸ i.2⟩] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
  | lin V W =>
    intro _ _ η δ ψ x y x' y' hx hy
    have hV : V.length = (V.map (substU η)).length := by simp
    have hW : W.length = (W.map (substU η)).length := by simp
    have hx : HEq (show Fin W.length → Fin V.length → ℝ from x)
        (show Fin (W.map (substU η)).length → Fin (V.map (substU η)).length → ℝ from x') := hx
    have hy : HEq (show Fin W.length → Fin V.length → ℝ from y)
        (show Fin (W.map (substU η)).length → Fin (V.map (substU η)).length → ℝ from y') := hy
    rw [Fin.heq_fun₂_iff hW hV] at hx hy
    show (∀ a i, y' a i
            = (ψ.scale ((W.map (substU η)).get a) / ψ.scale ((V.map (substU η)).get i)) * x' a i)
      ↔ ∀ a i, y a i
            = ((ψ.pull η).scale (W.get a) / (ψ.pull η).scale (V.get i)) * x a i
    constructor
    · intro h a i
      have := h ⟨(a : ℕ), hW ▸ a.2⟩ ⟨(i : ℕ), hV ▸ i.2⟩
      rw [← hx a i, ← hy a i] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
    · intro h a i
      have := h ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩
      rw [hx ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩,
          hy ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
  | all d τ ih =>
    intro _ _ η δ ψ x y x' y' hx hy
    have hτ := Ty.den_ground τ (liftU η) δ
    show (∀ r s : ℝ, Rel (Ty.ground (liftU η) δ τ) (ψ.cons s) (x' r) (y' (r + s)))
      ↔ ∀ r s : ℝ, Rel τ ((ψ.pull η).cons s) (x r) (y (r + s))
    constructor
    · intro h r s
      have := (ih (liftU η) δ (ψ.cons s)
        (heq_app rfl hτ.symm hx (HEq.refl r)) (heq_app rfl hτ.symm hy (HEq.refl (r + s)))).mp (h r s)
      rwa [Scaling.pull_liftU] at this
    · intro h r s
      refine (ih (liftU η) δ (ψ.cons s)
        (heq_app rfl hτ.symm hx (HEq.refl r)) (heq_app rfl hτ.symm hy (HEq.refl (r + s)))).mpr ?_
      rw [Scaling.pull_liftU]
      exact h r s
  | allDim τ ih =>
    intro _ _ η δ ψ x y x' y' hx hy
    exact ih η (liftU δ) ψ hx hy

/-- **Weakening is invisible to the relation.** The fresh unit variable is
unused, so whatever factor it is given cannot matter. -/
theorem rel_weaken {j k : ℕ} (τ : Ty B D j k) (ψ : Scaling B k) (s : ℝ)
    {x y : Ty.den τ} {x' y' : Ty.den (Ty.weaken τ)} (hx : HEq x x') (hy : HEq y y') :
    Rel (Ty.weaken τ) (ψ.cons s) x' y' ↔ Rel τ ψ x y := by
  have h := rel_ground τ (fun i => Term.ofVar i.succ) (idU D j) (ψ.cons s) hx hy
  rwa [Scaling.pull_weaken] at h

/-- **Instantiating a unit variable extends the scaling by that unit's
magnitude.** This is what makes `e[μ]` denote something related to itself: the
relation at the instantiated type is the relation at the quantified one, read at
`μ`'s scale factor. -/
theorem rel_subst {j k : ℕ} (τ : Ty B D j (k + 1)) (σ : UExp B k) (ψ : Scaling B k)
    {x y : Ty.den τ} {x' y' : Ty.den (τ.subst σ)} (hx : HEq x x') (hy : HEq y y') :
    Rel (τ.subst σ) ψ x' y' ↔ Rel τ (ψ.cons (ψ.logScale σ)) x y := by
  have h := rel_ground τ (Fin.cons σ (idU B k)) (idU D j) ψ hx hy
  rwa [Scaling.pull_subst] at h

/-- **Dimension weakening is invisible.** Units are untouched. -/
theorem rel_weakenDim {j k : ℕ} (τ : Ty B D j k) (ψ : Scaling B k)
    {x y : Ty.den τ} {x' y' : Ty.den (Ty.weakenDim τ)} (hx : HEq x x') (hy : HEq y y') :
    Rel (Ty.weakenDim τ) ψ x' y' ↔ Rel τ ψ x y := by
  have h := rel_ground τ (idU B k) (fun i => Term.ofVar i.succ) ψ hx hy
  rwa [Scaling.pull_id] at h

/-- **Instantiating a dimension variable is invisible.** Dimensions have no
magnitudes, so nothing about the relation moves. -/
theorem rel_substDim {j k : ℕ} (τ : Ty B D (j + 1) k) (d : DExp D j) (ψ : Scaling B k)
    {x y : Ty.den τ} {x' y' : Ty.den (τ.substDim d)} (hx : HEq x x') (hy : HEq y y') :
    Rel (τ.substDim d) ψ x' y' ↔ Rel τ ψ x y := by
  have h := rel_ground τ (idU B k) (Fin.cons d (idU D j)) ψ hx hy
  rwa [Scaling.pull_id] at h

/-- The logical relation at scalar type: *"the same quantity, read in unit
systems that differ by `ψ`"*. The two readings differ by exactly the scale
factor of the unit. -/
def RelQ (u : UExp B k) (ψ : Scaling B k) (x y : ℝ) : Prop := y = ψ.scale u * x

/-- Under the trivial scaling the relation is equality: nothing moves when
nothing is rescaled. -/
@[simp] theorem relQ_id {u : UExp B k} {x y : ℝ} :
    RelQ u (Scaling.id B k) x y ↔ y = x := by simp [RelQ]

/-! ## The arithmetic operations preserve the relation -/

/-- Dimensionless literals are **invariant**: the same number in every unit
system. This is why `lit` has type `Q 1`, and why there is no unitless *type*,
only the unit `1`. -/
theorem relQ_lit (ψ : Scaling B k) (q : ℝ) : RelQ (1 : UExp B k) ψ q q := by
  simp [RelQ]

/-- Multiplication: units multiply, and so do scale factors. -/
theorem relQ_mul {u v : UExp B k} {ψ : Scaling B k} {x y x' y' : ℝ}
    (h : RelQ u ψ x y) (h' : RelQ v ψ x' y') :
    RelQ (Term.mul u v) ψ (x * x') (y * y') := by
  simp only [RelQ] at *
  rw [h, h', Scaling.scale_mul]; ring

/-- Division. -/
theorem relQ_div {u v : UExp B k} {ψ : Scaling B k} {x y x' y' : ℝ}
    (h : RelQ u ψ x y) (h' : RelQ v ψ x' y') :
    RelQ (Term.div u v) ψ (x / x') (y / y') := by
  simp only [RelQ] at *
  rw [h, h', Scaling.scale_div]
  field_simp

/-- **Addition requires the same unit on both sides.**

Not a convention. State it at different units and it is false: the summands
would scale by different factors and the sum by neither. -/
theorem relQ_add {u : UExp B k} {ψ : Scaling B k} {x y x' y' : ℝ}
    (h : RelQ u ψ x y) (h' : RelQ u ψ x' y') :
    RelQ u ψ (x + x') (y + y') := by
  simp only [RelQ] at *
  rw [h, h']; ring

/-- **Rational powers need positivity.**

Kennedy's standing assumption that floats are positive, appearing as the
hypothesis it actually is. The scale factor is positive by construction, so only
the value needs it. -/
theorem relQ_rpow {u : UExp B k} {ψ : Scaling B k} {x y : ℝ} (q : ℚ)
    (hx : 0 ≤ x) (h : RelQ u ψ x y) :
    RelQ (Term.rpow u q) ψ (x ^ (q : ℝ)) (y ^ (q : ℝ)) := by
  simp only [RelQ] at *
  rw [h, Scaling.scale_rpow, Real.mul_rpow (le_of_lt (ψ.scale_pos u)) hx]

/-- **`log` is invariant only at the trivial unit**: the semantic content of the
base-measure problem. -/
theorem relQ_log {ψ : Scaling B k} {x y : ℝ} (h : RelQ (1 : UExp B k) ψ x y) :
    RelQ (1 : UExp B k) ψ (Real.log x) (Real.log y) := by
  simp only [RelQ, Scaling.scale_one, one_mul] at *
  rw [h]

/-- `exp`, likewise. -/
theorem relQ_exp {ψ : Scaling B k} {x y : ℝ} (h : RelQ (1 : UExp B k) ψ x y) :
    RelQ (1 : UExp B k) ψ (Real.exp x) (Real.exp y) := by
  simp only [RelQ, Scaling.scale_one, one_mul] at *
  rw [h]

/-! ## Zero is the unique scale-invariant magnitude

Kennedy's explanation of why `0.0 : ∀u. float<u>` while every other literal is
`float<1>`. Not a special case bolted on to make arithmetic work: forced. It is
also what makes identity matrices and the `n = 0` term of `exp` well-typed in
`LambdaS.Map`, where the off-diagonal zeros must inhabit every unit. -/

/-- Zero relates to itself at **every** unit and every scaling. -/
theorem relQ_zero (u : UExp B k) (ψ : Scaling B k) : RelQ u ψ 0 0 := by
  simp [RelQ]

/-- And it is the only one. A magnitude related to itself under *every* scaling
of a unit variable must be zero. -/
theorem eq_zero_of_relQ_self {x : ℝ}
    (h : ∀ ψ : Scaling B 1, RelQ (Term.ofVar (0 : Fin 1)) ψ x x) : x = 0 := by
  have h2 := h ⟨fun _ => 0, fun _ => Real.log 2⟩
  simp only [RelQ, Scaling.scale, Scaling.logScale, Term.ofVar] at h2
  norm_num at h2
  rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h2
  linarith

/-! ## A theorem for free

The first result at higher type, and the shape Kennedy's Pi theorem generalizes:
the *type alone* constrains the function's behavior, whatever its code. -/

/-- The relation at `.Q` is exactly `RelQ`, so every arithmetic lemma above is a
lemma about `Rel`. -/
theorem rel_Q_eq (u : UExp B k) (ψ : Scaling B k) (x y : ℝ) :
    Rel (D := D) (j := j) (.Q u) ψ x y ↔ RelQ u ψ x y := Iff.rfl

/-- **Theorems for free.** Any `f` related to itself at `∀u. Q u → Q (u·u)`
satisfies `f (k·x) = k² · f x` for every positive `k`.

`f` takes the instantiating unit's log-magnitude as its first argument, and
rescaling by `k` moves that argument by `log k`: the unit the term was applied
to gets rescaled along with everything else. Read at a fixed `r` this is the
familiar statement.

Note how `∀u` is written: `∀δ. ∀u:δ.`, a unit variable bounded by a *dimension*
variable. That is unbounded quantification, and it is where the full strength of
the free theorem comes from, since nothing concrete matches `δ` and so `convert`
is unavailable at `u`.

Nothing is known about `f` except its type. This is what Kennedy's parametricity
buys, and it is the mechanism the Pi theorem runs on. -/
theorem free_theorem_sqr {f : ℝ → ℝ → ℝ}
    (h : Rel (D := D) (j := 0) (.allDim (.all (Term.ofVar 0)
                (.arrow (.Q (Term.ofVar 0))
                        (.Q (Term.mul (Term.ofVar 0) (Term.ofVar 0))))))
             (Scaling.id B 0) f f)
    (r : ℝ) {k : ℝ} (hk : 0 < k) (x : ℝ) :
    f (r + Real.log k) (k * x) = k ^ 2 * f r x := by
  have hs : ((Scaling.id B 0).cons (Real.log k)).scale (Term.ofVar (0 : Fin 1)) = k := by
    simp [Scaling.scale, Scaling.logScale, Scaling.cons, Scaling.id, Term.ofVar,
      Real.exp_log hk]
  have hs2 : ((Scaling.id B 0).cons (Real.log k)).scale
      (Term.mul (Term.ofVar (0 : Fin 1)) (Term.ofVar 0)) = k ^ 2 := by
    rw [Scaling.scale_mul, hs]; ring
  have hr := h r (Real.log k) x (k * x) (by simp [Rel, hs])
  simpa [Rel, hs2] using hr

end LambdaS

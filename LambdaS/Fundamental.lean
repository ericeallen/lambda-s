import LambdaS.Parametricity
import LambdaS.Conversion

/-!
# The fundamental theorem, and what conversion costs

Every well-typed term is related to itself. This is what makes the logical
relation say anything: without it, `Rel` is a definition and the free theorems
are unproved conjectures about particular functions.

## The point of this file

There are two fundamental theorems here, and the difference between them is the
whole story about conversion.

* `fundamental_free`: a **convert-free** term is related to itself under
  *every* scaling. This is Kennedy's theorem, and it is what the Pi theorem
  consumes.
* `fundamental`: an **arbitrary** term is related to itself under every
  **coherent** scaling, one that factors through dimension.

Conversion is the only operation in Λs that can observe a unit, so it is the
only operation that can pay. And `cvt_rel_iff_coherent` shows the price is
exactly right rather than merely sufficient: for a single conversion applied to
a nonzero argument, the relation holds **if and only if** the scaling identifies
the two units. Coherence is not a convenient hypothesis that makes the proof go
through; it is what the term forces.

That is the gap in the literature. Kennedy (POPL'97) and Atkey–Johann–Kennedy
(POPL'13) have unconditional abstraction theorems because nothing in their
calculi observes a unit: there is no conversion operator to break anything.
Practical systems have conversion and no invariance theory. Λs has both, and
this file is where they meet.

## The semantics runs on typing derivations

`den` recurses over `HasTy`, which is `Type`-valued precisely so that it can: a
denotation is data, and a `Prop`-valued derivation cannot eliminate into `Type`.
There is no second, intrinsically typed syntax: the term a derivation types is
its index, so the checker and the semantics are the same calculus by
construction rather than by a bridging theorem. Derivations being unique
(`Subsingleton (HasTy Δ Γ e τ)`) is what makes the denotation a function of the
*term*, and what lets the syntactic side conditions below be predicates on terms
rather than on derivations.

Unit and dimension application transport along `Ty.den_subst` and
`Ty.den_substDim`. Those casts are not an artifact of the encoding: they are
where "instantiating a unit moves no magnitudes" is discharged.

## Why the denotation takes a valuation

`den` is parameterized by a `Scaling B k`: the *declared* valuation, what each
base unit is worth. Nothing but `convert` reads it (`den_indep` proves exactly
that; note that `ucon` does **not** read it), but `convert` must: a conversion
factor is a ratio of declared magnitudes and cannot be recovered from the term
alone.

This is also why the fundamental theorem relates `den V` to `den (V.comp ψ)`
rather than `den` to itself. Rescaling is a change of the declared unit system,
so it acts on the valuation as well as on the environment. For convert-free
terms the distinction is invisible, which is precisely `den_indep`, with
`den_eq_of_convertFree` its closed-scalar corollary, closed because an open term
may have a free variable of quantified type whose family the environment
chooses non-constantly.

## No unit constants, and that is not an oversight

`Tm.Parametric` excludes `ucon`. **Unit constants break parametricity**, and
the reason is worth stating because it explains a feature of Kennedy's calculus
that otherwise looks arbitrary.

`ucon m : Q m` denotes the number `1`. The relation at `Q m` demands the two
readings differ by `ψ(m)`, so self-relatedness would need `1 = ψ(m) · 1`, false
for any scaling that actually moves the metre. A term that can *name* a unit can
detect a rescaling.

This is why Λu has no unit constants, and why Kennedy's own "converting kg into
lb" example rewrites the literals: `1.0<kg>` becomes `2.2<lb>`. The rescaling
acts on the program text, not only on the environment. Dimensioned values enter
through the environment (as free variables), never by naming a unit.

## Scope

Every form of Λs except `ucon` and `root`: variables, abstraction, application,
literals, the arithmetic, spaces and linear maps, conversion, and unit and
dimension abstraction and application. The two exclusions are `Tm.Parametric`'s,
and each is argued where it bites: `ucon` in the previous section, `root` next.

`root` is excluded for a reason already visible in `relQ_rpow`: it
needs `0 ≤ x`, so admitting it means denoting quantities by non-negative reals,
which `log` would then break. That is Kennedy's positivity assumption showing up
as a real constraint on the domain rather than a footnote.
-/

namespace LambdaS

open scoped BigOperators

variable {B D : Type} [Fintype B] [Fintype D] [UnitSys B D] {j k : ℕ}



variable {Δ : DCtx D j k}

/-- An environment: a denotation for each type in the context.

`@[reducible]` for the same reason `Ty.den` is: the elaborator must see through
it to project a pair. -/
@[reducible] def Env : Ctx B D j k → Type
  | [] => PUnit
  | τ :: Γ => Ty.den τ × Env Γ


/-- Looking a variable up in an environment, given the proof that the context
assigns it that type. This replaces a separate well-typed-variable inductive:
`HasTy.var` already carries the lookup as a hypothesis, so nothing else is
needed. -/
def Env.lookup : {Γ : Ctx B D j k} → {τ : Ty B D j k} → (n : ℕ) → Γ[n]? = some τ →
    Env Γ → Ty.den τ
  | [], _, _, h, _ => absurd h (by simp)
  | _ :: _, _, 0, h, ρ => Option.some.inj h ▸ ρ.1
  | _ :: _, _, n + 1, h, ρ => Env.lookup n (by simpa using h) ρ.2

/-- Reading an environment under a unit binder. The magnitudes are untouched;
only the types they are indexed by move, and `Ty.den_weaken` says that costs
nothing. -/
def Env.weaken : {Γ : Ctx B D j k} → Env Γ → Env Γ.weaken
  | [], _ => PUnit.unit
  | τ :: _, ρ => (cast (Ty.den_weaken τ).symm ρ.1, Env.weaken ρ.2)

/-- Reading an environment under a dimension binder. -/
def Env.weakenDim : {Γ : Ctx B D j k} → Env Γ → Env Γ.weakenDim
  | [], _ => PUnit.unit
  | τ :: _, ρ => (cast (Ty.den_weakenDim τ).symm ρ.1, Env.weakenDim ρ.2)

/-- Transport a denotation across a dimension instantiation. Phrased with the
quantified type on the *argument* so that elaboration reads the body's type off
the derivation rather than having to guess it. -/
def denDapp {j k : ℕ} {τ : Ty B D (j + 1) k} (d : DExp D j)
    (x : Ty.den (Ty.allDim τ)) : Ty.den (τ.substDim d) :=
  cast (Ty.den_substDim τ d).symm x

/-- **The denotation**, over typing derivations. Units are erased; only
magnitudes remain.

The valuation `V` is read by `convert` and by nothing else; `ucon` denotes `1`
without consulting it.
Under a unit binder it is extended by `Scaling.cons`, which is what gives
`Λu:δ. e` its family: the body is denoted once for each magnitude the bound unit
might be declared to have, and `e[μ]` selects the one at `V`'s reading of `μ`.

Unit and dimension application transport along `Ty.den_subst` and
`Ty.den_substDim`. Those casts are the erasure content of the definition: they
are where "instantiating a unit moves no magnitudes" is discharged. -/
noncomputable def den : {j k : ℕ} → {Δ : DCtx D j k} → {Γ : Ctx B D j k} →
    {e : Tm B D j k} → {τ : Ty B D j k} → Scaling B k → HasTy Δ Γ e τ → Env Γ → Ty.den τ
  | _, _, _, _, .var n, _, _, .var h, ρ => Env.lookup n h ρ
  | _, _, _, _, .lam _ _, _, V, .lam b, ρ => fun x => den V b (x, ρ)
  | _, _, _, _, .app _ _, _, V, .app f a, ρ => (den V f ρ) (den V a ρ)
  | _, _, _, _, .lit q, _, _, .lit, _ => (q : ℝ)
  | _, _, _, _, .ucon _, _, _, .ucon, _ => 1
  | _, _, _, _, .mul _ _, _, V, .mul a b, ρ => den V a ρ * den V b ρ
  | _, _, _, _, .div _ _, _, V, .div a b, ρ => den V a ρ / den V b ρ
  | _, _, _, _, .add _ _, _, V, .add a b, ρ => den V a ρ + den V b ρ
  | _, _, _, _, .root n _, _, V, .root _ a, ρ => (den V a ρ) ^ ((1 / (n : ℚ) : ℚ) : ℝ)
  | _, _, _, _, .idx _ i, _, V, .idx a hu, ρ =>
      den V a ρ ⟨i, (List.getElem?_eq_some_iff.mp hu).1⟩
  | _, _, _, _, .mapp _ _, _, V, .mapp f x, ρ =>
      fun a => ∑ i, den V f ρ a i * den V x ρ i
  | _, _, _, _, .comp _ _, _, V, .comp f g, ρ =>
      fun a i => ∑ b, den V f ρ a b * den V g ρ b i
  | _, _, _, _, .log _, _, V, .log a, ρ => Real.log (den V a ρ)
  | _, _, _, _, .exp _, _, V, .exp a, ρ => Real.exp (den V a ρ)
  | _, _, _, Γ, .ulam _ _, _, V, .ulam b, ρ =>
      fun r => den (Γ := Γ.weaken) (V.cons r) b (Env.weaken ρ)
  | _, _, _, _, .uapp _ σ, _, V, .uapp f _, ρ =>
      cast (Ty.den_subst _ σ).symm (den V f ρ (V.logScale σ))
  | _, _, _, Γ, .dlam _, _, V, .dlam b, ρ =>
      den (Γ := Γ.weakenDim) V b (Env.weakenDim ρ)
  | _, _, _, _, .dapp _ d, _, V, .dapp f, ρ => denDapp d (den V f ρ)
  | _, _, _, _, .convert _ u v, _, V, .convert a _, ρ => den V a ρ * conv V u v




/-- Two environments are related when they are related pointwise. -/
def RelEnv : (Γ : Ctx B D j k) → Scaling B k → Env Γ → Env Γ → Prop
  | [], _, _, _ => True
  | τ :: Γ, ψ, ρ, ρ' => Rel τ ψ ρ.1 ρ'.1 ∧ RelEnv Γ ψ ρ.2 ρ'.2

/-! ## The relation for coherent rescalings

`Rel` at `∀u:δ. τ` quantifies over *every* scaling of the bound variable. That is
right for convert-free terms, which cannot observe one, and wrong as soon as
conversion is admitted: `Λu:Length. convert x u metre` is related to itself only
when the bound unit is rescaled the way `metre` is.

`RelCo` is that relation. It is indexed by a scaling of **dimensions**, which is
what a coherent rescaling really is, and then the `∀` case needs no side
condition at all: the factor the bound unit receives is `Φ δ`, determined rather
than quantified. The two relations agree at quantifier-free types. -/

/-- **The logical relation for coherent rescalings.** -/
def RelCo : {j k : ℕ} → DCtx D j k → Scaling D j → (τ : Ty B D j k) → Scaling B k →
    Ty.den τ → Ty.den τ → Prop
  | _, _, _, _, .Q u, ψ, x, y => y = ψ.scale u * x
  | _, _, Δ, Φ, .arrow a b, ψ, f, g =>
      ∀ x y, RelCo Δ Φ a ψ x y → RelCo Δ Φ b ψ (f x) (g y)
  | _, _, _, _, .vec V, ψ, v, w => ∀ i, w i = ψ.scale (V.get i) * v i
  | _, _, _, _, .lin V W, ψ, A, C =>
      ∀ a i, C a i = (ψ.scale (W.get a) / ψ.scale (V.get i)) * A a i
  | _, _, Δ, Φ, .all d τ, ψ, F, G =>
      ∀ r : ℝ, RelCo (Δ.cons d) Φ τ (ψ.cons (Φ.logScale d)) (F r) (G (r + Φ.logScale d))
  | _, _, Δ, Φ, .allDim τ, ψ, F, G =>
      ∀ t : ℝ, RelCo Δ.weakenDim (Φ.cons t) τ ψ F G

/-- The substitution respects the declared dimensions: each unit substituted has
the dimension the source context gave the variable it replaces. -/
def Respects {j k j₀ k₀ : ℕ} (Δ : DCtx D j k) (Δ₀ : DCtx D j₀ k₀)
    (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀) : Prop :=
  ∀ i, substU δ (Δ i) = dimOf (D := D) Δ₀ (η i)

/-- **`RelCo` transports along grounding**, exactly as `Rel` does, with the
dimension scaling pulled back alongside the unit scaling. -/
theorem relCo_ground : ∀ {j k : ℕ} (τ : Ty B D j k) {j₀ k₀ : ℕ}
    (Δ : DCtx D j k) (Δ₀ : DCtx D j₀ k₀) (Φ₀ : Scaling D j₀)
    (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀) (ψ : Scaling B k₀),
    Respects Δ Δ₀ η δ →
    ∀ {x y : Ty.den τ} {x' y' : Ty.den (Ty.ground η δ τ)}, HEq x x' → HEq y y' →
    (RelCo Δ₀ Φ₀ (Ty.ground η δ τ) ψ x' y' ↔ RelCo Δ (Φ₀.pull δ) τ (ψ.pull η) x y) := by
  intro j k τ
  induction τ with
  | Q u =>
    intro _ _ _ _ _ η δ ψ _ x y x' y' hx hy
    obtain rfl := eq_of_heq hx
    obtain rfl := eq_of_heq hy
    simp [Ty.ground, RelCo, Scaling.scale_pull]
  | arrow a b iha ihb =>
    intro _ _ Δ Δ₀ Φ₀ η δ ψ hres x y x' y' hx hy
    have ha := Ty.den_ground a η δ
    have hb := Ty.den_ground b η δ
    constructor
    · intro h p q hpq
      exact (ihb Δ Δ₀ Φ₀ η δ ψ hres (heq_app ha.symm hb.symm hx (cast_heq ha.symm p).symm)
          (heq_app ha.symm hb.symm hy (cast_heq ha.symm q).symm)).mp
        (h _ _ ((iha Δ Δ₀ Φ₀ η δ ψ hres (cast_heq ha.symm p).symm
          (cast_heq ha.symm q).symm).mpr hpq))
    · intro h p' q' hpq'
      exact (ihb Δ Δ₀ Φ₀ η δ ψ hres (heq_app ha.symm hb.symm hx (cast_heq ha p'))
          (heq_app ha.symm hb.symm hy (cast_heq ha q'))).mpr
        (h _ _ ((iha Δ Δ₀ Φ₀ η δ ψ hres (cast_heq ha p') (cast_heq ha q')).mp hpq'))
  | vec V =>
    intro _ _ _ _ _ η δ ψ _ x y x' y' hx hy
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
    intro _ _ _ _ _ η δ ψ _ x y x' y' hx hy
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
    intro _ _ Δ Δ₀ Φ₀ η δ ψ hres x y x' y' hx hy
    have hτ := Ty.den_ground τ (liftU η) δ
    have hc : (Φ₀.pull δ).logScale d = Φ₀.logScale (substU δ d) := Scaling.logScale_pull ..
    have hres' : Respects (Δ.cons d) (Δ₀.cons (substU δ d)) (liftU η) δ := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [DCtx.cons, liftU]
      · simpa [DCtx.cons, liftU] using hres i
    show (∀ r : ℝ, RelCo (Δ₀.cons (substU δ d)) Φ₀ (Ty.ground (liftU η) δ τ)
            (ψ.cons (Φ₀.logScale (substU δ d))) (x' r)
            (y' (r + Φ₀.logScale (substU δ d))))
      ↔ ∀ r : ℝ, RelCo (Δ.cons d) (Φ₀.pull δ) τ ((ψ.pull η).cons ((Φ₀.pull δ).logScale d))
            (x r) (y (r + (Φ₀.pull δ).logScale d))
    rw [hc]
    constructor
    · intro h r
      have := (ih (Δ.cons d) (Δ₀.cons (substU δ d)) Φ₀ (liftU η) δ
        (ψ.cons (Φ₀.logScale (substU δ d))) hres'
        (heq_app rfl hτ.symm hx (HEq.refl r))
        (heq_app rfl hτ.symm hy (HEq.refl (r + Φ₀.logScale (substU δ d))))).mp (h r)
      rwa [Scaling.pull_liftU] at this
    · intro h r
      refine (ih (Δ.cons d) (Δ₀.cons (substU δ d)) Φ₀ (liftU η) δ
        (ψ.cons (Φ₀.logScale (substU δ d))) hres'
        (heq_app rfl hτ.symm hx (HEq.refl r))
        (heq_app rfl hτ.symm hy (HEq.refl (r + Φ₀.logScale (substU δ d))))).mpr ?_
      rw [Scaling.pull_liftU]
      exact h r
  | allDim τ ih =>
    intro _ _ Δ Δ₀ Φ₀ η δ ψ hres x y x' y' hx hy
    have hres' : Respects Δ.weakenDim Δ₀.weakenDim η (liftU δ) := by
      intro i
      simpa [DCtx.weakenDim, substU_weaken] using congrArg UExp.weaken (hres i)
    show (∀ t : ℝ, RelCo Δ₀.weakenDim (Φ₀.cons t) (Ty.ground η (liftU δ) τ) ψ x' y')
      ↔ ∀ t : ℝ, RelCo Δ.weakenDim ((Φ₀.pull δ).cons t) τ (ψ.pull η) x y
    constructor
    · intro h t
      have := (ih Δ.weakenDim Δ₀.weakenDim (Φ₀.cons t) η (liftU δ) ψ hres' hx hy).mp (h t)
      rwa [Scaling.pull_liftU] at this
    · intro h t
      refine (ih Δ.weakenDim Δ₀.weakenDim (Φ₀.cons t) η (liftU δ) ψ hres' hx hy).mpr ?_
      rw [Scaling.pull_liftU]
      exact h t

/-- Instantiating a unit variable, for `RelCo`. -/
theorem relCo_subst {j k : ℕ} (Δ : DCtx D j k) (Φ : Scaling D j) (τ : Ty B D j (k + 1))
    (σ : UExp B k) (ψ : Scaling B k)
    {x y : Ty.den τ} {x' y' : Ty.den (τ.subst σ)} (hx : HEq x x') (hy : HEq y y') :
    RelCo Δ Φ (τ.subst σ) ψ x' y'
      ↔ RelCo (Δ.cons (dimOf (D := D) Δ σ)) Φ τ (ψ.cons (ψ.logScale σ)) x y := by
  have hres : Respects (Δ.cons (dimOf (D := D) Δ σ)) Δ (Fin.cons σ (idU B k)) (idU D j) := by
    intro i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [DCtx.cons, idU]
  have h := relCo_ground τ (Δ.cons (dimOf (D := D) Δ σ)) Δ Φ (Fin.cons σ (idU B k))
    (idU D j) ψ hres hx hy
  rwa [Scaling.pull_id, Scaling.pull_subst] at h

/-- Weakening under a unit binder, for `RelCo`. -/
theorem relCo_weaken {j k : ℕ} (Δ : DCtx D j k) (Φ : Scaling D j) (d : DExp D j)
    (τ : Ty B D j k) (ψ : Scaling B k) (s : ℝ)
    {x y : Ty.den τ} {x' y' : Ty.den (Ty.weaken τ)} (hx : HEq x x') (hy : HEq y y') :
    RelCo (Δ.cons d) Φ (Ty.weaken τ) (ψ.cons s) x' y' ↔ RelCo Δ Φ τ ψ x y := by
  have hres : Respects Δ (Δ.cons d)
      (fun i : Fin k => (Term.ofVar i.succ : UExp B (k + 1))) (idU D j) := by
    intro i; simp [DCtx.cons]
  have h := relCo_ground τ Δ (Δ.cons d) Φ
    (fun i : Fin k => (Term.ofVar i.succ : UExp B (k + 1))) (idU D j) (ψ.cons s) hres hx hy
  rwa [Scaling.pull_id, Scaling.pull_weaken] at h

/-- Instantiating a dimension variable, for `RelCo`. -/
theorem relCo_substDim {j k : ℕ} (Δ : DCtx D j k) (Φ : Scaling D j)
    (τ : Ty B D (j + 1) k) (d : DExp D j) (ψ : Scaling B k)
    {x y : Ty.den τ} {x' y' : Ty.den (τ.substDim d)} (hx : HEq x x') (hy : HEq y y') :
    RelCo Δ Φ (τ.substDim d) ψ x' y'
      ↔ RelCo Δ.weakenDim (Φ.cons (Φ.logScale d)) τ ψ x y := by
  have hres : Respects Δ.weakenDim Δ (idU B k) (Fin.cons d (idU D j)) := by
    intro i; simp [DCtx.weakenDim, substU_weaken_cons, idU]
  have h := relCo_ground τ Δ.weakenDim Δ Φ (idU B k) (Fin.cons d (idU D j)) ψ hres hx hy
  rwa [Scaling.pull_id, Scaling.pull_subst] at h

/-- Weakening under a dimension binder, for `RelCo`. -/
theorem relCo_weakenDim {j k : ℕ} (Δ : DCtx D j k) (Φ : Scaling D j) (t : ℝ)
    (τ : Ty B D j k) (ψ : Scaling B k)
    {x y : Ty.den τ} {x' y' : Ty.den (Ty.weakenDim τ)} (hx : HEq x x') (hy : HEq y y') :
    RelCo Δ.weakenDim (Φ.cons t) (Ty.weakenDim τ) ψ x' y' ↔ RelCo Δ Φ τ ψ x y := by
  have hres : Respects Δ Δ.weakenDim (idU B k)
      (fun i : Fin j => (Term.ofVar i.succ : DExp D (j + 1))) := by
    intro i; simp [DCtx.weakenDim, idU]
  have h := relCo_ground τ Δ Δ.weakenDim (Φ.cons t) (idU B k)
    (fun i : Fin j => (Term.ofVar i.succ : DExp D (j + 1))) ψ hres hx hy
  rwa [Scaling.pull_id, Scaling.pull_weaken] at h

/-- Environments related coherently, pointwise. -/
def RelEnvCo : (Γ : Ctx B D j k) → DCtx D j k → Scaling D j → Scaling B k →
    Env Γ → Env Γ → Prop
  | [], _, _, _, _, _ => True
  | τ :: Γ, Δ, Φ, ψ, ρ, ρ' => RelCo Δ Φ τ ψ ρ.1 ρ'.1 ∧ RelEnvCo Γ Δ Φ ψ ρ.2 ρ'.2

theorem relCo_lookup : ∀ {Γ : Ctx B D j k} {τ : Ty B D j k} (n : ℕ) (h : Γ[n]? = some τ)
    {Δ : DCtx D j k} {Φ : Scaling D j} {ψ : Scaling B k} {ρ ρ' : Env Γ},
    RelEnvCo Γ Δ Φ ψ ρ ρ' → RelCo Δ Φ τ ψ (Env.lookup n h ρ) (Env.lookup n h ρ')
  | [], _, _, h, _, _, _, _, _, _ => absurd h (by simp)
  | _ :: _, _, 0, h, _, _, _, _, _, hr => by
      obtain rfl := Option.some.inj h
      exact hr.1
  | _ :: _, _, n + 1, _, _, _, _, _, _, hr => relCo_lookup n _ hr.2

theorem relEnvCo_weaken : ∀ (Γ : Ctx B D j k) (Δ : DCtx D j k) (Φ : Scaling D j)
    (d : DExp D j) (ψ : Scaling B k) (s : ℝ) (ρ ρ' : Env Γ), RelEnvCo Γ Δ Φ ψ ρ ρ' →
    RelEnvCo Γ.weaken (Δ.cons d) Φ (ψ.cons s) (Env.weaken ρ) (Env.weaken ρ')
  | [], _, _, _, _, _, _, _, _ => trivial
  | τ :: Γ, Δ, Φ, d, ψ, s, ρ, ρ', h =>
      ⟨(relCo_weaken Δ Φ d τ ψ s (cast_heq _ _).symm (cast_heq _ _).symm).mpr h.1,
       relEnvCo_weaken Γ Δ Φ d ψ s ρ.2 ρ'.2 h.2⟩

theorem relEnvCo_weakenDim : ∀ (Γ : Ctx B D j k) (Δ : DCtx D j k) (Φ : Scaling D j)
    (t : ℝ) (ψ : Scaling B k) (ρ ρ' : Env Γ), RelEnvCo Γ Δ Φ ψ ρ ρ' →
    RelEnvCo Γ.weakenDim Δ.weakenDim (Φ.cons t) ψ (Env.weakenDim ρ) (Env.weakenDim ρ')
  | [], _, _, _, _, _, _, _ => trivial
  | τ :: Γ, Δ, Φ, t, ψ, ρ, ρ', h =>
      ⟨(relCo_weakenDim Δ Φ t τ ψ (cast_heq _ _).symm (cast_heq _ _).symm).mpr h.1,
       relEnvCo_weakenDim Γ Δ Φ t ψ ρ.2 ρ'.2 h.2⟩

/-! ## Two syntactic conditions

Both are properties of *terms*, not of derivations. That is legitimate because
derivations are unique (`Subsingleton (HasTy Δ Γ e τ)`), so a predicate on terms
is exactly as expressive and considerably simpler. -/

/-- A term is **parametric** when it never names a unit and never takes a root.

Both exclusions are forced, and for different reasons.

`ucon u : Q u` denotes the number `1`, so self-relatedness would demand
`1 = ψ(u) · 1`, false for any scaling that actually moves the unit. **A term
that can name a unit can detect a rescaling.** This is why Kennedy's calculus
has no unit constants, and why his "converting kg into lb" example rewrites the
literals rather than the environment: `1.0<kg>` becomes `2.2<lb>`. Λs *does*
have unit constants, because a language needs them; the cost is that they sit
outside the invariance theory, and this predicate is where that is recorded.

`root` is excluded because `relQ_rpow` needs `0 ≤ x`, and admitting it here would
mean denoting quantities by non-negative reals, which `log` would then break.
That is Kennedy's positivity assumption appearing as a genuine constraint on the
domain rather than a footnote. -/
def Tm.Parametric : {j k : ℕ} → Tm B D j k → Prop
  | _, _, .var _ => True
  | _, _, .lam _ b => b.Parametric
  | _, _, .app f a => f.Parametric ∧ a.Parametric
  | _, _, .lit _ => True
  | _, _, .ucon _ => False
  | _, _, .mul a b => a.Parametric ∧ b.Parametric
  | _, _, .div a b => a.Parametric ∧ b.Parametric
  | _, _, .add a b => a.Parametric ∧ b.Parametric
  | _, _, .root _ _ => False
  | _, _, .idx a _ => a.Parametric
  | _, _, .mapp f x => f.Parametric ∧ x.Parametric
  | _, _, .comp f g => f.Parametric ∧ g.Parametric
  | _, _, .log a => a.Parametric
  | _, _, .exp a => a.Parametric
  | _, _, .ulam _ b => b.Parametric
  | _, _, .uapp f _ => f.Parametric
  | _, _, .dlam b => b.Parametric
  | _, _, .dapp f _ => f.Parametric
  | _, _, .convert a _ _ => a.Parametric

/-- A term is **convert-free** when it contains no conversion.

This is the syntactic condition that decides which fundamental theorem applies,
and it is a property of terms rather than of types: no type forces a term to
convert. That is why the parametricity split does not live in the quantifier. -/
def Tm.ConvertFree : {j k : ℕ} → Tm B D j k → Prop
  | _, _, .var _ => True
  | _, _, .lam _ b => b.ConvertFree
  | _, _, .app f a => f.ConvertFree ∧ a.ConvertFree
  | _, _, .lit _ => True
  | _, _, .ucon _ => True
  | _, _, .mul a b => a.ConvertFree ∧ b.ConvertFree
  | _, _, .div a b => a.ConvertFree ∧ b.ConvertFree
  | _, _, .add a b => a.ConvertFree ∧ b.ConvertFree
  | _, _, .root _ a => a.ConvertFree
  | _, _, .idx a _ => a.ConvertFree
  | _, _, .mapp f x => f.ConvertFree ∧ x.ConvertFree
  | _, _, .comp f g => f.ConvertFree ∧ g.ConvertFree
  | _, _, .log a => a.ConvertFree
  | _, _, .exp a => a.ConvertFree
  | _, _, .ulam _ b => b.ConvertFree
  | _, _, .uapp f _ => f.ConvertFree
  | _, _, .dlam b => b.ConvertFree
  | _, _, .dapp f _ => f.ConvertFree
  | _, _, .convert _ _ _ => False


/-- Variable lookup respects the relation. -/
theorem rel_lookup : ∀ {Γ : Ctx B D j k} {τ : Ty B D j k} (n : ℕ) (h : Γ[n]? = some τ)
    {ψ : Scaling B k} {ρ ρ' : Env Γ}, RelEnv Γ ψ ρ ρ' →
    Rel τ ψ (Env.lookup n h ρ) (Env.lookup n h ρ')
  | [], _, _, h, _, _, _, _ => absurd h (by simp)
  | _ :: _, _, 0, h, _, _, _, hr => by
      obtain rfl := Option.some.inj h
      exact hr.1
  | _ :: _, _, n + 1, _, _, _, _, hr => rel_lookup n _ hr.2

/-- **Weakening an environment preserves relatedness**, at whatever factor the
fresh unit variable is given. This is what lets the body of a `Λu` appeal to the
induction hypothesis. -/
theorem relEnv_weaken : ∀ (Γ : Ctx B D j k) (ψ : Scaling B k) (s : ℝ) (ρ ρ' : Env Γ),
    RelEnv Γ ψ ρ ρ' → RelEnv Γ.weaken (ψ.cons s) (Env.weaken ρ) (Env.weaken ρ')
  | [], _, _, _, _, _ => trivial
  | τ :: Γ, ψ, s, ρ, ρ', h =>
      ⟨(rel_weaken τ ψ s (cast_heq _ _).symm (cast_heq _ _).symm).mpr h.1,
       relEnv_weaken Γ ψ s ρ.2 ρ'.2 h.2⟩

/-- The same under a dimension binder, where nothing moves at all. -/
theorem relEnv_weakenDim : ∀ (Γ : Ctx B D j k) (ψ : Scaling B k) (ρ ρ' : Env Γ),
    RelEnv Γ ψ ρ ρ' → RelEnv Γ.weakenDim ψ (Env.weakenDim ρ) (Env.weakenDim ρ')
  | [], _, _, _, _ => trivial
  | τ :: Γ, ψ, ρ, ρ', h =>
      ⟨(rel_weakenDim τ ψ (cast_heq _ _).symm (cast_heq _ _).symm).mpr h.1,
       relEnv_weakenDim Γ ψ ρ.2 ρ'.2 h.2⟩

/-! ## Independence of the valuation

A convert-free term cannot read how big a metre is. Stating that as *"it denotes
the same thing under `V` and `V'`"* is too naive once unit abstraction is in the
language: at `e[μ]` the two readings consult the family at `V μ` and at `V' μ`,
which are different points. For a `Λu` body the family is constant and nothing
goes wrong, but a *free* variable of quantified type has whatever family the
environment supplies, and that need not be constant.

The fix is the usual one: state it as a logical relation. `Indep` is equality at
every observable type and, at `∀u:δ. τ`, relates the two families **at
independent indices**, which is exactly the constancy the naive statement
silently assumed. -/

/-- Two denotations are **independent of the valuation** when they agree
observably, and their unit-indexed families agree at *any* two indices. -/
def Indep : {j k : ℕ} → (τ : Ty B D j k) → Ty.den τ → Ty.den τ → Prop
  | _, _, .Q _, x, y => x = y
  | _, _, .arrow a b, f, g => ∀ x y, Indep a x y → Indep b (f x) (g y)
  | _, _, .vec _, v, w => v = w
  | _, _, .lin _ _, A, C => A = C
  | _, _, .all _ τ, F, G => ∀ r r' : ℝ, Indep τ (F r) (G r')
  | _, _, .allDim τ, F, G => Indep τ F G

/-- Heterogeneous equalities transfer an equation across a type equality. -/
theorem eq_iff_of_heq {α β : Sort _} {x y : α} {x' y' : β}
    (hx : HEq x x') (hy : HEq y y') : x' = y' ↔ x = y := by
  have hαβ : α = β := type_eq_of_heq hx
  subst hαβ; cases hx; cases hy; rfl

/-- **Independence transports along grounding.** Simpler than `rel_ground`,
because `Indep` does not mention units at all. -/
theorem indep_ground : ∀ {j k : ℕ} (τ : Ty B D j k) {j₀ k₀ : ℕ}
    (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀)
    {x y : Ty.den τ} {x' y' : Ty.den (Ty.ground η δ τ)}, HEq x x' → HEq y y' →
    (Indep (Ty.ground η δ τ) x' y' ↔ Indep τ x y) := by
  intro j k τ
  induction τ with
  | Q u => intro _ _ _ _ x y x' y' hx hy; exact eq_iff_of_heq hx hy
  | vec V => intro _ _ _ _ x y x' y' hx hy; exact eq_iff_of_heq hx hy
  | lin V W => intro _ _ _ _ x y x' y' hx hy; exact eq_iff_of_heq hx hy
  | arrow a b iha ihb =>
    intro _ _ η δ x y x' y' hx hy
    have ha := Ty.den_ground a η δ
    have hb := Ty.den_ground b η δ
    constructor
    · intro h p q hpq
      exact (ihb η δ (heq_app ha.symm hb.symm hx (cast_heq ha.symm p).symm)
          (heq_app ha.symm hb.symm hy (cast_heq ha.symm q).symm)).mp
        (h _ _ ((iha η δ (cast_heq ha.symm p).symm (cast_heq ha.symm q).symm).mpr hpq))
    · intro h p' q' hpq'
      exact (ihb η δ (heq_app ha.symm hb.symm hx (cast_heq ha p'))
          (heq_app ha.symm hb.symm hy (cast_heq ha q'))).mpr
        (h _ _ ((iha η δ (cast_heq ha p') (cast_heq ha q')).mp hpq'))
  | all d τ ih =>
    intro _ _ η δ x y x' y' hx hy
    have hτ := Ty.den_ground τ (liftU η) δ
    show (∀ r r' : ℝ, Indep (Ty.ground (liftU η) δ τ) (x' r) (y' r'))
      ↔ ∀ r r' : ℝ, Indep τ (x r) (y r')
    constructor
    · intro h r r'
      exact (ih (liftU η) δ (heq_app rfl hτ.symm hx (HEq.refl r))
        (heq_app rfl hτ.symm hy (HEq.refl r'))).mp (h r r')
    · intro h r r'
      exact (ih (liftU η) δ (heq_app rfl hτ.symm hx (HEq.refl r))
        (heq_app rfl hτ.symm hy (HEq.refl r'))).mpr (h r r')
  | allDim τ ih => intro _ _ η δ x y x' y' hx hy; exact ih η (liftU δ) hx hy

/-- Environments independent of the valuation, pointwise. -/
def IndepEnv : (Γ : Ctx B D j k) → Env Γ → Env Γ → Prop
  | [], _, _ => True
  | τ :: Γ, ρ, ρ' => Indep τ ρ.1 ρ'.1 ∧ IndepEnv Γ ρ.2 ρ'.2

theorem indep_lookup : ∀ {Γ : Ctx B D j k} {τ : Ty B D j k} (n : ℕ) (h : Γ[n]? = some τ)
    {ρ ρ' : Env Γ}, IndepEnv Γ ρ ρ' → Indep τ (Env.lookup n h ρ) (Env.lookup n h ρ')
  | [], _, _, h, _, _, _ => absurd h (by simp)
  | _ :: _, _, 0, h, _, _, hr => by obtain rfl := Option.some.inj h; exact hr.1
  | _ :: _, _, n + 1, _, _, _, hr => indep_lookup n _ hr.2

theorem indepEnv_weaken : ∀ (Γ : Ctx B D j k) (ρ ρ' : Env Γ), IndepEnv Γ ρ ρ' →
    IndepEnv Γ.weaken (Env.weaken ρ) (Env.weaken ρ')
  | [], _, _, _ => trivial
  | τ :: Γ, ρ, ρ', h =>
      ⟨(indep_ground τ _ _ (cast_heq _ _).symm (cast_heq _ _).symm).mpr h.1,
       indepEnv_weaken Γ ρ.2 ρ'.2 h.2⟩

theorem indepEnv_weakenDim : ∀ (Γ : Ctx B D j k) (ρ ρ' : Env Γ), IndepEnv Γ ρ ρ' →
    IndepEnv Γ.weakenDim (Env.weakenDim ρ) (Env.weakenDim ρ')
  | [], _, _, _ => trivial
  | τ :: Γ, ρ, ρ', h =>
      ⟨(indep_ground τ _ _ (cast_heq _ _).symm (cast_heq _ _).symm).mpr h.1,
       indepEnv_weakenDim Γ ρ.2 ρ'.2 h.2⟩

/-- **A convert-free term cannot read the valuation.**

Note that `ucon` is *not* excluded: naming a unit breaks parametricity, but it
does not read how big that unit is: `ucon u` denotes `1` whatever `u` is worth.
Only `convert` consults the valuation, which is the precise sense in which units
are static. -/
theorem den_indep : ∀ {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
    {e : Tm B D j k} {τ : Ty B D j k} (d : HasTy Δ Γ e τ), e.ConvertFree →
    ∀ (V V' : Scaling B k) {ρ ρ' : Env Γ}, IndepEnv Γ ρ ρ' →
      Indep τ (den V d ρ) (den V' d ρ') := by
  intro j k Δ Γ e τ d
  induction d with
  | var h => intro _ _ _ _ _ hr; exact indep_lookup _ h hr
  | lam b ih => intro hf V V' ρ ρ' hr x y hxy; exact ih hf V V' ⟨hxy, hr⟩
  | app f a ihf iha =>
    intro hf V V' ρ ρ' hr; exact ihf hf.1 V V' hr _ _ (iha hf.2 V V' hr)
  | lit => intro _ _ _ _ _ _; rfl
  | ucon => intro _ _ _ _ _ _; rfl
  | mul a b iha ihb =>
    intro hf V V' ρ ρ' hr
    show _ * _ = _ * _; rw [iha hf.1 V V' hr, ihb hf.2 V V' hr]
  | div a b iha ihb =>
    intro hf V V' ρ ρ' hr
    show _ / _ = _ / _; rw [iha hf.1 V V' hr, ihb hf.2 V V' hr]
  | add a b iha ihb =>
    intro hf V V' ρ ρ' hr
    show _ + _ = _ + _; rw [iha hf.1 V V' hr, ihb hf.2 V V' hr]
  | root hn a ih =>
    intro hf V V' ρ ρ' hr
    show _ ^ _ = _ ^ _; rw [ih hf V V' hr]
  | idx a hu ih =>
    intro hf V V' ρ ρ' hr
    show den V a ρ _ = den V' a ρ' _; rw [ih hf V V' hr]
  | mapp f x ihf ihx =>
    intro hf V V' ρ ρ' hr
    show (fun a => ∑ i, den V f ρ a i * den V x ρ i)
        = fun a => ∑ i, den V' f ρ' a i * den V' x ρ' i
    rw [ihf hf.1 V V' hr, ihx hf.2 V V' hr]
  | comp f g ihf ihg =>
    intro hf V V' ρ ρ' hr
    show (fun a i => ∑ b, den V f ρ a b * den V g ρ b i)
        = fun a i => ∑ b, den V' f ρ' a b * den V' g ρ' b i
    rw [ihf hf.1 V V' hr, ihg hf.2 V V' hr]
  | log a ih =>
    intro hf V V' ρ ρ' hr; show Real.log _ = Real.log _; rw [ih hf V V' hr]
  | exp a ih =>
    intro hf V V' ρ ρ' hr; show Real.exp _ = Real.exp _; rw [ih hf V V' hr]
  | ulam b ih =>
    intro hf V V' ρ ρ' hr r r'
    exact ih hf (V.cons r) (V'.cons r') (indepEnv_weaken _ ρ ρ' hr)
  | uapp f hd ihf =>
    intro hf V V' ρ ρ' hr
    exact (indep_ground _ _ _ (cast_heq _ _).symm (cast_heq _ _).symm).mpr
      (ihf hf V V' hr _ _)
  | dlam b ih =>
    intro hf V V' ρ ρ' hr; exact ih hf V V' (indepEnv_weakenDim _ ρ ρ' hr)
  | dapp f ihf =>
    intro hf V V' ρ ρ' hr
    exact (indep_ground _ _ _ (cast_heq _ _).symm (cast_heq _ _).symm).mpr
      (ihf hf V V' hr)
  | convert a hsd ih => intro hf _ _ _ _ _; exact absurd hf not_false

/-- **The valuation is invisible to closed convert-free terms.** A program that
does not convert cannot tell you how big a metre is.

This is the precise sense in which units are static, and it is stated for closed
terms because that is where it is true: an open term may have a free variable of
quantified type whose family the environment chooses non-constantly, and then
the two readings land at different indices. `den_indep` is the general form. -/
theorem den_eq_of_convertFree {j k : ℕ} {Δ : DCtx D j k} {e : Tm B D j k}
    {u : UExp B k} (d : HasTy Δ ([] : Ctx B D j k) e (.Q u)) (hf : e.ConvertFree)
    (V V' : Scaling B k) : den V d PUnit.unit = den V' d PUnit.unit :=
  den_indep d hf V V' trivial

/-- **The fundamental theorem, for coherent rescalings.**

Every parametric term (conversions and all) is related to itself at its type,
under every rescaling that factors through dimension.

`convert` is the only operation that pays, and this is where it pays: the case
is `conv_invariant_of_coherent` together with coherence at the converted pair.
Every other case is the convert-free proof unchanged, read at `RelCo`.

Note what the `Λu` case does *not* need: no side condition, no quantification
over admissible extensions. The factor the bound unit receives is `Φ δ`,
determined by its dimension, because a coherent rescaling *is* a rescaling of
dimensions. That is the sense in which coherence is exactly what conversion
under a binder forces. -/
theorem fundamental : ∀ {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
    {e : Tm B D j k} {τ : Ty B D j k} (d : HasTy Δ Γ e τ), e.Parametric →
    ∀ (V ψ : Scaling B k) (Φ : Scaling D j), ψ.Factors Δ Φ → ∀ {ρ ρ' : Env Γ},
      RelEnvCo Γ Δ Φ ψ ρ ρ' → RelCo Δ Φ τ ψ (den V d ρ) (den (V.comp ψ) d ρ') := by
  intro j k Δ Γ e τ d
  induction d with
  | var h => intro _ _ _ _ _ _ _ hr; exact relCo_lookup _ h hr
  | lam b ih => intro hp V ψ Φ hΦ ρ ρ' hr x y hxy; exact ih hp V ψ Φ hΦ ⟨hxy, hr⟩
  | app f a ihf iha =>
    intro hp V ψ Φ hΦ ρ ρ' hr
    exact ihf hp.1 V ψ Φ hΦ hr _ _ (iha hp.2 V ψ Φ hΦ hr)
  | lit => intro _ _ ψ _ _ _ _ _; exact relQ_lit ψ _
  | ucon => intro hp _ _ _ _ _ _ _; exact absurd hp not_false
  | mul a b iha ihb =>
    intro hp V ψ Φ hΦ ρ ρ' hr
    exact relQ_mul (iha hp.1 V ψ Φ hΦ hr) (ihb hp.2 V ψ Φ hΦ hr)
  | div a b iha ihb =>
    intro hp V ψ Φ hΦ ρ ρ' hr
    exact relQ_div (iha hp.1 V ψ Φ hΦ hr) (ihb hp.2 V ψ Φ hΦ hr)
  | add a b iha ihb =>
    intro hp V ψ Φ hΦ ρ ρ' hr
    exact relQ_add (iha hp.1 V ψ Φ hΦ hr) (ihb hp.2 V ψ Φ hΦ hr)
  | root hn a ih => intro hp _ _ _ _ _ _ _; exact absurd hp not_false
  | idx a hu ih =>
    intro hp V ψ Φ hΦ ρ ρ' hr
    have h := ih hp V ψ Φ hΦ hr ⟨_, (List.getElem?_eq_some_iff.mp hu).1⟩
    rw [List.get_eq_getElem, (List.getElem?_eq_some_iff.mp hu).2] at h
    exact h
  | mapp f x ihf ihx =>
    intro hp V ψ Φ hΦ ρ ρ' hr a
    have hF := ihf hp.1 V ψ Φ hΦ hr
    have hX := ihx hp.2 V ψ Φ hΦ hr
    show (∑ i, den (V.comp ψ) f ρ' a i * den (V.comp ψ) x ρ' i)
      = _ * ∑ i, den V f ρ a i * den V x ρ i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hF a i, hX i]
    have := ne_of_gt (ψ.scale_pos ((_ : Sp B _).get i))
    field_simp
  | comp f g ihf ihg =>
    intro hp V ψ Φ hΦ ρ ρ' hr a i
    have hF := ihf hp.1 V ψ Φ hΦ hr
    have hG := ihg hp.2 V ψ Φ hΦ hr
    show (∑ b, den (V.comp ψ) f ρ' a b * den (V.comp ψ) g ρ' b i)
      = _ * ∑ b, den V f ρ a b * den V g ρ b i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hF a b, hG b i]
    have h1 := ne_of_gt (ψ.scale_pos ((_ : Sp B _).get b))
    field_simp
  | log a ih => intro hp V ψ Φ hΦ ρ ρ' hr; exact relQ_log (ih hp V ψ Φ hΦ hr)
  | exp a ih => intro hp V ψ Φ hΦ ρ ρ' hr; exact relQ_exp (ih hp V ψ Φ hΦ hr)
  | ulam b ih =>
    intro hp V ψ Φ hΦ ρ ρ' hr r
    have h := ih hp (V.cons r) (ψ.cons (Φ.logScale _)) Φ (hΦ.cons _)
      (relEnvCo_weaken _ _ Φ _ ψ _ ρ ρ' hr)
    rwa [Scaling.comp_cons] at h
  | uapp f hd ihf =>
    intro hp V ψ Φ hΦ ρ ρ' hr
    refine (relCo_subst _ Φ _ _ ψ (cast_heq _ _).symm (cast_heq _ _).symm).mpr ?_
    rw [Scaling.logScale_comp, hΦ.logScale, hd]
    exact ihf hp V ψ Φ hΦ hr _
  | dlam b ih =>
    intro hp V ψ Φ hΦ ρ ρ' hr t
    exact ih hp V ψ (Φ.cons t) (hΦ.weakenDim t) (relEnvCo_weakenDim _ _ Φ t ψ ρ ρ' hr)
  | dapp f ihf =>
    intro hp V ψ Φ hΦ ρ ρ' hr
    exact (relCo_substDim _ Φ _ _ ψ (cast_heq _ _).symm
      (cast_heq _ _).symm).mpr (ihf hp V ψ Φ hΦ hr _)
  | convert a hsd ih =>
    intro hp V ψ Φ hΦ ρ ρ' hr
    have hIH := ih hp V ψ Φ hΦ hr
    show den (V.comp ψ) a ρ' * conv (V.comp ψ) _ _ = ψ.scale _ * (den V a ρ * conv V _ _)
    rw [show den (V.comp ψ) a ρ' = ψ.scale _ * den V a ρ from hIH,
        conv_invariant_of_coherent V hΦ.coherent hsd, hΦ.coherent _ _ hsd]
    ring

/-- **The fundamental theorem, unconditionally, for convert-free terms.**

Every parametric, convert-free term is related to itself at its type, under
*every* scaling. This is Kennedy's theorem, and it is the version the Pi theorem
consumes, now at the whole calculus rather than a first-order fragment, so the
quantifier cases are present and carry their weight.

Rescaling acts on the declared valuation as well as on the environment, which is
why `V` appears on one side and `V.comp ψ` on the other.

The three binder cases are where the work is. `Λu` extends both valuation and
scaling and appeals to `relEnv_weaken`; `e[μ]` reads the family at `μ`'s
magnitude on one side and at the *rescaled* magnitude on the other, which is
exactly `logScale_comp`; `Λδ` and `e{d}` move nothing, because dimensions have
no magnitudes. -/
theorem fundamental_free : ∀ {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
    {e : Tm B D j k} {τ : Ty B D j k} (d : HasTy Δ Γ e τ),
    e.Parametric → e.ConvertFree → ∀ (V ψ : Scaling B k) {ρ ρ' : Env Γ},
      RelEnv Γ ψ ρ ρ' → Rel τ ψ (den V d ρ) (den (V.comp ψ) d ρ') := by
  intro j k Δ Γ e τ d
  induction d with
  | var h => intro _ _ _ _ _ _ hr; exact rel_lookup _ h hr
  | lam b ih =>
    intro hp hf V ψ ρ ρ' hr x y hxy
    exact ih hp hf V ψ ⟨hxy, hr⟩
  | app f a ihf iha =>
    intro hp hf V ψ ρ ρ' hr
    exact ihf hp.1 hf.1 V ψ hr _ _ (iha hp.2 hf.2 V ψ hr)
  | lit => intro _ _ _ ψ _ _ _; exact relQ_lit ψ _
  | ucon => intro hp _ _ _ _ _ _; exact absurd hp not_false
  | mul a b iha ihb =>
    intro hp hf V ψ ρ ρ' hr
    exact relQ_mul (iha hp.1 hf.1 V ψ hr) (ihb hp.2 hf.2 V ψ hr)
  | div a b iha ihb =>
    intro hp hf V ψ ρ ρ' hr
    exact relQ_div (iha hp.1 hf.1 V ψ hr) (ihb hp.2 hf.2 V ψ hr)
  | add a b iha ihb =>
    intro hp hf V ψ ρ ρ' hr
    exact relQ_add (iha hp.1 hf.1 V ψ hr) (ihb hp.2 hf.2 V ψ hr)
  | root hn a ih => intro hp _ _ _ _ _ _; exact absurd hp not_false
  | idx a hu ih =>
    intro hp hf V ψ ρ ρ' hr
    have h := ih hp hf V ψ hr ⟨_, (List.getElem?_eq_some_iff.mp hu).1⟩
    rw [List.get_eq_getElem, (List.getElem?_eq_some_iff.mp hu).2] at h
    exact h
  | mapp f x ihf ihx =>
    intro hp hf V ψ ρ ρ' hr a
    have hF := ihf hp.1 hf.1 V ψ hr
    have hX := ihx hp.2 hf.2 V ψ hr
    show (∑ i, den (V.comp ψ) f ρ' a i * den (V.comp ψ) x ρ' i)
      = _ * ∑ i, den V f ρ a i * den V x ρ i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hF a i, hX i]
    have := ne_of_gt (ψ.scale_pos ((_ : Sp B _).get i))
    field_simp
  | comp f g ihf ihg =>
    intro hp hf V ψ ρ ρ' hr a i
    have hF := ihf hp.1 hf.1 V ψ hr
    have hG := ihg hp.2 hf.2 V ψ hr
    show (∑ b, den (V.comp ψ) f ρ' a b * den (V.comp ψ) g ρ' b i)
      = _ * ∑ b, den V f ρ a b * den V g ρ b i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hF a b, hG b i]
    have h1 := ne_of_gt (ψ.scale_pos ((_ : Sp B _).get b))
    field_simp
  | log a ih => intro hp hf V ψ ρ ρ' hr; exact relQ_log (ih hp hf V ψ hr)
  | exp a ih => intro hp hf V ψ ρ ρ' hr; exact relQ_exp (ih hp hf V ψ hr)
  | ulam b ih =>
    intro hp hf V ψ ρ ρ' hr r s
    have h := ih hp hf (V.cons r) (ψ.cons s) (relEnv_weaken _ ψ s ρ ρ' hr)
    rwa [Scaling.comp_cons] at h
  | uapp f hd ihf =>
    intro hp hf V ψ ρ ρ' hr
    refine (rel_subst _ _ ψ (cast_heq _ _).symm (cast_heq _ _).symm).mpr ?_
    rw [Scaling.logScale_comp]
    exact ihf hp hf V ψ hr _ _
  | dlam b ih =>
    intro hp hf V ψ ρ ρ' hr
    exact ih hp hf V ψ (relEnv_weakenDim _ ψ ρ ρ' hr)
  | dapp f ihf =>
    intro hp hf V ψ ρ ρ' hr
    exact (rel_substDim _ _ ψ (cast_heq _ _).symm (cast_heq _ _).symm).mpr (ihf hp hf V ψ hr)
  | convert a hsd ih => intro _ hf _ _ _ _ _; exact absurd hf not_false



/-! ## Coherence is necessary, not merely sufficient

The theorems above say coherence *suffices*. This section says it is *forced*:
one conversion, applied to a nonzero argument, is scale-invariant exactly when
the scaling identifies the two units.

So `fundamental`'s hypothesis is not an artifact of the proof. A term that
converts can detect any rescaling that separates units of the same dimension,
and the coherent scalings are precisely the ones it cannot detect. -/

/-! ## The canonical one-conversion program -/

/-- `convert x u v`, with `x` the sole free variable. -/
def cvtTm {j k : ℕ} (u v : UExp B k) : Tm B D j k := .convert (.var 0) u v

/-- Its derivation. -/
def cvtDeriv {j k : ℕ} {Δ : DCtx D j k} {u v : UExp B k} (h : SameDim Δ u v) :
    HasTy Δ [Ty.Q u] (cvtTm u v) (.Q v) := .convert (.var rfl) h

/-- **Coherence at a pair is exactly what one conversion requires.**

Left to right is the converse of `fundamental`, restricted to this term: if the
relation holds for a nonzero input then the scaling must identify `u` and `v`.
Right to left is `fundamental` itself.

The hypothesis `x ≠ 0` is necessary and not a technicality: the zero function is
invariant under everything, which is the same degeneracy that makes
`eq_zero_of_relQ_self` true. -/
theorem cvt_rel_iff_coherent {j k : ℕ} {Δ : DCtx D j k} {u v : UExp B k}
    (h : SameDim Δ u v) (V ψ : Scaling B k) {x : ℝ} (hx : x ≠ 0) :
    Rel (.Q v) ψ (den V (cvtDeriv h) (x, PUnit.unit))
        (den (V.comp ψ) (cvtDeriv h) (ψ.scale u * x, PUnit.unit))
      ↔ ψ.scale u = ψ.scale v := by
  have hpu := ψ.scale_pos u
  have hpv := ψ.scale_pos v
  have hcv : conv V u v ≠ 0 := conv_ne_zero V u v
  show (ψ.scale u * x) * conv (V.comp ψ) u v = ψ.scale v * (x * conv V u v) ↔ _
  rw [conv_comp]
  constructor
  · intro heq
    have hcancel : ψ.scale u * ψ.scale u = ψ.scale v * ψ.scale v := by
      have h0 : (ψ.scale u * ψ.scale u) * (x * conv V u v)
          = (ψ.scale v * ψ.scale v) * (x * conv V u v) := by
        field_simp at heq ⊢
        nlinarith [heq]
      exact mul_right_cancel₀ (mul_ne_zero hx hcv) h0
    nlinarith [hpu, hpv, hcancel]
  · intro heq
    rw [heq]
    have := ne_of_gt hpv
    field_simp

/-- **Scaling invariance for closed terms.** A closed convert-free term of scalar
type denotes a number invariant under *every* rescaling of the units, which
forces it to be zero unless its unit is trivial.

The immediate corollary, and the reason `ucon` had to be excluded from
`Parametric`: a term that could name a unit would be a counterexample. -/
theorem closed_invariant {j k : ℕ} {Δ : DCtx D j k} {e : Tm B D j k} {u : UExp B k}
    (d : HasTy Δ ([] : Ctx B D j k) e (.Q u)) (hp : e.Parametric) (hf : e.ConvertFree)
    (V ψ : Scaling B k) : den V d PUnit.unit = ψ.scale u * den V d PUnit.unit := by
  have h := fundamental_free d hp hf V ψ (ρ := PUnit.unit) (ρ' := PUnit.unit) trivial
  rwa [den_eq_of_convertFree d hf (V.comp ψ) V] at h

/-! ## The bridge to first-order signatures

The fundamental theorem states scale-invariance for an arbitrary type. The Pi
theorem needs it in the specific shape of a first-order signature: `n` scalar
arguments and a scalar result. That is what this section extracts. -/

/-- The context of scalar types for a list of argument units. -/
def scalarCtx (us : List (UExp B k)) : Ctx B D j k := us.map Ty.Q

/-- Rescale an environment of scalars componentwise. -/
noncomputable def scaleEnv (ψ : Scaling B k) :
    (us : List (UExp B k)) → Env (scalarCtx (D := D) (j := j) us) →
      Env (scalarCtx (D := D) (j := j) us)
  | [], ρ => ρ
  | u :: us, ρ => (ψ.scale u * ρ.1, scaleEnv ψ us ρ.2)

/-- An environment is related to its own rescaling. -/
theorem relEnv_scaleEnv (ψ : Scaling B k) :
    ∀ (us : List (UExp B k)) (ρ : Env (scalarCtx (D := D) (j := j) us)),
      RelEnv (scalarCtx (D := D) (j := j) us) ψ ρ (scaleEnv (D := D) (j := j) ψ us ρ)
  | [], _ => trivial
  | _ :: us, ρ => ⟨rfl, relEnv_scaleEnv ψ us ρ.2⟩

/-- An environment of scalars is trivially independent of the valuation: at
scalar type the relation is equality, and the environment is compared with
itself. -/
theorem indepEnv_scalarCtx : ∀ (us : List (UExp B k))
    (ρ : Env (scalarCtx (D := D) (j := j) us)), IndepEnv (scalarCtx (D := D) (j := j) us) ρ ρ
  | [], _ => trivial
  | _ :: us, ρ => ⟨rfl, indepEnv_scalarCtx us ρ.2⟩

/-- **The scaling law of a first-order term**, derived from the fundamental
theorem.

Rescaling every argument by the scale factor of its unit rescales the result by
the scale factor of *its* unit. This is the hypothesis the Pi theorem consumes,
now supplied by an actual well-typed term rather than assumed.

Stated for **convert-free** terms, and that restriction is what makes the Pi
theorem's unrestricted quantification over scalings legitimate: a term that
converts obeys the law only for coherent `ψ`, which is not enough freedom for
the argument the Pi theorem runs. -/
theorem scaleLaw {j k : ℕ} {Δ : DCtx D j k} {e : Tm B D j k} {us : List (UExp B k)}
    {u₀ : UExp B k} (d : HasTy Δ (scalarCtx us) e (.Q u₀)) (hp : e.Parametric)
    (hf : e.ConvertFree) (V ψ : Scaling B k)
    (ρ : Env (scalarCtx (D := D) (j := j) us)) :
    den V d (scaleEnv ψ us ρ) = ψ.scale u₀ * den V d ρ := by
  have h := fundamental_free d hp hf V ψ (relEnv_scaleEnv ψ us ρ)
  rwa [den_indep d hf (V.comp ψ) V (indepEnv_scalarCtx us (scaleEnv ψ us ρ))] at h

/-- A program using two unit constants, with the constants as free variables:
`x / y` at type `Q (u/v)`. This is `1 u / 1 v` with `ucon` compiled away. -/
def velocityTm {j k : ℕ} : Tm B D j k := .div (.var 0) (.var 1)

/-- Its derivation, in the context of the two constants. -/
def velocityDeriv {j k : ℕ} {Δ : DCtx D j k} (u v : UExp B k) :
    HasTy Δ (scalarCtx [u, v]) velocityTm (.Q (Term.div u v)) :=
  .div (.var rfl) (.var rfl)

theorem velocityTm_parametric {j k : ℕ} :
    (velocityTm : Tm B D j k).Parametric := ⟨trivial, trivial⟩

theorem velocityTm_convertFree {j k : ℕ} :
    (velocityTm : Tm B D j k).ConvertFree := ⟨trivial, trivial⟩

/-- **A program that mentions units is scale-invariant once its constants scale
with it.**

Supplying "one `u`" and "one `v`" gives one answer; supplying the *rescaled*
constants gives that answer times the scale factor of `u/v`. Derived straight
from the fundamental theorem, with the environment relation carrying the whole
content: each constant is related to its rescaled self. -/
theorem velocity_scales {j k : ℕ} {Δ : DCtx D j k} (u v : UExp B k)
    (V ψ : Scaling B k) (ρ : Env (scalarCtx (D := D) (j := j) [u, v])) :
    den V (velocityDeriv (Δ := Δ) u v) (scaleEnv ψ [u, v] ρ)
      = ψ.scale (Term.div u v) * den V (velocityDeriv (Δ := Δ) u v) ρ :=
  scaleLaw _ velocityTm_parametric velocityTm_convertFree V ψ ρ





/-! ## Where unit constants belong

The exclusion of `ucon` is not a hole in the theorem; it locates a design
decision.

A term that names a unit is not scale-invariant, and it *should not be*. `1.3 m`
is a definite physical quantity, but the number `1.3` is its magnitude *in
metres*. Rescale the metre and the same quantity has a different magnitude, so
the numeral must change with it, which is exactly why Kennedy's kg-to-lb
example rewrites `1.0<kg>` as `2.2<lb>` rather than leaving the program alone.

The fix is to stop treating unit constants as *term* constructors and treat them
as **environment entries**: precisely Kennedy's "pervasive environment", now
with a reason rather than a convention. A program mentioning metres is a program
with a free variable standing for *one metre*, and it is scale-invariant
relative to environments that scale that variable along with everything else.

Nothing new is needed: `ucon u` compiles to a variable in a context prefixed by
the unit constants, and the fundamental theorem applies unchanged. `velocityTm`
and `velocity_scales` above are the whole construction. -/





end LambdaS

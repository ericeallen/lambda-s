import LambdaS.Fundamental

/-!
# What invariance detects

`fundamental` says a parametric term is scale-invariant for coherent scalings,
and `fundamental_free` says a parametric convert-free term is invariant for
*all* of them — parametric meaning no `ucon` and no `root`.
This file proves the converse: invariance under all scalings detects **exactly**
the conversions that do something.

## The theorem that is not available

The tempting statement — "invariant under all scalings implies definable" — is
false, and not for any interesting reason. Take `f x = π · x` at type
`Q u → Q u`. It satisfies the scaling law for every `ψ`, since `f (k·x) = k·f x`.
No term denotes it: literals are rational, and the arithmetic of Λs over
rationals and the input cannot produce `π`. Definability results of that shape fail in System F
too, and units have nothing to do with it.

So the right target is not definability in general but a completeness result for
`convert` in particular. That is what is proved here.

## The theorem that is available

Call a conversion **inert** when it converts a unit to itself. An inert
conversion multiplies by `conv V u u = 1`, so it is denotationally invisible;
`exists_convertFree_of_inert` turns a term whose conversions are all inert
into a convert-free term with the same denotation.

The converse is `cvt_invariant_iff_eq`: a single conversion applied to a nonzero
argument is invariant under *all* scalings if and only if `u = v` on the nose.
Not "same dimension" — literally the same exponent vector. The mechanism is
`scale_eq_iff`: scalings separate points of the unit group, so `∀ψ, ψ.scale u =
ψ.scale v` collapses to `u = v`.

Putting the two together, for the canonical conversion program the three
conditions

* invariant under every scaling,
* inert,
* denotationally convert-free,

coincide. Coherent invariance, by contrast, is strictly weaker and holds for
every conversion between same-dimension units — and that gap is exactly what
conversion costs.

## And the first-order dichotomy

`scaleLaw_forces_zero` is the general form of `NonDef.convert_not_definable`: if
a first-order term's result unit mentions a base unit that none of its arguments
mention, then all-scalings invariance forces the term to denote zero. This is
`Pi.eq_zero_of_appears_once` — the pendulum argument — reappearing as a
statement about terms rather than about exponent matrices.
-/

namespace LambdaS

open scoped BigOperators

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [UnitSys B D] {j k : ℕ}
variable {Δ : DCtx D j k}

/-! ## Scalings separate units -/

/-- The scaling that reads off one base coordinate. -/
noncomputable def Scaling.coord (b : B) : Scaling B k :=
  ⟨fun b' => if b' = b then 1 else 0, fun _ => 0⟩

/-- The scaling that reads off one unit-variable coordinate. -/
noncomputable def Scaling.coordVar (i : Fin k) : Scaling B k :=
  ⟨fun _ => 0, fun i' => if i' = i then 1 else 0⟩

@[simp] theorem Scaling.scale_coord (b : B) (u : UExp B k) :
    (Scaling.coord (k := k) b).scale u = Real.exp (u.base b) := by
  simp only [scale, logScale, coord]
  congr 1
  rw [Finset.sum_eq_single b] <;> simp_all

@[simp] theorem Scaling.scale_coordVar (i : Fin k) (u : UExp B k) :
    (Scaling.coordVar (B := B) i).scale u = Real.exp (u.vars i) := by
  simp only [scale, logScale, coordVar]
  congr 1
  rw [Finset.sum_eq_single i] <;> simp_all

/-- **Scalings separate units.** Two unit expressions are scaled alike by every
scaling exactly when they are the same exponent vector.

This is what makes all-scalings invariance so much stronger than coherent
invariance: coherence identifies units of equal dimension, whereas quantifying
over every scaling identifies nothing at all. -/
theorem scale_eq_iff {u v : UExp B k} :
    (∀ ψ : Scaling B k, ψ.scale u = ψ.scale v) ↔ u = v := by
  constructor
  · intro h
    refine Term.ext' (funext fun b => ?_) (funext fun i => ?_)
    · have hb := h (Scaling.coord b)
      rw [Scaling.scale_coord, Scaling.scale_coord, Real.exp_eq_exp] at hb
      exact_mod_cast hb
    · have hi := h (Scaling.coordVar i)
      rw [Scaling.scale_coordVar, Scaling.scale_coordVar, Real.exp_eq_exp] at hi
      exact_mod_cast hi
  · rintro rfl _; rfl

/-! ## Inert conversions

A conversion is **inert** when it converts a unit to itself, so multiplies by
`1`. That is much stronger than the typing side condition, which asks only for
equal dimensions. -/

/-- A term's conversions are all inert. -/
def Tm.Inert : {j k : ℕ} → Tm B D j k → Prop
  | _, _, .var _ => True
  | _, _, .lam _ b => b.Inert
  | _, _, .app f a => f.Inert ∧ a.Inert
  | _, _, .lit _ => True
  | _, _, .ucon _ => True
  | _, _, .mul a b => a.Inert ∧ b.Inert
  | _, _, .div a b => a.Inert ∧ b.Inert
  | _, _, .add a b => a.Inert ∧ b.Inert
  | _, _, .root _ a => a.Inert
  | _, _, .idx a _ => a.Inert
  | _, _, .mapp f x => f.Inert ∧ x.Inert
  | _, _, .comp f g => f.Inert ∧ g.Inert
  | _, _, .log a => a.Inert
  | _, _, .exp a => a.Inert
  | _, _, .ulam _ b => b.Inert
  | _, _, .uapp f _ => f.Inert
  | _, _, .dlam b => b.Inert
  | _, _, .dapp f _ => f.Inert
  | _, _, .convert a u v => u = v ∧ a.Inert

/-- Convert-free terms are inert, vacuously. -/
theorem Tm.inert_of_convertFree : ∀ {j k : ℕ} (e : Tm B D j k), e.ConvertFree → e.Inert
  | _, _, .var _, _ => trivial
  | _, _, .lam _ b, h => Tm.inert_of_convertFree b h
  | _, _, .app f a, h => ⟨Tm.inert_of_convertFree f h.1, Tm.inert_of_convertFree a h.2⟩
  | _, _, .lit _, _ => trivial
  | _, _, .ucon _, _ => trivial
  | _, _, .mul a b, h => ⟨Tm.inert_of_convertFree a h.1, Tm.inert_of_convertFree b h.2⟩
  | _, _, .div a b, h => ⟨Tm.inert_of_convertFree a h.1, Tm.inert_of_convertFree b h.2⟩
  | _, _, .add a b, h => ⟨Tm.inert_of_convertFree a h.1, Tm.inert_of_convertFree b h.2⟩
  | _, _, .root _ a, h => Tm.inert_of_convertFree a h
  | _, _, .idx a _, h => Tm.inert_of_convertFree a h
  | _, _, .mapp f x, h => ⟨Tm.inert_of_convertFree f h.1, Tm.inert_of_convertFree x h.2⟩
  | _, _, .comp f g, h => ⟨Tm.inert_of_convertFree f h.1, Tm.inert_of_convertFree g h.2⟩
  | _, _, .log a, h => Tm.inert_of_convertFree a h
  | _, _, .exp a, h => Tm.inert_of_convertFree a h
  | _, _, .ulam _ b, h => Tm.inert_of_convertFree b h
  | _, _, .uapp f _, h => Tm.inert_of_convertFree f h
  | _, _, .dlam b, h => Tm.inert_of_convertFree b h
  | _, _, .dapp f _, h => Tm.inert_of_convertFree f h
  | _, _, .convert _ _ _, h => absurd h not_false

/-- **Inert conversions are removable.** A term whose conversions are all inert
denotes exactly what some convert-free term denotes — at the same type, in every
environment, under every valuation.

Stated over derivations this says what it should: there is another **term**,
convert-free, with a derivation at the same type and the same denotation. Over
an intrinsically typed syntax the term and its derivation are one object, so the
statement could not distinguish them.

Carrying the source unit on `convert` is what makes this work: with `u = v` the
rule is type-preserving, so the conversion can simply be deleted. -/
theorem exists_convertFree_of_inert : ∀ {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
    {e : Tm B D j k} {τ : Ty B D j k} (d : HasTy Δ Γ e τ), e.Inert →
    ∃ (e' : Tm B D j k) (d' : HasTy Δ Γ e' τ), e'.ConvertFree ∧
      (e.Parametric → e'.Parametric) ∧
      ∀ (V : Scaling B k) (ρ : Env Γ), den V d' ρ = den V d ρ := by
  intro j k Δ Γ e τ d
  induction d with
  | var h => intro _; exact ⟨_, .var h, trivial, id, fun _ _ => rfl⟩
  | lam b ih =>
    intro hi
    obtain ⟨b', d', hf, hp, hd⟩ := ih hi
    exact ⟨_, .lam d', hf, hp, fun V ρ => funext fun x => hd V (x, ρ)⟩
  | app f a ihf iha =>
    intro hi
    obtain ⟨f', df, hf1, hp1, hd1⟩ := ihf hi.1
    obtain ⟨a', da, hf2, hp2, hd2⟩ := iha hi.2
    refine ⟨_, .app df da, ⟨hf1, hf2⟩, fun h => ⟨hp1 h.1, hp2 h.2⟩, fun V ρ => ?_⟩
    show (den V df ρ) (den V da ρ) = (den V f ρ) (den V a ρ)
    rw [hd1, hd2]
  | lit =>
    intro _
    refine ⟨_, .lit, ?_, ?_, fun _ _ => rfl⟩
    · trivial
    · exact fun _ => trivial
  | ucon => intro _; exact ⟨_, .ucon, trivial, id, fun _ _ => rfl⟩
  | mul a b iha ihb =>
    intro hi
    obtain ⟨a', da, hf1, hp1, hd1⟩ := iha hi.1
    obtain ⟨b', db, hf2, hp2, hd2⟩ := ihb hi.2
    refine ⟨_, .mul da db, ⟨hf1, hf2⟩, fun h => ⟨hp1 h.1, hp2 h.2⟩, fun V ρ => ?_⟩
    show _ * _ = _ * _; rw [hd1, hd2]
  | div a b iha ihb =>
    intro hi
    obtain ⟨a', da, hf1, hp1, hd1⟩ := iha hi.1
    obtain ⟨b', db, hf2, hp2, hd2⟩ := ihb hi.2
    refine ⟨_, .div da db, ⟨hf1, hf2⟩, fun h => ⟨hp1 h.1, hp2 h.2⟩, fun V ρ => ?_⟩
    show _ / _ = _ / _; rw [hd1, hd2]
  | add a b iha ihb =>
    intro hi
    obtain ⟨a', da, hf1, hp1, hd1⟩ := iha hi.1
    obtain ⟨b', db, hf2, hp2, hd2⟩ := ihb hi.2
    refine ⟨_, .add da db, ⟨hf1, hf2⟩, fun h => ⟨hp1 h.1, hp2 h.2⟩, fun V ρ => ?_⟩
    show _ + _ = _ + _; rw [hd1, hd2]
  | root hn a ih =>
    intro hi
    obtain ⟨a', da, hf, hp, hd⟩ := ih hi
    refine ⟨_, .root hn da, hf, fun h => absurd h not_false, fun V ρ => ?_⟩
    show _ ^ _ = _ ^ _; rw [hd]
  | idx a hu ih =>
    intro hi
    obtain ⟨a', da, hf, hp, hd⟩ := ih hi
    refine ⟨_, .idx da hu, hf, hp, fun V ρ => ?_⟩
    show den V da ρ _ = den V a ρ _; rw [hd]
  | mapp f x ihf ihx =>
    intro hi
    obtain ⟨f', df, hf1, hp1, hd1⟩ := ihf hi.1
    obtain ⟨x', dx, hf2, hp2, hd2⟩ := ihx hi.2
    refine ⟨_, .mapp df dx, ⟨hf1, hf2⟩, fun h => ⟨hp1 h.1, hp2 h.2⟩, fun V ρ => ?_⟩
    show (fun a => ∑ i, den V df ρ a i * den V dx ρ i)
        = fun a => ∑ i, den V f ρ a i * den V x ρ i
    rw [hd1, hd2]
  | comp f g ihf ihg =>
    intro hi
    obtain ⟨f', df, hf1, hp1, hd1⟩ := ihf hi.1
    obtain ⟨g', dg, hf2, hp2, hd2⟩ := ihg hi.2
    refine ⟨_, .comp df dg, ⟨hf1, hf2⟩, fun h => ⟨hp1 h.1, hp2 h.2⟩, fun V ρ => ?_⟩
    show (fun a i => ∑ b, den V df ρ a b * den V dg ρ b i)
        = fun a i => ∑ b, den V f ρ a b * den V g ρ b i
    rw [hd1, hd2]
  | log a ih =>
    intro hi
    obtain ⟨a', da, hf, hp, hd⟩ := ih hi
    refine ⟨_, .log da, hf, hp, fun V ρ => ?_⟩
    show Real.log _ = Real.log _; rw [hd]
  | exp a ih =>
    intro hi
    obtain ⟨a', da, hf, hp, hd⟩ := ih hi
    refine ⟨_, .exp da, hf, hp, fun V ρ => ?_⟩
    show Real.exp _ = Real.exp _; rw [hd]
  | ulam b ih =>
    intro hi
    obtain ⟨b', db, hf, hp, hd⟩ := ih hi
    exact ⟨_, .ulam db, hf, hp, fun V ρ => funext fun r => hd (V.cons r) _⟩
  | uapp f hdim ihf =>
    intro hi
    obtain ⟨f', df, hf, hp, hd⟩ := ihf hi
    refine ⟨_, .uapp df hdim, hf, hp, fun V ρ => ?_⟩
    show cast _ (den V df ρ _) = cast _ (den V f ρ _); rw [hd]
  | dlam b ih =>
    intro hi
    obtain ⟨b', db, hf, hp, hd⟩ := ih hi
    exact ⟨_, .dlam db, hf, hp, fun V ρ => hd V _⟩
  | dapp f ihf =>
    intro hi
    obtain ⟨f', df, hf, hp, hd⟩ := ihf hi
    refine ⟨_, .dapp df, hf, hp, fun V ρ => ?_⟩
    show denDapp _ (den V df ρ) = denDapp _ (den V f ρ); rw [hd]
  | convert a hsd ih =>
    rintro ⟨rfl, hin⟩
    obtain ⟨a', da, hf, hp, hd⟩ := ih hin
    refine ⟨a', da, hf, fun h => hp h, fun V ρ => ?_⟩
    show den V da ρ = den V a ρ * conv V _ _
    rw [hd, conv_self, mul_one]

/-- **Inert terms are invariant under every scaling**, not merely the coherent
ones — because they are convert-free in all but name. -/
theorem fundamental_of_inert {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
    {e : Tm B D j k} {τ : Ty B D j k} (d : HasTy Δ Γ e τ) (hp : e.Parametric)
    (hi : e.Inert) (V ψ : Scaling B k) {ρ ρ' : Env Γ} (hr : RelEnv Γ ψ ρ ρ') :
    Rel τ ψ (den V d ρ) (den (V.comp ψ) d ρ') := by
  obtain ⟨e', d', hf, hpp, hden⟩ := exists_convertFree_of_inert d hi
  rw [← hden V ρ, ← hden (V.comp ψ) ρ']
  exact fundamental_free d' (hpp hp) hf V ψ hr


omit [DecidableEq B] in

omit [DecidableEq B] in

omit [DecidableEq B] in

/-! ## The converse

`cvt_rel_iff_coherent` said invariance of the canonical one-conversion program
under a *given* `ψ` is equivalent to `ψ` identifying the two units. Quantifying
over every `ψ` and applying `scale_eq_iff` collapses that to `u = v`. -/

/-- **All-scalings invariance is exactly inertness**, for the canonical
conversion applied to a nonzero argument.

The three conditions coincide: invariant under every scaling, inert, and — by
`exists_convertFree_of_inert` — denotationally convert-free. Contrast
`fundamental`, which holds for *every* well-typed conversion once the
scalings are restricted to coherent ones. -/
theorem cvt_invariant_iff_eq {u v : UExp B k} (h : SameDim Δ u v)
    (V : Scaling B k) {x : ℝ} (hx : x ≠ 0) :
    (∀ ψ : Scaling B k,
        Rel (.Q v) ψ (den V (cvtDeriv h) (x, PUnit.unit))
            (den (V.comp ψ) (cvtDeriv h) (ψ.scale u * x, PUnit.unit)))
      ↔ u = v := by
  rw [← scale_eq_iff]
  exact forall_congr' fun ψ => cvt_rel_iff_coherent h V ψ hx

/-- Restated as the design claim: a conversion that actually converts is
**detectable**. Some rescaling of the unit system changes what the program
computes, which is the precise sense in which `convert` reads the units. -/
theorem cvt_detectable {u v : UExp B k} (h : SameDim Δ u v) (V : Scaling B k)
    {x : ℝ} (hx : x ≠ 0) (huv : u ≠ v) :
    ∃ ψ : Scaling B k,
      ¬ Rel (.Q v) ψ (den V (cvtDeriv h) (x, PUnit.unit))
          (den (V.comp ψ) (cvtDeriv h) (ψ.scale u * x, PUnit.unit)) := by
  by_contra hc
  push Not at hc
  exact huv ((cvt_invariant_iff_eq h V hx).mp hc)

/-! ## The first-order dichotomy

`NonDef.convert_not_definable` collapsed a function between two distinct base
units to zero. The same argument works for any first-order signature, and the
hypothesis is the pendulum condition: a base unit the result mentions and no
argument does. -/

omit [DecidableEq B] [UnitSys B D] in
/-- Rescaling by a scaling that fixes every argument unit changes nothing. -/
theorem scaleEnv_eq_self (ψ : Scaling B k) :
    ∀ (us : List (UExp B k)), (∀ u ∈ us, ψ.scale u = 1) →
      ∀ ρ : Env (scalarCtx (D := D) (j := j) us), scaleEnv ψ us ρ = ρ
  | [], _, _ => rfl
  | u :: us, h, ρ => by
      have h1 : ψ.scale u = 1 := h u (by simp)
      have hrest := scaleEnv_eq_self ψ us (fun w hw => h w (List.mem_cons_of_mem _ hw)) ρ.2
      show (ψ.scale u * ρ.1, scaleEnv ψ us ρ.2) = ρ
      rw [h1, one_mul, hrest]
      rfl

/-- **Invariance forces zero when the result escapes the arguments.**

If some base unit occurs in the result unit but in no argument unit, then a
first-order function invariant under every scaling is the zero function.

This is the semantic form of the pendulum argument: the scaling that moves only
that base unit fixes every input and moves the output, so the output has nowhere
to go but zero. Compare `Pi.eq_zero_of_appears_once`, which says the same thing
about exponent matrices. -/
theorem scaleLaw_forces_zero {us : List (UExp B k)} {u₀ : UExp B k}
    (f : Env (scalarCtx (D := D) (j := j) us) → ℝ)
    (hlaw : ∀ (ψ : Scaling B k) (ρ : Env (scalarCtx (D := D) (j := j) us)),
      f (scaleEnv ψ us ρ) = ψ.scale u₀ * f ρ)
    (b : B) (hus : ∀ u ∈ us, u.base b = 0) (h0 : u₀.base b ≠ 0)
    (ρ : Env (scalarCtx (D := D) (j := j) us)) : f ρ = 0 := by
  have hfix : ∀ u ∈ us, (Scaling.coord (k := k) b).scale u = 1 := by
    intro u hu; simp [Scaling.scale_coord, hus u hu]
  have hmove : (Scaling.coord (k := k) b).scale u₀ ≠ 1 := by
    rw [Scaling.scale_coord]
    intro hcon
    have hz : Real.exp ((u₀.base b : ℝ)) = Real.exp 0 := by rw [hcon, Real.exp_zero]
    exact h0 (by exact_mod_cast Real.exp_eq_exp.mp hz)
  have hk := hlaw (Scaling.coord (k := k) b) ρ
  rw [scaleEnv_eq_self _ us hfix ρ] at hk
  have hz : (1 - (Scaling.coord (k := k) b).scale u₀) * f ρ = 0 := by linarith [hk]
  rcases mul_eq_zero.mp hz with hc | hc
  · exact absurd (by linarith [hc] : (Scaling.coord (k := k) b).scale u₀ = 1) hmove
  · exact hc

/-- The dichotomy for actual terms: a first-order term whose result unit escapes
its arguments denotes zero, if it is invariant under every scaling. Otherwise it
is not invariant — so by the contrapositive of `fundamental_free` it is not
both parametric and convert-free. -/
theorem forced_zero {us : List (UExp B k)} {u₀ : UExp B k} {e : Tm B D j k}
    (d : HasTy Δ (scalarCtx us) e (.Q u₀)) (V : Scaling B k)
    (hlaw : ∀ (ψ : Scaling B k) (ρ : Env (scalarCtx (D := D) (j := j) us)),
      den V d (scaleEnv ψ us ρ) = ψ.scale u₀ * den V d ρ)
    (b : B) (hus : ∀ u ∈ us, u.base b = 0) (h0 : u₀.base b ≠ 0)
    (ρ : Env (scalarCtx (D := D) (j := j) us)) : den V d ρ = 0 :=
  scaleLaw_forces_zero (den V d) hlaw b hus h0 ρ

/-! ### Trivial ratios -/

omit [DecidableEq B] in
@[simp] theorem Term.one_mul' {V : Type} (t : Term B V) : Term.mul 1 t = t := by
  refine Term.ext' (funext fun b => ?_) (funext fun i => ?_) <;> simp

omit [DecidableEq B] in
@[simp] theorem Term.mul_one' {V : Type} (t : Term B V) : Term.mul t 1 = t := by
  refine Term.ext' (funext fun b => ?_) (funext fun i => ?_) <;> simp

omit [DecidableEq B] in
@[simp] theorem Term.div_one' {V : Type} (t : Term B V) : Term.div t 1 = t := by
  refine Term.ext' (funext fun b => ?_) (funext fun i => ?_) <;> simp

omit [Fintype B] [DecidableEq B] in
/-- A ratio is trivial exactly when its two units agree. The unit group is
torsion-free and cancellative, so `u/v = 1` really does mean `u = v`. -/
theorem div_eq_one_iff {u v : UExp B k} : Term.div u v = 1 ↔ u = v := by
  constructor
  · intro h
    refine Term.ext' (funext fun b => ?_) (funext fun i => ?_)
    · have := congrArg (fun t => Term.base t b) h; simp at this; linarith [this]
    · have := congrArg (fun t => Term.vars t i) h; simp at this; linarith [this]
  · rintro rfl
    refine Term.ext' (funext fun b => ?_) (funext fun i => ?_) <;> simp

end LambdaS
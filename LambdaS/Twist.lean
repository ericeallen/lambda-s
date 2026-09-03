/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Ratio
import LambdaS.Definability
import LambdaS.Adequacy

/-!
# Accumulated conversion ratios, over first-order syntax

`LambdaS.Definability` proves that a *single* conversion is detectable, and that
a term whose conversions are all inert is invariant under every scaling. Between
those lies the general question: a term may convert many times, and what matters
is whether the conversions **cancel**.

`Twist` assigns a term its accumulated ratio, an element of `Tw`, the
first-order ratio syntax of `LambdaS.Ratio`. Multiplication multiplies ratios,
division divides them, addition forces its branches to agree, and `convert u v`
contributes `u/v`. Abstraction binds a ratio variable and application applies
one, which is what carries the analysis past first order.

## What the first-order ratios buy here

Unit and dimension abstraction are present, which they could not be while ratios
were a function space: `Λu. e` has the ratio of its body one unit scope out, and
`e[μ]` records the instantiation. The old `TwistTy` had `PUnit` at both
quantifiers because there was no way to transport a function space along a
substitution.

The ratio context `Θ` is an index of the relation rather than a function of `Γ`.
That is deliberate: `Ctx.shapes Γ.weaken = Ctx.shapes Γ` is a theorem, not a
definitional equality, so tying `Θ` to `Γ` would put a transport in every binder
rule. Keeping it free puts the correspondence in the `var` rule, where it is one
hypothesis.

`Tw.castShape` appears at `uapp` and `dapp` for the same reason in the other
index: the result type is `τ.subst σ`, and `Ty.shape_subst` is a theorem.
-/

namespace LambdaS

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D]

/-- **The conversion-ratio semantics.** A second reading of Λs, valued in the
ratio syntax, running alongside `den`.

Addition forces its branches to agree, which is what makes the ratio a property
of a term rather than of a path through it. -/
inductive Twist : {j k : ℕ} → {Δ : DCtx D j k} → {Γ : Ctx B D j k} →
    {e : Tm B D j k} → {τ : Ty B D j k} → (Θ : List Shape) →
    HasTy Δ Γ e τ → Tw B k Θ (Ty.shape τ) → Prop where
  | var {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {τ n Θ} (h : Γ[n]? = some τ)
      (h' : Θ[n]? = some (Ty.shape τ)) :
      Twist (Δ := Δ) Θ (.var h) (.var n h')
  | lam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {σ τ e Θ}
      {d : HasTy Δ (σ :: Γ) e τ} {t : Tw B k (Ty.shape σ :: Θ) (Ty.shape τ)} :
      Twist (Ty.shape σ :: Θ) d t → Twist Θ (.lam d) (.lam t)
  | app {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {σ τ f a Θ}
      {df : HasTy Δ Γ f (.arrow σ τ)} {da : HasTy Δ Γ a σ}
      {tf : Tw B k Θ (Ty.shape (Ty.arrow σ τ))} {ta : Tw B k Θ (Ty.shape σ)} :
      Twist Θ df tf → Twist Θ da ta → Twist Θ (.app df da) (.app tf ta)
  | lit {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {q Θ} :
      Twist (Δ := Δ) (Γ := Γ) Θ (.lit (q := q)) (.unit 1)
  | mul {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u v a b Θ}
      {da : HasTy Δ Γ a (.Q u)} {db : HasTy Δ Γ b (.Q v)} {s t : Tw B k Θ .scalar} :
      Twist Θ da s → Twist Θ db t → Twist Θ (.mul da db) (.mul s t)
  | div {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u v a b Θ}
      {da : HasTy Δ Γ a (.Q u)} {db : HasTy Δ Γ b (.Q v)} {s t : Tw B k Θ .scalar} :
      Twist Θ da s → Twist Θ db t → Twist Θ (.div da db) (.div s t)
  | add {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u a b Θ}
      {da : HasTy Δ Γ a (.Q u)} {db : HasTy Δ Γ b (.Q u)} {s t : Tw B k Θ .scalar}
      (heq : ∀ (ψ : Scaling B k) (θρ : TwEnv Θ), Tw.eval ψ s θρ = Tw.eval ψ t θρ) :
      Twist Θ da s → Twist Θ db t → Twist Θ (.add da db) s
  | convert {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u v a Θ}
      {da : HasTy Δ Γ a (.Q u)} {s : Tw B k Θ .scalar} (h : SameDim Δ u v) :
      Twist Θ da s → Twist Θ (.convert da h) (.mul s (.div (.unit u) (.unit v)))
  | ulam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {d τ e Θ}
      {db : HasTy (Δ.cons d) Γ.weaken e τ} {t : Tw B (k + 1) Θ (Ty.shape τ)} :
      Twist Θ db t → Twist Θ (.ulam db) (.ulam t)
  | uapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f d τ σ Θ}
      {df : HasTy Δ Γ f (.all d τ)} {t : Tw B k Θ (Ty.shape (Ty.all d τ))}
      (hd : dimOf Δ σ = d) :
      Twist Θ df t →
      Twist Θ (.uapp df hd) (Tw.castShape (Ty.shape_subst τ σ).symm (.uapp t σ))
  | dlam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {τ e Θ}
      {db : HasTy Δ.weakenDim Γ.weakenDim e τ} {t : Tw B k Θ (Ty.shape τ)} :
      Twist Θ db t → Twist Θ (.dlam db) t
  | dapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f τ Θ} {d : DExp D j}
      {df : HasTy Δ Γ f (.allDim τ)} {t : Tw B k Θ (Ty.shape τ)} :
      Twist Θ df t →
      Twist Θ (.dapp df) (Tw.castShape (Ty.shape_substDim τ d).symm t)

/-! ## The scaling law with a twist -/

/-- Environments related at given ratios, pointwise. The `cons` rule carries an
equation of shapes rather than demanding a definitional match, because under
`ulam` the context is `Γ.weaken` and `Ty.shape (Ty.weaken τ) = Ty.shape τ` is a
theorem. Localizing the transport here keeps it out of every other rule. -/
inductive TwRelEnv {j k : ℕ} (ψ : Scaling B k) :
    (Γ : Ctx B D j k) → (Θ : List Shape) → TwEnv Θ → Env Γ → Env Γ → Prop where
  | nil {θρ : TwEnv []} {ρ ρ' : Env ([] : Ctx B D j k)} :
      TwRelEnv ψ [] [] θρ ρ ρ'
  | cons {τ : Ty B D j k} {Γ : Ctx B D j k} {s : Shape} {Θ : List Shape}
      {θρ : TwEnv (s :: Θ)} {ρ ρ' : Env (τ :: Γ)}
      (hs : s = Ty.shape τ) :
      TwRel τ (hs ▸ θρ.1) ψ ρ.1 ρ'.1 → TwRelEnv ψ Γ Θ θρ.2 ρ.2 ρ'.2 →
      TwRelEnv ψ (τ :: Γ) (s :: Θ) θρ ρ ρ'

/-- Looking up related environments. -/
theorem twRelEnv_lookup {j k : ℕ} {ψ : Scaling B k} : ∀ {Γ : Ctx B D j k}
    {Θ : List Shape} {θρ : TwEnv Θ} {ρ ρ' : Env Γ}, TwRelEnv ψ Γ Θ θρ ρ ρ' →
    ∀ {τ : Ty B D j k} (n : ℕ) (h : Γ[n]? = some τ) (h' : Θ[n]? = some (Ty.shape τ)),
    TwRel τ (TwEnv.lookup n h' θρ) ψ (Env.lookup n h ρ) (Env.lookup n h ρ') := by
  intro Γ Θ θρ ρ ρ' henv
  induction henv with
  | nil => intro τ n h; exact absurd h (by simp)
  | @cons τ Γ s Θ θρ ρ ρ' hs hw hrest ih =>
    intro σ n h h'
    cases n with
    | zero =>
      obtain rfl := Option.some.inj h
      obtain rfl := Option.some.inj h'
      exact hw
    | succ n => exact ih n (by simpa using h) (by simpa using h')

/-- **Weakening related environments under a unit binder.** The value
environments are retyped by `Env.weaken`; the ratio environment is untouched,
because shape is blind to units, which is the entire design working as
intended. -/
theorem twRelEnv_weaken {j k : ℕ} {ψ : Scaling B k} (s : ℝ) :
    ∀ {Γ : Ctx B D j k} {Θ : List Shape} {θρ : TwEnv Θ} {ρ ρ' : Env Γ},
    TwRelEnv ψ Γ Θ θρ ρ ρ' →
    TwRelEnv (ψ.cons s) Γ.weaken Θ θρ (Env.weaken ρ) (Env.weaken ρ') := by
  intro Γ Θ θρ ρ ρ' h
  induction h with
  | nil => exact TwRelEnv.nil
  | @cons τ Γ sh Θ θρ ρ ρ' hs hw hrest ih =>
    subst hs
    refine TwRelEnv.cons (Ty.shape_weaken τ).symm ?_ ih
    exact (twRel_weaken τ ψ s (w := θρ.1) (eqRec_heq _ _).symm
      (cast_heq _ _).symm (cast_heq _ _).symm).mpr hw

/-- The same under a dimension binder, where nothing at all moves. -/
theorem twRelEnv_weakenDim {j k : ℕ} {ψ : Scaling B k} :
    ∀ {Γ : Ctx B D j k} {Θ : List Shape} {θρ : TwEnv Θ} {ρ ρ' : Env Γ},
    TwRelEnv ψ Γ Θ θρ ρ ρ' →
    TwRelEnv ψ Γ.weakenDim Θ θρ (Env.weakenDim ρ) (Env.weakenDim ρ') := by
  intro Γ Θ θρ ρ ρ' h
  induction h with
  | nil => exact TwRelEnv.nil
  | @cons τ Γ sh Θ θρ ρ ρ' hs hw hrest ih =>
    subst hs
    refine TwRelEnv.cons (Ty.shape_weakenDim τ).symm ?_ ih
    refine (twRel_ground τ (idU B k) (fun i => Term.ofVar i.succ) ψ
      (w := θρ.1) (eqRec_heq _ _).symm
      (cast_heq _ _).symm (cast_heq _ _).symm).mpr ?_
    rwa [Scaling.pull_id]

private theorem div_twist (xu xv xs xt A Bv : ℝ) :
    (xu * (xs * xs) * A) / (xv * (xt * xt) * Bv)
      = xu / xv * (xs / xt * (xs / xt)) * (A / Bv) := by
  rw [mul_div_mul_comm, mul_div_mul_comm, mul_div_mul_comm]

/-- **The scaling law with a twist.** A term whose conversions accumulate to `t`
rescales by its type's factor times the *square* of `t`'s value: both readings
carry the conversion factor, so it appears twice. At trivial ratio this is the
fundamental theorem.

Now proved at the whole calculus: the binder cases are the ones `TwistTy` could
not state. -/
theorem Twist.scaling : ∀ {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
    {e : Tm B D j k} {τ : Ty B D j k} {Θ : List Shape}
    {d : HasTy Δ Γ e τ} {t : Tw B k Θ (Ty.shape τ)}, Twist Θ d t →
    ∀ (V ψ : Scaling B k) (θρ : TwEnv Θ) {ρ ρ' : Env Γ},
      TwRelEnv ψ Γ Θ θρ ρ ρ' →
      TwRel τ (Tw.eval ψ t θρ) ψ (den V d ρ) (den (V.comp ψ) d ρ') := by
  intro j k Δ Γ e τ Θ d t ht
  induction ht with
  | var h h' => intro V ψ θρ ρ ρ' hr; exact twRelEnv_lookup hr _ h h'
  | lam htb ih =>
    intro V ψ θρ ρ ρ' hr r x y hxy
    exact ih V ψ (r, θρ) (TwRelEnv.cons rfl hxy hr)
  | app htf hta ihf iha =>
    intro V ψ θρ ρ ρ' hr
    exact ihf V ψ θρ hr _ _ _ (iha V ψ θρ hr)
  | @lit _ _ _ _ q _ =>
    intro V ψ θρ ρ ρ' _
    show (den (V.comp ψ) (HasTy.lit (q := q)) ρ' : ℝ)
        = ψ.scale 1 * (Tw.eval ψ (Tw.unit 1) θρ * Tw.eval ψ (Tw.unit 1) θρ)
          * den V (HasTy.lit (q := q)) ρ
    show ((q : ℚ) : ℝ) = ψ.scale 1 * (ψ.scale 1 * ψ.scale 1) * ((q : ℚ) : ℝ)
    simp
  | @mul _ _ _ _ _ _ _ _ _ da db st tt hta htb iha ihb =>
    intro V ψ θρ ρ ρ' hr
    have h1 := iha V ψ θρ hr
    have h2 := ihb V ψ θρ hr
    simp only [TwRel] at h1 h2
    show den (V.comp ψ) (da.mul db) ρ'
        = ψ.scale (Term.mul _ _)
          * (Tw.eval ψ (st.mul tt) θρ * Tw.eval ψ (st.mul tt) θρ)
          * den V (da.mul db) ρ
    show den (V.comp ψ) da ρ' * den (V.comp ψ) db ρ'
        = _ * _ * (den V da ρ * den V db ρ)
    rw [h1, h2, Scaling.scale_mul]
    show _ = _ * (Tw.eval ψ st θρ * Tw.eval ψ tt θρ
        * (Tw.eval ψ st θρ * Tw.eval ψ tt θρ)) * _
    ring
  | @div _ _ _ _ _ _ _ _ _ da db st tt hta htb iha ihb =>
    intro V ψ θρ ρ ρ' hr
    have h1 := iha V ψ θρ hr
    have h2 := ihb V ψ θρ hr
    simp only [TwRel] at h1 h2
    show den (V.comp ψ) (da.div db) ρ'
        = ψ.scale (Term.div _ _)
          * (Tw.eval ψ (st.div tt) θρ * Tw.eval ψ (st.div tt) θρ)
          * den V (da.div db) ρ
    show den (V.comp ψ) da ρ' / den (V.comp ψ) db ρ'
        = _ * _ * (den V da ρ / den V db ρ)
    rw [h1, h2, Scaling.scale_div]
    show _ = _ * (Tw.eval ψ st θρ / Tw.eval ψ tt θρ
        * (Tw.eval ψ st θρ / Tw.eval ψ tt θρ)) * _
    exact div_twist _ _ _ _ _ _
  | @add _ _ _ _ _ _ _ _ da db st tt heq hta htb iha ihb =>
    intro V ψ θρ ρ ρ' hr
    have h1 := iha V ψ θρ hr
    have h2 := ihb V ψ θρ hr
    simp only [TwRel] at h1 h2
    show den (V.comp ψ) (da.add db) ρ'
        = ψ.scale _ * (Tw.eval ψ st θρ * Tw.eval ψ st θρ) * den V (da.add db) ρ
    show den (V.comp ψ) da ρ' + den (V.comp ψ) db ρ'
        = _ * _ * (den V da ρ + den V db ρ)
    rw [h1, h2, heq ψ θρ]
    ring
  | @convert _ _ _ _ u v _ _ da st h hta ih =>
    intro V ψ θρ ρ ρ' hr
    have h1 := ih V ψ θρ hr
    simp only [TwRel] at h1
    show den (V.comp ψ) (da.convert h) ρ'
        = ψ.scale v
          * (Tw.eval ψ (st.mul ((Tw.unit u).div (Tw.unit v))) θρ
            * Tw.eval ψ (st.mul ((Tw.unit u).div (Tw.unit v))) θρ)
          * den V (da.convert h) ρ
    show den (V.comp ψ) da ρ' * conv (V.comp ψ) u v
        = _ * _ * (den V da ρ * conv V u v)
    rw [h1, conv_comp]
    show _ = _ * (Tw.eval ψ st θρ * (ψ.scale u / ψ.scale v)
        * (Tw.eval ψ st θρ * (ψ.scale u / ψ.scale v))) * _
    have hv : ∀ w : UExp B _, ψ.scale w ≠ 0 := fun w => ne_of_gt (ψ.scale_pos w)
    rw [conv]
    field_simp
    try ring
  | @ulam _ _ _ _ _ _ _ _ db tb htb ih =>
    intro V ψ θρ ρ ρ' hr r s
    have h := ih (V.cons r) (ψ.cons s) θρ (twRelEnv_weaken s hr)
    show TwRel _ (Tw.eval (ψ.cons s) tb θρ) (ψ.cons s)
      (den (V.cons r) db (Env.weaken ρ)) (den ((V.comp ψ).cons (r + s)) db (Env.weaken ρ'))
    rwa [← Scaling.comp_cons]
  | @uapp _ _ _ _ _ _ τ σ _ df tf hd htf ihf =>
    intro V ψ θρ ρ ρ' hr
    have h := ihf V ψ θρ hr
    have hIH := h (V.logScale σ) (ψ.logScale σ)
    rw [Tw.eval_castShape]
    refine (twRel_subst τ σ ψ (w := Tw.eval ψ (Tw.uapp tf σ) θρ)
      ?_ (cast_heq _ _).symm (cast_heq _ _).symm).mpr ?_
    · exact (eqRec_heq _ _).symm
    · show TwRel τ (Tw.eval ψ tf θρ (ψ.logScale σ)) (ψ.cons (ψ.logScale σ))
        (den V df ρ (V.logScale σ)) (den (V.comp ψ) df ρ' ((V.comp ψ).logScale σ))
      rw [Scaling.logScale_comp]
      exact hIH
  | dlam htb ih =>
    intro V ψ θρ ρ ρ' hr
    exact ih V ψ θρ (twRelEnv_weakenDim hr)
  | @dapp _ _ _ _ _ τ _ dm df tf htf ihf =>
    intro V ψ θρ ρ ρ' hr
    have h := ihf V ψ θρ hr
    rw [Tw.eval_castShape]
    refine (twRel_substDim τ dm ψ (w := Tw.eval ψ tf θρ)
      (eqRec_heq _ _).symm (cast_heq _ _).symm (cast_heq _ _).symm).mpr h

/-! ## The characterization at first order

A term of scalar type over a context of scalars: a program computing a number
from numbers, whatever abstraction and application it uses inside. Its ratio is
a closed scalar `Tw`, and the characterization says: the program obeys the
unrestricted scaling law exactly when that ratio's value is `1` under every
scaling. The next section makes that condition *syntactic*, and hence decidable.
-/

/-- Scalar contexts and their shape lists. -/
@[simp] theorem shapes_scalarCtx {j k : ℕ} (us : List (UExp B k)) :
    Ctx.shapes (scalarCtx (D := D) (j := j) us) = us.map fun _ => Shape.scalar := by
  simp [Ctx.shapes, scalarCtx, List.map_map, Function.comp_def, Ty.shape]

/-- A scalar environment is related to its own rescaling at trivial ratios. -/
theorem twRelEnv_scaleEnv {j k : ℕ} (ψ : Scaling B k) :
    ∀ (us : List (UExp B k)) (ρ : Env (scalarCtx (D := D) (j := j) us)),
    TwRelEnv ψ (scalarCtx us) (us.map fun _ => Shape.scalar)
      (oneTwEnv (us.map fun _ => Shape.scalar)) ρ (scaleEnv ψ us ρ)
  | [], _ => TwRelEnv.nil
  | u :: us, ρ => by
      refine TwRelEnv.cons rfl ?_ (twRelEnv_scaleEnv ψ us ρ.2)
      show ψ.scale u * ρ.1 = ψ.scale u * ((1 : ℝ) * 1) * ρ.1
      ring

/-- **Invariance under all scalings forces the ratio's value to `1`.**

The general converse for any term of scalar type over a context of scalars,
higher-order structure and unit polymorphism inside the term included. A nonzero
denotation obeying the scaling law for *every* scaling has a ratio worth `1`
under every scaling.

Compare `fundamental`, which gives the law for coherent scalings and no
conclusion at all about the ratio: coherence is precisely blind to conversion,
which is why the two theorems are the two halves of one story. -/
theorem Twist.eq_one_of_invariant {j k : ℕ} {Δ : DCtx D j k} {us : List (UExp B k)}
    {u : UExp B k} {e : Tm B D j k} {d : HasTy Δ (scalarCtx us) e (.Q u)}
    {t : Tw B k (us.map fun _ => Shape.scalar) .scalar}
    (ht : Twist _ d t) (V : Scaling B k)
    {ρ : Env (scalarCtx (D := D) (j := j) us)} (hne : den V d ρ ≠ 0)
    (hinv : ∀ ψ : Scaling B k,
        den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ)
    (ψ : Scaling B k) : Tw.eval ψ t (oneTwEnv _) = 1 := by
  have hr := twRelEnv_scaleEnv (D := D) (j := j) ψ us ρ
  have htw := ht.scaling V ψ (oneTwEnv _) hr
  simp only [TwRel] at htw
  rw [hinv ψ] at htw
  have hu := ne_of_gt (ψ.scale_pos u)
  set c := Tw.eval ψ t (oneTwEnv (us.map fun _ => Shape.scalar)) with hc
  have hsq : c * c = 1 := by
    have h0 : ψ.scale u * den V d ρ * (c * c - 1) = 0 := by nlinarith [htw]
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hu
      · exact absurd h' hne
    · linarith [h]
  have hone : PosEnv (us.map fun _ => Shape.scalar)
      (oneTwEnv (us.map fun _ => Shape.scalar)) := by
    clear * -
    induction us with
    | nil => trivial
    | cons u us ih => exact ⟨one_pos, ih⟩
  have hpos : 0 < c := Tw.eval_pos ψ t (oneTwEnv _) hone
  nlinarith [hsq, hpos]

/-- **Cancelling conversions are invisible.** A term whose ratio is worth `1`
under every scaling obeys the unrestricted scaling law, exactly as a
convert-free term does, even though it may convert repeatedly along the way. -/
theorem Twist.invariant_of_eq_one {j k : ℕ} {Δ : DCtx D j k} {us : List (UExp B k)}
    {u : UExp B k} {e : Tm B D j k} {d : HasTy Δ (scalarCtx us) e (.Q u)}
    {t : Tw B k (us.map fun _ => Shape.scalar) .scalar}
    (ht : Twist _ d t)
    (hone : ∀ ψ : Scaling B k, Tw.eval ψ t (oneTwEnv _) = 1)
    (V ψ : Scaling B k) (ρ : Env (scalarCtx (D := D) (j := j) us)) :
    den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ := by
  have hr := twRelEnv_scaleEnv (D := D) (j := j) ψ us ρ
  have htw := ht.scaling V ψ (oneTwEnv _) hr
  simp only [TwRel] at htw
  rw [hone ψ] at htw
  simpa using htw

/-- **The characterization.** For a term of scalar type over a context of
scalars with nonzero denotation, invariance under every scaling holds exactly
when its accumulated ratio is worth `1` under every scaling.

This is `cvt_invariant_iff_eq` for arbitrary terms rather than a single
conversion, and it says precisely what "conversion is the only thing that pays"
means: the payment is the accumulated ratio, and unrestricted parametricity
charges for exactly that and nothing else. The condition on the right is
*semantic*; `Tw.nfOne` decides it syntactically, via `Tw.nfOne_eq_one_iff`. -/
theorem Twist.invariant_iff {j k : ℕ} {Δ : DCtx D j k} {us : List (UExp B k)}
    {u : UExp B k} {e : Tm B D j k} {d : HasTy Δ (scalarCtx us) e (.Q u)}
    {t : Tw B k (us.map fun _ => Shape.scalar) .scalar}
    (ht : Twist _ d t) (V : Scaling B k)
    {ρ : Env (scalarCtx (D := D) (j := j) us)} (hne : den V d ρ ≠ 0) :
    (∀ ψ : Scaling B k,
        den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ)
      ↔ ∀ ψ : Scaling B k, Tw.eval ψ t (oneTwEnv _) = 1 := by
  constructor
  · exact fun hinv ψ => ht.eq_one_of_invariant V hne hinv ψ
  · exact fun hone ψ => ht.invariant_of_eq_one hone V ψ ρ

/-! ### The decision -/

/-- **The normal ratio**: the unit expression a scalar ratio is worth, at the
all-ones environment, with unit variables read as themselves. -/
def Tw.nfOne {k : ℕ} {Θ : List Shape} (t : Tw B k Θ .scalar) : UExp B k :=
  Tw.nf (idU B k) t (SynEnv.ones Θ)

/-- **Triviality of a ratio is decidable.** It is worth `1` under *every*
scaling exactly when its normal form is the unit of the group: an equality in a
free ℚ-vector space, decided coordinatewise.

This is the theorem that turns the characterization into an algorithm. -/
theorem Tw.nfOne_eq_one_iff [DecidableEq B] {k : ℕ} {Θ : List Shape}
    (t : Tw B k Θ .scalar) :
    Tw.nfOne t = 1 ↔ ∀ ψ : Scaling B k, Tw.eval ψ t (oneTwEnv Θ) = 1 := by
  have hval : ∀ ψ : Scaling B k, Tw.eval ψ t (oneTwEnv Θ) = ψ.scale (Tw.nfOne t) := by
    intro ψ
    have h := Tw.nf_correct ψ (idU B k) t (SynEnv.ones Θ) (oneTwEnv Θ)
      (srelEnv_ones ψ Θ)
    rwa [Scaling.pull_id] at h
  constructor
  · intro h1 ψ
    rw [hval ψ, h1, Scaling.scale_one]
  · intro hall
    have : ∀ ψ : Scaling B k, ψ.scale (Tw.nfOne t) = ψ.scale 1 := by
      intro ψ; rw [← hval ψ, hall ψ, Scaling.scale_one]
    exact scale_eq_iff.mp this

/-- **The decidable characterization.** For a first-order program with nonzero
denotation, unrestricted scale invariance holds exactly when the normal form of
its accumulated ratio is the unit of the group: one equality of exponent
vectors, decided coordinatewise.

The compiler diagnostic, as a theorem: check `Tw.nfOne t = 1` and either
conclude the program's result is independent of the unit system, or exhibit the
nontrivial ratio as the reason it is not. -/
theorem Twist.invariant_iff_nfOne {j k : ℕ} {Δ : DCtx D j k} {us : List (UExp B k)}
    {u : UExp B k} {e : Tm B D j k} {d : HasTy Δ (scalarCtx us) e (.Q u)}
    {t : Tw B k (us.map fun _ => Shape.scalar) .scalar}
    (ht : Twist _ d t) (V : Scaling B k)
    {ρ : Env (scalarCtx (D := D) (j := j) us)} (hne : den V d ρ ≠ 0) :
    (∀ ψ : Scaling B k,
        den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ)
      ↔ Tw.nfOne t = 1 :=
  (ht.invariant_iff V hne).trans (Tw.nfOne_eq_one_iff t).symm

/-! ## Computing the ratio

`Twist` is a relation; the compiler needs a function. `twistOf` computes, for a
derivation, a ratio together with its `Twist` derivation, or `none`.

It fails in exactly two circumstances, and they are different in kind. At `add`
the two branches' ratios must be *the same term*, and the check is syntactic:
sound, and incomplete only when the branches compute equal ratios by different
syntax; the semantic question "are these two ratio terms equal in value" is the
one `Tw.nfOne` decides for a *closed* interface, and sharpening the check to it
is possible but not done here. At `root`, `log`, `exp`, `idx`, `mapp`, `comp`
and `ucon` there is no rule to apply. `root` is *inside* the invariance theory
(`Tm.Parametric` admits it, and `fundamental` covers it through `relQ_rpow`),
but its scale factor is a rational power `ψ(u)^(1/n)` and the ratio grammar
`Tw` has no rational-power former, so declining it here is a limitation of
this analysis rather than an exclusion of the theory.
`log` and `exp` are nonlinear, so no
single ratio describes how they move; `idx`, `mapp` and `comp` would need
ratios at space shapes, which `triv` does not carry. And `ucon` names a unit,
which no scaling story survives. -/

/-- Decidable equality of ratio terms at matching indices. Proof fields are
propositions, so `var` compares only its index. -/
def Tw.beq : {k : ℕ} → {Θ : List Shape} → {s : Shape} →
    Tw B k Θ s → Tw B k Θ s → Bool
  | _, _, _, .var n _, .var m _ => n == m
  | _, _, _, .unit u, .unit v => u == v
  | _, _, _, .mul a b, .mul a' b' => a.beq a' && b.beq b'
  | _, _, _, .div a b, .div a' b' => a.beq a' && b.beq b'
  | _, _, _, .lam t, .lam t' => t.beq t'
  | _, _, _, .app (s := s₁) f a, .app (s := s₂) f' a' =>
      if h : s₁ = s₂ then (h ▸ f).beq f' && (h ▸ a).beq a' else false
  | _, _, _, .triv, .triv => true
  | _, _, _, .ulam t, .ulam t' => t.beq t'
  | _, _, _, .uapp t μ, .uapp t' μ' => t.beq t' && μ == μ'
  | _, _, _, _, _ => false

/-- `beq` decides equality. Proof fields vanish by proof irrelevance; the `app`
case pattern-matches the existential shape. -/
theorem Tw.beq_sound : ∀ {k : ℕ} {Θ : List Shape} {s : Shape}
    (t t' : Tw B k Θ s), t.beq t' = true → t = t' := by
  intro k Θ s t
  induction t with
  | var n h =>
    intro t' hb
    cases t' <;> simp [Tw.beq] at hb
    next m h' => subst hb; rfl
  | unit u =>
    intro t' hb
    cases t' <;> simp [Tw.beq] at hb
    next v => subst hb; rfl
  | mul a b iha ihb =>
    intro t' hb
    cases t' <;> simp [Tw.beq] at hb
    next a' b' => rw [iha a' hb.1, ihb b' hb.2]
  | div a b iha ihb =>
    intro t' hb
    cases t' <;> simp [Tw.beq] at hb
    next a' b' => rw [iha a' hb.1, ihb b' hb.2]
  | lam t iht =>
    intro t' hb
    cases t' <;> simp [Tw.beq] at hb
    next t'' => rw [iht t'' hb]
  | @app _ _ s₁ _ f a ihf iha =>
    intro t' hb
    cases t' with
    | var n h => exact Bool.noConfusion hb
    | unit u => exact Bool.noConfusion hb
    | mul a b => exact Bool.noConfusion hb
    | div a b => exact Bool.noConfusion hb
    | lam t => exact Bool.noConfusion hb
    | triv => exact Bool.noConfusion hb
    | ulam t => exact Bool.noConfusion hb
    | uapp t μ => exact Bool.noConfusion hb
    | app f' a' =>
      simp only [Tw.beq] at hb
      split at hb
      · next h =>
        subst h
        simp only [Bool.and_eq_true] at hb
        rw [ihf f' hb.1, iha a' hb.2]
      · exact absurd hb (by simp)
  | triv =>
    intro t' hb
    cases t' <;> (try (exact Bool.noConfusion hb))
    rfl
  | ulam t iht =>
    intro t' hb
    cases t' <;> simp [Tw.beq] at hb
    next t'' => rw [iht t'' hb]
  | uapp t μ iht =>
    intro t' hb
    cases t' with
    | var n h => exact Bool.noConfusion hb
    | unit u => exact Bool.noConfusion hb
    | mul a b => exact Bool.noConfusion hb
    | div a b => exact Bool.noConfusion hb
    | lam t => exact Bool.noConfusion hb
    | triv => exact Bool.noConfusion hb
    | ulam t => exact Bool.noConfusion hb
    | app f a => exact Bool.noConfusion hb
    | uapp tt μ' =>
      simp only [Tw.beq, Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨hb1, rfl⟩ := hb
      rw [iht tt hb1]

/-! ## Comparing branch ratios up to the unit algebra

`Tw.beq` is syntactic. At a sum, syntactic comparison rejects branches whose
ratios are the same conversions written in a different order, so we compare a
*flattened* form instead: a scalar ratio splits into its unit-constant part
(one exponent vector, merged by the group operations) and two bags of opaque
atoms, numerator and denominator. Atoms are compared as bags because real
multiplication is commutative; they are **never cancelled across the fraction
bar**, because an atom is the ratio of a free variable and may be zero, where
`x / x = 1` fails. Cancelling unit constants is sound because a scaling is
positive; cancelling atoms is not. -/

/-- `t.beq t` holds. With `Tw.beq_sound`, `beq` is a lawful equality test. -/
theorem Tw.beq_refl : ∀ {k : ℕ} {Θ : List Shape} {s : Shape}
    (t : Tw B k Θ s), t.beq t = true := by
  intro k Θ s t
  induction t with
  | var n h => simp [Tw.beq]
  | unit u => simp [Tw.beq]
  | mul a b iha ihb => simp [Tw.beq, iha, ihb]
  | div a b iha ihb => simp [Tw.beq, iha, ihb]
  | lam t ih => simp [Tw.beq, ih]
  | app f a ihf iha =>
    rw [Tw.beq]
    rw [dif_pos rfl]
    simp [ihf, iha]
  | triv => simp [Tw.beq]
  | ulam t ih => simp [Tw.beq, ih]
  | uapp t μ ih => simp [Tw.beq, ih]

instance {k : ℕ} {Θ : List Shape} {s : Shape} : BEq (Tw B k Θ s) := ⟨Tw.beq⟩

instance {k : ℕ} {Θ : List Shape} {s : Shape} : LawfulBEq (Tw B k Θ s) where
  eq_of_beq h := Tw.beq_sound _ _ h
  rfl := Tw.beq_refl _

/-- Flatten a scalar ratio into its unit-constant part and two bags of opaque
atoms (numerator, denominator). Unit constants merge into one exponent vector;
everything else is an atom. -/
def Tw.flat : {k : ℕ} → {Θ : List Shape} → Tw B k Θ .scalar →
    UExp B k × List (Tw B k Θ .scalar) × List (Tw B k Θ .scalar)
  | _, _, .unit u => (u, [], [])
  | _, _, .mul a b =>
      (Term.mul a.flat.1 b.flat.1, a.flat.2.1 ++ b.flat.2.1, a.flat.2.2 ++ b.flat.2.2)
  | _, _, .div a b =>
      (Term.div a.flat.1 b.flat.1, a.flat.2.1 ++ b.flat.2.2, a.flat.2.2 ++ b.flat.2.1)
  | _, _, t => (1, [t], [])

/-- Flattening preserves the value: a scalar ratio evaluates to its
unit-constant part's scale times the product of its numerator atoms over the
product of its denominator atoms. All divisions are `ℝ`'s total division; the
`div` case is the `GroupWithZero` computation, valid with zeros. -/
theorem Tw.flat_eval {k : ℕ} {Θ : List Shape} (ψ : Scaling B k) (θρ : TwEnv Θ) :
    ∀ (t : Tw B k Θ .scalar),
    Tw.eval ψ t θρ = ψ.scale t.flat.1
      * ((t.flat.2.1.map fun a => Tw.eval ψ a θρ).prod)
      / ((t.flat.2.2.map fun a => Tw.eval ψ a θρ).prod)
  | .var n h => by simp [Tw.flat]
  | .unit u => by simp [Tw.eval, Tw.flat]
  | .mul a b => by
      have iha := Tw.flat_eval ψ θρ a
      have ihb := Tw.flat_eval ψ θρ b
      show Tw.eval ψ a θρ * Tw.eval ψ b θρ = _
      rw [iha, ihb]
      simp only [Tw.flat, List.map_append, List.prod_append, Scaling.scale_mul,
        div_mul_div_comm]
      ring
  | .div a b => by
      have iha := Tw.flat_eval ψ θρ a
      have ihb := Tw.flat_eval ψ θρ b
      show Tw.eval ψ a θρ / Tw.eval ψ b θρ = _
      rw [iha, ihb]
      simp only [Tw.flat, List.map_append, List.prod_append, Scaling.scale_div,
        div_eq_mul_inv, mul_inv, inv_inv]
      ring
  | .app f a => by simp [Tw.flat]
  | .uapp t μ => by simp [Tw.flat]

/-- Decides whether two scalar ratios are equal up to the unit algebra: equal
unit-constant
parts (one exponent-vector comparison) and permutation-equal atom bags on each
side of the fraction bar. Sound, and strictly wider than `Tw.beq`: it accepts
the same conversions reassociated, reordered, and with their unit constants
combined differently. -/
def Tw.scalarEq {k : ℕ} {Θ : List Shape} (a b : Tw B k Θ .scalar) : Bool :=
  a.flat.1 == b.flat.1 && a.flat.2.1.isPerm b.flat.2.1
    && a.flat.2.2.isPerm b.flat.2.2

/-- `scalarEq` is sound: it implies evaluation equality in every scaling and
every environment: the hypothesis `Twist.add` carries. -/
theorem Tw.scalarEq_sound {k : ℕ} {Θ : List Shape} (a b : Tw B k Θ .scalar)
    (h : Tw.scalarEq a b = true) :
    ∀ (ψ : Scaling B k) (θρ : TwEnv Θ), Tw.eval ψ a θρ = Tw.eval ψ b θρ := by
  intro ψ θρ
  simp only [Tw.scalarEq, Bool.and_eq_true] at h
  obtain ⟨⟨hw, hn⟩, hd⟩ := h
  have hweq : a.flat.1 = b.flat.1 := eq_of_beq hw
  have hneq : ((a.flat.2.1.map fun t => Tw.eval ψ t θρ).prod)
      = ((b.flat.2.1.map fun t => Tw.eval ψ t θρ).prod) :=
    ((List.isPerm_iff.mp hn).map _).prod_eq
  have hdeq : ((a.flat.2.2.map fun t => Tw.eval ψ t θρ).prod)
      = ((b.flat.2.2.map fun t => Tw.eval ψ t θρ).prod) :=
    ((List.isPerm_iff.mp hd).map _).prod_eq
  rw [Tw.flat_eval ψ θρ a, Tw.flat_eval ψ θρ b, hweq, hneq, hdeq]

/-- **Computing the ratio.** For a derivation, the accumulated conversion ratio
together with its `Twist` derivation, or `none` where the analysis does not
apply.

The `add` check is `Tw.scalarEq`: branch ratios compare with their unit
constants merged into one exponent vector and their opaque atoms compared as
bags, so the same conversions reordered or reassociated are accepted. What the
check never does is cancel an atom against itself across the fraction bar (an
atom is the ratio of a free variable and may be zero, where `x / x = 1` fails),
and completeness at that boundary would need nonzero-ness tracked through the
relation. Everything downstream of the check is complete: `Tw.nfOne` decides
triviality of the *resulting* ratio exactly. -/
def twistOf : {j k : ℕ} → {Δ : DCtx D j k} → {Γ : Ctx B D j k} → {e : Tm B D j k} →
    {τ : Ty B D j k} → (Θ : List Shape) → (hΘ : Θ = Γ.shapes) →
    (d : HasTy Δ Γ e τ) → Option (Σ' t : Tw B k Θ (Ty.shape τ), Twist Θ d t)
  | _, _, _, Γ, _, _, Θ, hΘ, .var (n := n) h =>
      match hn : Θ[n]? with
      | some s =>
          if hs : s = Ty.shape _ then
            some ⟨.var n (hs ▸ hn), .var h (hs ▸ hn)⟩
          else none
      | none => none
  | _, _, _, _, _, _, Θ, hΘ, .lam (τ := σ) db => do
      let ⟨t, ht⟩ ← twistOf (Ty.shape σ :: Θ) (by simp [hΘ]) db
      some ⟨.lam t, .lam ht⟩
  | _, _, _, _, _, _, Θ, hΘ, .app df da => do
      let ⟨tf, htf⟩ ← twistOf Θ hΘ df
      let ⟨ta, hta⟩ ← twistOf Θ hΘ da
      some ⟨.app tf ta, .app htf hta⟩
  | _, _, _, _, _, _, Θ, _, .lit => some ⟨.unit 1, .lit⟩
  | _, _, _, _, _, _, Θ, hΘ, .mul da db => do
      let ⟨ta, hta⟩ ← twistOf Θ hΘ da
      let ⟨tb, htb⟩ ← twistOf Θ hΘ db
      some ⟨.mul ta tb, .mul hta htb⟩
  | _, _, _, _, _, _, Θ, hΘ, .div da db => do
      let ⟨ta, hta⟩ ← twistOf Θ hΘ da
      let ⟨tb, htb⟩ ← twistOf Θ hΘ db
      some ⟨.div ta tb, .div hta htb⟩
  | _, _, _, _, _, _, Θ, hΘ, .add da db => do
      let ⟨ta, hta⟩ ← twistOf Θ hΘ da
      let ⟨tb, htb⟩ ← twistOf Θ hΘ db
      if hb : Tw.scalarEq ta tb then
        some ⟨ta, .add (Tw.scalarEq_sound ta tb hb) hta htb⟩
      else none
  | _, _, _, _, _, _, Θ, hΘ, .convert (u := u) (v := v) da hsd => do
      let ⟨ta, hta⟩ ← twistOf Θ hΘ da
      some ⟨.mul ta (.div (.unit u) (.unit v)), .convert hsd hta⟩
  | _, _, _, _, _, _, Θ, hΘ, .ulam db => do
      let ⟨t, ht⟩ ← twistOf Θ (by simp [hΘ]) db
      some ⟨.ulam t, .ulam ht⟩
  | _, _, _, _, _, _, Θ, hΘ, .uapp (τ := τ) (σ := σ) df hd => do
      let ⟨tf, htf⟩ ← twistOf Θ hΘ df
      some ⟨Tw.castShape (Ty.shape_subst τ σ).symm (.uapp tf σ), .uapp hd htf⟩
  | _, _, _, _, _, _, Θ, hΘ, .dlam db => do
      let ⟨t, ht⟩ ← twistOf Θ (by simp [hΘ]) db
      some ⟨t, .dlam ht⟩
  | _, _, _, _, _, _, Θ, hΘ, .dapp (τ := τ) (d := dm) df => do
      let ⟨tf, htf⟩ ← twistOf Θ hΘ df
      some ⟨Tw.castShape (Ty.shape_substDim τ dm).symm tf, .dapp htf⟩
  | _, _, _, _, _, _, _, _, .ucon => none
  | _, _, _, _, _, _, _, _, .root _ _ => none
  | _, _, _, _, _, _, _, _, .idx _ _ => none
  | _, _, _, _, _, _, _, _, .mapp _ _ => none
  | _, _, _, _, _, _, _, _, .comp _ _ => none
  | _, _, _, _, _, _, _, _, .log _ => none
  | _, _, _, _, _, _, _, _, .exp _ => none

/-! ## The diagnostic, end to end -/

/-- **Unit drift**: the normal form of a program's accumulated conversion
ratio, computed from its derivation. `some 1` means the conversions cancel;
`some w` with `w ≠ 1` exhibits the drift; `none` means the analysis does not
apply (an unhandled form, or an `add` whose branch ratios `Tw.scalarEq`
cannot identify). -/
def unitDrift {j k : ℕ} {Δ : DCtx D j k} {us : List (UExp B k)} {u : UExp B k}
    {e : Tm B D j k} (d : HasTy Δ (scalarCtx us) e (.Q u)) : Option (UExp B k) :=
  (twistOf (us.map fun _ => Shape.scalar) (shapes_scalarCtx us).symm d).map
    fun p => Tw.nfOne p.1

/-- **The diagnostic is exact.** When `unitDrift` answers, invariance under
every rescaling holds precisely when the answer is `1`.

This is the compiler check: one group computation per derivation, one equality
of exponent vectors, and the program's dependence on the declared unit
magnitudes is decided, with unit polymorphism, higher-order structure and
conversion chains all handled by the one computation. -/
theorem unitDrift_spec {j k : ℕ} {Δ : DCtx D j k} {us : List (UExp B k)}
    {u : UExp B k} {e : Tm B D j k} {d : HasTy Δ (scalarCtx us) e (.Q u)}
    {w : UExp B k} (hw : unitDrift d = some w) (V : Scaling B k)
    {ρ : Env (scalarCtx (D := D) (j := j) us)} (hne : den V d ρ ≠ 0) :
    (∀ ψ : Scaling B k,
        den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ)
      ↔ w = 1 := by
  obtain ⟨⟨t, ht⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp hw
  exact ht.invariant_iff_nfOne V hne

/-! ## Closing the loop with the declarations

A closed dimensionless program whose conversions cancel computes a number that
does not depend on the declared unit magnitudes at all. Composed with adequacy,
the same statement holds of the compiled program: its output is invariant
across every consistent extension of the declaration set. This is the
ratio-level analogue of `evalC_convert_declared`: `Twist` joined to `Declare`
the way `eval_adeq` joined `Dynamics` to `Declare`. -/

/-- Any scaling is reachable from any other by composition: log-space is a
group. -/
theorem Scaling.comp_sub {k : ℕ} (V V' : Scaling B k) :
    V.comp ⟨fun b => V'.base b - V.base b, fun i => V'.vars i - V.vars i⟩ = V' := by
  cases V' with | mk b' v' =>
  simp only [Scaling.comp, Scaling.mk.injEq]
  exact ⟨funext fun x => by ring, funext fun x => by ring⟩

/-- **Drift-free programs are declaration-independent.** A closed dimensionless
program with cancelling conversions denotes the same number under every
valuation, however the units it converts between are declared. -/
theorem den_indep_of_driftFree {e : Tm B D 0 0}
    {d : HasTy (DCtx.nil D) ([] : Ctx B D 0 0) e (.Q 1)}
    (h1 : unitDrift (us := []) d = some 1) (V V' : Scaling B 0) :
    den V d PUnit.unit = den V' d PUnit.unit := by
  obtain ⟨⟨t, ht⟩, hp, hnf⟩ := Option.map_eq_some_iff.mp h1
  set ψ : Scaling B 0 :=
    ⟨fun b => V'.base b - V.base b, fun i => V'.vars i - V.vars i⟩ with hψ
  have hone := (Tw.nfOne_eq_one_iff t).mp hnf
  have hlaw := ht.invariant_of_eq_one hone V ψ PUnit.unit
  have hV' : den V' d PUnit.unit = den (V.comp ψ) d PUnit.unit := by
    rw [Scaling.comp_sub]
  rw [hV']
  have := hlaw
  simp only [scaleEnv, Scaling.scale_one, one_mul] at this
  exact this.symm

/-- **The compiled program is declaration-independent**, drift-free case. The
binary's output (a real scalar at the trivial unit) is the same number under
every valuation, hence under every consistent set of unit declarations that the
conversion oracle is drawn from. The theorem the diagnostic justifies. -/
theorem evalC_indep_of_driftFree {e : Tm B D 0 0}
    {d : HasTy (DCtx.nil D) ([] : Ctx B D 0 0) e (.Q 1)}
    (h1 : unitDrift (us := []) d = some 1) (V V' : Scaling B 0) :
    ∃ (n n' : ℕ) (m : ℝ),
      evalC (conv V) n [] e = some (.scalar ⟨m, 1⟩) ∧
      evalC (conv V') n' [] e = some (.scalar ⟨m, 1⟩) := by
  obtain ⟨n, hn⟩ := evalC_eq_den V d
  obtain ⟨n', hn'⟩ := evalC_eq_den V' d
  refine ⟨n, n', den V d PUnit.unit, hn, ?_⟩
  rw [den_indep_of_driftFree h1 V V']
  exact hn'

end LambdaS

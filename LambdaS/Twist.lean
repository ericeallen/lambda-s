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

Ratio variables enter in one place only: at a `lam` binder, whose future
argument may carry any ratio. The free variables of the program itself are
measurements, and the certified theorems only ever instantiate their ratios
at `1` (the inputs rescale ideally), so the analysis assigns them the literal
ratio `1` rather than an atom: the **frees-at-one assignment**, carried by
the pin marker `p` below. Asking the `add` agreement to hold at arbitrary
ratios for the program's own inputs would answer a stronger question than
the theorems ask, and would wrongly decline `(x in ft) + (y in ft)` for
distinct measurements `x y : Q m`.

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
index: the result type is `τ.subst σ`, and `Ty.shape_subst` is a theorem. It
appears once more at `mcons`, where a row's space is a `map` over the column
space and `List.length_map` is likewise a theorem.
-/

namespace LambdaS

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D]

/-- **The conversion-ratio semantics.** A second reading of Λs, valued in the
ratio syntax, running alongside `den`.

Addition forces its branches to agree, which is what makes the ratio a property
of a term rather than of a path through it.

The index `p` is the **frees-at-one assignment**, in de Bruijn form. Because
`lam` always prepends its ratio variable, the genuine atoms are exactly the
positions below `p` and the program's own context variables are the positions
at `p` and beyond. A `lam`-bound variable stands for a future argument, which
may carry any ratio, so it enters as an atom (`var`); a context variable is a
measurement, which rescales ideally, so it enters at the trivial ratio
(`varOne`). The exported diagnostic runs at `p = 0`: every free variable of
the program is pinned at `1`, and atoms arise only under binders. -/
inductive Twist : {j k : ℕ} → {Δ : DCtx D j k} → {Γ : Ctx B D j k} →
    {e : Tm B D j k} → {τ : Ty B D j k} → (p : ℕ) → (Θ : List Shape) →
    HasTy Δ Γ e τ → Tw B k Θ (Ty.shape τ) → Prop where
  /-- A `lam`-bound variable, below the pin marker: a genuine atom. -/
  | var {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {τ n p Θ} (h : Γ[n]? = some τ)
      (h' : Θ[n]? = some (Ty.shape τ)) (hp : n < p) :
      Twist (Δ := Δ) p Θ (.var h) (.var n h')
  /-- A context variable of the program, at or beyond the pin marker: its
  ratio is `1` at every shape, because inputs are measurements and
  measurements rescale ideally. -/
  | varOne {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {τ n p Θ} (h : Γ[n]? = some τ)
      (h' : Θ[n]? = some (Ty.shape τ)) (hp : p ≤ n) :
      Twist (Δ := Δ) p Θ (.var h) (Tw.one (Ty.shape τ))
  | lam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {σ τ e p Θ}
      {d : HasTy Δ (σ :: Γ) e τ} {t : Tw B k (Ty.shape σ :: Θ) (Ty.shape τ)} :
      Twist (p + 1) (Ty.shape σ :: Θ) d t → Twist p Θ (.lam d) (.lam t)
  | app {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {σ τ f a p Θ}
      {df : HasTy Δ Γ f (.arrow σ τ)} {da : HasTy Δ Γ a σ}
      {tf : Tw B k Θ (Ty.shape (Ty.arrow σ τ))} {ta : Tw B k Θ (Ty.shape σ)} :
      Twist p Θ df tf → Twist p Θ da ta → Twist p Θ (.app df da) (.app tf ta)
  | lit {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {q p Θ} :
      Twist (Δ := Δ) (Γ := Γ) p Θ (.lit (q := q)) (.unit 1)
  | mul {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u v a b p Θ}
      {da : HasTy Δ Γ a (.Q u)} {db : HasTy Δ Γ b (.Q v)} {s t : Tw B k Θ .scalar} :
      Twist p Θ da s → Twist p Θ db t → Twist p Θ (.mul da db) (.mul s t)
  | div {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u v a b p Θ}
      {da : HasTy Δ Γ a (.Q u)} {db : HasTy Δ Γ b (.Q v)} {s t : Tw B k Θ .scalar} :
      Twist p Θ da s → Twist p Θ db t → Twist p Θ (.div da db) (.div s t)
  | add {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u a b p Θ}
      {da : HasTy Δ Γ a (.Q u)} {db : HasTy Δ Γ b (.Q u)} {s t : Tw B k Θ .scalar}
      (heq : ∀ (ψ : Scaling B k) (θρ : TwEnv Θ), Tw.eval ψ s θρ = Tw.eval ψ t θρ) :
      Twist p Θ da s → Twist p Θ db t → Twist p Θ (.add da db) s
  | convert {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u v a p Θ}
      {da : HasTy Δ Γ a (.Q u)} {s : Tw B k Θ .scalar} (h : SameDim Δ u v) :
      Twist p Θ da s → Twist p Θ (.convert da h) (.mul s (.div (.unit u) (.unit v)))
  | pow {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {q : ℚ} {e : Tm B D j k}
      {u : UExp B k} {p : ℕ} {Θ : List Shape} {de : HasTy Δ Γ e (.Q u)}
      {s : Tw B k Θ .scalar} :
      Twist p Θ de s → Twist p Θ (.pow (q := q) de) (.qpow s q)
  /-- `log` of a trivial-ratio argument, with the `add`-style side condition
  that the argument's ratio is worth `1` under every scaling and environment.
  A trivial-ratio argument is unmoved by every rescaling: the typing rule pins
  it at `Q 1`, so the type's factor is `ψ(1) = 1` and the ratio is `1`, hence
  its logarithm is unmoved too and the result carries the trivial ratio.
  Beyond drift-`1` arguments the defect leaves the multiplicative group:
  `log` turns a multiplicative discrepancy into an additive one, which no
  ratio expresses, and the decline in `twistOf` stands. -/
  | log {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k} {p : ℕ}
      {Θ : List Shape} {de : HasTy Δ Γ e (.Q 1)} {s : Tw B k Θ .scalar}
      (hone : ∀ (ψ : Scaling B k) (θρ : TwEnv Θ), Tw.eval ψ s θρ = 1) :
      Twist p Θ de s → Twist p Θ (.log de) (.unit 1)
  /-- `exp` of a trivial-ratio argument, under the same side condition and for
  the same reason: an argument at `Q 1` with ratio `1` is unmoved by every
  rescaling, so its exponential is unmoved too. Beyond drift-`1` arguments the
  defect leaves the multiplicative group: how `exp` moves would depend on the
  argument's value, not merely its unit, and the decline in `twistOf`
  stands. -/
  | exp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k} {p : ℕ}
      {Θ : List Shape} {de : HasTy Δ Γ e (.Q 1)} {s : Tw B k Θ .scalar}
      (hone : ∀ (ψ : Scaling B k) (θρ : TwEnv Θ), Tw.eval ψ s θρ = 1) :
      Twist p Θ de s → Twist p Θ (.exp de) (.unit 1)
  | ulam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {d τ e p Θ}
      {db : HasTy (Δ.cons d) Γ.weaken e τ} {t : Tw B (k + 1) Θ (Ty.shape τ)} :
      Twist p Θ db t → Twist p Θ (.ulam db) (.ulam t)
  | uapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f d τ σ p Θ}
      {df : HasTy Δ Γ f (.all d τ)} {t : Tw B k Θ (Ty.shape (Ty.all d τ))}
      (hd : dimOf Δ σ = d) :
      Twist p Θ df t →
      Twist p Θ (.uapp df hd) (Tw.castShape (Ty.shape_subst τ σ).symm (.uapp t σ))
  | dlam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {τ e p Θ}
      {db : HasTy Δ.weakenDim Γ.weakenDim e τ} {t : Tw B k Θ (Ty.shape τ)} :
      Twist p Θ db t → Twist p Θ (.dlam db) t
  | dapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f τ p Θ} {d : DExp D j}
      {df : HasTy Δ Γ f (.allDim τ)} {t : Tw B k Θ (Ty.shape τ)} :
      Twist p Θ df t →
      Twist p Θ (.dapp df) (Tw.castShape (Ty.shape_substDim τ d).symm t)
  /-- The empty vector: the empty drift vector. -/
  | vnil {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {p Θ} :
      Twist (Δ := Δ) (Γ := Γ) p Θ .vnil .vecnil
  /-- Consing a scalar onto a vector conses its drift onto the drift vector.
  No side condition: the relation at vector shapes carries one ratio per
  component, so a drifting component is reported rather than declined. -/
  | vcons {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e v : Tm B D j k}
      {u : UExp B k} {V : Sp B k} {p : ℕ} {Θ : List Shape}
      {de : HasTy Δ Γ e (.Q u)} {dv : HasTy Δ Γ v (.vec V)}
      {s : Tw B k Θ .scalar} {t : Tw B k Θ (.vec V.length)} :
      Twist p Θ de s → Twist (τ := .vec V) p Θ dv t →
      Twist (τ := .vec (u :: V)) p Θ (.vcons de dv) (.veccons s t)
  /-- The zero-row matrix: the zero-row drift matrix. -/
  | mnil {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {V p Θ} :
      Twist (Δ := Δ) (Γ := Γ) p Θ (.mnil (V := V)) .matnil
  /-- Consing a row onto a matrix conses the row's drift vector onto the drift
  matrix. The row lives at the mapped space, whose length equals the column
  space's by `List.length_map`, so its drift vector is retyped along that
  equality. -/
  | mcons {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {w : UExp B k}
      {r M : Tm B D j k} {V W : Sp B k} {p : ℕ} {Θ : List Shape}
      {dr : HasTy Δ Γ r (.vec (V.map fun u => Term.div w u))}
      {dM : HasTy Δ Γ M (.lin V W)}
      {tr : Tw B k Θ (.vec (V.map fun u => Term.div w u).length)}
      {tM : Tw B k Θ (.mat V.length W.length)} :
      Twist (τ := .vec (V.map fun u => Term.div w u)) p Θ dr tr →
      Twist (τ := .lin V W) p Θ dM tM →
      Twist (τ := .lin V (w :: W)) p Θ (.mcons dr dM) (.matcons (Tw.castShape
        (show Shape.vec (V.map fun u => Term.div w u).length = Shape.vec V.length
          by simp) tr) tM)
  /-- Indexing projects the component's drift out of the drift vector. -/
  | idx {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
      {V : Sp B k} {i : ℕ} {u : UExp B k} {p : ℕ} {Θ : List Shape}
      {de : HasTy Δ Γ e (.vec V)} {t : Tw B k Θ (.vec V.length)}
      (hu : V[i]? = some u) :
      Twist (τ := .vec V) p Θ de t →
      Twist p Θ (.idx de hu) (.proj t ⟨i, (List.getElem?_eq_some_iff.mp hu).1⟩)
  /-- Matrix application. The `add`-style agreement condition, per output row
  `a`: the product of the entry drift at `(a, i)` with the argument drift at
  `i` must be worth the output drift at `a`, for every column `i`, in every
  scaling and environment. Over the empty domain the condition is vacuous and
  any output drift is sound, since the output is the zero vector. -/
  | mapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f x : Tm B D j k}
      {V W : Sp B k} {p : ℕ} {Θ : List Shape}
      {df : HasTy Δ Γ f (.lin V W)} {dx : HasTy Δ Γ x (.vec V)}
      {tf : Tw B k Θ (.mat V.length W.length)} {tx : Tw B k Θ (.vec V.length)}
      {tw : Tw B k Θ (.vec W.length)}
      (heq : ∀ (ψ : Scaling B k) (θρ : TwEnv Θ) (a : Fin W.length) (i : Fin V.length),
          Tw.eval ψ tf θρ a i * Tw.eval ψ tx θρ i = Tw.eval ψ tw θρ a) :
      Twist (τ := .lin V W) p Θ df tf → Twist (τ := .vec V) p Θ dx tx →
      Twist (τ := .vec W) p Θ (.mapp df dx) tw
  /-- Composition. The analogous agreement condition per entry `(a, i)`,
  across the middle index `b`. -/
  | comp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f g : Tm B D j k}
      {U V W : Sp B k} {p : ℕ} {Θ : List Shape}
      {df : HasTy Δ Γ f (.lin V W)} {dg : HasTy Δ Γ g (.lin U V)}
      {tf : Tw B k Θ (.mat V.length W.length)} {tg : Tw B k Θ (.mat U.length V.length)}
      {tw : Tw B k Θ (.mat U.length W.length)}
      (heq : ∀ (ψ : Scaling B k) (θρ : TwEnv Θ) (a : Fin W.length) (i : Fin U.length)
          (b : Fin V.length),
          Tw.eval ψ tf θρ a b * Tw.eval ψ tg θρ b i = Tw.eval ψ tw θρ a i) :
      Twist (τ := .lin V W) p Θ df tf → Twist (τ := .lin U V) p Θ dg tg →
      Twist (τ := .lin U W) p Θ (.comp df dg) tw
  /-- Ratio conversion: a ratio may be replaced by one of equal value under
  every scaling and environment. This is how `twistOf` β-normalizes as it
  builds: `app` on a literal `lam` emits the substituted body (`Tw.appE`),
  `uapp` on a literal `ulam` performs the recorded instantiation
  (`Tw.uappE`), and `idx` reduces projections of vector literals
  (`Tw.projE`), each justified by its evaluation lemma. -/
  | ratio {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
      {τ : Ty B D j k} {p Θ} {d : HasTy Δ Γ e τ}
      {t t' : Tw B k Θ (Ty.shape τ)}
      (heq : ∀ (ψ : Scaling B k) (θρ : TwEnv Θ),
        Tw.eval ψ t θρ = Tw.eval ψ t' θρ) :
      Twist p Θ d t → Twist p Θ d t'

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

omit [DecidableEq B] [Fintype D] [DecidableEq D] [UnitSys B D] in
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

omit [DecidableEq B] [Fintype D] [DecidableEq D] [UnitSys B D] in
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

omit [DecidableEq B] [Fintype D] [DecidableEq D] in
omit [UnitSys B D] in
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

omit [DecidableEq B] [Fintype D] [DecidableEq D] in
/-- **The scaling law with a twist.** A term whose conversions accumulate to `t`
rescales by its type's factor times the *square* of `t`'s value: both readings
carry the conversion factor, so it appears twice. At trivial ratio this is the
fundamental theorem.

The value environments are related at the **evaluation of the assignment**:
the ratio environment is arbitrary at the atoms (positions below `p`, the
`lam`-bound variables) and pinned at `1` from `p` on (`TwEnv.OnesFrom`),
which is where the `varOne` rule reads its trivial ratio back. The exported
theorems instantiate at `p = 0` and the all-ones environment, the
instantiation they performed already.

Now proved at the whole calculus: the binder cases are the ones `TwistTy` could
not state. -/
theorem Twist.scaling : ∀ {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
    {e : Tm B D j k} {τ : Ty B D j k} {p : ℕ} {Θ : List Shape}
    {d : HasTy Δ Γ e τ} {t : Tw B k Θ (Ty.shape τ)}, Twist p Θ d t →
    ∀ (V ψ : Scaling B k) (θρ : TwEnv Θ), TwEnv.OnesFrom p θρ →
      ∀ {ρ ρ' : Env Γ}, TwRelEnv ψ Γ Θ θρ ρ ρ' →
      TwRel τ (Tw.eval ψ t θρ) ψ (den V d ρ) (den (V.comp ψ) d ρ') := by
  intro j k Δ Γ e τ p Θ d t ht
  induction ht with
  | var h h' hp => intro V ψ θρ hOnes ρ ρ' hr; exact twRelEnv_lookup hr _ h h'
  | varOne h h' hp =>
    intro V ψ θρ hOnes ρ ρ' hr
    have hl := twRelEnv_lookup hr _ h h'
    rwa [Tw.eval_one, ← hOnes _ _ h' hp]
  | lam htb ih =>
    intro V ψ θρ hOnes ρ ρ' hr r x y hxy
    exact ih V ψ (r, θρ) (hOnes.cons r) (TwRelEnv.cons rfl hxy hr)
  | app htf hta ihf iha =>
    intro V ψ θρ hOnes ρ ρ' hr
    exact ihf V ψ θρ hOnes hr _ _ _ (iha V ψ θρ hOnes hr)
  | @lit _ _ _ _ q _ _ =>
    intro V ψ θρ hOnes ρ ρ' _
    show (den (V.comp ψ) (HasTy.lit (q := q)) ρ' : ℝ)
        = ψ.scale 1 * (Tw.eval ψ (Tw.unit 1) θρ * Tw.eval ψ (Tw.unit 1) θρ)
          * den V (HasTy.lit (q := q)) ρ
    show ((q : ℚ) : ℝ) = ψ.scale 1 * (ψ.scale 1 * ψ.scale 1) * ((q : ℚ) : ℝ)
    simp
  | @mul _ _ _ _ _ _ _ _ _ _ da db st tt hta htb iha ihb =>
    intro V ψ θρ hOnes ρ ρ' hr
    have h1 := iha V ψ θρ hOnes hr
    have h2 := ihb V ψ θρ hOnes hr
    simp only [TwRel] at h1 h2
    show den (V.comp ψ) (da.mul db) ρ'
        = ψ.scale (Term.mul _ _)
          * (Tw.eval ψ (st.mul tt) θρ * Tw.eval ψ (st.mul tt) θρ)
          * den V (da.mul db) ρ
    show den (V.comp ψ) da ρ' * den (V.comp ψ) db ρ'
        = _ * _ * (den V da ρ * den V db ρ)
    rw [h1, h2, Scaling.scale_mul]
    show _ = _ * ((Tw.eval ψ st θρ : ℝ) * (Tw.eval ψ tt θρ : ℝ)
        * ((Tw.eval ψ st θρ : ℝ) * (Tw.eval ψ tt θρ : ℝ))) * _
    ring
  | @div _ _ _ _ _ _ _ _ _ _ da db st tt hta htb iha ihb =>
    intro V ψ θρ hOnes ρ ρ' hr
    have h1 := iha V ψ θρ hOnes hr
    have h2 := ihb V ψ θρ hOnes hr
    simp only [TwRel] at h1 h2
    show den (V.comp ψ) (da.div db) ρ'
        = ψ.scale (Term.div _ _)
          * (Tw.eval ψ (st.div tt) θρ * Tw.eval ψ (st.div tt) θρ)
          * den V (da.div db) ρ
    show den (V.comp ψ) da ρ' / den (V.comp ψ) db ρ'
        = _ * _ * (den V da ρ / den V db ρ)
    rw [h1, h2, Scaling.scale_div]
    show _ = _ * ((Tw.eval ψ st θρ : ℝ) / (Tw.eval ψ tt θρ : ℝ)
        * ((Tw.eval ψ st θρ : ℝ) / (Tw.eval ψ tt θρ : ℝ))) * _
    exact div_twist _ _ _ _ _ _
  | @add _ _ _ _ _ _ _ _ _ da db st tt heq hta htb iha ihb =>
    intro V ψ θρ hOnes ρ ρ' hr
    have h1 := iha V ψ θρ hOnes hr
    have h2 := ihb V ψ θρ hOnes hr
    simp only [TwRel] at h1 h2
    show den (V.comp ψ) (da.add db) ρ'
        = ψ.scale _ * (Tw.eval ψ st θρ * Tw.eval ψ st θρ) * den V (da.add db) ρ
    show den (V.comp ψ) da ρ' + den (V.comp ψ) db ρ'
        = _ * _ * (den V da ρ + den V db ρ)
    rw [h1, h2, heq ψ θρ]
    ring
  | @convert _ _ _ _ u v _ _ _ da st h hta ih =>
    intro V ψ θρ hOnes ρ ρ' hr
    have h1 := ih V ψ θρ hOnes hr
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
  | pow hte ih =>
    rename_i q e' u' p' Θ' de s
    intro V ψ θρ hOnes ρ ρ' hr
    have h := ih V ψ θρ hOnes hr
    simp only [TwRel] at h ⊢
    show (den (V.comp ψ) de ρ') ^ ((q : ℚ) : ℝ)
        = ψ.scale (Term.rpow u' q)
          * ((Tw.eval ψ s θρ : ℝ) ^ (q : ℝ) * (Tw.eval ψ s θρ : ℝ) ^ (q : ℝ))
          * (den V de ρ) ^ ((q : ℚ) : ℝ)
    rw [h, mul_rpow_of_pos_left
        (mul_pos (ψ.scale_pos u') (mul_pos (Tw.eval ψ s θρ).2 (Tw.eval ψ s θρ).2)),
      Real.mul_rpow (le_of_lt (ψ.scale_pos u'))
        (le_of_lt (mul_pos (Tw.eval ψ s θρ).2 (Tw.eval ψ s θρ).2)),
      Real.mul_rpow (le_of_lt (Tw.eval ψ s θρ).2) (le_of_lt (Tw.eval ψ s θρ).2),
      ← Scaling.scale_rpow]
    try ring
  | log hone hte ih =>
    rename_i e' p' Θ' de s
    intro V ψ θρ hOnes ρ ρ' hr
    have h1 := ih V ψ θρ hOnes hr
    simp only [TwRel] at h1
    rw [hone ψ θρ] at h1
    have harg : den (V.comp ψ) de ρ' = den V de ρ := by simpa using h1
    show Real.log (den (V.comp ψ) de ρ')
        = ψ.scale 1 * (ψ.scale 1 * ψ.scale 1) * Real.log (den V de ρ)
    rw [harg]
    simp
  | exp hone hte ih =>
    rename_i e' p' Θ' de s
    intro V ψ θρ hOnes ρ ρ' hr
    have h1 := ih V ψ θρ hOnes hr
    simp only [TwRel] at h1
    rw [hone ψ θρ] at h1
    have harg : den (V.comp ψ) de ρ' = den V de ρ := by simpa using h1
    show Real.exp (den (V.comp ψ) de ρ')
        = ψ.scale 1 * (ψ.scale 1 * ψ.scale 1) * Real.exp (den V de ρ)
    rw [harg]
    simp
  | @ulam _ _ _ _ _ _ _ _ _ db tb htb ih =>
    intro V ψ θρ hOnes ρ ρ' hr r s
    have h := ih (V.cons r) (ψ.cons s) θρ hOnes (twRelEnv_weaken s hr)
    show TwRel _ (Tw.eval (ψ.cons s) tb θρ) (ψ.cons s)
      (den (V.cons r) db (Env.weaken ρ)) (den ((V.comp ψ).cons (r + s)) db (Env.weaken ρ'))
    rwa [← Scaling.comp_cons]
  | @uapp _ _ _ _ _ _ τ σ _ _ df tf hd htf ihf =>
    intro V ψ θρ hOnes ρ ρ' hr
    have h := ihf V ψ θρ hOnes hr
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
    intro V ψ θρ hOnes ρ ρ' hr
    exact ih V ψ θρ hOnes (twRelEnv_weakenDim hr)
  | @dapp _ _ _ _ _ τ _ _ dm df tf htf ihf =>
    intro V ψ θρ hOnes ρ ρ' hr
    have h := ihf V ψ θρ hOnes hr
    rw [Tw.eval_castShape]
    refine (twRel_substDim τ dm ψ (w := Tw.eval ψ tf θρ)
      (eqRec_heq _ _).symm (cast_heq _ _).symm (cast_heq _ _).symm).mpr h
  | vnil =>
    intro V ψ θρ hOnes ρ ρ' hr i
    exact i.elim0
  | vcons hte htv ihe ihv =>
    rename_i u Vs p' Θ' de dv s tv
    intro V ψ θρ hOnes ρ ρ' hr
    have h1 := ihe V ψ θρ hOnes hr
    have h2 := ihv V ψ θρ hOnes hr
    simp only [TwRel] at h1 h2
    intro i
    show Fin.cons (α := fun _ => ℝ) (den (V.comp ψ) de ρ') (den (V.comp ψ) dv ρ') i
        = ψ.scale ((u :: Vs).get i)
          * (Tw.eval ψ (Tw.veccons s tv) θρ i * Tw.eval ψ (Tw.veccons s tv) θρ i)
          * Fin.cons (α := fun _ => ℝ) (den V de ρ) (den V dv ρ) i
    cases i using Fin.cases with
    | zero => simpa [Tw.eval] using h1
    | succ i => simpa [Tw.eval] using h2 i
  | mnil =>
    intro V ψ θρ hOnes ρ ρ' hr a
    exact a.elim0
  | mcons htr htM ihr ihM =>
    rename_i w r' M' Vs Ws p' Θ' dr dM tr tM
    intro V ψ θρ hOnes ρ ρ' hr
    have h1 := ihr V ψ θρ hOnes hr
    have h2 := ihM V ψ θρ hOnes hr
    simp only [TwRel] at h1 h2
    intro a i
    show Fin.cons (α := fun _ => Fin Vs.length → ℝ)
          (fun i => den (V.comp ψ) dr ρ' (Fin.cast (by simp) i))
          (den (V.comp ψ) dM ρ') a i
        = (ψ.scale ((w :: Ws).get a) / ψ.scale (Vs.get i))
          * (Tw.eval ψ (Tw.matcons (Tw.castShape (by simp) tr) tM) θρ a i
            * Tw.eval ψ (Tw.matcons (Tw.castShape (by simp) tr) tM) θρ a i)
          * Fin.cons (α := fun _ => Fin Vs.length → ℝ)
            (fun i => den V dr ρ (Fin.cast (by simp) i)) (den V dM ρ) a i
    cases a using Fin.cases with
    | zero =>
      have h := h1 (Fin.cast (by simp) i)
      simp only [Fin.cons_zero, List.get_eq_getElem, List.getElem_map, Fin.val_cast,
        Fin.val_zero, List.getElem_cons_zero, Tw.eval, Tw.eval_castShape_vec] at h ⊢
      rw [h, Scaling.scale_div]
    | succ a =>
      simpa [Tw.eval] using h2 a i
  | idx hu hte ih =>
    rename_i e' Vs i u p' Θ' de t
    intro V ψ θρ hOnes ρ ρ' hr
    have h := ih V ψ θρ hOnes hr
    simp only [TwRel] at h ⊢
    have hlt := (List.getElem?_eq_some_iff.mp hu).1
    have hget : Vs.get ⟨i, hlt⟩ = u := by
      simpa [List.get_eq_getElem] using (List.getElem?_eq_some_iff.mp hu).2
    show den (V.comp ψ) de ρ' ⟨i, hlt⟩
        = ψ.scale u * (Tw.eval ψ t θρ ⟨i, hlt⟩ * Tw.eval ψ t θρ ⟨i, hlt⟩)
          * den V de ρ ⟨i, hlt⟩
    rw [← hget]
    exact h ⟨i, hlt⟩
  | mapp heq htf htx ihf ihx =>
    rename_i f' x' Vs Ws p' Θ' df dx tf tx tw
    intro V ψ θρ hOnes ρ ρ' hr
    have hf := ihf V ψ θρ hOnes hr
    have hx := ihx V ψ θρ hOnes hr
    simp only [TwRel] at hf hx ⊢
    intro a
    show (∑ i, den (V.comp ψ) df ρ' a i * den (V.comp ψ) dx ρ' i)
        = ψ.scale (Ws.get a) * (Tw.eval ψ tw θρ a * Tw.eval ψ tw θρ a)
          * ∑ i, den V df ρ a i * den V dx ρ i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf a i, hx i, ← heq ψ θρ a i]
    simp only [Positive.val_mul]
    have hvi := ne_of_gt (ψ.scale_pos (Vs.get i))
    field_simp
    try ring
  | comp heq htf htg ihf ihg =>
    rename_i f' g' Us Vs Ws p' Θ' df dg tf tg tw
    intro V ψ θρ hOnes ρ ρ' hr
    have hf := ihf V ψ θρ hOnes hr
    have hg := ihg V ψ θρ hOnes hr
    simp only [TwRel] at hf hg ⊢
    intro a i
    show (∑ b, den (V.comp ψ) df ρ' a b * den (V.comp ψ) dg ρ' b i)
        = ψ.scale (Ws.get a) / ψ.scale (Us.get i)
          * (Tw.eval ψ tw θρ a i * Tw.eval ψ tw θρ a i)
          * ∑ b, den V df ρ a b * den V dg ρ b i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hf a b, hg b i, ← heq ψ θρ a i b]
    simp only [Positive.val_mul]
    have hvb := ne_of_gt (ψ.scale_pos (Vs.get b))
    have hui := ne_of_gt (ψ.scale_pos (Us.get i))
    field_simp
    try ring
  | ratio heq ht ih =>
    intro V ψ θρ hOnes ρ ρ' hr
    exact heq ψ θρ ▸ ih V ψ θρ hOnes hr

/-! ## The characterization at first order

A term of scalar type over a context of scalars: a program computing a number
from numbers, whatever abstraction and application it uses inside. Its ratio is
a closed scalar `Tw`, and the characterization says: the program obeys the
unrestricted scaling law exactly when that ratio's value is `1` under every
scaling. The next section makes that condition *syntactic*, and hence decidable.
-/

omit [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D] [UnitSys B D] in
/-- Scalar contexts and their shape lists. -/
@[simp] theorem shapes_scalarCtx {j k : ℕ} (us : List (UExp B k)) :
    Ctx.shapes (scalarCtx (D := D) (j := j) us) = us.map fun _ => Shape.scalar := by
  simp [Ctx.shapes, scalarCtx, List.map_map, Function.comp_def, Ty.shape]

omit [DecidableEq B] [Fintype D] [DecidableEq D] [UnitSys B D] in
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

omit [DecidableEq B] [Fintype D] [DecidableEq D] in
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
    (ht : Twist 0 _ d t) (V : Scaling B k)
    {ρ : Env (scalarCtx (D := D) (j := j) us)} (hne : den V d ρ ≠ 0)
    (hinv : ∀ ψ : Scaling B k,
        den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ)
    (ψ : Scaling B k) : Tw.eval ψ t (oneTwEnv _) = 1 := by
  have hr := twRelEnv_scaleEnv (D := D) (j := j) ψ us ρ
  have htw := ht.scaling V ψ (oneTwEnv _) (TwEnv.onesFrom_oneTwEnv 0) hr
  simp only [TwRel] at htw
  rw [hinv ψ] at htw
  have hu := ne_of_gt (ψ.scale_pos u)
  set c : ℝ := (Tw.eval ψ t (oneTwEnv (us.map fun _ => Shape.scalar)) : ℝ) with hc
  have hsq : c * c = 1 := by
    have h0 : ψ.scale u * den V d ρ * (c * c - 1) = 0 := by nlinarith [htw]
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hu
      · exact absurd h' hne
    · linarith [h]
  have hpos : 0 < c := (Tw.eval ψ t (oneTwEnv _)).2
  refine Subtype.ext ?_
  show c = 1
  nlinarith [hsq, hpos]

omit [DecidableEq B] [Fintype D] [DecidableEq D] in
/-- **Cancelling conversions are invisible.** A term whose ratio is worth `1`
under every scaling obeys the unrestricted scaling law, exactly as a
convert-free term does, even though it may convert repeatedly along the way. -/
theorem Twist.invariant_of_eq_one {j k : ℕ} {Δ : DCtx D j k} {us : List (UExp B k)}
    {u : UExp B k} {e : Tm B D j k} {d : HasTy Δ (scalarCtx us) e (.Q u)}
    {t : Tw B k (us.map fun _ => Shape.scalar) .scalar}
    (ht : Twist 0 _ d t)
    (hone : ∀ ψ : Scaling B k, Tw.eval ψ t (oneTwEnv _) = 1)
    (V ψ : Scaling B k) (ρ : Env (scalarCtx (D := D) (j := j) us)) :
    den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ := by
  have hr := twRelEnv_scaleEnv (D := D) (j := j) ψ us ρ
  have htw := ht.scaling V ψ (oneTwEnv _) (TwEnv.onesFrom_oneTwEnv 0) hr
  simp only [TwRel] at htw
  rw [hone ψ] at htw
  simpa using htw

omit [DecidableEq B] [Fintype D] [DecidableEq D] in
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
    (ht : Twist 0 _ d t) (V : Scaling B k)
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
theorem Tw.nfOne_eq_one_iff {k : ℕ} {Θ : List Shape}
    (t : Tw B k Θ .scalar) :
    Tw.nfOne t = 1 ↔ ∀ ψ : Scaling B k, Tw.eval ψ t (oneTwEnv Θ) = 1 := by
  have hval : ∀ ψ : Scaling B k,
      (Tw.eval ψ t (oneTwEnv Θ) : ℝ) = ψ.scale (Tw.nfOne t) := by
    intro ψ
    have h := Tw.nf_correct ψ (idU B k) t (SynEnv.ones Θ) (oneTwEnv Θ)
      (srelEnv_ones ψ Θ)
    rwa [Scaling.pull_id] at h
  constructor
  · intro h1 ψ
    exact Subtype.ext (by rw [hval ψ, h1, Scaling.scale_one, Positive.val_one])
  · intro hall
    have : ∀ ψ : Scaling B k, ψ.scale (Tw.nfOne t) = ψ.scale 1 := by
      intro ψ; rw [← hval ψ, hall ψ, Positive.val_one, Scaling.scale_one]
    exact scale_eq_iff.mp this

omit [Fintype D] [DecidableEq D] in
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
    (ht : Twist 0 _ d t) (V : Scaling B k)
    {ρ : Env (scalarCtx (D := D) (j := j) us)} (hne : den V d ρ ≠ 0) :
    (∀ ψ : Scaling B k,
        den (V.comp ψ) d (scaleEnv ψ us ρ) = ψ.scale u * den V d ρ)
      ↔ Tw.nfOne t = 1 :=
  (ht.invariant_iff V hne).trans (Tw.nfOne_eq_one_iff t).symm

/-! ## Computing the ratio

`Twist` is a relation; the compiler needs a function. `twistOf` computes, for a
derivation, a ratio together with its `Twist` derivation, or `none`.

It fails in exactly two circumstances, and they are different in kind. At `add`
the two branches' ratios must agree up to the unit algebra (`Tw.scalarEq`):
unit constants merge into one exponent vector and atoms into one rational
exponent each, so reordered, reassociated and differently split conversions
are accepted. The same check runs per output component at `mapp` and `comp`,
whose sums mix one drift per summand: the products along the summed index must
agree, and the common value is the component's drift; disagreement declines,
exactly as at `add`. Under the frees-at-one assignment the program's own
context variables contribute the literal ratio `1` rather than atoms, so a
first-order ratio is atom-free and the check is *exact* there
(`Tw.scalarEq_iff_eval_eq`): the only first-order declines at `add`, `mapp`
and `comp` are genuine drift disagreements, such as `(x in ft) + y`. The
residual incompleteness is that distinct atoms, which arise only under `lam`
binders, are never identified. At `log` and `exp` the same check runs against
the literal ratio `1`: a trivial-ratio argument at `Q 1` is unmoved by every
rescaling, so its logarithm or exponential is unmoved too, and the result
carries the trivial ratio (`log ((x in ft)/(x in ft))` is
declaration-independent, and is accepted). Beyond drift-`1` arguments the two
forms are nonlinear and no ratio of any kind describes how they move: `log`
turns a multiplicative defect into an additive one, and `exp`'s would have to
depend on the argument's value, not merely its unit, so a nontrivial argument
ratio declines. The one *unconditional* decline is `ucon`, which names a
unit, and that is outside the invariance theory: no scaling story survives
naming a magnitude.

The vector and matrix forms are *accepted*, at the `vec` and `mat` shapes,
with no side conditions at the introductions: the drift of a vector is a
vector of drifts, the drift of a matrix is a matrix of drifts, and a drifting
literal component is reported rather than declined. `idx` projects a drift
back out. `pow` is accepted too: the drift of `e ^ q` is the drift of `e`
lifted to the `q` by `Tw.qpow`, which the positive scalar carrier makes
sound. -/

/-- Decidable equality of ratio terms at matching indices. Proof fields are
propositions, so `var` compares only its index. -/
def Tw.beq : {k : ℕ} → {Θ : List Shape} → {s : Shape} →
    Tw B k Θ s → Tw B k Θ s → Bool
  | _, _, _, .var n _, .var m _ => n == m
  | _, _, _, .unit u, .unit v => u == v
  | _, _, _, .mul a b, .mul a' b' => a.beq a' && b.beq b'
  | _, _, _, .div a b, .div a' b' => a.beq a' && b.beq b'
  | _, _, _, .qpow t q, .qpow t' q' => t.beq t' && q == q'
  | _, _, _, .lam t, .lam t' => t.beq t'
  | _, _, _, .app (s := s₁) f a, .app (s := s₂) f' a' =>
      if h : s₁ = s₂ then (h ▸ f).beq f' && (h ▸ a).beq a' else false
  | _, _, _, .vecnil, .vecnil => true
  | _, _, _, .veccons a v, .veccons a' v' => a.beq a' && v.beq v'
  | _, _, _, .proj (n := n₁) v i, .proj (n := n₂) v' i' =>
      if h : n₁ = n₂ then (h ▸ v).beq v' && i.val == i'.val else false
  | _, _, _, .matnil, .matnil => true
  | _, _, _, .matcons r M, .matcons r' M' => r.beq r' && M.beq M'
  | _, _, _, .row (m := m₁) M j, .row (m := m₂) M' j' =>
      if h : m₁ = m₂ then (h ▸ M).beq M' && j.val == j'.val else false
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
  | qpow t q iht =>
    intro t' hb
    cases t' <;> try exact Bool.noConfusion hb
    case qpow =>
      rename_i q₂ t₂
      simp only [Tw.beq, Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨hb1, rfl⟩ := hb
      rw [iht t₂ hb1]
  | lam t iht =>
    intro t' hb
    cases t' <;> simp [Tw.beq] at hb
    next t'' => rw [iht t'' hb]
  | @app _ _ s₁ _ f a ihf iha =>
    intro t' hb
    cases t' <;> try exact Bool.noConfusion hb
    case app =>
      rename_i s₂ a' f'
      simp only [Tw.beq] at hb
      split at hb
      · next h =>
        subst h
        simp only [Bool.and_eq_true] at hb
        rw [ihf f' hb.1, iha a' hb.2]
      · exact absurd hb (by simp)
  | vecnil =>
    intro t' hb
    cases t' <;> (try (exact Bool.noConfusion hb))
    rfl
  | veccons a v iha ihv =>
    intro t' hb
    cases t' <;> try exact Bool.noConfusion hb
    case veccons =>
      rename_i a' v'
      simp only [Tw.beq, Bool.and_eq_true] at hb
      rw [iha a' hb.1, ihv v' hb.2]
  | @proj _ _ n₁ v i ihv =>
    intro t' hb
    cases t' <;> try exact Bool.noConfusion hb
    case proj =>
      rename_i n₂ i' v'
      simp only [Tw.beq] at hb
      split at hb
      · next h =>
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain rfl : i = i' := Fin.ext hb.2
        rw [ihv v' hb.1]
      · exact absurd hb (by simp)
  | matnil =>
    intro t' hb
    cases t' <;> (try (exact Bool.noConfusion hb))
    rfl
  | matcons r M ihr ihM =>
    intro t' hb
    cases t' <;> try exact Bool.noConfusion hb
    case matcons =>
      rename_i r' M'
      simp only [Tw.beq, Bool.and_eq_true] at hb
      rw [ihr r' hb.1, ihM M' hb.2]
  | @row _ _ _ m₁ M j ihM =>
    intro t' hb
    cases t' <;> try exact Bool.noConfusion hb
    case row =>
      rename_i m₂ j' M'
      simp only [Tw.beq] at hb
      split at hb
      · next h =>
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain rfl : j = j' := Fin.ext hb.2
        rw [ihM M' hb.1]
      · exact absurd hb (by simp)
  | ulam t iht =>
    intro t' hb
    cases t' <;> simp [Tw.beq] at hb
    next t'' => rw [iht t'' hb]
  | uapp t μ iht =>
    intro t' hb
    cases t' <;> try exact Bool.noConfusion hb
    case uapp =>
      rename_i μ' t₂
      simp only [Tw.beq, Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨hb1, rfl⟩ := hb
      rw [iht t₂ hb1]

/-! ## Comparing branch ratios up to the unit algebra

`Tw.beq` is syntactic. At a sum, syntactic comparison rejects branches whose
ratios are the same conversions written in a different order, so we compare a
*flattened* form instead: a scalar ratio splits into its unit-constant part
(one exponent vector, merged by the group operations) and a list of opaque
atoms each carrying a rational exponent, a vector in the free ℚ-vector space
the atoms generate, exactly as the units themselves are vectors over the base
units. Multiplication appends, division negates the exponents, and `qpow`
scales them. Two ratios compare equal when their unit parts agree and every
atom carries the same total exponent on both sides. What the comparison never
does is identify *distinct* atoms: an atom is the ratio of a `lam`-bound
variable, standing for a future argument, and nothing relates two arguments'
ratios. The program's own context variables produce no atoms at all under the
frees-at-one assignment, which is what makes the comparison complete at first
order (`Tw.scalarEq_complete`). Soundness of the exponent
arithmetic needs every atom's value positive, which the carrier `SemScalar`
provides: `x ^ p · x ^ q = x ^ (p + q)` already fails at `x = 0`. -/

/-- `t.beq t` holds. With `Tw.beq_sound`, `beq` is a lawful equality test. -/
theorem Tw.beq_refl : ∀ {k : ℕ} {Θ : List Shape} {s : Shape}
    (t : Tw B k Θ s), t.beq t = true := by
  intro k Θ s t
  induction t with
  | var n h => simp [Tw.beq]
  | unit u => simp [Tw.beq]
  | mul a b iha ihb => simp [Tw.beq, iha, ihb]
  | div a b iha ihb => simp [Tw.beq, iha, ihb]
  | qpow t q ih => simp [Tw.beq, ih]
  | lam t ih => simp [Tw.beq, ih]
  | app f a ihf iha =>
    rw [Tw.beq]
    rw [dif_pos rfl]
    simp [ihf, iha]
  | vecnil => simp [Tw.beq]
  | veccons a v iha ihv => simp [Tw.beq, iha, ihv]
  | proj v i ihv =>
    rw [Tw.beq]
    rw [dif_pos rfl]
    simp [ihv]
  | matnil => simp [Tw.beq]
  | matcons r M ihr ihM => simp [Tw.beq, ihr, ihM]
  | row M j ihM =>
    rw [Tw.beq]
    rw [dif_pos rfl]
    simp [ihM]
  | ulam t ih => simp [Tw.beq, ih]
  | uapp t μ ih => simp [Tw.beq, ih]

instance {k : ℕ} {Θ : List Shape} {s : Shape} : BEq (Tw B k Θ s) := ⟨Tw.beq⟩

instance {k : ℕ} {Θ : List Shape} {s : Shape} : LawfulBEq (Tw B k Θ s) where
  eq_of_beq h := Tw.beq_sound _ _ h
  rfl := Tw.beq_refl _

instance {k : ℕ} {Θ : List Shape} {s : Shape} : DecidableEq (Tw B k Θ s) :=
  fun a b =>
    if h : a.beq b = true then .isTrue (Tw.beq_sound a b h)
    else .isFalse fun he => h (he ▸ Tw.beq_refl a)

/-- Flatten a scalar ratio into its unit-constant part and its atoms, each
with a rational exponent. Unit constants merge into one exponent vector;
everything else is an atom at exponent `1`, negated under the fraction bar and
scaled under `qpow`. -/
def Tw.flat : {k : ℕ} → {Θ : List Shape} → Tw B k Θ .scalar →
    UExp B k × List (Tw B k Θ .scalar × ℚ)
  | _, _, .unit u => (u, [])
  | _, _, .mul a b => (Term.mul a.flat.1 b.flat.1, a.flat.2 ++ b.flat.2)
  | _, _, .div a b =>
      (Term.div a.flat.1 b.flat.1, a.flat.2 ++ b.flat.2.map fun p => (p.1, -p.2))
  | _, _, .qpow t q => (Term.rpow t.flat.1 q, t.flat.2.map fun p => (p.1, q * p.2))
  | _, _, t => (1, [(t, 1)])

omit [DecidableEq B] in
/-- Product of inverses is the inverse of the product, for lists over ℝ. -/
private theorem list_prod_map_inv {α : Type} (l : List α) (f : α → ℝ) :
    (l.map fun a => (f a)⁻¹).prod = ((l.map f).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, mul_inv, ih]
    try ring

omit [DecidableEq B] in
/-- A rational power distributes over a product of nonnegative factors. -/
private theorem list_prod_map_rpow {α : Type} (q : ℝ) :
    ∀ (l : List α) (f : α → ℝ), (∀ a ∈ l, 0 ≤ f a) →
    ((l.map f).prod) ^ q = (l.map fun a => f a ^ q).prod
  | [], _, _ => by simp
  | a :: l, f, hf => by
      simp only [List.map_cons, List.prod_cons]
      rw [Real.mul_rpow (hf a (List.mem_cons_self ..))
          (List.prod_nonneg fun x hx => by
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
            exact hf b (List.mem_cons_of_mem _ hb)),
        list_prod_map_rpow q l f fun b hb => hf b (List.mem_cons_of_mem _ hb)]

omit [DecidableEq B] in
/-- Flattening preserves the value: a scalar ratio evaluates to its
unit-constant part's scale times the product of its atoms' values raised to
their exponents. Everything in sight is positive, which is what licenses the
exponent arithmetic. -/
theorem Tw.flat_eval {k : ℕ} {Θ : List Shape} (ψ : Scaling B k) (θρ : TwEnv Θ) :
    ∀ (t : Tw B k Θ .scalar),
    (Tw.eval ψ t θρ : ℝ) = ψ.scale t.flat.1
      * ((t.flat.2.map fun p => (Tw.eval ψ p.1 θρ : ℝ) ^ (p.2 : ℝ)).prod)
  | .var n h => by simp [Tw.flat]
  | .unit u => by simp [Tw.eval, Tw.flat]
  | .mul a b => by
      have iha := Tw.flat_eval ψ θρ a
      have ihb := Tw.flat_eval ψ θρ b
      show (Tw.eval ψ a θρ : ℝ) * (Tw.eval ψ b θρ : ℝ) = _
      rw [iha, ihb]
      simp only [Tw.flat, List.map_append, List.prod_append, Scaling.scale_mul]
      ring
  | .div a b => by
      have iha := Tw.flat_eval ψ θρ a
      have ihb := Tw.flat_eval ψ θρ b
      show (Tw.eval ψ a θρ : ℝ) / (Tw.eval ψ b θρ : ℝ) = _
      rw [iha, ihb]
      simp only [Tw.flat, List.map_append, List.prod_append, Scaling.scale_div,
        List.map_map, Function.comp_def]
      rw [show (b.flat.2.map fun p => (Tw.eval ψ p.1 θρ : ℝ) ^ ((-p.2 : ℚ) : ℝ)).prod
          = ((b.flat.2.map fun p => (Tw.eval ψ p.1 θρ : ℝ) ^ (p.2 : ℝ)).prod)⁻¹ by
        rw [← list_prod_map_inv]
        refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
        push_cast
        rw [Real.rpow_neg (le_of_lt (Tw.eval ψ p.1 θρ).2)]]
      field_simp
      try ring
  | .qpow t q => by
      have ih := Tw.flat_eval ψ θρ t
      show ((Tw.eval ψ t θρ : ℝ)) ^ (q : ℝ) = _
      simp only [Tw.flat, List.map_map, Function.comp_def]
      rw [ih, mul_rpow_of_pos_left (ψ.scale_pos t.flat.1), ← Scaling.scale_rpow,
        list_prod_map_rpow (q : ℝ) t.flat.2
          (fun p => (Tw.eval ψ p.1 θρ : ℝ) ^ (p.2 : ℝ))
          (fun p _ => le_of_lt (Real.rpow_pos_of_pos (Tw.eval ψ p.1 θρ).2 _))]
      refine congrArg (_ * ·) (congrArg List.prod (List.map_congr_left fun p _ => ?_))
      rw [← Real.rpow_mul (le_of_lt (Tw.eval ψ p.1 θρ).2)]
      push_cast
      ring_nf
  | .app f a => by simp [Tw.flat]
  | .proj v i => by simp [Tw.flat]
  | .uapp t μ => by simp [Tw.flat]

/-- The total exponent an atom carries in a flattened atom list. -/
def Tw.keyMult {k : ℕ} {Θ : List Shape} (L : List (Tw B k Θ .scalar × ℚ))
    (a : Tw B k Θ .scalar) : ℚ :=
  (L.map fun p => if p.1 == a then p.2 else 0).sum

/-- Decides whether two scalar ratios are equal up to the unit algebra: equal
unit-constant parts (one exponent-vector comparison), and equal total
exponents on every atom either side mentions. Sound, and strictly wider than
`Tw.beq`: it accepts the same conversions reassociated, reordered, with their
unit constants combined differently, and with atom exponents split
differently. -/
def Tw.scalarEq {k : ℕ} {Θ : List Shape} (a b : Tw B k Θ .scalar) : Bool :=
  a.flat.1 == b.flat.1
    && (a.flat.2 ++ b.flat.2).all fun p =>
        Tw.keyMult a.flat.2 p.1 == Tw.keyMult b.flat.2 p.1

/-- An atom list as a finitely supported exponent vector: the coordinates of
the ratio in the free ℚ-vector space over the atoms. Proof-side only; the
executable comparison is `Tw.keyMult`. -/
private noncomputable def atomExp {k : ℕ} {Θ : List Shape}
    (L : List (Tw B k Θ .scalar × ℚ)) : Tw B k Θ .scalar →₀ ℚ :=
  (L.map fun p => Finsupp.single p.1 p.2).sum

private theorem atomExp_apply {k : ℕ} {Θ : List Shape}
    (L : List (Tw B k Θ .scalar × ℚ)) (t : Tw B k Θ .scalar) :
    atomExp L t = Tw.keyMult L t := by
  induction L with
  | nil => simp [atomExp, Tw.keyMult]
  | cons p L ih =>
    simp only [atomExp, Tw.keyMult, List.map_cons, List.sum_cons, Finsupp.add_apply,
      Finsupp.single_apply, beq_iff_eq] at ih ⊢
    rw [ih]

omit [DecidableEq B] in
/-- The weighted product of an atom list is a function of its exponent vector
alone. -/
private theorem wprod_eq_atomExp {k : ℕ} {Θ : List Shape} (ψ : Scaling B k)
    (θρ : TwEnv Θ) (L : List (Tw B k Θ .scalar × ℚ)) :
    (L.map fun p => (Tw.eval ψ p.1 θρ : ℝ) ^ (p.2 : ℝ)).prod
      = (atomExp L).prod fun t q => (Tw.eval ψ t θρ : ℝ) ^ (q : ℝ) := by
  induction L with
  | nil => simp [atomExp]
  | cons p L ih =>
    have hstep : atomExp (p :: L) = Finsupp.single p.1 p.2 + atomExp L := by
      simp [atomExp]
    rw [List.map_cons, List.prod_cons, hstep,
      Finsupp.prod_add_index' (fun t => by simp) (fun t q₁ q₂ => by
        push_cast
        exact Real.rpow_add (Tw.eval ψ t θρ).2 _ _),
      Finsupp.prod_single_index (by simp), ih]

/-- `scalarEq` is sound: it implies evaluation equality in every scaling and
every environment: the hypotheses `Twist.add`, `Twist.mapp` and `Twist.comp`
carry. -/
theorem Tw.scalarEq_sound {k : ℕ} {Θ : List Shape} (a b : Tw B k Θ .scalar)
    (h : Tw.scalarEq a b = true) :
    ∀ (ψ : Scaling B k) (θρ : TwEnv Θ), Tw.eval ψ a θρ = Tw.eval ψ b θρ := by
  intro ψ θρ
  simp only [Tw.scalarEq, Bool.and_eq_true] at h
  obtain ⟨hw, hm⟩ := h
  have hweq : a.flat.1 = b.flat.1 := eq_of_beq hw
  have hzero : ∀ (L : List (Tw B k Θ .scalar × ℚ)) (t : Tw B k Θ .scalar),
      (∀ p ∈ L, p.1 ≠ t) → Tw.keyMult L t = 0 := by
    intro L t hL
    induction L with
    | nil => simp [Tw.keyMult]
    | cons p L ih =>
      simp only [Tw.keyMult, List.map_cons, List.sum_cons] at ih ⊢
      rw [if_neg (by simpa using hL p (List.mem_cons_self ..)),
        ih fun p hp => hL p (List.mem_cons_of_mem _ hp), add_zero]
  have hmult : ∀ t, Tw.keyMult a.flat.2 t = Tw.keyMult b.flat.2 t := by
    intro t
    by_cases hmem : ∃ p ∈ a.flat.2 ++ b.flat.2, p.1 = t
    · obtain ⟨p, hp, rfl⟩ := hmem
      exact eq_of_beq (List.all_eq_true.mp hm p hp)
    · have hmem' : ∀ p ∈ a.flat.2 ++ b.flat.2, p.1 ≠ t := fun p hp he =>
        hmem ⟨p, hp, he⟩
      rw [hzero _ _ fun p hp => hmem' p (List.mem_append_left _ hp),
        hzero _ _ fun p hp => hmem' p (List.mem_append_right _ hp)]
  have hfq : atomExp a.flat.2 = atomExp b.flat.2 :=
    Finsupp.ext fun t => by rw [atomExp_apply, atomExp_apply, hmult t]
  refine Subtype.ext ?_
  rw [Tw.flat_eval ψ θρ a, Tw.flat_eval ψ θρ b, hweq,
    wprod_eq_atomExp ψ θρ, wprod_eq_atomExp ψ θρ, hfq]

/-! ### Completeness on the atom-free fragment

With the frees-at-one assignment, a first-order program's ratios contain no
atoms at all: every context variable contributes the literal ratio `1`, so
the flat form is a bare exponent vector. On that fragment the comparison is
complete, not merely sound. The separating lemma is `scale_eq_iff`: scalings
tell apart any two distinct exponent vectors, by scaling a base where they
differ. -/

/-- A scalar ratio is **atom-free** when its flat form carries no atoms:
the ratio is built from `unit`, `mul`, `div` and `qpow` alone. Under the
frees-at-one assignment this is every ratio a first-order program produces,
since `lam`-bound variables are the only atoms there are. -/
def Tw.AtomFree {k : ℕ} {Θ : List Shape} (t : Tw B k Θ .scalar) : Prop :=
  t.flat.2 = []

/-- **The comparison is complete on the atom-free fragment.** Two atom-free
scalar ratios that evaluate equal under every scaling compare equal: each
value is `ψ.scale` of the flat form's unit part, and scalings separate
distinct exponent vectors (`scale_eq_iff`), so agreement in every scaling
forces the unit parts to be the *same* vector, which `Tw.scalarEq` accepts. -/
theorem Tw.scalarEq_complete {k : ℕ} {Θ : List Shape}
    (a b : Tw B k Θ .scalar) (ha : a.AtomFree) (hb : b.AtomFree)
    (h : ∀ ψ : Scaling B k, Tw.eval ψ a (oneTwEnv Θ) = Tw.eval ψ b (oneTwEnv Θ)) :
    Tw.scalarEq a b = true := by
  have hu : a.flat.1 = b.flat.1 := by
    refine scale_eq_iff.mp fun ψ => ?_
    have hav := Tw.flat_eval ψ (oneTwEnv Θ) a
    have hbv := Tw.flat_eval ψ (oneTwEnv Θ) b
    rw [show a.flat.2 = [] from ha] at hav
    rw [show b.flat.2 = [] from hb] at hbv
    simp only [List.map_nil, List.prod_nil, mul_one] at hav hbv
    rw [← hav, ← hbv, h ψ]
  simp only [Tw.scalarEq, show a.flat.2 = [] from ha, show b.flat.2 = [] from hb,
    hu, List.nil_append, List.all_nil, beq_self_eq_true, Bool.and_true]

/-- **The comparison is exact on the atom-free fragment**: for atom-free
scalar ratios, `Tw.scalarEq` answers `true` precisely when the two ratios
evaluate equal under every scaling and every environment. With the
frees-at-one assignment this covers every first-order program, so at first
order the conditional declines at `add`, `mapp` and `comp` are exactly the
genuine drift disagreements. -/
theorem Tw.scalarEq_iff_eval_eq {k : ℕ} {Θ : List Shape}
    (a b : Tw B k Θ .scalar) (ha : a.AtomFree) (hb : b.AtomFree) :
    Tw.scalarEq a b = true
      ↔ ∀ (ψ : Scaling B k) (θρ : TwEnv Θ), Tw.eval ψ a θρ = Tw.eval ψ b θρ :=
  ⟨Tw.scalarEq_sound a b, fun h => Tw.scalarEq_complete a b ha hb fun ψ => h ψ _⟩

/-- The drift of a matrix application, when the analysis can name one. Per
output row `a`, the products of an entry drift with the matching argument
drift must agree across the row up to the unit algebra (`Tw.scalarEq`, exactly
the `add` check), and the representative at column `0` is the row's output
drift. Entries are extracted with `projE`/`rowE` so that literal rows compare
by their components rather than as opaque projections. Over the empty domain
the sum is empty and the output is the zero vector, so the output drift is `1`
per component. -/
def mappDrift {k : ℕ} {Θ : List Shape} {n m : ℕ}
    (tf : Tw B k Θ (.mat n m)) (tx : Tw B k Θ (.vec n)) :
    Option (Σ' tw : Tw B k Θ (.vec m),
      ∀ (ψ : Scaling B k) (θρ : TwEnv Θ) (a : Fin m) (i : Fin n),
        Tw.eval ψ tf θρ a i * Tw.eval ψ tx θρ i = Tw.eval ψ tw θρ a) :=
  match n, tf, tx with
  | 0, _, _ => some ⟨Tw.vecOfFn fun _ => .unit 1, fun _ _ _ i => i.elim0⟩
  | n' + 1, tf, tx =>
    if h : ∀ a : Fin m, ∀ i : Fin (n' + 1),
        Tw.scalarEq (.mul (Tw.projE (Tw.rowE tf a) i) (Tw.projE tx i))
          (.mul (Tw.projE (Tw.rowE tf a) 0) (Tw.projE tx 0)) then
      some ⟨Tw.vecOfFn fun a => .mul (Tw.projE (Tw.rowE tf a) 0) (Tw.projE tx 0),
        fun ψ θρ a i => by
          have hs := Tw.scalarEq_sound _ _ (h a i) ψ θρ
          rw [Tw.eval_vecOfFn]
          simpa [Tw.eval, Tw.eval_projE, Tw.eval_rowE] using hs⟩
    else none

/-- The drift of a composition, when the analysis can name one: the analogue
of `mappDrift` per entry `(a, i)`, with agreement across the middle index and
the representative taken at middle index `0`. -/
def compDrift {k : ℕ} {Θ : List Shape} {p n m : ℕ}
    (tf : Tw B k Θ (.mat n m)) (tg : Tw B k Θ (.mat p n)) :
    Option (Σ' tw : Tw B k Θ (.mat p m),
      ∀ (ψ : Scaling B k) (θρ : TwEnv Θ) (a : Fin m) (i : Fin p) (b : Fin n),
        Tw.eval ψ tf θρ a b * Tw.eval ψ tg θρ b i = Tw.eval ψ tw θρ a i) :=
  match n, tf, tg with
  | 0, _, _ =>
      some ⟨Tw.matOfFn fun _ => Tw.vecOfFn fun _ => .unit 1, fun _ _ _ _ b => b.elim0⟩
  | n' + 1, tf, tg =>
    if h : ∀ a : Fin m, ∀ i : Fin p, ∀ b : Fin (n' + 1),
        Tw.scalarEq (.mul (Tw.projE (Tw.rowE tf a) b) (Tw.projE (Tw.rowE tg b) i))
          (.mul (Tw.projE (Tw.rowE tf a) 0) (Tw.projE (Tw.rowE tg 0) i)) then
      some ⟨Tw.matOfFn fun a => Tw.vecOfFn fun i =>
          .mul (Tw.projE (Tw.rowE tf a) 0) (Tw.projE (Tw.rowE tg 0) i),
        fun ψ θρ a i b => by
          have hs := Tw.scalarEq_sound _ _ (h a i b) ψ θρ
          rw [Tw.eval_matOfFn, Tw.eval_vecOfFn]
          simpa [Tw.eval, Tw.eval_projE, Tw.eval_rowE] using hs⟩
    else none

/-- **Computing the ratio.** For a derivation, the accumulated conversion ratio
together with its `Twist` derivation, or `none` where the analysis does not
apply. The pin marker `p` is the frees-at-one assignment: a variable below `p`
is `lam`-bound and enters as an atom, a variable at or beyond `p` is a context
variable of the program and enters at the literal ratio `1`. The exported
diagnostic runs at `p = 0`.

The `add` check is `Tw.scalarEq`: branch ratios compare with their unit
constants merged into one exponent vector and their atoms as coordinates of a
free ℚ-vector space, one total exponent per atom, so the same conversions
reordered, reassociated, split into different rational powers, and cancelled
against themselves across the fraction bar are all accepted; the positive
scalar carrier is what makes `x / x = 1` sound. What the check never does is
identify *distinct* atoms, since nothing relates two arguments' ratios; but
atoms arise only under `lam` binders, so a first-order ratio has none and the
check is exact there (`Tw.scalarEq_iff_eval_eq`).
`mapp` and `comp` run the same check per output component, across the summed
index, and `log` and `exp` run it against the literal ratio `1`, accepting
exactly the arguments whose ratio is identifiably trivial. Everything
downstream of the checks is complete: `Tw.nfOne` decides triviality of the
*resulting* ratio exactly. -/
def twistOf : {j k : ℕ} → {Δ : DCtx D j k} → {Γ : Ctx B D j k} → {e : Tm B D j k} →
    {τ : Ty B D j k} → (p : ℕ) → (Θ : List Shape) → (hΘ : Θ = Γ.shapes) →
    (d : HasTy Δ Γ e τ) → Option (Σ' t : Tw B k Θ (Ty.shape τ), Twist p Θ d t)
  | _, _, _, Γ, _, _, p, Θ, hΘ, .var (n := n) h =>
      if hp : n < p then
        match hn : Θ[n]? with
        | some s =>
            if hs : s = Ty.shape _ then
              some ⟨.var n (hs ▸ hn), .var h (hs ▸ hn) hp⟩
            else none
        | none => none
      else
        some ⟨Tw.one _, .varOne h (by rw [hΘ]; exact Ctx.shapes_getElem? h)
          (Nat.le_of_not_lt hp)⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .lam (τ := σ) db => do
      let ⟨t, ht⟩ ← twistOf (p + 1) (Ty.shape σ :: Θ) (by simp [hΘ]) db
      some ⟨.lam t, .lam ht⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .app df da => do
      let ⟨tf, htf⟩ ← twistOf p Θ hΘ df
      let ⟨ta, hta⟩ ← twistOf p Θ hΘ da
      some ⟨Tw.appE tf ta,
        .ratio (t := .app tf ta)
          (fun ψ θρ => (Tw.eval_appE ψ tf ta θρ).symm) (.app htf hta)⟩
  | _, _, _, _, _, _, p, Θ, _, .lit => some ⟨.unit 1, .lit⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .mul da db => do
      let ⟨ta, hta⟩ ← twistOf p Θ hΘ da
      let ⟨tb, htb⟩ ← twistOf p Θ hΘ db
      some ⟨.mul ta tb, .mul hta htb⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .div da db => do
      let ⟨ta, hta⟩ ← twistOf p Θ hΘ da
      let ⟨tb, htb⟩ ← twistOf p Θ hΘ db
      some ⟨.div ta tb, .div hta htb⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .add da db => do
      let ⟨ta, hta⟩ ← twistOf p Θ hΘ da
      let ⟨tb, htb⟩ ← twistOf p Θ hΘ db
      if hb : Tw.scalarEq ta tb then
        some ⟨ta, .add (Tw.scalarEq_sound ta tb hb) hta htb⟩
      else none
  | _, _, _, _, _, _, p, Θ, hΘ, .convert (u := u) (v := v) da hsd => do
      let ⟨ta, hta⟩ ← twistOf p Θ hΘ da
      some ⟨.mul ta (.div (.unit u) (.unit v)), .convert hsd hta⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .ulam db => do
      let ⟨t, ht⟩ ← twistOf p Θ (by simp [hΘ]) db
      some ⟨.ulam t, .ulam ht⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .uapp (τ := τ) (σ := σ) df hd => do
      let ⟨tf, htf⟩ ← twistOf p Θ hΘ df
      some ⟨Tw.castShape (Ty.shape_subst τ σ).symm (Tw.uappE tf σ),
        .ratio (t := Tw.castShape (Ty.shape_subst τ σ).symm (.uapp tf σ))
          (fun ψ θρ => by
            rw [Tw.eval_castShape, Tw.eval_castShape]
            exact congrArg (fun x => (Ty.shape_subst τ σ).symm ▸ x)
              (Tw.eval_uappE ψ tf σ θρ).symm) (.uapp hd htf)⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .dlam db => do
      let ⟨t, ht⟩ ← twistOf p Θ (by simp [hΘ]) db
      some ⟨t, .dlam ht⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .dapp (τ := τ) (d := dm) df => do
      let ⟨tf, htf⟩ ← twistOf p Θ hΘ df
      some ⟨Tw.castShape (Ty.shape_substDim τ dm).symm tf, .dapp htf⟩
  | _, _, _, _, _, _, p, Θ, _, .vnil => some ⟨.vecnil, .vnil⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .vcons de dv => do
      let ⟨te, hte⟩ ← twistOf p Θ hΘ de
      let ⟨tv, htv⟩ ← twistOf p Θ hΘ dv
      some ⟨.veccons te tv, .vcons hte htv⟩
  | _, _, _, _, _, _, p, Θ, _, .mnil => some ⟨.matnil, .mnil⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .mcons dr dM => do
      let ⟨tr, htr⟩ ← twistOf p Θ hΘ dr
      let ⟨tM, htM⟩ ← twistOf p Θ hΘ dM
      some ⟨.matcons (Tw.castShape (by simp) tr) tM, .mcons htr htM⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .idx (i := i) de hu => do
      let ⟨t, ht⟩ ← twistOf p Θ hΘ de
      let hlt : i < _ := (List.getElem?_eq_some_iff.mp hu).1
      let heqp : ∀ (ψ : Scaling B _) (θρ : TwEnv Θ),
          Tw.eval ψ (Tw.proj t ⟨i, hlt⟩) θρ
            = Tw.eval ψ (Tw.projE t ⟨i, hlt⟩) θρ :=
        fun ψ θρ => (Tw.eval_projE ψ t ⟨i, hlt⟩ θρ).symm
      some ⟨Tw.projE t ⟨i, hlt⟩, .ratio heqp (.idx hu ht)⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .mapp df dx => do
      let ⟨tf, htf⟩ ← twistOf p Θ hΘ df
      let ⟨tx, htx⟩ ← twistOf p Θ hΘ dx
      let ⟨tw, heq⟩ ← mappDrift tf tx
      some ⟨tw, .mapp heq htf htx⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .comp df dg => do
      let ⟨tf, htf⟩ ← twistOf p Θ hΘ df
      let ⟨tg, htg⟩ ← twistOf p Θ hΘ dg
      let ⟨tw, heq⟩ ← compDrift tf tg
      some ⟨tw, .comp heq htf htg⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .pow (q := q) de => do
      let ⟨t, ht⟩ ← twistOf p Θ hΘ de
      some ⟨.qpow t q, .pow ht⟩
  | _, _, _, _, _, _, p, Θ, hΘ, .log de => do
      let ⟨t, ht⟩ ← twistOf p Θ hΘ de
      if h1 : Tw.scalarEq t (.unit 1) then
        some ⟨.unit 1, .log (fun ψ θρ =>
          (Tw.scalarEq_sound t (.unit 1) h1 ψ θρ).trans
            (Tw.eval_one ψ .scalar θρ)) ht⟩
      else none
  | _, _, _, _, _, _, p, Θ, hΘ, .exp de => do
      let ⟨t, ht⟩ ← twistOf p Θ hΘ de
      if h1 : Tw.scalarEq t (.unit 1) then
        some ⟨.unit 1, .exp (fun ψ θρ =>
          (Tw.scalarEq_sound t (.unit 1) h1 ψ θρ).trans
            (Tw.eval_one ψ .scalar θρ)) ht⟩
      else none
  -- `ucon` is the one unconditional decline, by design rather than necessity.
  -- The relation would accept it at ratio `u^(-1/2)` (its defect is incurred
  -- once where conversion's is incurred twice, hence the half exponent), but a
  -- unit constant's defect is a covariance failure with no dependence on the
  -- declarations, and tracking it would make a reported drift mean two
  -- different things. With `ucon` declined, conversion remains the only
  -- analyzed construct that reads the valuation.
  | _, _, _, _, _, _, _, _, _, .ucon => none

/-! ## The diagnostic, end to end -/

/-- **Unit drift**: the normal form of a program's accumulated conversion
ratio, computed from its derivation. `some 1` means the conversions cancel;
`some w` with `w ≠ 1` exhibits the drift; `none` means the analysis does not
apply (a `ucon`, a `log` or `exp` whose argument ratio is not identifiably
trivial, or an `add` whose branch ratios `Tw.scalarEq` cannot identify). -/
def unitDrift {j k : ℕ} {Δ : DCtx D j k} {us : List (UExp B k)} {u : UExp B k}
    {e : Tm B D j k} (d : HasTy Δ (scalarCtx us) e (.Q u)) : Option (UExp B k) :=
  (twistOf 0 (us.map fun _ => Shape.scalar) (shapes_scalarCtx us).symm d).map
    fun p => Tw.nfOne p.1

omit [Fintype D] [DecidableEq D] in
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

/-! ### Top-level abstractions as inputs

A first-order kernel is as often written `λx. λy. e` as it is written as an
open term over a context. The two spellings name the same inputs, so the
diagnostic should give them the same verdict. -/

/-- **Unit drift, through leading abstractions.** Strips the leading `lam`
binders and analyzes the body over the extended context with the all-ones
assignment (`p = 0`): every stripped binder is a program input, pinned at
ratio `1` exactly as a context variable is, so a lambda-wrapped kernel
receives the same verdict as its open-term spelling. Abstractions in
non-leading position keep their atoms. Answers at quantity-typed bodies and
returns `none` elsewhere, exactly as `unitDrift`. -/
def unitDriftLam : {j k : ℕ} → {Δ : DCtx D j k} → {Γ : Ctx B D j k} →
    {e : Tm B D j k} → {τ : Ty B D j k} → HasTy Δ Γ e τ → Option (UExp B k)
  | _, _, _, _, _, _, .lam db => unitDriftLam db
  | _, _, _, Γ, _, .Q _, d =>
      (twistOf 0 (Ctx.shapes Γ) rfl d).map fun p => Tw.nfOne p.1
  | _, _, _, _, _, _, _ => none

/-! ## Closing the loop with the declarations

A closed dimensionless program whose conversions cancel computes a number that
does not depend on the declared unit magnitudes at all. Composed with adequacy,
the same statement holds of the compiled program: its output is invariant
across every consistent extension of the declaration set. This is the
ratio-level analogue of `evalC_convert_declared`: `Twist` joined to `Declare`
the way `eval_adeq` joined `Dynamics` to `Declare`. -/

omit [Fintype B] [DecidableEq B] in
/-- Any scaling is reachable from any other by composition: log-space is a
group. -/
theorem Scaling.comp_sub {k : ℕ} (V V' : Scaling B k) :
    V.comp ⟨fun b => V'.base b - V.base b, fun i => V'.vars i - V.vars i⟩ = V' := by
  cases V' with | mk b' v' =>
  simp only [Scaling.comp, Scaling.mk.injEq]
  exact ⟨funext fun x => by ring, funext fun x => by ring⟩

omit [Fintype D] [DecidableEq D] in
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

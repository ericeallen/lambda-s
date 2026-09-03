/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Syntax

/-!
# Typing for Λs, and a checker proved correct against it

Two things live here, and the point is that only one of them can be wrong:

* `HasTy`, the **declarative** typing relation: what it *means* for a term to
  have a type;
* `check`, an **executable** decision procedure that returns the derivation.

Because `check` returns a derivation rather than a type, soundness is not a
theorem. There is nothing for it to say: a checker that cannot produce a type
without producing its justification cannot accept an ill-typed term. That
deletes the usual half of the correctness statement, and with it the usual place
for a refinement gap to hide.

What remains is `check_eq`, and it is stated more sharply than completeness
normally is: the checker finds not merely *a* derivation of a well-typed term
but *the* one it was given. Since `check Δ Γ e` is a single value, uniqueness of
derivations follows at once, and `HasTy` is a `Subsingleton`.

`HasTy` is `Type`-valued rather than `Prop`-valued, so that a derivation may be
eliminated into `Type`, which is what a denotation of terms requires. By the
`Subsingleton` instance nothing is lost by this: the data a derivation carries
is determined by the judgement it proves.

## Where the units bite

Five rules do the work, and each corresponds to something argued for in the
design:

* `add` requires the two units to be **equal**. This is where dimensional errors
  are caught.
* `root` is **primitive**, with side condition `n ≠ 0`. It is not definable from
  the field operations, because the closure of the arguments under arithmetic is
  the subgroup they generate and roots escape it. Over ℚ exponents it is
  *total*, so `√` of a volume is well-typed here and is a type error in F#.
* `idx` reads the unit **out of the space**. `V[i]? = some u` is Λs in one
  hypothesis: the unit of a component is determined by its index.
* `uapp` **substitutes** a unit expression for a unit variable, and checks that
  the expression has the **declared dimension**. Because unit expressions are
  exponent vectors, substitution is a linear map and equality needs no
  normalization pass.
* `convert` requires the two units to have the same dimension. Decidable, so the
  trusted core checks it rather than delegating to an elaborator.

## Two contexts

Typing carries a dimension context `Δ` alongside the usual `Γ`. `Δ` records the
declared dimension of each unit variable in scope, which is what `dimOf` needs
to give a total answer under a binder, and hence what makes `convert` usable in
polymorphic code. `∀u. τ` is `∀δ. ∀u:δ. τ`, so an "unbounded" unit variable is
bounded by a dimension *variable*: `dimOf` reports it, and it matches nothing
concrete, which is exactly the rejection an unbounded quantifier should give.

## Why completeness is available

The calculus is explicitly typed (lambdas are annotated, `Λu.e` and `e[μ]` are
written rather than inferred), so typing is syntax-directed and types are
*unique*. `infer` therefore returns **the** type or nothing, with no
most-general-type caveat, and `infer_complete` holds. Inferring the `Λu` and
`[μ]` instead would require let-generalization and hence the abelian-group
unification in `LambdaS.Unify`, where the guarantee weakens from uniqueness to
principality.
-/

namespace LambdaS

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D]

/-- The declarative typing relation, over a dimension context `Δ` and a value
context `Γ`. -/
inductive HasTy : {j k : ℕ} → DCtx D j k → Ctx B D j k → Tm B D j k → Ty B D j k → Type where
  | var {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {n τ} :
      Γ[n]? = some τ → HasTy Δ Γ (.var n) τ
  | lam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {τ e σ} :
      HasTy Δ (τ :: Γ) e σ → HasTy Δ Γ (.lam τ e) (.arrow τ σ)
  | app {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f a τ σ} :
      HasTy Δ Γ f (.arrow τ σ) → HasTy Δ Γ a τ → HasTy Δ Γ (.app f a) σ
  | lit {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {q} : HasTy Δ Γ (.lit q) (.Q 1)
  | ucon {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u} : HasTy Δ Γ (.ucon u) (.Q u)
  | mul {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {a b u v} :
      HasTy Δ Γ a (.Q u) → HasTy Δ Γ b (.Q v) → HasTy Δ Γ (.mul a b) (.Q (Term.mul u v))
  | div {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {a b u v} :
      HasTy Δ Γ a (.Q u) → HasTy Δ Γ b (.Q v) → HasTy Δ Γ (.div a b) (.Q (Term.div u v))
  /-- Addition demands equal units. The rule that catches the errors.

  Equal, not merely same-dimension: adding metres to feet is a type error, and
  `convert` is how you say you meant it. -/
  | add {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {a b u} :
      HasTy Δ Γ a (.Q u) → HasTy Δ Γ b (.Q u) → HasTy Δ Γ (.add a b) (.Q u)
  /-- Roots are primitive and, over ℚ, total. -/
  | root {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {n e u} :
      n ≠ 0 → HasTy Δ Γ e (.Q u) → HasTy Δ Γ (.root n e) (.Q (Term.rpow u (1 / (n : ℚ))))
  /-- The unit of a component is read out of the space. -/
  | idx {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e V i u} :
      HasTy Δ Γ e (.vec V) → V[i]? = some u → HasTy Δ Γ (.idx e i) (.Q u)
  | mapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f x V W} :
      HasTy Δ Γ f (.lin V W) → HasTy Δ Γ x (.vec V) → HasTy Δ Γ (.mapp f x) (.vec W)
  | comp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f g U V W} :
      HasTy Δ Γ f (.lin V W) → HasTy Δ Γ g (.lin U V) → HasTy Δ Γ (.comp f g) (.lin U W)
  /-- `log` demands a dimensionless argument. This is the rule that makes the
  base-measure problem static: a probability density over a space with measure
  `μ` carries `μ⁻¹`, so `log p` is rejected, while `log (p/q)` for two densities
  of equal weight is fine because the ratio lands at `1`. -/
  | log {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e} :
      HasTy Δ Γ e (.Q 1) → HasTy Δ Γ (.log e) (.Q 1)
  | exp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e} :
      HasTy Δ Γ e (.Q 1) → HasTy Δ Γ (.exp e) (.Q 1)
  /-- Unit abstraction, `Λu:d. e`. Both contexts move: `Δ` records the bound
  variable's declared dimension, and `Γ` is weakened so the variable is
  genuinely fresh: nothing already in scope can mention it. -/
  | ulam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {d e τ} :
      HasTy (Δ.cons d) Γ.weaken e τ → HasTy Δ Γ (.ulam d e) (.all d τ)
  /-- Unit application. The instantiating expression must have the **declared
  dimension**: the check that makes bounded quantification mean something. -/
  | uapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f d τ σ} :
      HasTy Δ Γ f (.all d τ) → dimOf Δ σ = d → HasTy Δ Γ (.uapp f σ) (τ.subst σ)
  /-- Dimension abstraction, `Λδ. e`. -/
  | dlam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e τ} :
      HasTy Δ.weakenDim Γ.weakenDim e τ → HasTy Δ Γ (.dlam e) (.allDim τ)
  /-- Dimension application, `e{d}`. Unconstrained: any dimension may be
  supplied, which is what makes `∀δ. ∀u:δ. τ` genuinely unbounded. -/
  | dapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f τ} {d : DExp D j} :
      HasTy Δ Γ f (.allDim τ) → HasTy Δ Γ (.dapp f d) (τ.substDim d)
  /-- **Conversion.** Only between units of the same dimension, and `Δ` is what
  lets that be decided under a binder. -/
  | convert {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e u v} :
      HasTy Δ Γ e (.Q u) → SameDim Δ u v → HasTy Δ Γ (.convert e u v) (.Q v)

section Check

/-- The checker. Syntax-directed, total, executable, and it returns the
**derivation**, not merely the type.

That is the whole of soundness. A separate "anything the checker accepts is
well-typed" theorem would have to reconstruct a derivation the checker had
already built and thrown away; here there is nothing to reconstruct and nothing
to prove. What remains (`check_eq`) is the only direction with content: that
the checker never rejects a term the rules accept, and indeed finds the very
derivation it was given. -/
def check : {j k : ℕ} → (Δ : DCtx D j k) → (Γ : Ctx B D j k) → (e : Tm B D j k) →
    Option (Σ τ : Ty B D j k, HasTy Δ Γ e τ)
  | _, _, _, Γ, .var n =>
      match h : Γ[n]? with
      | some τ => some ⟨τ, .var h⟩
      | none => none
  | _, _, Δ, Γ, .lam τ e => (check Δ (τ :: Γ) e).map fun ⟨_, d⟩ => ⟨_, .lam d⟩
  | _, _, Δ, Γ, .app f a =>
      match check Δ Γ f, check Δ Γ a with
      | some ⟨.arrow τ _, df⟩, some ⟨τ', da⟩ =>
          if h : τ' = τ then some ⟨_, .app df (h ▸ da)⟩ else none
      | _, _ => none
  | _, _, _, _, .lit _ => some ⟨_, .lit⟩
  | _, _, _, _, .ucon _ => some ⟨_, .ucon⟩
  | _, _, Δ, Γ, .mul a b =>
      match check Δ Γ a, check Δ Γ b with
      | some ⟨.Q _, da⟩, some ⟨.Q _, db⟩ => some ⟨_, .mul da db⟩
      | _, _ => none
  | _, _, Δ, Γ, .div a b =>
      match check Δ Γ a, check Δ Γ b with
      | some ⟨.Q _, da⟩, some ⟨.Q _, db⟩ => some ⟨_, .div da db⟩
      | _, _ => none
  | _, _, Δ, Γ, .add a b =>
      match check Δ Γ a, check Δ Γ b with
      | some ⟨.Q u, da⟩, some ⟨.Q v, db⟩ =>
          if h : u = v then some ⟨_, .add (h ▸ da) db⟩ else none
      | _, _ => none
  | _, _, Δ, Γ, .root n e =>
      if h : n = 0 then none else
        match check Δ Γ e with
        | some ⟨.Q _, d⟩ => some ⟨_, .root h d⟩
        | _ => none
  | _, _, Δ, Γ, .idx e i =>
      match check Δ Γ e with
      | some ⟨.vec V, d⟩ =>
          match hv : V[i]? with
          | some _ => some ⟨_, .idx d hv⟩
          | none => none
      | _ => none
  | _, _, Δ, Γ, .mapp f x =>
      match check Δ Γ f, check Δ Γ x with
      | some ⟨.lin V _, df⟩, some ⟨.vec V', dx⟩ =>
          if h : V' = V then some ⟨_, .mapp df (h ▸ dx)⟩ else none
      | _, _ => none
  | _, _, Δ, Γ, .comp f g =>
      match check Δ Γ f, check Δ Γ g with
      | some ⟨.lin V _, df⟩, some ⟨.lin _ V', dg⟩ =>
          if h : V' = V then some ⟨_, .comp df (h ▸ dg)⟩ else none
      | _, _ => none
  | _, _, Δ, Γ, .log e =>
      match check Δ Γ e with
      | some ⟨.Q u, d⟩ => if h : u = 1 then some ⟨_, .log (h ▸ d)⟩ else none
      | _ => none
  | _, _, Δ, Γ, .exp e =>
      match check Δ Γ e with
      | some ⟨.Q u, d⟩ => if h : u = 1 then some ⟨_, .exp (h ▸ d)⟩ else none
      | _ => none
  | _, _, Δ, Γ, .ulam _ e => (check (Δ.cons _) Γ.weaken e).map fun ⟨_, d⟩ => ⟨_, .ulam d⟩
  | _, _, Δ, Γ, .uapp f σ =>
      match check Δ Γ f with
      | some ⟨.all d _, df⟩ =>
          if h : dimOf Δ σ = d then some ⟨_, .uapp df h⟩ else none
      | _ => none
  | _, _, Δ, Γ, .dlam e => (check Δ.weakenDim Γ.weakenDim e).map fun ⟨_, d⟩ => ⟨_, .dlam d⟩
  | _, _, Δ, Γ, .dapp f _ =>
      match check Δ Γ f with
      | some ⟨.allDim _, df⟩ => some ⟨_, .dapp df⟩
      | _ => none
  | _, _, Δ, Γ, .convert e u v =>
      match check Δ Γ e with
      | some ⟨.Q u', d⟩ =>
          if h : u' = u then
            if hs : SameDim Δ u v then some ⟨_, .convert (h ▸ d) hs⟩ else none
          else none
      | _ => none

/-- The type the checker assigns, when one is wanted without its derivation. -/
def infer {j k : ℕ} (Δ : DCtx D j k) (Γ : Ctx B D j k) (e : Tm B D j k) :
    Option (Ty B D j k) := (check Δ Γ e).map Sigma.fst

/-- **Completeness.** Everything the rules accept, the checker finds, at
exactly that type, and returning *that very derivation*.

The equation is stated against the given `d` rather than against some derivation
the checker happens to build, which is stronger than completeness usually is and
costs nothing: the proof is the same induction. Two things fall out. First,
together with `check` returning its derivation, the equation is the whole
correctness statement, so soundness needs no theorem: the checker cannot
produce a type without producing
the derivation that justifies it. Second, since `check Δ Γ e` is one value,
any two derivations of the same judgement are equal. -/
theorem check_eq : ∀ {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ : Ty B D j k} (d : HasTy Δ Γ e τ), check Δ Γ e = some ⟨τ, d⟩ := by
  intro j k Δ Γ e τ d
  induction d with
  | var hn =>
    simp only [check]
    split
    · next x h => obtain rfl : x = _ := Option.some.inj (h.symm.trans hn); rfl
    · next h => exact absurd (h.symm.trans hn) (by simp)
  | lam _ ih => simp [check, ih]
  | app _ _ ihf iha => simp [check, ihf, iha]
  | lit => rfl
  | ucon => rfl
  | mul _ _ iha ihb => simp [check, iha, ihb]
  | div _ _ iha ihb => simp [check, iha, ihb]
  | add _ _ iha ihb => simp [check, iha, ihb]
  | root hn _ ih => simp [check, ih, hn]
  | idx _ hu ih =>
    simp only [check, ih]
    split
    · next x h => obtain rfl : x = _ := Option.some.inj (h.symm.trans hu); rfl
    · next h => exact absurd (h.symm.trans hu) (by simp)
  | mapp _ _ ihf ihx => simp [check, ihf, ihx]
  | comp _ _ ihf ihg => simp [check, ihf, ihg]
  | log _ ih => simp [check, ih]
  | exp _ ih => simp [check, ih]
  | ulam _ ih => simp [check, ih]
  | uapp _ hd ihf => simp [check, ihf, hd]
  | dlam _ ih => simp [check, ih]
  | dapp _ ihf => simp [check, ihf]
  | convert _ hsd ih => simp [check, ih, hsd]

/-- **Derivations are unique.** A judgement is justified in at most one way, so
`HasTy` is a proposition in everything but its sort: it carries data only in
the sense that the data is determined.

This is what licenses speaking of *the* denotation of a term. Anything defined
by recursion over a derivation is thereby a function of the term alone, and no
theorem is needed to say so. It is also why making `HasTy` `Type`-valued costs
nothing in expressiveness: the elimination restriction that `Prop` would impose
is the only thing given up, and there was never a second derivation for it to
protect. -/
instance {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ : Ty B D j k} : Subsingleton (HasTy Δ Γ e τ) :=
  ⟨fun d₁ d₂ => by simpa using (check_eq d₁).symm.trans (check_eq d₂)⟩

/-- **Completeness**, stated for the type alone. -/
theorem infer_complete {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ : Ty B D j k} (d : HasTy Δ Γ e τ) : infer Δ Γ e = some τ := by
  simp [infer, check_eq d]

/-- **The checker decides typing exactly.** It accepts a term at a type
precisely when the rules derive it.

`Nonempty` because a derivation is data: what the judgement asserts is that one
*exists*, and that is a proposition even though the derivation is not. -/
theorem infer_eq_some_iff {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ : Ty B D j k} : infer Δ Γ e = some τ ↔ Nonempty (HasTy Δ Γ e τ) := by
  constructor
  · intro h
    obtain ⟨⟨_, d⟩, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨d⟩
  · rintro ⟨d⟩; exact infer_complete d

/-- Typing is decidable, as a corollary rather than a separate development. -/
instance {j k : ℕ} (Δ : DCtx D j k) (Γ : Ctx B D j k) (e : Tm B D j k) (τ : Ty B D j k) :
    Decidable (Nonempty (HasTy Δ Γ e τ)) :=
  decidable_of_iff (infer Δ Γ e = some τ) infer_eq_some_iff

/-- **Types are unique**, which is what makes `infer` return *the* type rather
than a most general one. -/
theorem HasTy.unique {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ σ : Ty B D j k} (h₁ : HasTy Δ Γ e τ) (h₂ : HasTy Δ Γ e σ) : τ = σ := by
  have := infer_complete h₁
  have := infer_complete h₂
  simp_all

end Check

end LambdaS

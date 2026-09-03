/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Normalization
import LambdaS.Fundamental
import LambdaS.Declare

/-!
# Adequacy: the evaluator computes the denotation, at the declared factors

Two halves of the conversion story have been proved separately and never joined.

`LambdaS.Declare` says when a set of unit declarations determines a valuation,
and rejects the sets that do not. `LambdaS.Conversion` says a valuation makes
conversion path-independent. `LambdaS.Fundamental` gives the denotational
semantics, in which `convert` reads that valuation for its factor. (Unit
application also consults it, but only to pick the index at which a family is
sampled.)
`LambdaS.Dynamics` gives the evaluator, which takes the conversion factor from
an **abstract oracle** `cf`, constrained by nothing at all.

So the declarations determine a number, and the evaluator multiplies by a
number, and nothing but `eval_adeq` says they are the same number.
Every worked example elsewhere passes `fun _ _ => 1.0`; this file is where the
conversion oracle is finally pinned.

`eval_adeq` is the join. Take the oracle to be `conv V` (the conversion the
valuation determines, hence the one the declarations determine), and evaluation
of a well-typed term agrees with its denotation, unit and magnitude both. The
`convert` case is where the content is: the evaluator's factor is
`conv V (substU η u) (substU η v)` and the denotation's is
`conv (V.pull η) u v`, and `Scaling.scale_pull` says those are equal.

## Why the relation carries the environments

`Adeq` is indexed by the runtime unit and dimension environments rather than
stated at grounded types. That is what keeps it free of transports: at `∀u:δ. τ`
the relation recurses at `Fin.cons μ η` and at `τ` itself, so the denotation
stays in `Ty.den τ` and never has to be cast along `Ty.den_subst`. The scaling
follows the environments by `Scaling.pull`, and `pull_cons` is the lemma that
says instantiating a unit variable and extending the scaling agree.

Function, unit-polymorphic and dimension-polymorphic values are related
behaviorally, as in `LambdaS.Normalization`: a closure is adequate when
applying it to adequate arguments yields adequate results. Nothing is said about
the closure's captured scope, which is what lets the relation live at a single
type while the evaluator works at many.
-/

namespace LambdaS

open scoped BigOperators

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D]

/-- **Adequacy at a type**: a runtime value carries exactly the magnitude the
denotation predicts, at exactly the unit the type predicts. -/
def Adeq (V : Scaling B 0) : {j k : ℕ} → UEnv B k → DEnv D j → (τ : Ty B D j k) →
    Val ℝ B D → Ty.den τ → Prop
  | _, _, η, _, .Q u, v, x => v = .scalar ⟨x, substU η u⟩
  | _, _, η, _, .vec Vs, v, f => v = .vector (List.ofFn f) (Vs.map (substU η))
  | _, _, η, _, .lin Vs Ws, v, A =>
      v = .matrix (List.ofFn fun a => List.ofFn fun i => A a i)
        (Vs.map (substU η)) (Ws.map (substU η))
  | _, _, η, δ, .arrow a b, v, f =>
      ∃ (j' k' : ℕ) (σ' : Ty B D j' k') (body : Tm B D j' k')
        (ρ' : List (Val ℝ B D)) (η' : UEnv B k') (δ' : DEnv D j'),
        v = .closure σ' body ρ' η' δ' ∧
        ∀ w y, Adeq V η δ a w y →
          ∀ n v', eval (conv V) n j' k' η' δ' (w :: ρ') body = some v' →
            Adeq V η δ b v' (f y)
  | _, _, η, δ, .all d τ, v, F =>
      ∃ (j' k' : ℕ) (d' : DExp D j') (body : Tm B D j' (k' + 1))
        (ρ' : List (Val ℝ B D)) (η' : UEnv B k') (δ' : DEnv D j'),
        v = .uclos d' body ρ' η' δ' ∧
        ∀ μ : UExp B 0, dimOf (D := D) (DCtx.nil D) μ = substU δ d →
          ∀ n v', eval (conv V) n j' (k' + 1) (Fin.cons μ η') δ' ρ' body = some v' →
            Adeq V (Fin.cons μ η) δ τ v' (F (V.logScale μ))
  | _, _, η, δ, .allDim τ, v, F =>
      ∃ (j' k' : ℕ) (body : Tm B D (j' + 1) k')
        (ρ' : List (Val ℝ B D)) (η' : UEnv B k') (δ' : DEnv D j'),
        v = .dclos body ρ' η' δ' ∧
        ∀ dd : DExp D 0, ∀ n v',
          eval (conv V) n (j' + 1) k' η' (Fin.cons dd δ') ρ' body = some v' →
            Adeq V η (Fin.cons dd δ) τ v' F

/-- Adequacy of an environment, pointwise. An inductive rather than a recursive
definition so that its indices unify up to definitional equality: the binder
cases present the context as `Γ.weaken`, not as a literal list. -/
inductive EnvAdeq (V : Scaling B 0) {j k : ℕ} (η : UEnv B k) (δ : DEnv D j) :
    (Γ : Ctx B D j k) → List (Val ℝ B D) → Env Γ → Prop where
  | nil {ρ : List (Val ℝ B D)} {ρd : Env ([] : Ctx B D j k)} : EnvAdeq V η δ [] ρ ρd
  | cons {τ : Ty B D j k} {Γ : Ctx B D j k} {w : Val ℝ B D}
      {ρ : List (Val ℝ B D)} {ρd : Env (τ :: Γ)} :
      Adeq V η δ τ w ρd.1 → EnvAdeq V η δ Γ ρ ρd.2 → EnvAdeq V η δ (τ :: Γ) (w :: ρ) ρd

/-! ## Transporting adequacy along a substitution

Grounding the *type* corresponds to composing the *environments*, which is what
lets the binder cases of `eval_adeq` appeal to the induction hypothesis. It is
the same shape as `rel_ground`, and for the same reason: `Adeq` is a type-indexed
family, so a change of type has to be matched by a transport of the denotation.
-/

/-- `List.ofFn` respects heterogeneous equality of index-shifted functions. -/
theorem ofFn_heq {m n : ℕ} (h : m = n) {f : Fin m → ℝ} {g : Fin n → ℝ}
    (hfg : HEq f g) : List.ofFn f = List.ofFn g := by
  subst h; cases hfg; rfl

/-- The two-index version, for linear maps. -/
theorem ofFn₂_heq {m n m' n' : ℕ} (h1 : m = m') (h2 : n = n')
    {A : Fin m → Fin n → ℝ} {C : Fin m' → Fin n' → ℝ} (hAC : HEq A C) :
    (List.ofFn fun a => List.ofFn fun i => A a i)
      = List.ofFn fun a => List.ofFn fun i => C a i := by
  subst h1; subst h2; cases hAC; rfl

/-- **Adequacy transports along grounding.** -/
theorem adeq_ground (V : Scaling B 0) : ∀ {j k : ℕ} (τ : Ty B D j k) {j₀ k₀ : ℕ}
    (η : UEnv B k₀) (δ : DEnv D j₀) (ηs : Fin k → UExp B k₀) (δs : Fin j → DExp D j₀)
    (v : Val ℝ B D) {x : Ty.den τ} {x' : Ty.den (Ty.ground ηs δs τ)}, HEq x x' →
    (Adeq V η δ (Ty.ground ηs δs τ) v x'
      ↔ Adeq V (fun i => substU η (ηs i)) (fun i => substU δ (δs i)) τ v x) := by
  intro j k τ
  induction τ with
  | Q u =>
    intro _ _ η δ ηs δs v x x' hx
    obtain rfl := eq_of_heq hx
    simp [Ty.ground, Adeq, substU_comp]
  | vec Vs =>
    intro _ _ η δ ηs δs v x x' hx
    have hlen : Vs.length = (Vs.map (substU ηs)).length := by simp
    have hx' : HEq (show Fin Vs.length → ℝ from x)
        (show Fin (Vs.map (substU ηs)).length → ℝ from x') := hx
    simp only [Ty.ground, Adeq, List.map_map, Function.comp_def, substU_comp,
      ofFn_heq hlen.symm hx'.symm]
  | lin Vs Ws =>
    intro _ _ η δ ηs δs v x x' hx
    have h1 : Ws.length = (Ws.map (substU ηs)).length := by simp
    have h2 : Vs.length = (Vs.map (substU ηs)).length := by simp
    have hx' : HEq (show Fin Ws.length → Fin Vs.length → ℝ from x)
        (show Fin (Ws.map (substU ηs)).length → Fin (Vs.map (substU ηs)).length → ℝ from x') := hx
    simp only [Ty.ground, Adeq, List.map_map, Function.comp_def, substU_comp,
      ofFn₂_heq h1.symm h2.symm hx'.symm]
  | arrow a b iha ihb =>
    intro _ _ η δ ηs δs v x x' hx
    have ha := Ty.den_ground a ηs δs
    have hb := Ty.den_ground b ηs δs
    simp only [Ty.ground, Adeq]
    constructor
    · rintro ⟨j', k', σ', body, ρ', η', δ', rfl, hcl⟩
      refine ⟨j', k', σ', body, ρ', η', δ', rfl, ?_⟩
      intro w y hw n v' hev
      refine (ihb η δ ηs δs v' (heq_app ha.symm hb.symm hx (cast_heq ha.symm y).symm)).mp ?_
      exact hcl w _ ((iha η δ ηs δs w (cast_heq ha.symm y).symm).mpr hw) n v' hev
    · rintro ⟨j', k', σ', body, ρ', η', δ', rfl, hcl⟩
      refine ⟨j', k', σ', body, ρ', η', δ', rfl, ?_⟩
      intro w y hw n v' hev
      refine (ihb η δ ηs δs v' (heq_app ha.symm hb.symm hx (cast_heq ha y))).mpr ?_
      exact hcl w _ ((iha η δ ηs δs w (cast_heq ha y)).mp hw) n v' hev
  | all d τ ih =>
    intro _ _ η δ ηs δs v x x' hx
    have hτ := Ty.den_ground τ (liftU ηs) δs
    simp only [Ty.ground, Adeq]
    have hcomp : ∀ μ : UExp B 0,
        (fun i => substU (Fin.cons μ η) (liftU ηs i))
          = Fin.cons μ (fun i => substU η (ηs i)) := by
      intro μ
      refine funext fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [liftU]
      · simp [liftU, substU_weaken_cons]
    constructor
    · rintro ⟨j', k', d', body, ρ', η', δ', rfl, hcl⟩
      refine ⟨j', k', d', body, ρ', η', δ', rfl, ?_⟩
      intro μ hμ n v' hev
      have := (ih (Fin.cons μ η) δ (liftU ηs) δs v'
        (heq_app rfl hτ.symm hx (HEq.refl (V.logScale μ)))).mp
        (hcl μ (by rw [hμ, substU_comp]) n v' hev)
      rwa [hcomp μ] at this
    · rintro ⟨j', k', d', body, ρ', η', δ', rfl, hcl⟩
      refine ⟨j', k', d', body, ρ', η', δ', rfl, ?_⟩
      intro μ hμ n v' hev
      refine (ih (Fin.cons μ η) δ (liftU ηs) δs v'
        (heq_app rfl hτ.symm hx (HEq.refl (V.logScale μ)))).mpr ?_
      rw [hcomp μ]
      exact hcl μ (by rw [hμ, ← substU_comp]) n v' hev
  | allDim τ ih =>
    intro _ _ η δ ηs δs v x x' hx
    simp only [Ty.ground, Adeq]
    have hcomp : ∀ dd : DExp D 0,
        (fun i => substU (Fin.cons dd δ) (liftU δs i))
          = Fin.cons dd (fun i => substU δ (δs i)) := by
      intro dd
      refine funext fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [liftU]
      · simp [liftU, substU_weaken_cons]
    constructor
    · rintro ⟨j', k', body, ρ', η', δ', rfl, hcl⟩
      refine ⟨j', k', body, ρ', η', δ', rfl, ?_⟩
      intro dd n v' hev
      have := (ih η (Fin.cons dd δ) ηs (liftU δs) v' hx).mp (hcl dd n v' hev)
      rwa [hcomp dd] at this
    · rintro ⟨j', k', body, ρ', η', δ', rfl, hcl⟩
      refine ⟨j', k', body, ρ', η', δ', rfl, ?_⟩
      intro dd n v' hev
      refine (ih η (Fin.cons dd δ) ηs (liftU δs) v' hx).mpr ?_
      rw [hcomp dd]
      exact hcl dd n v' hev

/-- Weakening under a unit binder. -/
theorem adeq_weaken (V : Scaling B 0) {j k : ℕ} (τ : Ty B D j k) (η : UEnv B k)
    (δ : DEnv D j) (μ : UExp B 0) (v : Val ℝ B D) {x : Ty.den τ}
    {x' : Ty.den (Ty.weaken τ)} (hx : HEq x x') :
    Adeq V (Fin.cons μ η) δ (Ty.weaken τ) v x' ↔ Adeq V η δ τ v x := by
  have h := adeq_ground V τ (Fin.cons μ η) δ (fun i => Term.ofVar i.succ) (idU D j) v hx
  refine h.trans (iff_of_eq ?_)
  congr 1
  · exact funext fun i => by simp
  · exact funext fun i => by simp [idU]

/-- Instantiating a unit variable. -/
theorem adeq_subst (V : Scaling B 0) {j k : ℕ} (τ : Ty B D j (k + 1)) (σ : UExp B k)
    (η : UEnv B k) (δ : DEnv D j) (v : Val ℝ B D) {x : Ty.den τ}
    {x' : Ty.den (τ.subst σ)} (hx : HEq x x') :
    Adeq V η δ (τ.subst σ) v x' ↔ Adeq V (Fin.cons (substU η σ) η) δ τ v x := by
  have h := adeq_ground V τ η δ (Fin.cons σ (idU B k)) (idU D j) v hx
  refine h.trans (iff_of_eq ?_)
  congr 1
  · exact funext fun i => Fin.cases rfl (fun i => by simp [idU]) i
  · exact funext fun i => by simp [idU]

/-- Weakening under a dimension binder. -/
theorem adeq_weakenDim (V : Scaling B 0) {j k : ℕ} (τ : Ty B D j k) (η : UEnv B k)
    (δ : DEnv D j) (dd : DExp D 0) (v : Val ℝ B D) {x : Ty.den τ}
    {x' : Ty.den (Ty.weakenDim τ)} (hx : HEq x x') :
    Adeq V η (Fin.cons dd δ) (Ty.weakenDim τ) v x' ↔ Adeq V η δ τ v x := by
  have h := adeq_ground V τ η (Fin.cons dd δ) (idU B k) (fun i => Term.ofVar i.succ) v hx
  refine h.trans (iff_of_eq ?_)
  congr 1
  · exact funext fun i => by simp [idU]
  · exact funext fun i => by simp

/-- Instantiating a dimension variable. -/
theorem adeq_substDim (V : Scaling B 0) {j k : ℕ} (τ : Ty B D (j + 1) k)
    (dd : DExp D j) (η : UEnv B k) (δ : DEnv D j) (v : Val ℝ B D) {x : Ty.den τ}
    {x' : Ty.den (τ.substDim dd)} (hx : HEq x x') :
    Adeq V η δ (τ.substDim dd) v x' ↔ Adeq V η (Fin.cons (substU δ dd) δ) τ v x := by
  have h := adeq_ground V τ η δ (idU B k) (Fin.cons dd (idU D j)) v hx
  refine h.trans (iff_of_eq ?_)
  congr 1
  · exact funext fun i => by simp [idU]
  · exact funext fun i => Fin.cases rfl (fun i => by simp [idU]) i

/-- Environment weakening under a unit binder. -/
theorem envAdeq_weaken (V : Scaling B 0) {j k : ℕ} {η : UEnv B k} {δ : DEnv D j}
    (μ : UExp B 0) : ∀ {Γ : Ctx B D j k} {ρ : List (Val ℝ B D)} {ρd : Env Γ},
    EnvAdeq V η δ Γ ρ ρd → EnvAdeq V (Fin.cons μ η) δ Γ.weaken ρ (Env.weaken ρd) := by
  intro Γ ρ ρd h
  induction h with
  | nil => exact EnvAdeq.nil
  | @cons τ Γ w ρ ρd hw _ ih =>
    exact EnvAdeq.cons ((adeq_weaken V τ η δ μ w (cast_heq _ _).symm).mpr hw) ih

/-- Environment weakening under a dimension binder. -/
theorem envAdeq_weakenDim (V : Scaling B 0) {j k : ℕ} {η : UEnv B k} {δ : DEnv D j}
    (dd : DExp D 0) : ∀ {Γ : Ctx B D j k} {ρ : List (Val ℝ B D)} {ρd : Env Γ},
    EnvAdeq V η δ Γ ρ ρd → EnvAdeq V η (Fin.cons dd δ) Γ.weakenDim ρ (Env.weakenDim ρd) := by
  intro Γ ρ ρd h
  induction h with
  | nil => exact EnvAdeq.nil
  | @cons τ Γ w ρ ρd hw _ ih =>
    exact EnvAdeq.cons ((adeq_weakenDim V τ η δ dd w (cast_heq _ _).symm).mpr hw) ih

/-! ## The list arithmetic the space forms need -/

theorem foldl_add (l : List ℝ) (a : ℝ) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

theorem zipWith_ofFn {n : ℕ} (f g : Fin n → ℝ) :
    List.zipWith (· * ·) (List.ofFn f) (List.ofFn g) = List.ofFn fun i => f i * g i := by
  apply List.ext_getElem <;> simp

theorem map_range_eq_ofFn {α : Type} (n : ℕ) (g : ℕ → α) :
    (List.range n).map g = List.ofFn fun i : Fin n => g (i : ℕ) := by
  apply List.ext_getElem <;> simp

theorem colOf_ofFn {m n : ℕ} (N : Fin m → Fin n → ℝ) (i : Fin n) :
    colOf (List.ofFn fun b => List.ofFn fun t => N b t) (i : ℕ)
      = List.ofFn fun b => N b i := by
  simp [colOf, List.map_ofFn, Function.comp_def]

/-- The dot product of two tabulated vectors, in the form `Num.matVec` unfolds
to: the class default for `dot` is inlined, so this is the shape that appears. -/
@[simp] theorem foldl_zipWith_ofFn {n : ℕ} (f g : Fin n → ℝ) :
    (List.zipWith (· * ·) (List.ofFn f) (List.ofFn g)).foldl (· + ·) (((0 : ℚ) : ℝ))
      = ∑ i, f i * g i := by
  rw [zipWith_ofFn, foldl_add, List.sum_ofFn]
  norm_num

/-- The dot product of two tabulated vectors is their inner product. -/
theorem dot_ofFn {n : ℕ} (f g : Fin n → ℝ) :
    Num.dot (List.ofFn f) (List.ofFn g) = ∑ i, f i * g i := by
  have hd : Num.dot (List.ofFn f) (List.ofFn g)
      = (List.zipWith (· * ·) (List.ofFn f) (List.ofFn g)).foldl (· + ·) (((0 : ℚ) : ℝ)) := rfl
  rw [hd, zipWith_ofFn, foldl_add, List.sum_ofFn]
  norm_num

/-- Looking up an adequate environment gives an adequate value. -/
theorem adeq_lookup (V : Scaling B 0) : ∀ {j k : ℕ} {η : UEnv B k} {δ : DEnv D j}
    {Γ : Ctx B D j k} {τ : Ty B D j k} {ρ : List (Val ℝ B D)} {ρd : Env Γ},
    EnvAdeq V η δ Γ ρ ρd → ∀ (n : ℕ) (h : Γ[n]? = some τ),
    ∃ w, ρ[n]? = some w ∧ Adeq V η δ τ w (Env.lookup n h ρd) := by
  intro j k η δ Γ τ ρ ρd hr
  induction hr with
  | nil => intro n h; exact absurd h (by simp)
  | @cons σ Γ w ρ ρd hw hrest ih =>
    intro n h
    cases n with
    | zero => obtain rfl := Option.some.inj h; exact ⟨w, rfl, hw⟩
    | succ n =>
      obtain ⟨w', hw', ha⟩ := ih n (by simpa using h)
      exact ⟨w', by simpa using hw', ha⟩

/-- **Adequacy.** With the conversion oracle taken to be the one the valuation
determines, evaluation of a well-typed term agrees with its denotation: the
unit it carries and the magnitude it holds.

This is the theorem that joins the declaration story to the evaluator. The
`convert` case is its content: the evaluator multiplies by
`conv V (substU η u) (substU η v)` and the denotation by `conv (V.pull η) u v`,
and `Scaling.scale_pull` says those agree. Everything else is bookkeeping. -/
theorem eval_adeq (V : Scaling B 0) :
    ∀ {j k : ℕ} (e : Tm B D j k) (η : UEnv B k) (δ : DEnv D j)
      (ρ : List (Val ℝ B D)) (Δ : DCtx D j k) (Γ : Ctx B D j k) (τ : Ty B D j k)
      (ρd : Env Γ) (d : HasTy Δ Γ e τ),
      EnvAdeq V η δ Γ ρ ρd → EnvOkD Δ η δ →
      ∀ (n : ℕ) (v : Val ℝ B D), eval (conv V) n j k η δ ρ e = some v →
        Adeq V η δ τ v (den (V.pull η) d ρd) := by
  intro j k e
  induction e with
  | var m =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | var h =>
      obtain ⟨w, hw, ha⟩ := adeq_lookup V hρ m h
      simp only [eval] at hv
      rw [hw] at hv
      obtain rfl := Option.some.inj hv
      exact ha
  | lam σ b ihb =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | lam db =>
      simp only [eval] at hv
      obtain rfl := (Option.some.inj hv).symm
      refine ⟨_, _, σ, b, ρ, η, δ, rfl, ?_⟩
      intro w y hw n' v' hev
      exact ihb η δ (w :: ρ) Δ (σ :: Γ) _ (y, ρd) db (EnvAdeq.cons hw hρ) hΔ n' v' hev
  | ulam dd b ihb =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | ulam db =>
      simp only [eval] at hv
      obtain rfl := (Option.some.inj hv).symm
      refine ⟨_, _, dd, b, ρ, η, δ, rfl, ?_⟩
      intro μ hμ n' v' hev
      have hok : EnvOkD (Δ.cons dd) (Fin.cons μ η) δ := hΔ.cons hμ
      have := ihb (Fin.cons μ η) δ ρ (Δ.cons dd) Γ.weaken _ (Env.weaken ρd) db
        (envAdeq_weaken V μ hρ) hok n' v' hev
      rwa [Scaling.pull_cons] at this
  | dlam b ihb =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | dlam db =>
      simp only [eval] at hv
      obtain rfl := (Option.some.inj hv).symm
      refine ⟨_, _, b, ρ, η, δ, rfl, ?_⟩
      intro ddim n' v' hev
      exact ihb η (Fin.cons ddim δ) ρ Δ.weakenDim Γ.weakenDim _ (Env.weakenDim ρd) db
        (envAdeq_weakenDim V ddim hρ) (hΔ.consDim ddim) n' v' hev
  | app g a ihg iha =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | app dg da =>
      cases n with
      | zero => simp [eval] at hv
      | succ fu =>
        simp only [eval] at hv
        cases hg : eval (conv V) (fu + 1) _ _ η δ ρ g with
        | none => rw [hg] at hv; simp at hv
        | some vg =>
          cases ha : eval (conv V) (fu + 1) _ _ η δ ρ a with
          | none => rw [hg, ha] at hv; cases vg <;> simp at hv
          | some va =>
            rw [hg, ha] at hv
            obtain ⟨j', k', σ', body, ρ', η', δ', rfl, hcl⟩ :=
              ihg η δ ρ Δ Γ _ ρd dg hρ hΔ _ _ hg
            exact hcl va _ (iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ ha) fu v hv
  | uapp f σ ihf =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | uapp df hdim =>
      cases n with
      | zero => simp [eval] at hv
      | succ fu =>
        simp only [eval] at hv
        cases hf : eval (conv V) (fu + 1) _ _ η δ ρ f with
        | none => rw [hf] at hv; simp at hv
        | some vf =>
          rw [hf] at hv
          obtain ⟨j', k', d', body, ρ', η', δ', rfl, hcl⟩ :=
            ihf η δ ρ Δ Γ _ ρd df hρ hΔ _ _ hf
          have hdim' := dimOf_substU (Δ := Δ) hΔ σ
          rw [hdim] at hdim'
          have := hcl (substU η σ) hdim' fu v hv
          exact (adeq_subst V _ σ η δ v (cast_heq _ _).symm).mpr
            (by rwa [Scaling.logScale_pull])
  | dapp f dm ihf =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | dapp df =>
      cases n with
      | zero => simp [eval] at hv
      | succ fu =>
        simp only [eval] at hv
        cases hf : eval (conv V) (fu + 1) _ _ η δ ρ f with
        | none => rw [hf] at hv; simp at hv
        | some vf =>
          rw [hf] at hv
          obtain ⟨j', k', body, ρ', η', δ', rfl, hcl⟩ :=
            ihf η δ ρ Δ Γ _ ρd df hρ hΔ _ _ hf
          exact (adeq_substDim V _ dm η δ v (cast_heq _ _).symm).mpr
            (hcl (substU δ dm) fu v hv)
  | lit q =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | lit =>
      simp only [eval] at hv
      obtain rfl := (Option.some.inj hv).symm
      show _ = _
      simp only [Adeq, substU_one]
      rfl
  | ucon u =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | ucon =>
      simp only [eval] at hv
      obtain rfl := (Option.some.inj hv).symm
      show _ = _
      simp only [Adeq, Val.scalar.injEq, Meas.mk.injEq, and_true]
      show ((1 : ℚ) : ℝ) = (1 : ℝ)
      norm_num
  | mul a b iha ihb =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | mul da db =>
      simp only [eval] at hv
      cases hA : eval (conv V) n _ _ η δ ρ a with
      | none => rw [hA] at hv; simp at hv
      | some va =>
        cases hB : eval (conv V) n _ _ η δ ρ b with
        | none => rw [hA, hB] at hv; cases va <;> simp at hv
        | some vb =>
          rw [hA, hB] at hv
          have h1 := iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ hA
          have h2 := ihb η δ ρ Δ Γ _ ρd db hρ hΔ _ _ hB
          simp only [Adeq] at h1 h2
          subst h1; subst h2
          simp only at hv
          obtain rfl := (Option.some.inj hv).symm
          show _ = _
          simp only [Adeq, substU_mul, Val.scalar.injEq, Meas.mk.injEq, and_true]
          rfl
  | div a b iha ihb =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | div da db =>
      simp only [eval] at hv
      cases hA : eval (conv V) n _ _ η δ ρ a with
      | none => rw [hA] at hv; simp at hv
      | some va =>
        cases hB : eval (conv V) n _ _ η δ ρ b with
        | none => rw [hA, hB] at hv; cases va <;> simp at hv
        | some vb =>
          rw [hA, hB] at hv
          have h1 := iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ hA
          have h2 := ihb η δ ρ Δ Γ _ ρd db hρ hΔ _ _ hB
          simp only [Adeq] at h1 h2
          subst h1; subst h2
          simp only at hv
          obtain rfl := (Option.some.inj hv).symm
          show _ = _
          simp only [Adeq, substU_div, Val.scalar.injEq, Meas.mk.injEq, and_true]
          rfl
  | add a b iha ihb =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | add da db =>
      simp only [eval] at hv
      cases hA : eval (conv V) n _ _ η δ ρ a with
      | none => rw [hA] at hv; simp at hv
      | some va =>
        cases hB : eval (conv V) n _ _ η δ ρ b with
        | none => rw [hA, hB] at hv; cases va <;> simp at hv
        | some vb =>
          rw [hA, hB] at hv
          have h1 := iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ hA
          have h2 := ihb η δ ρ Δ Γ _ ρd db hρ hΔ _ _ hB
          simp only [Adeq] at h1 h2
          subst h1; subst h2
          simp only [if_pos rfl] at hv
          obtain rfl := (Option.some.inj hv).symm
          show _ = _
          simp only [Adeq, Val.scalar.injEq, Meas.mk.injEq, and_true]
          rfl
  | root m a iha =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | root hm da =>
      simp only [eval, if_neg hm] at hv
      cases hA : eval (conv V) n _ _ η δ ρ a with
      | none => rw [hA] at hv; simp at hv
      | some va =>
        rw [hA] at hv
        have h1 := iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ hA
        simp only [Adeq] at h1
        subst h1
        simp only at hv
        obtain rfl := (Option.some.inj hv).symm
        show _ = _
        simp only [Adeq, substU_rpow, Val.scalar.injEq, Meas.mk.injEq, and_true]
        show _ ^ _ = _ ^ _
        push_cast
        ring_nf
  | log a iha =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | log da =>
      simp only [eval] at hv
      cases hA : eval (conv V) n _ _ η δ ρ a with
      | none => rw [hA] at hv; simp at hv
      | some va =>
        rw [hA] at hv
        have h1 := iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ hA
        simp only [Adeq] at h1
        subst h1
        simp only [substU_one, if_pos rfl] at hv
        obtain rfl := (Option.some.inj hv).symm
        show _ = _
        simp only [Adeq, substU_one, Val.scalar.injEq, Meas.mk.injEq, and_true]
        rfl
  | exp a iha =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | exp da =>
      simp only [eval] at hv
      cases hA : eval (conv V) n _ _ η δ ρ a with
      | none => rw [hA] at hv; simp at hv
      | some va =>
        rw [hA] at hv
        have h1 := iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ hA
        simp only [Adeq] at h1
        subst h1
        simp only [substU_one, if_pos rfl] at hv
        obtain rfl := (Option.some.inj hv).symm
        show _ = _
        simp only [Adeq, substU_one, Val.scalar.injEq, Meas.mk.injEq, and_true]
        rfl
  | convert a u w iha =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | convert da hsd =>
      simp only [eval] at hv
      cases hA : eval (conv V) n _ _ η δ ρ a with
      | none => rw [hA] at hv; simp at hv
      | some va =>
        rw [hA] at hv
        have h1 := iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ hA
        simp only [Adeq] at h1
        subst h1
        have hsd' : SameDim (DCtx.nil D) (substU η u) (substU η w) := by
          unfold SameDim
          rw [dimOf_substU hΔ, dimOf_substU hΔ, hsd]
        simp only at hv
        rw [if_pos (And.intro True.intro hsd')] at hv
        obtain rfl := (Option.some.inj hv).symm
        show _ = _
        simp only [Adeq, Val.scalar.injEq, Meas.mk.injEq, and_true]
        show _ * _ = _ * _
        rw [conv, conv, Scaling.scale_pull, Scaling.scale_pull]
  | idx a i iha =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | @idx _ _ _ _ _ Vs _ u da hu =>
      simp only [eval] at hv
      cases hA : eval (conv V) n _ _ η δ ρ a with
      | none => rw [hA] at hv; simp at hv
      | some va =>
        rw [hA] at hv
        have h1 := iha η δ ρ Δ Γ _ ρd da hρ hΔ _ _ hA
        simp only [Adeq] at h1
        subst h1
        have hlt := (List.getElem?_eq_some_iff.mp hu).1
        have hval : (List.ofFn (den (V.pull η) da ρd))[i]?
            = some (den (V.pull η) da ρd ⟨i, hlt⟩) := by
          simp [List.getElem?_ofFn, hlt]
        have hunit : (List.map (substU η) Vs)[i]? = some (substU η u) := by
          simp [List.getElem?_map, hu]
        simp only at hv
        rw [hval, hunit] at hv
        obtain rfl := (Option.some.inj hv).symm
        rfl
  | mapp f x ihf ihx =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | mapp df dx =>
      simp only [eval] at hv
      cases hF : eval (conv V) n _ _ η δ ρ f with
      | none => rw [hF] at hv; simp at hv
      | some vf =>
        cases hX : eval (conv V) n _ _ η δ ρ x with
        | none => rw [hF, hX] at hv; cases vf <;> simp at hv
        | some vx =>
          rw [hF, hX] at hv
          have h1 := ihf η δ ρ Δ Γ _ ρd df hρ hΔ _ _ hF
          have h2 := ihx η δ ρ Δ Γ _ ρd dx hρ hΔ _ _ hX
          simp only [Adeq] at h1 h2
          subst h1; subst h2
          simp only [if_pos rfl] at hv
          obtain rfl := (Option.some.inj hv).symm
          show _ = _
          simp only [Adeq, Val.vector.injEq, and_true]
          show Num.matVec _ _ = _
          simp only [Num.matVec, List.map_ofFn, Function.comp_def, foldl_zipWith_ofFn]
          rfl
  | comp f g ihf ihg =>
    intro η δ ρ Δ Γ τ ρd d hρ hΔ n v hv
    cases d with
    | comp df dg =>
      simp only [eval] at hv
      cases hF : eval (conv V) n _ _ η δ ρ f with
      | none => rw [hF] at hv; simp at hv
      | some vf =>
        cases hG : eval (conv V) n _ _ η δ ρ g with
        | none => rw [hF, hG] at hv; cases vf <;> simp at hv
        | some vg =>
          rw [hF, hG] at hv
          have h1 := ihf η δ ρ Δ Γ _ ρd df hρ hΔ _ _ hF
          have h2 := ihg η δ ρ Δ Γ _ ρd dg hρ hΔ _ _ hG
          simp only [Adeq] at h1 h2
          subst h1; subst h2
          simp only [if_pos rfl] at hv
          obtain rfl := (Option.some.inj hv).symm
          show _ = _
          simp only [Adeq, Val.matrix.injEq, and_true, true_and]
          simp only [List.map_ofFn, Function.comp_def, List.length_map,
            map_range_eq_ofFn, colOf_ofFn, dotp, dot_ofFn]
          rfl

/-! ## What the declarations buy

`LambdaS.Declare` decides whether a set of unit declarations determines a
valuation, and rejects the sets that do not. `eval_adeq` says what a valuation
is worth to the evaluator. Composing them is the point of this file: the number
the evaluator multiplies by is the number the declarations name.

And when the declarations conflict, `not_satisfiable_of_chain` says no valuation
exists, so there is no oracle to run with, rather than a choice of oracles to
pick wrongly between. -/

/-- **Adequacy for closed terms of scalar type.** -/
theorem evalC_adeq (V : Scaling B 0) {e : Tm B D 0 0} {u : UExp B 0}
    (d : HasTy (DCtx.nil D) ([] : Ctx B D 0 0) e (.Q u)) {n : ℕ} {v : Val ℝ B D}
    (hv : evalC (conv V) n [] e = some v) :
    v = .scalar ⟨den V d PUnit.unit, u⟩ := by
  have h := eval_adeq V e (nilU B) (nilU D) [] (DCtx.nil D) [] (.Q u) PUnit.unit d
    EnvAdeq.nil (fun i => i.elim0) n v hv
  simpa [Adeq] using h

/-- **The evaluator computes the denotation.** Every well-typed closed term of
scalar type evaluates (at some finite fuel, by normalization) to exactly the
magnitude its denotation predicts, carrying exactly the unit its type predicts,
provided the conversion oracle is the one the valuation determines.

This is the join. Before it, `LambdaS.Dynamics` multiplied by a number nobody had
constrained and `LambdaS.Fundamental` reasoned about a number nobody computed. -/
theorem evalC_eq_den (V : Scaling B 0) {e : Tm B D 0 0} {u : UExp B 0}
    (d : HasTy (DCtx.nil D) ([] : Ctx B D 0 0) e (.Q u)) :
    ∃ n, evalC (conv V) n [] e = some (.scalar ⟨den V d PUnit.unit, u⟩) := by
  obtain ⟨n, v, hv, _⟩ := eval_terminates (conv V) d
  exact ⟨n, by rw [hv, evalC_adeq V d hv]⟩

/-- **The evaluator multiplies by the declared factor.** Converting along a
declaration multiplies the magnitude by the number the declaration
names: not something equal to it up to a chain of intermediate steps, but
that number.

`Decl.conv_eq_factor` said the *valuation* assigns that factor; this says the
evaluator uses it. -/
theorem evalC_convert_declared {ψ : Scaling B 0} {dcl : Decl B}
    (hsat : Decl.Satisfies ψ dcl) {e : Tm B D 0 0}
    (d : HasTy (DCtx.nil D) ([] : Ctx B D 0 0) e (.Q (Term.ofBase dcl.lhs)))
    (hsd : SameDim (DCtx.nil D) (Term.ofBase dcl.lhs) dcl.rhs) :
    ∃ n, evalC (conv ψ) n [] (.convert e (Term.ofBase dcl.lhs) dcl.rhs)
      = some (.scalar ⟨den ψ d PUnit.unit * (dcl.factor : ℝ), dcl.rhs⟩) := by
  obtain ⟨n, hn⟩ := evalC_eq_den ψ (d.convert hsd)
  refine ⟨n, ?_⟩
  rw [hn]
  congr 2
  simp only [Meas.mk.injEq, and_true]
  show den ψ d PUnit.unit * conv ψ (Term.ofBase dcl.lhs) dcl.rhs
      = den ψ d PUnit.unit * (dcl.factor : ℝ)
  rw [Decl.conv_eq_factor hsat]

end LambdaS

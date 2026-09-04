/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Soundness

/-!
# Normalization: enough fuel always exists

`eval_sound` is preservation: *if* evaluation returns a value, that value has the
predicted type. The `if` is an artifact of the evaluator being a function in a
total logic: a definitional interpreter cannot be structurally recursive even
for a normalizing calculus, because `app` recurses into a closure body, which is
not a subterm. Fuel buys past that, and the price is that `none` conflates
"ill-typed" with "ran out".

Λs is normalizing, so a large enough bound always exists. This file proves that a
well-typed term evaluates for *some* fuel, which together with `eval_sound`
gives the statement one actually wants: every well-typed term evaluates to a
value of the predicted type.

## Why this is Tait and not Girard

Λs's quantifiers range over units and dimensions: elements of a free abelian
group, first-order algebraic data. There is no `∀X:Type`, hence no
impredicativity, hence no need for reducibility candidates. Erase the unit
annotations from a Λs type and what remains is a plain simple type, so the
reducibility predicate can recurse on that **skeleton**: instantiating a
quantifier substitutes units, which leaves the skeleton alone.
-/

namespace LambdaS

variable {B D R : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D] [Num R]

/-! ## Fuel monotonicity

More fuel never turns a success into a failure. Needed because the fundamental
lemma combines sub-evaluations that each came with their own bound. -/

theorem eval_mono (cf : UExp B 0 → UExp B 0 → R) :
    ∀ (n : ℕ) {j k : ℕ} (e : Tm B D j k) (m : ℕ) (η : UEnv B k) (δ : DEnv D j)
      (ρ : List (Val R B D)) (v : Val R B D),
      n ≤ m → eval cf n j k η δ ρ e = some v → eval cf m j k η δ ρ e = some v
  | _, _, _, .var i, _, _, _, _, _, _, h => by simpa [eval] using h
  | _, _, _, .lam σ b, _, _, _, _, _, _, h => by simpa [eval] using h
  | _, _, _, .ulam d b, _, _, _, _, _, _, h => by simpa [eval] using h
  | _, _, _, .dlam b, _, _, _, _, _, _, h => by simpa [eval] using h
  | _, _, _, .lit q, _, _, _, _, _, _, h => by simpa [eval] using h
  | _, _, _, .ucon u, _, _, _, _, _, _, h => by simpa [eval] using h
  | 0, _, _, .app _ _, _, _, _, _, _, _, h => by simp [eval] at h
  | 0, _, _, .uapp _ _, _, _, _, _, _, _, h => by simp [eval] at h
  | 0, _, _, .dapp _ _, _, _, _, _, _, _, h => by simp [eval] at h
  | fu + 1, _, _, .app g a, m, η, δ, ρ, v, hnm, h => by
      match m, hnm with
      | fu' + 1, hnm =>
        simp only [eval] at h ⊢
        split at h
        · rename_i σ' b' ρ' η' δ' av hg ha
          rw [eval_mono cf (fu + 1) g (fu' + 1) η δ ρ _ (by omega) hg,
              eval_mono cf (fu + 1) a (fu' + 1) η δ ρ _ (by omega) ha]
          exact eval_mono cf fu b' fu' η' δ' _ _ (by omega) h
        · exact absurd h (by simp)
  | fu + 1, _, _, .uapp f μ, m, η, δ, ρ, v, hnm, h => by
      match m, hnm with
      | fu' + 1, hnm =>
        simp only [eval] at h ⊢
        split at h
        · rename_i d' b' ρ' η' δ' hf
          rw [eval_mono cf (fu + 1) f (fu' + 1) η δ ρ _ (by omega) hf]
          exact eval_mono cf fu b' fu' _ δ' ρ' _ (by omega) h
        · exact absurd h (by simp)
  | fu + 1, _, _, .dapp f d, m, η, δ, ρ, v, hnm, h => by
      match m, hnm with
      | fu' + 1, hnm =>
        simp only [eval] at h ⊢
        split at h
        · rename_i b' ρ' η' δ' hf
          rw [eval_mono cf (fu + 1) f (fu' + 1) η δ ρ _ (by omega) hf]
          exact eval_mono cf fu b' fu' η' _ ρ' _ (by omega) h
        · exact absurd h (by simp)
  | n, _, _, .mul a b, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i x y ha hb
        rw [eval_mono cf n a m η δ ρ _ hnm ha, eval_mono cf n b m η δ ρ _ hnm hb]
        exact h
      · exact absurd h (by simp)
  | n, _, _, .div a b, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i x y ha hb
        rw [eval_mono cf n a m η δ ρ _ hnm ha, eval_mono cf n b m η δ ρ _ hnm hb]
        exact h
      · exact absurd h (by simp)
  | n, _, _, .add a b, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i x y ha hb
        rw [eval_mono cf n a m η δ ρ _ hnm ha, eval_mono cf n b m η δ ρ _ hnm hb]
        exact h
      · exact absurd h (by simp)
  | n, _, _, .pow q a, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i x ha
        rw [eval_mono cf n a m η δ ρ _ hnm ha]; exact h
      · exact absurd h (by simp)
  | n, _, _, .log a, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i x ha
        rw [eval_mono cf n a m η δ ρ _ hnm ha]; exact h
      · exact absurd h (by simp)
  | n, _, _, .exp a, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i x ha
        rw [eval_mono cf n a m η δ ρ _ hnm ha]; exact h
      · exact absurd h (by simp)
  | n, _, _, .idx a i, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i xs V ha
        rw [eval_mono cf n a m η δ ρ _ hnm ha]; exact h
      · exact absurd h (by simp)
  | n, _, _, .mapp f x, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i M V W xs V' hf hx
        rw [eval_mono cf n f m η δ ρ _ hnm hf, eval_mono cf n x m η δ ρ _ hnm hx]
        exact h
      · exact absurd h (by simp)
  | n, _, _, .comp f g, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i M V W N U V' hf hg
        rw [eval_mono cf n f m η δ ρ _ hnm hf, eval_mono cf n g m η δ ρ _ hnm hg]
        exact h
      · exact absurd h (by simp)
  | n, _, _, .vnil, m, η, δ, ρ, v, hnm, h => by simpa [eval] using h
  | n, _, _, .vcons a b, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i x xs V ha hb
        rw [eval_mono cf n a m η δ ρ _ hnm ha, eval_mono cf n b m η δ ρ _ hnm hb]
        exact h
      · exact absurd h (by simp)
  | n, _, _, .mnil V, m, η, δ, ρ, v, hnm, h => by simpa [eval] using h
  | n, _, _, .mcons w r M, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i xs Vr N V W hr hM
        rw [eval_mono cf n r m η δ ρ _ hnm hr, eval_mono cf n M m η δ ρ _ hnm hM]
        exact h
      · exact absurd h (by simp)
  | n, _, _, .convert a u w, m, η, δ, ρ, v, hnm, h => by
      simp only [eval] at h ⊢
      split at h
      · rename_i x ha
        rw [eval_mono cf n a m η δ ρ _ hnm ha]; exact h
      · exact absurd h (by simp)
termination_by n j k e m η δ ρ v _hnm _h => (n, sizeOf e)

/-! ## Reducibility

Tait's predicate. At scalar, vector and linear-map types it is just "has the
right shape"; at the three binding types it is the interesting clause: a
closure is reducible when applying it to anything reducible *terminates* at a
reducible value. -/

def Red (cf : UExp B 0 → UExp B 0 → R) : Ty B D 0 0 → Val R B D → Prop
  | .Q u, v => ∃ m, v = .scalar ⟨m, u⟩
  | .vec V, v => ∃ xs, v = .vector xs V ∧ xs.length = V.length
  | .lin V W, v => ∃ M, v = .matrix M V W ∧ M.length = W.length ∧
      ∀ r ∈ M, r.length = V.length
  | .arrow σ τ, v => ∃ (j k : ℕ) (σ' : Ty B D j k) (b : Tm B D j k)
      (ρ' : List (Val R B D)) (η' : UEnv B k) (δ' : DEnv D j),
      v = .closure σ' b ρ' η' δ' ∧
      ∀ w, Red cf σ w → ∃ n v', eval cf n j k η' δ' (w :: ρ') b = some v' ∧ Red cf τ v'
  | .all d τ, v => ∃ (j k : ℕ) (d' : DExp D j) (b : Tm B D j (k + 1))
      (ρ' : List (Val R B D)) (η' : UEnv B k) (δ' : DEnv D j),
      v = .uclos d' b ρ' η' δ' ∧
      ∀ μ : UExp B 0, dimOf (D := D) (DCtx.nil D) μ = d →
        ∃ n v', eval cf n j (k + 1) (Fin.cons μ η') δ' ρ' b = some v' ∧
          Red cf (Ty.subst τ μ) v'
  | .allDim τ, v => ∃ (j k : ℕ) (b : Tm B D (j + 1) k)
      (ρ' : List (Val R B D)) (η' : UEnv B k) (δ' : DEnv D j),
      v = .dclos b ρ' η' δ' ∧
      ∀ d : DExp D 0, ∃ n v', eval cf n (j + 1) k η' (Fin.cons d δ') ρ' b = some v' ∧
        Red cf (Ty.substDim τ d) v'
termination_by τ _ => Ty.skel τ
decreasing_by all_goals simp only [Ty.skel, Ty.skel_subst, Ty.skel_substDim]; omega

/-- Reducible values are well-shaped, which is all the evaluator's matches
need. -/
inductive RedEnv (cf : UExp B 0 → UExp B 0 → R) :
    List (Val R B D) → Ctx B D 0 0 → Prop where
  | nil : RedEnv cf ([] : List (Val R B D)) []
  | cons {v ρ τ Γ} : Red cf τ v → RedEnv cf ρ Γ → RedEnv cf (v :: ρ) (τ :: Γ)

theorem RedEnv.lookup {cf : UExp B 0 → UExp B 0 → R} :
    ∀ {ρ : List (Val R B D)} {Γ : Ctx B D 0 0} {n : ℕ} {τ},
    RedEnv cf ρ Γ → Γ[n]? = some τ → ∃ v, ρ[n]? = some v ∧ Red cf τ v := by
  intro ρ Γ n
  induction n generalizing ρ Γ with
  | zero =>
    intro τ h hτ
    cases h with
    | nil => simp at hτ
    | cons hval _ => simp at hτ ⊢; subst hτ; exact hval
  | succ m ih =>
    intro τ h hτ
    cases h with
    | nil => simp at hτ
    | cons _ henv =>
      obtain ⟨v, hv, hval⟩ := ih henv (by simpa using hτ)
      exact ⟨v, by simpa using hv, hval⟩

/-! ## The fundamental lemma

Every well-typed term evaluates, for some fuel, to a reducible value. Note there
is no induction on fuel here: the reducibility predicate at arrow type already
*carries* the obligation that applying the closure terminates, so induction on
the term suffices. Fuel only has to be reconciled between subterms, which is what
`eval_mono` is for. -/

theorem red_eval (cf : UExp B 0 → UExp B 0 → R) :
    ∀ {j k : ℕ} (e : Tm B D j k) (η : UEnv B k) (δ : DEnv D j) (ρ : List (Val R B D))
      (Δ : DCtx D j k) (Γ : Ctx B D j k) (τ : Ty B D j k),
      RedEnv cf ρ (groundCtx η δ Γ) → EnvOkD Δ η δ → HasTy Δ Γ e τ →
      ∃ n v, eval cf n j k η δ ρ e = some v ∧ Red cf (Ty.ground η δ τ) v := by
  intro j k e
  induction e with
  | var i =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | var hn =>
      have hmap : (groundCtx η δ Γ)[i]? = some (Ty.ground η δ τ) := by
        simp [groundCtx, hn]
      obtain ⟨v, hv, hred⟩ := RedEnv.lookup hρ hmap
      exact ⟨0, v, by simpa [eval] using hv, hred⟩
  | lam σ b ihb =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | lam htb =>
      refine ⟨0, Val.closure σ b ρ η δ, by simp [eval], ?_⟩
      simp only [Ty.ground, Red]
      refine ⟨_, _, σ, b, ρ, η, δ, rfl, fun w hw => ?_⟩
      exact ihb η δ (w :: ρ) Δ (σ :: Γ) _ (.cons hw hρ) hΔ htb
  | ulam d b ihb =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | ulam htb =>
      refine ⟨0, Val.uclos d b ρ η δ, by simp [eval], ?_⟩
      simp only [Ty.ground, Red]
      refine ⟨_, _, d, b, ρ, η, δ, rfl, fun μ hμ => ?_⟩
      obtain ⟨n, v, hev, hred⟩ :=
        ihb (Fin.cons μ η) δ ρ (Δ.cons d) Γ.weaken _
          (by simpa [groundCtx, Ctx.weaken, List.map_map, Function.comp_def,
                Ty.ground_weaken] using hρ) (hΔ.cons hμ) htb
      exact ⟨n, v, hev, by rwa [Ty.ground_liftU_subst]⟩
  | dlam b ihb =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | dlam htb =>
      refine ⟨0, Val.dclos b ρ η δ, by simp [eval], ?_⟩
      simp only [Ty.ground, Red]
      refine ⟨_, _, b, ρ, η, δ, rfl, fun d => ?_⟩
      obtain ⟨n, v, hev, hred⟩ :=
        ihb η (Fin.cons d δ) ρ Δ.weakenDim Γ.weakenDim _
          (by simpa [groundCtx, Ctx.weakenDim, List.map_map, Function.comp_def,
                Ty.ground_weakenDim] using hρ) (hΔ.consDim d) htb
      exact ⟨n, v, hev, by rwa [Ty.ground_liftD_substDim]⟩
  | app g a ihg iha =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | app htg hta =>
      obtain ⟨n₁, vf, hf, hredf⟩ := ihg η δ ρ Δ Γ _ hρ hΔ htg
      obtain ⟨n₂, va, ha, hreda⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hredf
      obtain ⟨j', k', σ', b', ρ', η', δ', rfl, hprop⟩ := hredf
      obtain ⟨n₃, v, hb, hredv⟩ := hprop va hreda
      refine ⟨max n₁ (max n₂ n₃) + 1, v, ?_, hredv⟩
      simp only [eval]
      rw [eval_mono cf n₁ g _ η δ ρ _ (by omega) hf,
          eval_mono cf n₂ a _ η δ ρ _ (by omega) ha]
      exact eval_mono cf n₃ b' _ η' δ' _ _ (by omega) hb
  | uapp f μ ihf =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | uapp htf hdim =>
      obtain ⟨n₁, vf, hf, hredf⟩ := ihf η δ ρ Δ Γ _ hρ hΔ htf
      simp only [Ty.ground, Red] at hredf
      obtain ⟨j', k', d', b', ρ', η', δ', rfl, hprop⟩ := hredf
      obtain ⟨n₂, v, hb, hredv⟩ := hprop (substU η μ) (by rw [dimOf_substU hΔ, hdim])
      refine ⟨max n₁ n₂ + 1, v, ?_, ?_⟩
      · simp only [eval]
        rw [eval_mono cf n₁ f _ η δ ρ _ (by omega) hf]
        exact eval_mono cf n₂ b' _ _ δ' ρ' _ (by omega) hb
      · rwa [Ty.ground_subst, ← Ty.ground_liftU_subst]
  | dapp f d ihf =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | dapp htf =>
      obtain ⟨n₁, vf, hf, hredf⟩ := ihf η δ ρ Δ Γ _ hρ hΔ htf
      simp only [Ty.ground, Red] at hredf
      obtain ⟨j', k', b', ρ', η', δ', rfl, hprop⟩ := hredf
      obtain ⟨n₂, v, hb, hredv⟩ := hprop (substU δ d)
      refine ⟨max n₁ n₂ + 1, v, ?_, ?_⟩
      · simp only [eval]
        rw [eval_mono cf n₁ f _ η δ ρ _ (by omega) hf]
        exact eval_mono cf n₂ b' _ η' _ ρ' _ (by omega) hb
      · rwa [Ty.ground_substDim, ← Ty.ground_liftD_substDim]
  | lit q =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht
    refine ⟨0, Val.scalar ⟨Num.ofRat q, 1⟩, by simp [eval], ?_⟩
    simp only [Ty.ground, Red, substU_one]
    exact ⟨_, rfl⟩
  | ucon u =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht
    refine ⟨0, Val.scalar ⟨Num.ofRat 1, substU η u⟩, by simp [eval], ?_⟩
    simp only [Ty.ground, Red]
    exact ⟨_, rfl⟩
  | mul a b iha ihb =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | mul hta htb =>
      obtain ⟨n₁, va, ha, hra⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hra
      obtain ⟨m, rfl⟩ := hra
      obtain ⟨n₂, vb, hb, hrb⟩ := ihb η δ ρ Δ Γ _ hρ hΔ htb
      simp only [Ty.ground, Red] at hrb
      obtain ⟨m', rfl⟩ := hrb
      refine ⟨max n₁ n₂, ?v_mul, ?e_mul, ?r_mul⟩
      case e_mul =>
        simp only [eval]
        rw [eval_mono cf n₁ a _ η δ ρ _ (by omega) ha,
            eval_mono cf n₂ b _ η δ ρ _ (by omega) hb]
      case r_mul =>
        simp only [Ty.ground, Red, substU_mul]
        exact ⟨_, rfl⟩
  | div a b iha ihb =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | div hta htb =>
      obtain ⟨n₁, va, ha, hra⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hra
      obtain ⟨m, rfl⟩ := hra
      obtain ⟨n₂, vb, hb, hrb⟩ := ihb η δ ρ Δ Γ _ hρ hΔ htb
      simp only [Ty.ground, Red] at hrb
      obtain ⟨m', rfl⟩ := hrb
      refine ⟨max n₁ n₂, ?v_div, ?e_div, ?r_div⟩
      case e_div =>
        simp only [eval]
        rw [eval_mono cf n₁ a _ η δ ρ _ (by omega) ha,
            eval_mono cf n₂ b _ η δ ρ _ (by omega) hb]
      case r_div =>
        simp only [Ty.ground, Red, substU_div]
        exact ⟨_, rfl⟩
  | add a b iha ihb =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | add hta htb =>
      obtain ⟨n₁, va, ha, hra⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hra
      obtain ⟨m, rfl⟩ := hra
      obtain ⟨n₂, vb, hb, hrb⟩ := ihb η δ ρ Δ Γ _ hρ hΔ htb
      simp only [Ty.ground, Red] at hrb
      obtain ⟨m', rfl⟩ := hrb
      refine ⟨max n₁ n₂, ?v_add, ?e_add, ?r_add⟩
      case e_add =>
        simp only [eval]
        rw [eval_mono cf n₁ a _ η δ ρ _ (by omega) ha,
            eval_mono cf n₂ b _ η δ ρ _ (by omega) hb]
        simp
        rfl
      case r_add =>
        simp only [Ty.ground, Red]
        exact ⟨_, rfl⟩
  | pow q a iha =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | pow hta =>
      obtain ⟨n₁, va, ha, hra⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hra
      obtain ⟨m, rfl⟩ := hra
      refine ⟨n₁, ?v_pow, ?e_pow, ?r_pow⟩
      case e_pow =>
        simp only [eval]
        rw [ha]
      case r_pow =>
        simp only [Ty.ground, Red, substU_rpow]
        exact ⟨_, rfl⟩
  | log a iha =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | log hta =>
      obtain ⟨n₁, va, ha, hra⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hra
      obtain ⟨m, rfl⟩ := hra
      refine ⟨n₁, ?v_log, ?e_log, ?r_log⟩
      case e_log =>
        simp only [eval]
        rw [ha]
        simp
        rfl
      case r_log =>
        simp only [Ty.ground, Red, substU_one]
        exact ⟨_, rfl⟩
  | exp a iha =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | exp hta =>
      obtain ⟨n₁, va, ha, hra⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hra
      obtain ⟨m, rfl⟩ := hra
      refine ⟨n₁, ?v_exp, ?e_exp, ?r_exp⟩
      case e_exp =>
        simp only [eval]
        rw [ha]
        simp
        rfl
      case r_exp =>
        simp only [Ty.ground, Red, substU_one]
        exact ⟨_, rfl⟩
  | idx a i iha =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | @idx _ _ _ _ _ V _ u hta hu =>
      obtain ⟨n₁, va, ha, hra⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hra
      obtain ⟨xs, rfl, hlen⟩ := hra
      have hV : (List.map (substU η) V)[i]? = some (substU η u) := by
        simp [List.getElem?_map, hu]
      have hlt : i < xs.length := by
        rw [hlen, List.length_map]; exact (List.getElem?_eq_some_iff.mp hu).1
      refine ⟨n₁, ?v_idx, ?e_idx, ?r_idx⟩
      case e_idx =>
        simp only [eval]
        rw [ha]
        simp only [List.getElem?_eq_getElem hlt, hV]
        rfl
      case r_idx =>
        simp only [Ty.ground, Red]
        exact ⟨_, rfl⟩
  | mapp f x ihf ihx =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | mapp htf htx =>
      obtain ⟨n₁, vf, hf, hrf⟩ := ihf η δ ρ Δ Γ _ hρ hΔ htf
      simp only [Ty.ground, Red] at hrf
      obtain ⟨M, rfl, hMl, hMr⟩ := hrf
      obtain ⟨n₂, vx, hx, hrx⟩ := ihx η δ ρ Δ Γ _ hρ hΔ htx
      simp only [Ty.ground, Red] at hrx
      obtain ⟨xs, rfl, hxl⟩ := hrx
      refine ⟨max n₁ n₂, ?v_mapp, ?e_mapp, ?r_mapp⟩
      case e_mapp =>
        simp only [eval]
        rw [eval_mono cf n₁ f _ η δ ρ _ (by omega) hf,
            eval_mono cf n₂ x _ η δ ρ _ (by omega) hx]
        simp
        rfl
      case r_mapp =>
        simp only [Ty.ground, Red]
        exact ⟨_, rfl, by rw [Num.matVec_length]; exact hMl⟩
  | comp f g ihf ihg =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | comp htf htg =>
      obtain ⟨n₁, vf, hf, hrf⟩ := ihf η δ ρ Δ Γ _ hρ hΔ htf
      simp only [Ty.ground, Red] at hrf
      obtain ⟨M, rfl, hMl, hMr⟩ := hrf
      obtain ⟨n₂, vg, hg, hrg⟩ := ihg η δ ρ Δ Γ _ hρ hΔ htg
      simp only [Ty.ground, Red] at hrg
      obtain ⟨N, rfl, hNl, hNr⟩ := hrg
      refine ⟨max n₁ n₂, ?v_comp, ?e_comp, ?r_comp⟩
      case e_comp =>
        simp only [eval]
        rw [eval_mono cf n₁ f _ η δ ρ _ (by omega) hf,
            eval_mono cf n₂ g _ η δ ρ _ (by omega) hg]
        simp
        rfl
      case r_comp =>
        simp only [Ty.ground, Red]
        refine ⟨_, rfl, by simpa using hMl, ?_⟩
        intro r hr
        simp only [List.mem_map] at hr
        obtain ⟨_, _, rfl⟩ := hr
        simp
  | vnil =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht
    refine ⟨0, Val.vector [] [], by simp [eval], ?_⟩
    simp only [Ty.ground, Red]
    exact ⟨[], rfl, rfl⟩
  | vcons e vt ihe ihv =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | vcons hte htv =>
      obtain ⟨n₁, va, ha, hra⟩ := ihe η δ ρ Δ Γ _ hρ hΔ hte
      simp only [Ty.ground, Red] at hra
      obtain ⟨mx, rfl⟩ := hra
      obtain ⟨n₂, vb, hb, hrb⟩ := ihv η δ ρ Δ Γ _ hρ hΔ htv
      simp only [Ty.ground, Red] at hrb
      obtain ⟨xs, rfl, hlen⟩ := hrb
      refine ⟨max n₁ n₂, ?v_vcons, ?e_vcons, ?r_vcons⟩
      case e_vcons =>
        simp only [eval]
        rw [eval_mono cf n₁ e _ η δ ρ _ (by omega) ha,
            eval_mono cf n₂ vt _ η δ ρ _ (by omega) hb]
      case r_vcons =>
        simp only [Ty.ground, Red]
        exact ⟨_, rfl, by simpa using hlen⟩
  | mnil V =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht
    refine ⟨0, Val.matrix [] (V.map (substU η)) [], by simp [eval], ?_⟩
    simp only [Ty.ground, Red]
    exact ⟨[], rfl, rfl, by simp⟩
  | mcons w r M ihr ihM =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | mcons htr htM =>
      obtain ⟨n₁, vr, hr, hrr⟩ := ihr η δ ρ Δ Γ _ hρ hΔ htr
      simp only [Ty.ground, Red] at hrr
      obtain ⟨xs, rfl, hxlen⟩ := hrr
      obtain ⟨n₂, vM, hM, hrM⟩ := ihM η δ ρ Δ Γ _ hρ hΔ htM
      simp only [Ty.ground, Red] at hrM
      obtain ⟨N, rfl, hNlen, hNrow⟩ := hrM
      refine ⟨max n₁ n₂, ?v_mcons, ?e_mcons, ?r_mcons⟩
      case e_mcons =>
        simp only [eval]
        rw [eval_mono cf n₁ r _ η δ ρ _ (by omega) hr,
            eval_mono cf n₂ M _ η δ ρ _ (by omega) hM]
      case r_mcons =>
        simp only [Ty.ground, Red]
        refine ⟨_, rfl, by simpa using hNlen, ?_⟩
        intro row hrow
        rcases List.mem_cons.mp hrow with rfl | hmem
        · simpa using hxlen
        · exact hNrow row hmem
  | convert a u w iha =>
    intro η δ ρ Δ Γ τ hρ hΔ ht
    cases ht with
    | convert hta hsd =>
      obtain ⟨n₁, va, ha, hra⟩ := iha η δ ρ Δ Γ _ hρ hΔ hta
      simp only [Ty.ground, Red] at hra
      obtain ⟨m, rfl⟩ := hra
      have hsd' : SameDim (DCtx.nil D) (substU η u) (substU η w) := by
        unfold SameDim at hsd ⊢
        rw [dimOf_substU hΔ, dimOf_substU hΔ, hsd]
      refine ⟨n₁, ?v_convert, ?e_convert, ?r_convert⟩
      case e_convert =>
        simp only [eval]
        rw [ha]
        simp [hsd']
        rfl
      case r_convert =>
        simp only [Ty.ground, Red]
        exact ⟨_, rfl⟩

/-! ## Normalization

The fundamental lemma at the closed scope. `Ty.ground` disappears because both
environments are empty, so reducibility is stated at the type the checker wrote.
-/

omit [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D] [UnitSys B D] in
/-- At the closed scope the environments ground nothing. -/
@[simp] theorem Ty.ground_nil (τ : Ty B D 0 0) :
    Ty.ground (nilU B) (nilU D) τ = τ := by
  have hB : nilU B = idU B 0 := funext fun i => i.elim0
  have hD : nilU D = idU D 0 := funext fun i => i.elim0
  rw [hB, hD, Ty.ground_id]

/-- **Strong normalization.** Every well-typed closed term evaluates (at *some*
finite fuel) to a value reducible at its type.

This is what the fuel costs and what it buys. `eval` is a total function only
because it may answer `none`. Here the fuel is produced rather than assumed, so
`none` is not a
possible answer for a well-typed term: `eval` is partial in its definition and
total on the language. The fuel is an artifact of Lean's termination checker,
not of Λs. -/
theorem eval_terminates (cf : UExp B 0 → UExp B 0 → R) {e : Tm B D 0 0}
    {τ : Ty B D 0 0} (ht : HasTy (DCtx.nil D) [] e τ) :
    ∃ n v, evalC cf n [] e = some v ∧ Red cf τ v := by
  have hΔ : EnvOkD (DCtx.nil D) (nilU B) (nilU D) := fun i => i.elim0
  obtain ⟨n, v, hev, hred⟩ :=
    red_eval cf e (nilU B) (nilU D) [] (DCtx.nil D) [] τ (by simpa using RedEnv.nil) hΔ ht
  exact ⟨n, v, hev, by simpa using hred⟩

/-- **Totality and soundness together.** A well-typed closed term evaluates to a
value, and that value has the type the checker predicted.

Termination comes from `eval_terminates`, the typing of the result from
`eval_sound`; neither implies the other, and the theorem is their
conjunction. -/
theorem eval_total (cf : UExp B 0 → UExp B 0 → R) {e : Tm B D 0 0}
    {τ : Ty B D 0 0} (ht : HasTy (DCtx.nil D) [] e τ) :
    ∃ n v, evalC cf n [] e = some v ∧ ValTy v τ := by
  obtain ⟨n, v, hev, _⟩ := eval_terminates cf ht
  refine ⟨n, v, hev, ?_⟩
  have := eval_sound cf n e (nilU B) (nilU D) [] (DCtx.nil D) [] τ v
    (by simpa using EnvTy.nil) (fun i => i.elim0) ht hev
  simpa using this

/-- **Unit soundness, unrestricted.** Every well-typed closed term of scalar type
evaluates to a scalar carrying exactly the unit its type predicted.

A since-deleted ancestor in `LambdaS.Dynamics` said this for the first-order
arithmetic fragment, with the fuel assumed. Normalization removes both restrictions: the
term may abstract over values, units and dimensions, and the fuel is produced by
the proof. This is the statement that says the unit discipline has no runtime
escape hatch. -/
theorem unit_soundness_total (cf : UExp B 0 → UExp B 0 → R) {e : Tm B D 0 0}
    {u : UExp B 0} (ht : HasTy (DCtx.nil D) [] e (.Q u)) :
    ∃ n m, evalC cf n [] e = some (.scalar ⟨m, u⟩) := by
  obtain ⟨n, v, hev, hred⟩ := eval_terminates cf ht
  simp only [Red] at hred
  obtain ⟨m, rfl⟩ := hred
  exact ⟨n, m, hev⟩

/-- **Space soundness for linear maps.** Every well-typed closed term of map
type evaluates to a matrix value carrying exactly the spaces its type
predicted: the `Lin` analogue of `unit_soundness_total`. With the
introduction forms of `LambdaS.Syntax`, matrix literals are among the terms
it governs. -/
theorem lin_soundness_total (cf : UExp B 0 → UExp B 0 → R) {e : Tm B D 0 0}
    {V W : Sp B 0} (ht : HasTy (DCtx.nil D) [] e (.lin V W)) :
    ∃ n M, evalC cf n [] e = some (.matrix M V W) := by
  obtain ⟨n, v, hev, hvt⟩ := eval_total cf ht
  obtain ⟨M, rfl, -, -⟩ := hvt.matrix_inv
  exact ⟨n, M, hev⟩

end LambdaS

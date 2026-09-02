import LambdaS.Dynamics

/-!
# Type soundness

The System F proof, with units in place of type variables.

The shape is the textbook one: a value typing relation, an environment typing
relation defined mutually with it (a closure's type depends on the context its
captured environment satisfies), and a preservation theorem by induction on the
term with the fuel bound handled by an outer strong induction.

## Where units show up

In exactly two places, and neither is structural.

`EnvOkD` is the semantic counterpart of the dimension context: the runtime unit
environment must assign each unit variable a unit whose *dimension* is the one
the static context declared. `dimOf_substU` then says grounding commutes with
taking dimensions. That is the only genuinely dimensional lemma in the file, and
because units are exponent vectors it is a Fubini argument rather than an
induction: the same simplification Kennedy identifies as the payoff of treating
units as an abelian group rather than as syntax, here strengthened by the
representation being a vector rather than a normal form.

Everything else (that grounding commutes with product, quotient and rational
power, that it composes, that weakening is invisible to it) is discharged in
`LambdaS.Syntax` by linear algebra.

## What is proved

If evaluation returns a value, that value has the type the checker predicted, at
every type and every scope: closures, unit abstraction and dimension abstraction
included. Totality is not claimed here; a fuel-bounded evaluator cannot have it
without a normalization argument, and `none` stays ambiguous between ill-typed
and out-of-fuel. `LambdaS.Normalization` supplies the normalization argument,
and with it the "evaluation succeeds" statement at the whole language.
-/

namespace LambdaS

open scoped BigOperators

variable {B D R : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D] [Num R]

/-! ## The dimensional side condition -/

/-- The runtime environments **respect** the static dimension context: every unit
variable is bound to a unit of the dimension its binder declared.

This is what a unit environment must satisfy to be a semantic model of `Δ`, and
`HasTy.uapp`'s premise `dimOf Δ σ = d` is exactly the syntactic check that
maintains it. -/
def EnvOkD {j k : ℕ} (Δ : DCtx D j k) (η : UEnv B k) (δ : DEnv D j) : Prop :=
  ∀ i, dimOf (D := D) (DCtx.nil D) (η i) = substU δ (Δ i)

/-- **Grounding commutes with taking dimensions.**

The one dimensional lemma in the development. It holds because `dimOf` and
`substU` are both linear maps on exponent vectors, so the content is a change in
summation order rather than an induction over syntax. -/
theorem dimOf_substU {j k : ℕ} {Δ : DCtx D j k} {η : UEnv B k} {δ : DEnv D j}
    (h : EnvOkD Δ η δ) (u : UExp B k) :
    dimOf (D := D) (DCtx.nil D) (substU η u) = substU δ (dimOf Δ u) := by
  refine Term.ext' (funext fun d => ?_) (funext fun w => ?_)
  · have hη : ∀ i, ∑ b, (η i).base b * (UnitSys.dim (D := D) b).base d
        = (Δ i).base d + ∑ x, (Δ i).vars x * (δ x).base d := by
      intro i
      have hi := congrArg (fun t => Term.base t d) (h i)
      simpa [dimOf] using hi
    have fub : ∀ (g : Fin k → ℚ) (f : Fin k → B → ℚ),
        ∑ b, (∑ i, g i * f i b) * (UnitSys.dim (D := D) b).base d
          = ∑ i, g i * ∑ b, f i b * (UnitSys.dim (D := D) b).base d := by
      intro g f
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have fub2 : ∑ x, (∑ i, u.vars i * (Δ i).vars x) * (δ x).base d
        = ∑ i, u.vars i * ∑ x, (Δ i).vars x * (δ x).base d := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [dimOf, substU_base, substU_vars, add_mul, Finset.sum_add_distrib,
      fub, hη, fub2, mul_add, Finset.sum_empty, add_zero]
    ring
  · exact w.elim0

/-- Extending both the dimension context and the unit environment preserves the
condition, provided the new unit has the declared dimension. -/
theorem EnvOkD.cons {j k : ℕ} {Δ : DCtx D j k} {η : UEnv B k} {δ : DEnv D j}
    (h : EnvOkD Δ η δ) {d : DExp D j} {w : UExp B 0}
    (hw : dimOf (D := D) (DCtx.nil D) w = substU δ d) :
    EnvOkD (Δ.cons d) (Fin.cons w η) δ := by
  intro i
  cases i using Fin.cases with
  | zero => simpa [DCtx.cons] using hw
  | succ m => simpa [DCtx.cons] using h m

/-- The dimension analogue, for a dimension abstraction. -/
theorem EnvOkD.consDim {j k : ℕ} {Δ : DCtx D j k} {η : UEnv B k} {δ : DEnv D j}
    (h : EnvOkD Δ η δ) (w : DExp D 0) :
    EnvOkD Δ.weakenDim η (Fin.cons w δ) := by
  intro i
  simpa [DCtx.weakenDim, substU_weaken_cons] using h i

/-! ## Value and environment typing -/

/-- A context grounded through the environments. -/
abbrev groundCtx {j k : ℕ} (η : UEnv B k) (δ : DEnv D j) (Γ : Ctx B D j k) :
    Ctx B D 0 0 := Γ.map (Ty.ground η δ)

mutual

/-- A runtime value has the type the checker predicts, grounded. -/
inductive ValTy : Val R B D → Ty B D 0 0 → Prop where
  | scalar (m : R) (u : UExp B 0) : ValTy (Val.scalar ⟨m, u⟩ : Val R B D) (.Q u)
  | vector {xs : List R} {V : Sp B 0} :
      xs.length = V.length → ValTy (Val.vector xs V : Val R B D) (.vec V)
  | matrix {M : List (List R)} {V W : Sp B 0} :
      M.length = W.length → (∀ r ∈ M, r.length = V.length) →
      ValTy (Val.matrix M V W : Val R B D) (.lin V W)
  | closure {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {σ τ : Ty B D j k}
      {b : Tm B D j k} {ρ : List (Val R B D)} {η : UEnv B k} {δ : DEnv D j}
      {T : Ty B D 0 0} :
      EnvTy ρ (groundCtx η δ Γ) → EnvOkD Δ η δ → HasTy Δ (σ :: Γ) b τ →
      T = Ty.ground η δ (.arrow σ τ) → ValTy (Val.closure σ b ρ η δ) T
  | uclos {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {d : DExp D j}
      {τ : Ty B D j (k + 1)} {b : Tm B D j (k + 1)} {ρ : List (Val R B D)}
      {η : UEnv B k} {δ : DEnv D j} {T : Ty B D 0 0} :
      EnvTy ρ (groundCtx η δ Γ) → EnvOkD Δ η δ →
      HasTy (Δ.cons d) Γ.weaken b τ →
      T = Ty.ground η δ (.all d τ) → ValTy (Val.uclos d b ρ η δ) T
  | dclos {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
      {τ : Ty B D (j + 1) k} {b : Tm B D (j + 1) k} {ρ : List (Val R B D)}
      {η : UEnv B k} {δ : DEnv D j} {T : Ty B D 0 0} :
      EnvTy ρ (groundCtx η δ Γ) → EnvOkD Δ η δ →
      HasTy Δ.weakenDim Γ.weakenDim b τ →
      T = Ty.ground η δ (.allDim τ) → ValTy (Val.dclos b ρ η δ) T

/-- An environment supplies a well-typed value for every entry of a context. -/
inductive EnvTy : List (Val R B D) → Ctx B D 0 0 → Prop where
  | nil : EnvTy ([] : List (Val R B D)) []
  | cons {v : Val R B D} {ρ Γ τ} : ValTy v τ → EnvTy ρ Γ → EnvTy (v :: ρ) (τ :: Γ)

end

/-- Looking up a well-typed environment gives a well-typed value. -/
theorem EnvTy.lookup : ∀ {ρ : List (Val R B D)} {Γ : Ctx B D 0 0} {n : ℕ} {τ},
    EnvTy ρ Γ → Γ[n]? = some τ → ∃ v, ρ[n]? = some v ∧ ValTy v τ := by
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

/-! ## Inversion

A value's shape is determined by its type, which is what discharges the
evaluator's `| _ => none` branches. -/

theorem ValTy.scalar_inv {v : Val R B D} {u : UExp B 0} (h : ValTy v (.Q u)) :
    ∃ m, v = .scalar ⟨m, u⟩ := by
  cases h with
  | scalar m _ => exact ⟨m, rfl⟩
  | closure _ _ _ heq => simp [Ty.ground] at heq
  | uclos _ _ _ heq => simp [Ty.ground] at heq
  | dclos _ _ _ heq => simp [Ty.ground] at heq

theorem ValTy.vector_inv {v : Val R B D} {V : Sp B 0} (h : ValTy v (.vec V)) :
    ∃ xs, v = .vector xs V ∧ xs.length = V.length := by
  cases h with
  | vector hl => exact ⟨_, rfl, hl⟩
  | closure _ _ _ heq => simp [Ty.ground] at heq
  | uclos _ _ _ heq => simp [Ty.ground] at heq
  | dclos _ _ _ heq => simp [Ty.ground] at heq

theorem ValTy.matrix_inv {v : Val R B D} {V W : Sp B 0} (h : ValTy v (.lin V W)) :
    ∃ M, v = .matrix M V W ∧ M.length = W.length ∧ ∀ r ∈ M, r.length = V.length := by
  cases h with
  | matrix hl hr => exact ⟨_, rfl, hl, hr⟩
  | closure _ _ _ heq => simp [Ty.ground] at heq
  | uclos _ _ _ heq => simp [Ty.ground] at heq
  | dclos _ _ _ heq => simp [Ty.ground] at heq

/-! ## The theorem

Strong induction on the fuel, then ordinary induction on the term. The fuel
induction is needed only where evaluation leaves the term (entering a closure
body), and the term induction handles everything else, exactly as in the System F
development. -/

theorem eval_sound (cf : UExp B 0 → UExp B 0 → R) :
    ∀ (n : ℕ) {j k : ℕ} (e : Tm B D j k) (η : UEnv B k) (δ : DEnv D j)
      (ρ : List (Val R B D)) (Δ : DCtx D j k) (Γ : Ctx B D j k) (τ : Ty B D j k)
      (v : Val R B D),
      EnvTy ρ (groundCtx η δ Γ) → EnvOkD Δ η δ → HasTy Δ Γ e τ →
      eval cf n j k η δ ρ e = some v → ValTy v (Ty.ground η δ τ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro j k e
  induction e with
  | var m =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | var hn =>
      simp only [eval] at hv
      have hmap : (groundCtx η δ Γ)[m]? = some (Ty.ground η δ τ) := by
        simp [groundCtx, hn]
      obtain ⟨w, hw, hval⟩ := EnvTy.lookup hρ hmap
      rw [hw] at hv; injection hv with hv; subst hv; exact hval
  | lam σ b ihb =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | lam htb =>
      simp only [eval] at hv
      injection hv with hv; subst hv
      exact .closure hρ hΔ htb rfl
  | ulam d b ihb =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | ulam htb =>
      simp only [eval] at hv
      injection hv with hv; subst hv
      exact .uclos hρ hΔ htb rfl
  | dlam b ihb =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | dlam htb =>
      simp only [eval] at hv
      injection hv with hv; subst hv
      exact .dclos hρ hΔ htb rfl
  | app g a ihg iha =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | app htg hta =>
      cases n with
      | zero => simp only [eval] at hv; exact absurd hv (by simp)
      | succ fu =>
        simp only [eval] at hv
        split at hv
        · rename_i hg ha
          have hcl := ihg η δ ρ Δ Γ _ _ hρ hΔ htg hg
          cases hcl with
          | closure henv hok htb heq =>
            simp only [Ty.ground, Ty.arrow.injEq] at heq
            obtain ⟨he1, he2⟩ := heq
            rw [he2]
            refine ihn fu (by omega) _ _ _ _ _ _ _ _ (.cons ?_ henv) hok htb hv
            have hav := iha η δ ρ Δ Γ _ _ hρ hΔ hta ha
            rwa [he1] at hav
        · exact absurd hv (by simp)
  | uapp f μ ihf =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | uapp htf hdim =>
      cases n with
      | zero => simp only [eval] at hv; exact absurd hv (by simp)
      | succ fu =>
        simp only [eval] at hv
        split at hv
        · rename_i hf
          have hcl := ihf η δ ρ Δ Γ _ _ hρ hΔ htf hf
          cases hcl with
          | uclos henv hok htb heq =>
            simp only [Ty.ground, Ty.all.injEq] at heq
            obtain ⟨he1, he2⟩ := heq
            rw [Ty.ground_subst, ← Ty.ground_liftU_subst, he2, Ty.ground_liftU_subst]
            refine ihn fu (by omega) _ _ _ _ _ _ _ _ ?_
              (hok.cons (by rw [dimOf_substU hΔ, hdim]; exact he1)) htb hv
            simpa [groundCtx, Ctx.weaken, List.map_map, Function.comp_def,
              Ty.ground_weaken] using henv
        · exact absurd hv (by simp)
  | dapp f d ihf =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | dapp htf =>
      cases n with
      | zero => simp only [eval] at hv; exact absurd hv (by simp)
      | succ fu =>
        simp only [eval] at hv
        split at hv
        · rename_i hf
          have hcl := ihf η δ ρ Δ Γ _ _ hρ hΔ htf hf
          cases hcl with
          | dclos henv hok htb heq =>
            simp only [Ty.ground, Ty.allDim.injEq] at heq
            rw [Ty.ground_substDim, ← Ty.ground_liftD_substDim, heq,
              Ty.ground_liftD_substDim]
            refine ihn fu (by omega) _ _ _ _ _ _ _ _ ?_
              (hok.consDim (substU δ d)) htb hv
            simpa [groundCtx, Ctx.weakenDim, List.map_map, Function.comp_def,
              Ty.ground_weakenDim] using henv
        · exact absurd hv (by simp)
  | lit q =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht; simp only [eval] at hv; injection hv with hv; subst hv
    simpa [Ty.ground] using ValTy.scalar (Num.ofRat q) (1 : UExp B 0)
  | ucon u =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht; simp only [eval] at hv; injection hv with hv; subst hv
    exact ValTy.scalar _ _
  | mul a b iha ihb =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | mul hta htb =>
      simp only [eval] at hv
      split at hv
      · rename_i x y ha hb
        obtain ⟨m, hm⟩ := (iha η δ ρ Δ Γ _ _ hρ hΔ hta ha).scalar_inv
        obtain ⟨m', hm'⟩ := (ihb η δ ρ Δ Γ _ _ hρ hΔ htb hb).scalar_inv
        injection hm with hm; injection hm' with hm'; subst hm; subst hm'
        injection hv with hv; subst hv
        simpa [Ty.ground, substU_mul] using ValTy.scalar (R := R) _ _
      · exact absurd hv (by simp)
  | div a b iha ihb =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | div hta htb =>
      simp only [eval] at hv
      split at hv
      · rename_i x y ha hb
        obtain ⟨m, hm⟩ := (iha η δ ρ Δ Γ _ _ hρ hΔ hta ha).scalar_inv
        obtain ⟨m', hm'⟩ := (ihb η δ ρ Δ Γ _ _ hρ hΔ htb hb).scalar_inv
        injection hm with hm; injection hm' with hm'; subst hm; subst hm'
        injection hv with hv; subst hv
        simpa [Ty.ground, substU_div] using ValTy.scalar (R := R) _ _
      · exact absurd hv (by simp)
  | add a b iha ihb =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | add hta htb =>
      simp only [eval] at hv
      split at hv
      · rename_i x y ha hb
        obtain ⟨m, hm⟩ := (iha η δ ρ Δ Γ _ _ hρ hΔ hta ha).scalar_inv
        injection hm with hm; subst hm
        split at hv
        · injection hv with hv; subst hv; exact ValTy.scalar _ _
        · exact absurd hv (by simp)
      · exact absurd hv (by simp)
  | root i a iha =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | root hi hta =>
      simp only [eval] at hv
      split at hv
      · exact absurd hv (by simp)
      · split at hv
        · rename_i x ha
          obtain ⟨m, hm⟩ := (iha η δ ρ Δ Γ _ _ hρ hΔ hta ha).scalar_inv
          injection hm with hm; subst hm
          injection hv with hv; subst hv
          simpa [Ty.ground, substU_rpow] using ValTy.scalar (R := R) _ _
        · exact absurd hv (by simp)
  | log a iha =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | log hta =>
      simp only [eval] at hv
      split at hv
      · rename_i x ha
        split at hv
        · injection hv with hv; subst hv
          simpa [Ty.ground] using ValTy.scalar (R := R) (Num.nlog x.mag) 1
        · exact absurd hv (by simp)
      · exact absurd hv (by simp)
  | exp a iha =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | exp hta =>
      simp only [eval] at hv
      split at hv
      · rename_i x ha
        split at hv
        · injection hv with hv; subst hv
          simpa [Ty.ground] using ValTy.scalar (R := R) (Num.nexp x.mag) 1
        · exact absurd hv (by simp)
      · exact absurd hv (by simp)
  | idx a i iha =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | idx hta hu =>
      simp only [eval] at hv
      split at hv
      · rename_i xs V ha
        obtain ⟨xs', hx, _⟩ := (iha η δ ρ Δ Γ _ _ hρ hΔ hta ha).vector_inv
        injection hx with hx hV; subst hx; subst hV
        split at hv
        · rename_i x u' hx hu'
          injection hv with hv; subst hv
          simp only [List.getElem?_map, hu, Option.map_some] at hu'
          injection hu' with hu'
          subst hu'
          exact ValTy.scalar _ _
        · exact absurd hv (by simp)
      · exact absurd hv (by simp)
  | mapp f x ihf ihx =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | mapp htf htx =>
      simp only [eval] at hv
      split at hv
      · rename_i M V W xs V' hf hx
        obtain ⟨M', hM, hMl, _⟩ := (ihf η δ ρ Δ Γ _ _ hρ hΔ htf hf).matrix_inv
        obtain ⟨xs', hxs, _⟩ := (ihx η δ ρ Δ Γ _ _ hρ hΔ htx hx).vector_inv
        injection hM with hM hV hW; subst hM; subst hV; subst hW
        injection hxs with hxs hV'; subst hxs; subst hV'
        split at hv
        · injection hv with hv; subst hv
          exact ValTy.vector (by rw [Num.matVec_length]; exact hMl)
        · exact absurd hv (by simp)
      · exact absurd hv (by simp)
  | comp f g ihf ihg =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | comp htf htg =>
      simp only [eval] at hv
      split at hv
      · rename_i M V W N U V' hf hg
        obtain ⟨M', hM, hMl, _⟩ := (ihf η δ ρ Δ Γ _ _ hρ hΔ htf hf).matrix_inv
        obtain ⟨N', hN, _, _⟩ := (ihg η δ ρ Δ Γ _ _ hρ hΔ htg hg).matrix_inv
        injection hM with hM hV hW; subst hM; subst hV; subst hW
        injection hN with hN hU hV'; subst hN; subst hU; subst hV'
        split at hv
        · injection hv with hv; subst hv
          refine ValTy.matrix (by simpa using hMl) ?_
          intro r hr
          simp only [List.mem_map] at hr
          obtain ⟨_, _, rfl⟩ := hr
          simp
        · exact absurd hv (by simp)
      · exact absurd hv (by simp)
  | convert a u w iha =>
    intro η δ ρ Δ Γ τ v hρ hΔ ht hv
    cases ht with
    | convert hta hsd =>
      simp only [eval] at hv
      split at hv
      · rename_i x ha
        obtain ⟨m, hm⟩ := (iha η δ ρ Δ Γ _ _ hρ hΔ hta ha).scalar_inv
        injection hm with hm; subst hm
        split at hv
        · injection hv with hv; subst hv; exact ValTy.scalar _ _
        · exact absurd hv (by simp)
      · exact absurd hv (by simp)

end LambdaS

/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Normalization
import LambdaS.Adequacy

/-!
# Erasure, at the whole language

Unit elimination is a compiler optimization, not part of the semantics, and its
burden is to preserve the semantics. An ancestor in `LambdaS.Dynamics`, since
deleted, discharged that burden for the first-order arithmetic fragment; this
file discharges it for the whole of Λs.

## The erased evaluator

`eeval` is `eval` with two things removed: the **annotations** (values carry no
units, closures carry no type or dimension ascriptions) and the **checks**
(`add` does not compare units, `log` and `exp` do not demand dimensionlessness,
`convert` does not verify its source, `mapp` and `comp` do not compare spaces,
and `root` does not test its index). Nothing is checked because there is nothing
left to check against, which is the point: the erased evaluator is the one a
compiler would emit.

Two things deliberately survive erasure, and neither is a unit.

**Shape** survives: a vector is still a list, and a matrix keeps its column
count, without which the composite of a zero-row matrix has no width. That is
array-dimension information, and no compiler erases it. The syntax makes the
same commitment at the introduction form: `mnil` carries its column space, so
the width of a zero-row matrix is written in the term and the erased value
keeps exactly the length of that space.

**The unit environments** survive: `convert` under a unit binder takes its
factor from the unit the caller supplies at runtime, so the evaluator keeps `η`
and `δ`: a value the size of the *scope*, not of the data. This is the residue
of conversion: units are static except for the finitely many scale
factors a polymorphic conversion must receive, exactly as a dictionary-passing
compiler would arrange.

## The theorems

`eeval_erase` is a **simulation, with no typing hypothesis**: whenever the
instrumented evaluator produces a value, the erased evaluator produces its
erasure, step for step, at the same fuel. Typing is not needed because the
instrumented evaluator's success already witnesses that every erased check would
have passed.

Typing enters with the corollaries, which compose the simulation with
normalization and adequacy. `erasure_correct` says a well-typed closed scalar
term evaluates on **both** evaluators, to the same magnitude, at the unit the type
predicts, so the type system knows statically everything the erased evaluator no
longer carries. `eeval_den` says the erased evaluator computes the denotation,
with the conversion oracle the valuation determines: the compiled program's
output is the mathematical meaning, with the units gone from the values and
alive in the types.
-/

namespace LambdaS

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D]
variable {R : Type} [Num R]

/-- **Erased runtime values.** No units, no spaces, no ascriptions. A matrix
keeps its column count: shape, not units. -/
inductive EVal (R B D : Type) where
  | scalar : R → EVal R B D
  | vector : List R → EVal R B D
  | matrix : List (List R) → ℕ → EVal R B D
  | closure {j k : ℕ} : Tm B D j k → List (EVal R B D) →
      UEnv B k → DEnv D j → EVal R B D
  | uclos {j k : ℕ} : Tm B D j (k + 1) → List (EVal R B D) →
      UEnv B k → DEnv D j → EVal R B D
  | dclos {j k : ℕ} : Tm B D (j + 1) k → List (EVal R B D) →
      UEnv B k → DEnv D j → EVal R B D

/-- **The erased evaluator.** `eval` with the annotations and the checks gone. -/
def eeval (cf : UExp B 0 → UExp B 0 → R) :
    ℕ → (j k : ℕ) → UEnv B k → DEnv D j → List (EVal R B D) → Tm B D j k →
      Option (EVal R B D)
  | _, _, _, _, _, ρ, .var n => ρ[n]?
  | _, _, _, η, δ, ρ, .lam _ b => some (.closure b ρ η δ)
  | _, _, _, η, δ, ρ, .ulam _ b => some (.uclos b ρ η δ)
  | _, _, _, η, δ, ρ, .dlam b => some (.dclos b ρ η δ)
  | 0, _, _, _, _, _, .app _ _ => none
  | 0, _, _, _, _, _, .uapp _ _ => none
  | 0, _, _, _, _, _, .dapp _ _ => none
  | fu + 1, j, k, η, δ, ρ, .app g a =>
      match eeval cf (fu + 1) j k η δ ρ g, eeval cf (fu + 1) j k η δ ρ a with
      | some (.closure (j := j') (k := k') b ρ' η' δ'), some av =>
          eeval cf fu j' k' η' δ' (av :: ρ') b
      | _, _ => none
  | fu + 1, j, k, η, δ, ρ, .uapp f μ =>
      match eeval cf (fu + 1) j k η δ ρ f with
      | some (.uclos (j := j') (k := k') b ρ' η' δ') =>
          eeval cf fu j' (k' + 1) (Fin.cons (substU η μ) η') δ' ρ' b
      | _ => none
  | fu + 1, j, k, η, δ, ρ, .dapp f d =>
      match eeval cf (fu + 1) j k η δ ρ f with
      | some (.dclos (j := j') (k := k') b ρ' η' δ') =>
          eeval cf fu (j' + 1) k' η' (Fin.cons (substU δ d) δ') ρ' b
      | _ => none
  | _, _, _, _, _, _, .lit q => some (.scalar (Num.ofRat q))
  | _, _, _, _, _, _, .ucon _ => some (.scalar (Num.ofRat 1))
  | fu, j, k, η, δ, ρ, .mul a b =>
      match eeval cf fu j k η δ ρ a, eeval cf fu j k η δ ρ b with
      | some (.scalar x), some (.scalar y) => some (.scalar (Num.mul x y))
      | _, _ => none
  | fu, j, k, η, δ, ρ, .div a b =>
      match eeval cf fu j k η δ ρ a, eeval cf fu j k η δ ρ b with
      | some (.scalar x), some (.scalar y) => some (.scalar (Num.div x y))
      | _, _ => none
  | fu, j, k, η, δ, ρ, .add a b =>
      match eeval cf fu j k η δ ρ a, eeval cf fu j k η δ ρ b with
      | some (.scalar x), some (.scalar y) => some (.scalar (Num.add x y))
      | _, _ => none
  | fu, j, k, η, δ, ρ, .root n a =>
      match eeval cf fu j k η δ ρ a with
      | some (.scalar x) => some (.scalar (Num.nroot n x))
      | _ => none
  | fu, j, k, η, δ, ρ, .log a =>
      match eeval cf fu j k η δ ρ a with
      | some (.scalar x) => some (.scalar (Num.nlog x))
      | _ => none
  | fu, j, k, η, δ, ρ, .exp a =>
      match eeval cf fu j k η δ ρ a with
      | some (.scalar x) => some (.scalar (Num.nexp x))
      | _ => none
  | fu, j, k, η, δ, ρ, .idx a i =>
      match eeval cf fu j k η δ ρ a with
      | some (.vector xs) =>
          match xs[i]? with
          | some x => some (.scalar x)
          | none => none
      | _ => none
  | fu, j, k, η, δ, ρ, .mapp f x =>
      match eeval cf fu j k η δ ρ f, eeval cf fu j k η δ ρ x with
      | some (.matrix M _), some (.vector xs) => some (.vector (Num.matVec M xs))
      | _, _ => none
  | fu, j, k, η, δ, ρ, .comp f g =>
      match eeval cf fu j k η δ ρ f, eeval cf fu j k η δ ρ g with
      | some (.matrix M _), some (.matrix N c) =>
          some (.matrix (M.map fun row =>
            (List.range c).map fun i => dotp row (colOf N i)) c)
      | _, _ => none
  | _, _, _, _, _, _, .vnil => some (.vector [])
  | fu, j, k, η, δ, ρ, .vcons e v =>
      match eeval cf fu j k η δ ρ e, eeval cf fu j k η δ ρ v with
      | some (.scalar x), some (.vector xs) => some (.vector (x :: xs))
      | _, _ => none
  | _, _, _, _, _, _, .mnil V => some (.matrix [] V.length)
  | fu, j, k, η, δ, ρ, .mcons _ r M =>
      match eeval cf fu j k η δ ρ r, eeval cf fu j k η δ ρ M with
      | some (.vector xs), some (.matrix N c) => some (.matrix (xs :: N) c)
      | _, _ => none
  | fu, j, k, η, δ, ρ, .convert a u v =>
      match eeval cf fu j k η δ ρ a with
      | some (.scalar x) =>
          some (.scalar (Num.mul x (cf (substU η u) (substU η v))))
      | _ => none
termination_by fu _ _ _ _ _ e => (fu, sizeOf e)

mutual

/-- Erasing a value: drop the units, keep the shape. A closure's captured
environment is erased along with it. -/
def Val.erase : Val R B D → EVal R B D
  | .scalar x => .scalar x.mag
  | .vector xs _ => .vector xs
  | .matrix M V _ => .matrix M V.length
  | .closure _ b ρ η δ => .closure b (Val.eraseList ρ) η δ
  | .uclos _ b ρ η δ => .uclos b (Val.eraseList ρ) η δ
  | .dclos b ρ η δ => .dclos b (Val.eraseList ρ) η δ

/-- Erasing an environment. -/
def Val.eraseList : List (Val R B D) → List (EVal R B D)
  | [] => []
  | v :: ρ => v.erase :: Val.eraseList ρ

end

/-- Erasure commutes with lookup. -/
theorem eraseList_getElem? : ∀ (ρ : List (Val R B D)) (n : ℕ),
    (Val.eraseList ρ)[n]? = (ρ[n]?).map Val.erase
  | [], _ => by simp [Val.eraseList]
  | _ :: _, 0 => by simp [Val.eraseList]
  | _ :: ρ, n + 1 => by simpa [Val.eraseList] using eraseList_getElem? ρ n

/-- **The simulation.** Whenever the instrumented evaluator produces a value, the
erased evaluator produces its erasure: same term, same fuel, erased environment.

No typing hypothesis: the instrumented evaluator's success already witnesses that
every check the erased evaluator skips would have passed. -/
theorem eeval_erase (cf : UExp B 0 → UExp B 0 → R) :
    ∀ (n : ℕ) {j k : ℕ} (e : Tm B D j k) (η : UEnv B k) (δ : DEnv D j)
      (ρ : List (Val R B D)) (v : Val R B D),
      eval cf n j k η δ ρ e = some v →
      eeval cf n j k η δ (Val.eraseList ρ) e = some v.erase
  | _, _, _, .var i, η, δ, ρ, v, h => by
      simp only [eval] at h
      simp only [eeval, eraseList_getElem?, h, Option.map_some]
  | _, _, _, .lam σ b, η, δ, ρ, v, h => by
      simp only [eval] at h
      obtain rfl := Option.some.inj h
      simp [eeval, Val.erase]
  | _, _, _, .ulam d b, η, δ, ρ, v, h => by
      simp only [eval] at h
      obtain rfl := Option.some.inj h
      simp [eeval, Val.erase]
  | _, _, _, .dlam b, η, δ, ρ, v, h => by
      simp only [eval] at h
      obtain rfl := Option.some.inj h
      simp [eeval, Val.erase]
  | _, _, _, .lit q, η, δ, ρ, v, h => by
      simp only [eval] at h
      obtain rfl := Option.some.inj h
      simp [eeval, Val.erase]
  | _, _, _, .ucon u, η, δ, ρ, v, h => by
      simp only [eval] at h
      obtain rfl := Option.some.inj h
      simp [eeval, Val.erase]
  | 0, _, _, .app _ _, _, _, _, _, h => by simp [eval] at h
  | 0, _, _, .uapp _ _, _, _, _, _, h => by simp [eval] at h
  | 0, _, _, .dapp _ _, _, _, _, _, h => by simp [eval] at h
  | fu + 1, _, _, .app g a, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i σ' b' ρ' η' δ' av hg ha
        have hg' := eeval_erase cf (fu + 1) g η δ ρ _ hg
        have ha' := eeval_erase cf (fu + 1) a η δ ρ _ ha
        have hb' := eeval_erase cf fu b' η' δ' (av :: ρ') v h
        simp only [eeval, hg', ha', Val.erase]
        exact hb'
      · exact absurd h (by simp)
  | fu + 1, _, _, .uapp f μ, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i d' b' ρ' η' δ' hf
        have hf' := eeval_erase cf (fu + 1) f η δ ρ _ hf
        have hb' := eeval_erase cf fu b' (Fin.cons (substU η μ) η') δ' ρ' v h
        simp only [eeval, hf', Val.erase]
        exact hb'
      · exact absurd h (by simp)
  | fu + 1, _, _, .dapp f d, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i b' ρ' η' δ' hf
        have hf' := eeval_erase cf (fu + 1) f η δ ρ _ hf
        have hb' := eeval_erase cf fu b' η' (Fin.cons (substU δ d) δ') ρ' v h
        simp only [eeval, hf', Val.erase]
        exact hb'
      · exact absurd h (by simp)
  | fu, _, _, .mul a b, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i x y ha hb
        obtain rfl := Option.some.inj h.symm
        simp only [eeval, eeval_erase cf fu a η δ ρ _ ha,
          eeval_erase cf fu b η δ ρ _ hb, Val.erase]
      · exact absurd h (by simp)
  | fu, _, _, .div a b, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i x y ha hb
        obtain rfl := Option.some.inj h.symm
        simp only [eeval, eeval_erase cf fu a η δ ρ _ ha,
          eeval_erase cf fu b η δ ρ _ hb, Val.erase]
      · exact absurd h (by simp)
  | fu, _, _, .add a b, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i x y ha hb
        split at h
        · obtain rfl := Option.some.inj h.symm
          simp only [eeval, eeval_erase cf fu a η δ ρ _ ha,
            eeval_erase cf fu b η δ ρ _ hb, Val.erase]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | fu, _, _, .root n a, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · rename_i _ x ha
          obtain rfl := Option.some.inj h.symm
          simp only [eeval, eeval_erase cf fu a η δ ρ _ ha, Val.erase]
        · exact absurd h (by simp)
  | fu, _, _, .log a, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i x ha
        split at h
        · obtain rfl := Option.some.inj h.symm
          simp only [eeval, eeval_erase cf fu a η δ ρ _ ha, Val.erase]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | fu, _, _, .exp a, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i x ha
        split at h
        · obtain rfl := Option.some.inj h.symm
          simp only [eeval, eeval_erase cf fu a η δ ρ _ ha, Val.erase]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | fu, _, _, .idx a i, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i xs V ha
        split at h
        · rename_i x u hx hu
          obtain rfl := Option.some.inj h.symm
          simp only [eeval, eeval_erase cf fu a η δ ρ _ ha, Val.erase, hx]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | fu, _, _, .mapp f x, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i M V W xs V' hf hx
        split at h
        · obtain rfl := Option.some.inj h.symm
          simp only [eeval, eeval_erase cf fu f η δ ρ _ hf,
            eeval_erase cf fu x η δ ρ _ hx, Val.erase]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | fu, _, _, .comp f g, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i M V W N U V' hf hg
        split at h
        · obtain rfl := Option.some.inj h.symm
          simp only [eeval, eeval_erase cf fu f η δ ρ _ hf,
            eeval_erase cf fu g η δ ρ _ hg, Val.erase]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | _, _, _, .vnil, η, δ, ρ, v, h => by
      simp only [eval] at h
      obtain rfl := Option.some.inj h
      simp [eeval, Val.erase]
  | fu, _, _, .vcons e ev, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i x xs V he hv
        obtain rfl := Option.some.inj h.symm
        simp only [eeval, eeval_erase cf fu e η δ ρ _ he,
          eeval_erase cf fu ev η δ ρ _ hv, Val.erase]
      · exact absurd h (by simp)
  | _, _, _, .mnil V, η, δ, ρ, v, h => by
      simp only [eval] at h
      obtain rfl := Option.some.inj h
      simp [eeval, Val.erase]
  | fu, _, _, .mcons w r M, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i xs Vr N V W hr hM
        obtain rfl := Option.some.inj h.symm
        simp only [eeval, eeval_erase cf fu r η δ ρ _ hr,
          eeval_erase cf fu M η δ ρ _ hM, Val.erase]
      · exact absurd h (by simp)
  | fu, _, _, .convert a u w, η, δ, ρ, v, h => by
      simp only [eval] at h
      split at h
      · rename_i x ha
        split at h
        · rename_i hcheck
          obtain rfl := Option.some.inj h.symm
          have := eeval_erase cf fu a η δ ρ _ ha
          simp only [eeval, this, Val.erase, hcheck.1]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
termination_by n j k e => (n, sizeOf e)

/-! ## Erasure is safe, at the whole language -/

/-- **Erasure preserves results**: the full-language statement. A well-typed
closed term of scalar type evaluates on both evaluators at some common fuel: the
instrumented one to a measurement carrying exactly the unit its type predicts,
the erased one to exactly that measurement's magnitude.

Everything the erased evaluator no longer carries, the type system knew
statically. This is "units are static", proved rather than asserted, with unit
polymorphism, higher-order structure, spaces and conversion all included;
the fragment restriction of the old statement is gone, and so is its fuel
hypothesis, which normalization now discharges. -/
theorem erasure_correct (cf : UExp B 0 → UExp B 0 → R) {e : Tm B D 0 0}
    {u : UExp B 0} (d : HasTy (DCtx.nil D) ([] : Ctx B D 0 0) e (.Q u)) :
    ∃ (n : ℕ) (m : R),
      evalC cf n [] e = some (.scalar ⟨m, u⟩) ∧
      eeval cf n 0 0 (nilU B) (nilU D) [] e = some (.scalar m) := by
  obtain ⟨n, m, hm⟩ := unit_soundness_total cf d
  exact ⟨n, m, hm, eeval_erase cf n e (nilU B) (nilU D) [] _ hm⟩

/-- **The erased evaluator computes the denotation.** With the conversion oracle
the valuation determines, the compiled program's output is the mathematical
meaning: units gone from the values, alive in the types. Adequacy composed
with the simulation. -/
theorem eeval_den (V : Scaling B 0) {e : Tm B D 0 0} {u : UExp B 0}
    (d : HasTy (DCtx.nil D) ([] : Ctx B D 0 0) e (.Q u)) :
    ∃ n : ℕ, eeval (conv V) n 0 0 (nilU B) (nilU D) [] e
      = some (.scalar (den V d PUnit.unit)) := by
  obtain ⟨n, hn⟩ := evalC_eq_den V d
  exact ⟨n, eeval_erase (conv V) n e (nilU B) (nilU D) [] _ hn⟩

end LambdaS

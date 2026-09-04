/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Typing
import LambdaS.Num
import LambdaS.Conversion

/-!
# Instrumented dynamics

Kennedy argues (WMM 2008) that instrumenting runtime values with their units is
"cheating", on the grounds that it makes type soundness trivial. That objection
has force for **F#**, which erases units, so an instrumented semantics would not
model the language he shipped.

It does not have force for a core calculus, and the reason is worth stating.
Runtime units alone *would* merely relocate the checking to the runtime. But
paired with a theorem that **erasure preserves results**, they establish
something the erased semantics cannot state on its own: that the instrumentation
is *unnecessary*. That is precisely the content of "units are static", a
slogan easy to assert and, before these files, unproved.

So there are three things, and they are complementary rather than competing:

| | proves |
|---|---|
| instrumented dynamics + `unit_soundness_total` | the dynamic unit checks **never fire** on well-typed terms |
| `eeval_erase` (`LambdaS.Erasure`) | dropping units **does not change the numbers** |
| scaling parametricity, i.e. invariance of results under a change of units (`LambdaS.Fundamental`) | units have **observable meaning** |

Kennedy did the third column. This file defines the instrumented evaluator; its
soundness lives in `LambdaS.Soundness` and `LambdaS.Normalization`, and erasure
in `LambdaS.Erasure`; all three are stated at the whole language.
-/

namespace LambdaS

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D]

variable {R : Type} [Num R]

/-- A runtime **measurement**: a magnitude together with the unit it is measured
in. This is the OOPSLA'04 notion of a measurement as a value. -/
structure Meas (R B : Type) where
  mag : R
  unit : UExp B 0

/-! ## Environments

Evaluation has three environments, and they are the same idea three times over:
a value for each value variable, a **ground unit** for each unit variable, and a
**ground dimension** for each dimension variable.

Units are *looked up*, never substituted. Substituting a unit into a term during
evaluation would be compile-time work done at runtime, and it would also force
the evaluator to live only at the closed scope: a term under a unit binder
could not be evaluated at all without first eliminating the binder. With an
environment, `eval` is defined at every scope, which is what makes the ordinary
induction principles apply to it. -/

/-- A ground unit for each unit variable in scope. -/
abbrev UEnv (B : Type) (k : ℕ) := Fin k → UExp B 0

/-- A ground dimension for each dimension variable in scope. -/
abbrev DEnv (D : Type) (j : ℕ) := Fin j → DExp D 0

/-- A runtime **value**: a measurement, a vector over a space, a linear map
between spaces, or a closure.

Vectors and matrices carry their spaces, not a unit per entry. That is not an
optimization: `LambdaS.Map` proves the units of a linear map are rank-one, entry
`(j,i)` carrying `δ_W(j)/δ_V(i)`, so an `n×m` map needs `n+m` units rather than
`nm`. After type checking the numeric payload is a plain array, which is what
makes a BLAS kernel usable underneath without any per-entry tagging.

Closures package the scope they were built at, along with all three environments,
so a value is always ground even when the term it came from was not. -/
inductive Val (R B D : Type) where
  | scalar : Meas R B → Val R B D
  | vector : List R → Sp B 0 → Val R B D
  | matrix : List (List R) → Sp B 0 → Sp B 0 → Val R B D
  | closure {j k : ℕ} : Ty B D j k → Tm B D j k → List (Val R B D) →
      UEnv B k → DEnv D j → Val R B D
  | uclos {j k : ℕ} : DExp D j → Tm B D j (k + 1) → List (Val R B D) →
      UEnv B k → DEnv D j → Val R B D
  | dclos {j k : ℕ} : Tm B D (j + 1) k → List (Val R B D) →
      UEnv B k → DEnv D j → Val R B D

/-- The dot product an application of a linear map performs.

Forwards to `Num.dot`, which the `Float` carrier overrides with the native
kernel, so this is the point where a compiled Λs program crosses into C. -/
def dotp (a b : List R) : R := Num.dot a b

/-- Column `i` of a matrix, padded with zero. -/
def colOf (N : List (List R)) (i : ℕ) : List R :=
  N.map fun r => r[i]?.getD (Num.ofRat 0)


/-- **Instrumented evaluation.** Values carry their units, and the evaluator is
*partial*: adding mismatched units, taking a zeroth root, taking `log` of a
dimensioned quantity, and applying a linear map to a vector of the wrong space
all get stuck.

Those stuck states are the whole point. `unit_soundness_total` says they are
unreachable from a well-typed term.

Fuel is consumed only where a closure body is entered, which is the only place
the recursion leaves the term. Nothing else spends it, so first-order arithmetic
evaluates at every bound including zero.

Data may arrive through the environment or be built by the introduction forms:
`vnil`/`vcons` assemble a vector value one scalar at a time, and `mnil`/`mcons`
assemble a matrix one row at a time, with `mnil` grounding its annotated column
space so even a rowless matrix value knows its width. Like the other
introduction forms (`mul` building a product unit, `lam` building a closure),
they check nothing: the dynamic unit checks live at the eliminations, where a
mismatch would corrupt the arithmetic. A literal whose scalars name units via
`ucon` sits outside the invariance theory for exactly the reason
`LambdaS.Fundamental` gives about unit constants. -/
def eval (cf : UExp B 0 → UExp B 0 → R) :
    ℕ → (j k : ℕ) → UEnv B k → DEnv D j → List (Val R B D) → Tm B D j k →
      Option (Val R B D)
  | _, _, _, _, _, ρ, .var n => ρ[n]?
  | _, _, _, η, δ, ρ, .lam τ b => some (.closure τ b ρ η δ)
  | _, _, _, η, δ, ρ, .ulam d b => some (.uclos d b ρ η δ)
  | _, _, _, η, δ, ρ, .dlam b => some (.dclos b ρ η δ)
  | 0, _, _, _, _, _, .app _ _ => none
  | 0, _, _, _, _, _, .uapp _ _ => none
  | 0, _, _, _, _, _, .dapp _ _ => none
  | fu + 1, j, k, η, δ, ρ, .app g a =>
      match eval cf (fu + 1) j k η δ ρ g, eval cf (fu + 1) j k η δ ρ a with
      | some (.closure (j := j') (k := k') _ b ρ' η' δ'), some av =>
          eval cf fu j' k' η' δ' (av :: ρ') b
      | _, _ => none
  | fu + 1, j, k, η, δ, ρ, .uapp f μ =>
      match eval cf (fu + 1) j k η δ ρ f with
      | some (.uclos (j := j') (k := k') _ b ρ' η' δ') =>
          eval cf fu j' (k' + 1) (Fin.cons (substU η μ) η') δ' ρ' b
      | _ => none
  | fu + 1, j, k, η, δ, ρ, .dapp f d =>
      match eval cf (fu + 1) j k η δ ρ f with
      | some (.dclos (j := j') (k := k') b ρ' η' δ') =>
          eval cf fu (j' + 1) k' η' (Fin.cons (substU δ d) δ') ρ' b
      | _ => none
  | _, _, _, _, _, _, .lit q => some (.scalar ⟨Num.ofRat q, 1⟩)
  | _, _, _, η, _, _, .ucon u => some (.scalar ⟨Num.ofRat 1, substU η u⟩)
  | fu, j, k, η, δ, ρ, .mul a b =>
      match eval cf fu j k η δ ρ a, eval cf fu j k η δ ρ b with
      | some (.scalar x), some (.scalar y) =>
          some (.scalar ⟨Num.mul x.mag y.mag, Term.mul x.unit y.unit⟩)
      | _, _ => none
  | fu, j, k, η, δ, ρ, .div a b =>
      match eval cf fu j k η δ ρ a, eval cf fu j k η δ ρ b with
      | some (.scalar x), some (.scalar y) =>
          some (.scalar ⟨Num.div x.mag y.mag, Term.div x.unit y.unit⟩)
      | _, _ => none
  | fu, j, k, η, δ, ρ, .add a b =>
      match eval cf fu j k η δ ρ a, eval cf fu j k η δ ρ b with
      | some (.scalar x), some (.scalar y) =>
          if x.unit = y.unit then some (.scalar ⟨Num.add x.mag y.mag, x.unit⟩) else none
      | _, _ => none
  | fu, j, k, η, δ, ρ, .root n a =>
      if n = 0 then none else
        match eval cf fu j k η δ ρ a with
        | some (.scalar x) =>
            some (.scalar ⟨Num.nroot n x.mag, Term.rpow x.unit (1 / (n : ℚ))⟩)
        | _ => none
  | fu, j, k, η, δ, ρ, .log a =>
      match eval cf fu j k η δ ρ a with
      | some (.scalar x) =>
          if x.unit = 1 then some (.scalar ⟨Num.nlog x.mag, 1⟩) else none
      | _ => none
  | fu, j, k, η, δ, ρ, .exp a =>
      match eval cf fu j k η δ ρ a with
      | some (.scalar x) =>
          if x.unit = 1 then some (.scalar ⟨Num.nexp x.mag, 1⟩) else none
      | _ => none
  | fu, j, k, η, δ, ρ, .idx a i =>
      match eval cf fu j k η δ ρ a with
      | some (.vector xs V) =>
          match xs[i]?, V[i]? with
          | some x, some u => some (.scalar ⟨x, u⟩)
          | _, _ => none
      | _ => none
  | fu, j, k, η, δ, ρ, .mapp f x =>
      match eval cf fu j k η δ ρ f, eval cf fu j k η δ ρ x with
      | some (.matrix M V W), some (.vector xs V') =>
          if V' = V then some (.vector (Num.matVec M xs) W) else none
      | _, _ => none
  | fu, j, k, η, δ, ρ, .comp f g =>
      match eval cf fu j k η δ ρ f, eval cf fu j k η δ ρ g with
      | some (.matrix M V W), some (.matrix N U V') =>
          if V' = V then
            some (.matrix (M.map fun row =>
              (List.range U.length).map fun i => dotp row (colOf N i)) U W)
          else none
      | _, _ => none
  | _, _, _, _, _, _, .vnil => some (.vector [] [])
  | fu, j, k, η, δ, ρ, .vcons e v =>
      match eval cf fu j k η δ ρ e, eval cf fu j k η δ ρ v with
      | some (.scalar x), some (.vector xs V) =>
          some (.vector (x.mag :: xs) (x.unit :: V))
      | _, _ => none
  | _, _, _, η, _, _, .mnil V => some (.matrix [] (V.map (substU η)) [])
  | fu, j, k, η, δ, ρ, .mcons w r M =>
      match eval cf fu j k η δ ρ r, eval cf fu j k η δ ρ M with
      | some (.vector xs _), some (.matrix N V W) =>
          some (.matrix (xs :: N) V (substU η w :: W))
      | _, _ => none
  | fu, j, k, η, δ, ρ, .convert a u v =>
      match eval cf fu j k η δ ρ a with
      | some (.scalar x) =>
          if x.unit = substU η u ∧ SameDim (DCtx.nil D) (substU η u) (substU η v) then
            some (.scalar ⟨Num.mul x.mag (cf (substU η u) (substU η v)), substU η v⟩)
          else none
      | _ => none
termination_by fu _ _ _ _ _ e => (fu, sizeOf e)


/-- Evaluation of a closed term, with all three environments empty. -/
abbrev evalC (cf : UExp B 0 → UExp B 0 → R) (n : ℕ) (ρ : List (Val R B D))
    (e : Tm B D 0 0) : Option (Val R B D) :=
  eval cf n 0 0 (nilU B) (nilU D) ρ e




/-! ## The I/O boundary: measurements whose unit arrives at runtime

A measurement read from a file carries a unit *name*, resolved against the
declared system to a `UExp B 0`. What arrives is a `Meas`, and using it in typed
code means committing to a unit: a **checked cast**.

That cast is the whole content of a dimension-typed value `∃u:d. Q u`, and it is
deliberately *not* a type former. At runtime such a value is the pair
`(magnitude, factor)`: the magnitude, and the dictionary a bounded quantifier
would have been instantiated with. Once the unit name is resolved that pair is
exactly a `Meas`. Keeping it here rather than in `Ty` leaves every type in Λs
erasable, and confines the trust to one partial function, whose partiality is
the trust boundary, since nothing checks that a name off a disk denotes a
declared unit.
-/

/-- **The checked cast.** Read a measurement at a demanded unit: convert if the
dimensions agree, fail if they do not.

`Option` rather than a runtime error, so the boundary is visible in the type. -/
noncomputable def asUnit (Δ : DCtx D 0 0) (ψ : Scaling B 0) (x : Meas ℝ B) (μ : UExp B 0) :
    Option ℝ :=
  if SameDim Δ x.unit μ then some (x.mag * conv ψ x.unit μ) else none

omit [DecidableEq B] in
/-- **The cast preserves the quantity.** When it succeeds, the number it returns
denotes the same physical quantity read in the demanded unit.

This is what makes the boundary safe on the inside: everything past `asUnit` is
ordinary typed code with a correct magnitude. -/
theorem asUnit_preserves {Δ : DCtx D 0 0} {ψ : Scaling B 0} {x : Meas ℝ B} {μ : UExp B 0}
    {m : ℝ} (h : asUnit Δ ψ x μ = some m) : ψ.scale μ * m = ψ.scale x.unit * x.mag := by
  unfold asUnit at h
  split at h
  · injection h with h; subst h; exact conv_preserves ψ x.unit μ x.mag
  · exact absurd h (by simp)

omit [DecidableEq B] in
/-- **The cast rejects a dimension mismatch.** Reading a duration as a length
fails rather than silently scaling: the Mars Climate Orbiter failure at the one
place in Λs where it could still occur. -/
theorem asUnit_eq_none {Δ : DCtx D 0 0} {ψ : Scaling B 0} {x : Meas ℝ B} {μ : UExp B 0}
    (h : ¬ SameDim Δ x.unit μ) : asUnit Δ ψ x μ = none := by
  simp [asUnit, h]

/-- The cast agrees with the calculus: casting to `μ` is what `convert` computes,
so the boundary operation is not a second, unverified conversion path. -/
theorem asUnit_eq_eval_convert {Δ : DCtx D 0 0} {ψ : Scaling B 0} {a : Tm B D 0 0}
    {x : Meas ℝ B} {v : UExp B 0} {fuel : ℕ} (ha : evalC (conv ψ) fuel [] a = some (.scalar x)) (hΔ : Δ = DCtx.nil D) :
    evalC (conv ψ) fuel [] (.convert a x.unit v) = (asUnit Δ ψ x v).map (fun m => .scalar ⟨m, v⟩) := by
  subst hΔ
  simp only [eval, ha, asUnit]
  split <;> simp_all [Num.mul, conv]

/-! ### What has to be passed at runtime

The target unit `μ` of a cast is itself often read from I/O, so it too is a
runtime value, which raises the question of what a compiler actually has to
carry. The answer splits cleanly in two, and the split is the difference between
the dimension check and the arithmetic.

**The arithmetic needs only the factor.** Past the dimension check the unit
expression is not observable: the cast is computed from the magnitude and
`ψ.scale`, so two measurements with the same magnitude and the same scale factor
cast identically whatever units they name. That pair (magnitude and factor) is
exactly the dictionary a bounded quantifier is instantiated with, which is why
`∃u:d. Q u` needs no type former to be implementable.

**The check needs the unit itself.** `SameDim` is a statement about exponent
vectors and cannot be recovered from a single real number: two units of
different dimensions can share a scale factor. So a runtime unit must be carried
as data up to the check, and may be discarded after it.
-/

/-- The runtime **dictionary** of a measurement: its magnitude and the scale
factor of its unit. This is what a compiler passes when instantiating a bounded
unit quantifier at a unit known only at runtime. -/
noncomputable def Meas.dict (ψ : Scaling B 0) (x : Meas ℝ B) : ℝ × ℝ :=
  (x.mag, ψ.scale x.unit)

omit [DecidableEq B] in
/-- **The cast is computed from the dictionary.** Once the dimension check has
passed the unit expression plays no further part: the answer is the magnitude
times its own factor over the target's. -/
theorem asUnit_eq_dict {Δ : DCtx D 0 0} {ψ : Scaling B 0} {x : Meas ℝ B} {μ : UExp B 0}
    (h : SameDim Δ x.unit μ) :
    asUnit Δ ψ x μ = some ((x.dict ψ).1 * (x.dict ψ).2 / ψ.scale μ) := by
  simp [asUnit, h, Meas.dict, conv, mul_div_assoc]

omit [DecidableEq B] in
/-- **The dictionary determines the answer.** Two measurements agreeing on
magnitude and scale factor cast to the same number, whatever units they name.

This is the precise sense in which the unit need not survive past the check;
and, read the other way, the precise sense in which it must survive *up to* it,
since `SameDim` is not a function of the scale factor. -/
theorem asUnit_dict_determined {Δ : DCtx D 0 0} {ψ : Scaling B 0} {x y : Meas ℝ B}
    {μ : UExp B 0} (hd : x.dict ψ = y.dict ψ)
    (hx : SameDim Δ x.unit μ) (hy : SameDim Δ y.unit μ) :
    asUnit Δ ψ x μ = asUnit Δ ψ y μ := by
  rw [asUnit_eq_dict hx, asUnit_eq_dict hy, hd]

end LambdaS

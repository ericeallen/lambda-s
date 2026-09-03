/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Typing

/-!
# Surface syntax

Programs have so far been written as abstract syntax: `.div (.mul (.mul pi pi)
(.mul hbar hbar)) (.mul (.mul (num 2) mass) (.mul width width))`. That is a
faithful way to describe a calculus and a terrible way to write physics.

This file adds a bracket `⟪ … ⟫` with the usual arithmetic notation inside, so
the same term reads

    ⟪ (pi * pi * hbar * hbar) / (2 * mass * width * width) ⟫

Identifiers inside the bracket are ordinary Lean names bound to terms, so the
notation composes with definitions rather than replacing them. It is a
convenience layer over `Tm` and nothing more: no separate parser, no separate
AST, and every guard elsewhere still checks the same core terms.

## Elaboration, and where `convert` gets its annotation

`Tm.convert` carries the unit it converts **from**, because the evaluator must
recover the factor from the term and the unit environment alone. Making the user write it would be both tedious
and unsafe. `elabConvert` supplies it by running the *verified* checker: it
checks the subject, reads the unit off the type it derived, and builds the
annotated term.

This is what makes conversion-as-a-core-constructor tenable. `elabConvert`
returns the elaborated term *together with its derivation*, so a surface `in`
cannot produce a core term the checker would reject: the annotation is not
merely machine-generated but machine-justified.
-/

namespace LambdaS

/-! ## The bracket -/

declare_syntax_cat lamS

syntax:max "(" lamS ")" : lamS
syntax:max ident : lamS
syntax:max num : lamS
syntax:max scientific : lamS
/-- A unit constant, as in `‹metre›`. Guillemets rather than a prefix marker
because `!` is a legal identifier character in Lean, so `u!m` would lex as one
name. -/
syntax:max "‹" term "›" : lamS
/-- A de Bruijn value variable. -/
syntax:max "%" num : lamS
syntax:max "√" num ppSpace lamS:max : lamS
syntax:max "log" ppSpace lamS:max : lamS
syntax:max "exp" ppSpace lamS:max : lamS
/-- Abstraction, annotated with a Lean-level type. -/
syntax:max "fn" "[" term "]" ppSpace lamS : lamS
/-- Component of a vector. -/
syntax:80 lamS:80 "!" num : lamS
/-- A linear map applied to a vector. -/
syntax:80 lamS:80 " ⊙ " lamS:81 : lamS
/-- Ordinary application. -/
syntax:80 lamS:80 " ◃ " lamS:81 : lamS
syntax:70 lamS:70 " * " lamS:71 : lamS
syntax:70 lamS:70 " / " lamS:71 : lamS
syntax:65 lamS:65 " + " lamS:66 : lamS
syntax:65 lamS:65 " - " lamS:66 : lamS

syntax "⟪" lamS "⟫" : term

macro_rules
  | `(⟪ ($e) ⟫)          => `(⟪ $e ⟫)
  | `(⟪ $x:ident ⟫)      => `($x)
  | `(⟪ $n:num ⟫)        => `(Tm.lit $n)
  | `(⟪ $n:scientific ⟫) => `(Tm.lit $n)
  | `(⟪ ‹$u:term› ⟫)     => `(Tm.ucon $u)
  | `(⟪ %$n:num ⟫)       => `(Tm.var $n)
  | `(⟪ √$n:num $e ⟫)    => `(Tm.root $n ⟪ $e ⟫)
  | `(⟪ log $e ⟫)        => `(Tm.log ⟪ $e ⟫)
  | `(⟪ exp $e ⟫)        => `(Tm.exp ⟪ $e ⟫)
  | `(⟪ fn[$t] $e ⟫)     => `(Tm.lam $t ⟪ $e ⟫)
  | `(⟪ $e ! $n:num ⟫)   => `(Tm.idx ⟪ $e ⟫ $n)
  | `(⟪ $f ⊙ $x ⟫)       => `(Tm.mapp ⟪ $f ⟫ ⟪ $x ⟫)
  | `(⟪ $f ◃ $x ⟫)       => `(Tm.app ⟪ $f ⟫ ⟪ $x ⟫)
  | `(⟪ $a * $b ⟫)       => `(Tm.mul ⟪ $a ⟫ ⟪ $b ⟫)
  | `(⟪ $a / $b ⟫)       => `(Tm.div ⟪ $a ⟫ ⟪ $b ⟫)
  | `(⟪ $a + $b ⟫)       => `(Tm.add ⟪ $a ⟫ ⟪ $b ⟫)
  | `(⟪ $a - $b ⟫)       => `(Tm.add ⟪ $a ⟫ (Tm.mul (Tm.lit (-1)) ⟪ $b ⟫))

/-! ## Elaborating a conversion -/

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D]

/-- **Insert a conversion's source annotation by type inference.**

The surface writes `e in v`; the core needs `convert e u v` with `u` the unit of
`e`. This runs the verified checker to find it, so the annotation is derived
rather than trusted, and `convert`'s own typing rule still checks it. -/
def elabConvert {j k : ℕ} (Δ : DCtx D j k) (Γ : Ctx B D j k) (e : Tm B D j k)
    (v : UExp B k) : Option (Σ e' : Tm B D j k, HasTy Δ Γ e' (.Q v)) :=
  match check Δ Γ e with
  | some ⟨.Q u, d⟩ => if h : SameDim Δ u v then some ⟨.convert e u v, .convert d h⟩ else none
  | _ => none

/-- **Elaboration succeeds exactly when the surface syntax is meaningful**: the
subject is a scalar, and its unit shares the target's dimension.

That is the whole specification. There is no companion theorem saying the
elaborated term typechecks, because `elabConvert` returns the derivation: a
surface `in` cannot produce a core term the checker would reject. -/
theorem elabConvert_isSome {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k}
    {e : Tm B D j k} {u v : UExp B k} (hu : infer Δ Γ e = some (.Q u))
    (hd : SameDim Δ u v) : (elabConvert Δ Γ e v).isSome := by
  obtain ⟨⟨_, d⟩, hc, rfl⟩ := Option.map_eq_some_iff.mp hu
  simp [elabConvert, hc, hd]

end LambdaS

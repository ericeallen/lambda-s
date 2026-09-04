/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Examples
import LambdaS.Dynamics
import LambdaS.Notation

/-!
# A real computation: the particle in a box

Λs was argued for; this file runs it. The evaluator from `LambdaS.Dynamics` is
generic in its numeric carrier, so the *same* definition that
`unit_soundness_total` and `erasure_correct` are proved about is instantiated
here at `Float` and
executed by `#eval`, and compiled to C by `lake build`.

## What the type checker is asked to prove

Two things, and both are physics rather than bookkeeping.

**The uncertainty product is a pure number.** `ΔxΔp/ħ` has type `Q 1`. Nothing in
the term says so; it follows from `ħ` being `kg·m²/s`, `Δp` being `kg·m/s` and
`Δx` being `m`, and the checker deriving it. Had any exponent been wrong the term
would not typecheck at all, so the printed value cannot be a dimensionally
meaningless number.

**A wavefunction carries a half-power of length.** In one dimension `ψ` has unit
`m^(-1/2)`, so that `|ψ|²` is a probability *density* at `m⁻¹` and `|ψ|²dx` is
dimensionless. This is the example that forces ℚ exponents: `m^(-1/2)` is not
expressible in F#, in `Data.Dimensional`, or in the Isabelle ISQ development,
all of which fix exponents to ℤ. `root` is primitive here for the reason
`LambdaS.NonDef.sqrt_not_definable` gives, and over ℚ it is total.

## Numbers

CODATA values, written as exact rationals and converted to `Float` once per
literal by `Num.ofRat`. The box is 1 nm wide and holds an electron; the ground
state comes out near 0.376 eV, which is the textbook answer.
-/

namespace LambdaS.QM

open LambdaS.Examples

/-! ## Units of the problem -/

/-- The joule, `kg·m²/s²`. -/
abbrev joule : UExp Base 0 := Term.div (Term.mul kg (Term.mul m m)) (Term.mul sec sec)

/-- Action, `kg·m²/s`, the unit of `ħ`. -/
abbrev action : UExp Base 0 := Term.div (Term.mul kg (Term.mul m m)) sec

/-- Momentum, `kg·m/s`. -/
abbrev momentum : UExp Base 0 := Term.div (Term.mul kg m) sec

/-! ## Terms -/

/-- A dimensioned literal: a magnitude times a unit constant. -/
abbrev qty (v : ℚ) (u : UExp Base 0) : Term₀ := .mul (.lit v) (.ucon u)

/-- A dimensionless literal. -/
abbrev num (v : ℚ) : Term₀ := .lit v

/-- Subtraction, as addition of a negated literal multiple. Λs has no primitive
subtraction; `a − b` is `a + (−1)·b`, and the unit rule for `add` still forces
both sides to agree. -/
abbrev sub (a b : Term₀) : Term₀ := .add a (.mul (num (-1)) b)

/-- Reduced Planck constant, `1.054571817e-34 kg·m²/s`. -/
def hbar : Term₀ := qty (1054571817 / 10 ^ 43) action

/-- Electron mass, `9.1093837015e-31 kg`. -/
def mass : Term₀ := qty (91093837015 / 10 ^ 41) kg

/-- Box width, one nanometer. -/
def width : Term₀ := qty (1 / 10 ^ 9) m

/-- π, to fourteen places. Dimensionless, as every literal in Λs is. -/
def pi : Term₀ := num (314159265358979 / 10 ^ 14)

/-! ## The ground state

`E₁ = π²ħ² / (2mL²)`. -/

def groundEnergy : Term₀ := ⟪ (pi * pi * hbar * hbar) / (2 * mass * width * width) ⟫

/- The checker derives that this is an energy. Nothing in the term says so. -/
#guard typeOf groundEnergy == some (.Q joule)

/- And it is *not* any of the units one might have slipped into by dropping a
factor: these are the errors the rule for `add` and the rule for `div` exist to
catch. -/
#guard typeOf groundEnergy != some (.Q action)
#guard typeOf groundEnergy != some (.Q momentum)

/-! ## Uncertainties

For the ground state of an infinite square well,
`Δp = πħ/L` and `Δx = L·√(1/12 − 1/(2π²))`. -/

def deltaP : Term₀ := ⟪ (pi * hbar) / width ⟫

#guard typeOf deltaP == some (.Q momentum)

def deltaX : Term₀ := ⟪ width * √2 (1 / 12 - 1 / (2 * pi * pi)) ⟫

#guard typeOf deltaX == some (.Q m)

/-- **The physics statement is the type.** `ΔxΔp/ħ` is dimensionless, and the
checker proves it from the units of `ħ`, `Δp` and `Δx` alone. -/
def uncertainty : Term₀ := ⟪ (deltaX * deltaP) / hbar ⟫

#guard typeOf uncertainty == some (.Q 1)

/-! ## The wavefunction, where ℚ exponents are forced

`ψ(x) = √(2/L)·sin(πx/L)`. The amplitude carries `m^(-1/2)`. -/

/-- The normalization amplitude `√(2/L)`, at unit `m^(-1/2)`. -/
def amplitude : Term₀ := ⟪ √2 (2 / width) ⟫

/- Half a negative power of length: inexpressible in any ℤ-exponent system. -/
#guard typeOf amplitude == some (.Q (Term.rpow (Term.div 1 m) (1 / 2)))
#guard (Term.rpow (Term.div (1 : UExp Base 0) m) (1 / 2)).base .metre == (-1 / 2 : ℚ)

/-- `|ψ|²` is a probability **density**, at `m⁻¹`. -/
def density : Term₀ := ⟪ amplitude * amplitude ⟫

#guard typeOf density == some (.Q (Term.div 1 m))

/-- `|ψ|²·dx` is dimensionless, which is what makes the normalization integral
a pure number, and what makes `log` of it well-typed while `log |ψ|²` is not. -/
def probability : Term₀ := ⟪ density * ‹m› ⟫

#guard typeOf probability == some (.Q 1)

/- The base-measure problem, in this concrete instance: the density on its own
cannot be logged, its ratio against another density can. -/
#guard (typeOf (.log density)).isNone
#guard typeOf (.log (.div density density)) == some (.Q 1)

/-! ## Running it

`eval` is the evaluator of `LambdaS.Dynamics` (proved sound in
`LambdaS.Soundness` and total in `LambdaS.Normalization`), instantiated at
`Float`. No conversions occur here, so the conversion-factor argument is the
constant `1`. -/

/-- Evaluate a closed term to a magnitude. -/
def run (e : Term₀) : Option Float :=
  match evalC (D := Dim) (fun _ _ => (1.0 : Float)) 1000 [] e with
  | some (.scalar x) => some x.mag
  | _ => none

/-- Evaluate, keeping the unit the value carries at runtime, which
`unit_soundness_total` guarantees equals the one the checker predicted. -/
def runMeas (e : Term₀) : Option (Val Float Base Dim) :=
  evalC (D := Dim) (fun _ _ => (1.0 : Float)) 1000 [] e

/-- One electronvolt in joules, for reporting. -/
def eV : Float := 1.602176634e-19

/-- The report. -/
def report : String :=
  let fmt : Option Float → String := fun
    | some x => toString x
    | none => "<stuck>"
  "particle in a box: electron, L = 1 nm\n"
    ++ "  E1       = " ++ fmt ((run groundEnergy).map (· / eV)) ++ " eV\n"
    ++ "  dx       = " ++ fmt ((run deltaX).map (· * 1e9)) ++ " nm\n"
    ++ "  dp       = " ++ fmt ((run deltaP).map (· * 1e25)) ++ " e-25 kg m/s\n"
    ++ "  dx dp/hb = " ++ fmt (run uncertainty) ++ "   (>= 0.5)\n"
    ++ "  |psi|^2  = " ++ fmt ((run density).map (· * 1e-9)) ++ " /nm\n"

#eval report

/- The uncertainty principle, checked numerically as well as dimensionally. -/
#guard (run uncertainty).any (fun x => decide (0.5 ≤ x))

/- And the ground-state energy is the textbook 0.376 eV. -/
#guard (run groundEnergy).any (fun x => decide (0.375 * eV ≤ x) && decide (x ≤ 0.377 * eV))

/-! ## A two-state system

The particle in a box is closed-form scalars. This exercises the other half of
the calculus: spaces, linear maps, and the rank-one condition that makes their
units cheap.

The system is a symmetric two-level system (an ammonia molecule, a spin in a
transverse field, a qubit) with Hamiltonian

```
H = [ 0  -A ]        A = 10⁻⁴ eV
    [ -A  0 ]
```

Amplitudes are dimensionless, so the state space is `[1, 1]`; the Hamiltonian
maps it to `[J, J]`, and by `LambdaS.Map`'s rank-one condition its entries carry
`J / 1 = J`. Applying it to a state therefore yields energies, and
`⟨ψ|H|ψ⟩ : Q J`; the physics statement is the type. -/

section TwoState

/-- Dimensionless amplitudes. -/
abbrev St : Sp Base 0 := [1, 1]

/-- Energies. -/
abbrev En : Sp Base 0 := [joule, joule]

/-- The context: a Hamiltonian and a state, supplied as data.

Matrices and state vectors arrive through the environment for the same reason
unit constants do (`LambdaS.Fundamental`): a program that could *name* its data
would not be scale-invariant. A numeric program takes its operators as input. -/
abbrev qmCtx : Ctx Base Dim 0 0 := [.lin St En, .vec St]

/-- `(H|ψ⟩)ᵢ`: an energy. -/
abbrev ket (i : ℕ) : Term₀ := .idx (.mapp (.var 0) (.var 1)) i

/-- `⟨ψ|H|ψ⟩`, summed over the two basis states. Real amplitudes, so no
conjugation is needed; see the note on carriers in `LambdaS.Num`. -/
def expectH : Term₀ :=
  ⟪ %1 ! 0 * (%0 ⊙ %1) ! 0 + %1 ! 1 * (%0 ⊙ %1) ! 1 ⟫

/- **The expectation of the Hamiltonian is an energy**, derived by the checker
from the space of the state and the space of the Hamiltonian's codomain. -/
#guard typeOfIn qmCtx expectH == some (.Q joule)

/- The inner product `⟨ψ|ψ⟩` is dimensionless, since amplitudes are. -/
#guard typeOfIn qmCtx ⟪ %1 ! 0 * %1 ! 0 + %1 ! 1 * %1 ! 1 ⟫ == some (.Q 1)

/- **Applying the Hamiltonian to an energy vector is rejected.** `mapp` demands
the argument live in the map's domain, and `[J, J] ≠ [1, 1]`. -/
#guard (typeOfIn [.lin St En, .vec En] (.mapp (.var 0) (.var 1))).isNone

/-! ### The data -/

/-- The inversion splitting, `10⁻⁴ eV` in joules. -/
def splitJ : Float := 1.602176634e-23

/-- `H = [[0, −A], [−A, 0]]`, a linear map `St ⊸ En`. -/
def hamiltonian : Val Float Base Dim := .matrix [[0.0, -splitJ], [-splitJ, 0.0]] St En

/-- The symmetric eigenstate `(|1⟩ + |2⟩)/√2`, eigenvalue `−A`. -/
def statePlus : Val Float Base Dim :=
  .vector [0.7071067811865476, 0.7071067811865476] St

/-- The antisymmetric eigenstate `(|1⟩ − |2⟩)/√2`, eigenvalue `+A`. -/
def stateMinus : Val Float Base Dim :=
  .vector [0.7071067811865476, -0.7071067811865476] St

/-! ### Literals, and where parametricity draws its line

The introduction forms of `LambdaS.Syntax` let the eigenstate be written down
rather than supplied: its amplitudes are dimensionless literals, so the state
literal is parametric. A Hamiltonian literal is not: its entries are energies,
so each is a multiple of `1_J`, and writing the operator down names the joule,
which is precisely the unit constant the parametric fragment excludes
(`LambdaS.Fundamental`). That is why this file supplies `H` and `ψ` through
the environment above. -/

/-- `1/√2`, to sixteen places. -/
abbrev invSqrt2 : ℚ := 7071067811865476 / 10 ^ 16

/-- The symmetric eigenstate `(|1⟩ + |2⟩)/√2` as a vector literal. -/
def statePlusTm : Term₀ := .vcons (.lit invSqrt2) (.vcons (.lit invSqrt2) .vnil)

#guard typeOf statePlusTm == some (.vec St)

/- The state literal is parametric: it names no unit. -/
example : statePlusTm.Parametric := ⟨trivial, trivial, trivial⟩

/-- `H = [[0, −A], [−A, 0]]` as a matrix literal, entry by entry a multiple of
`1_J`. -/
def hamiltonianTm : Term₀ :=
  .mcons joule
    (.vcons (.mul (.lit 0) (.ucon joule))
      (.vcons (.mul (.lit (-(1602176634 / 10 ^ 32 : ℚ))) (.ucon joule)) .vnil))
    (.mcons joule
      (.vcons (.mul (.lit (-(1602176634 / 10 ^ 32 : ℚ))) (.ucon joule))
        (.vcons (.mul (.lit 0) (.ucon joule)) .vnil))
      (.mnil St))

#guard typeOf hamiltonianTm == some (.lin St En)

/- The Hamiltonian literal is not parametric: the `1_J` in its first row's
second entry already refutes it. -/
example : ¬ hamiltonianTm.Parametric := fun h => h.1.2.1.2

/-- Evaluate a scalar term in an environment. -/
def runIn (ρ : List (Val Float Base Dim)) (e : Term₀) : Option Float :=
  match evalC (D := Dim) (fun _ _ => (1.0 : Float)) 1000 ρ e with
  | some (.scalar x) => some x.mag
  | _ => none

/-- The same with an explicit fuel bound, so exhaustion is observable. -/
def runFuel (n : ℕ) (ρ : List (Val Float Base Dim)) (e : Term₀) : Option Float :=
  match evalC (D := Dim) (fun _ _ => (1.0 : Float)) n ρ e with
  | some (.scalar x) => some x.mag
  | _ => none

/- Numeric results are checked in `Main` rather than by `#guard`. `#guard` runs
in Lean's interpreter, and the `Float` carrier's `matVec` is `@[extern]`, so
reaching it would need a precompiled shared library. The compiled binary is where
the C actually executes, so that is where the checks belong. -/

/-! ### Dimensionless phase

Not evaluated: the point is the *type*. `exp` demands a dimensionless argument,
so a phase `A·t/ħ` typechecks only because the units of an energy, a time and an
action cancel. Get the Hamiltonian's units wrong and the program does not
compile. -/

def splitting : Term₀ := qty (1602176634 / 10 ^ 32) joule
def elapsed : Term₀ := qty (1 / 10 ^ 11) sec

/-- `A·t/ħ`. Dimensionless, and the checker says so. -/
def phase : Term₀ := ⟪ (splitting * elapsed) / hbar ⟫

#guard typeOf phase == some (.Q 1)
#guard typeOf ⟪ exp phase ⟫ == some (.Q 1)

/- Dividing by a mass instead of an action leaves a phase that `exp` refuses:
a units bug in a Hamiltonian is a type error, not a wrong number. -/
#guard (typeOf ⟪ exp ((splitting * elapsed) / mass) ⟫).isNone

/-! ### Higher order: the expectation as a reusable function

`expectH` is written against two specific free variables. Abstracting it is where
`eval` needs closures, and closure bodies are not subterms of the applications
that invoke them, so evaluation carries a fuel bound. Fuel is consumed only at
`app`, so first-order arithmetic evaluates at every bound including zero. -/

/-- `λ(H : St ⊸ En). λ(ψ : vec St). ⟨ψ|H|ψ⟩` -/
def expectation : Term₀ :=
  ⟪ fn[.lin St En] fn[.vec St]
      (%0 ! 0 * (%1 ⊙ %0) ! 0 + %0 ! 1 * (%1 ⊙ %0) ! 1) ⟫

#guard typeOfIn qmCtx expectation
    == some (.arrow (.lin St En) (.arrow (.vec St) (.Q joule)))

/-- Applied to the operator and state supplied in the environment. -/
def applied : Term₀ := ⟪ expectation ◃ %0 ◃ %1 ⟫

#guard typeOfIn qmCtx applied == some (.Q joule)

/- Applying it to the state before the operator is a type error, caught before
any number exists. -/
#guard (typeOfIn qmCtx ⟪ expectation ◃ %1 ◃ %0 ⟫).isNone

/-- Every numeric claim about the two-state system, checked in one place so the
compiled binary can report whether they all hold. -/
def twoStateChecks : Bool :=
  let near (x : Float) (y : Float) : Bool := decide (Float.abs (x - y) < 1e-28)
  (runIn [hamiltonian, statePlus] expectH).any (fun x => near x (-splitJ))
    && (runIn [hamiltonian, stateMinus] expectH).any (fun x => near x splitJ)
    && (runIn [hamiltonian, statePlus] applied).any (fun x => near x (-splitJ))
    && (runIn [hamiltonian, stateMinus] applied).any (fun x => near x splitJ)
    -- fuel is spent only on *nested* application: a `lam` under an `app` is free,
    -- so two applications need one unit, zero gets stuck, first-order needs none
    && (runFuel 1 [hamiltonian, statePlus] applied).isSome
    && (runFuel 0 [hamiltonian, statePlus] applied).isNone
    && (runFuel 0 [hamiltonian, statePlus] expectH).isSome

/-! ### Validation in the compiled binary

The box results are `#guard`ed at build time in Lean's interpreter; the
binary re-runs them on the compiled evaluator, so the C code path is
validated against the same numbers. The literal check is new coverage: the
expectation applied to the Hamiltonian and state *written as terms*, so the
evaluator's `vcons`/`mcons` cases and the extern `dgemv` are all on the
path of one closed program. -/

/-- The particle-in-a-box claims, re-checked by the compiled evaluator. -/
def boxChecks : Bool :=
  (run groundEnergy).any (fun x => decide (0.375 * eV ≤ x) && decide (x ≤ 0.377 * eV))
    && (run uncertainty).any (fun x => decide (0.5 ≤ x))
    && (run density).any (fun x => decide (1.999e9 ≤ x) && decide (x ≤ 2.001e9))

/-- `⟨ψ|H|ψ⟩` as one closed term: curried expectation, literal operator,
literal state. -/
def expectFromLiterals : Term₀ := ⟪ expectation ◃ hamiltonianTm ◃ statePlusTm ⟫

#guard typeOf expectFromLiterals == some (.Q joule)

/-- The literal program computes the symmetric eigenvalue `−A` through
`dgemv`. -/
def literalChecks : Bool :=
  (runIn [] expectFromLiterals).any (fun x => decide (Float.abs (x - (-splitJ)) < 1e-28))

/-- Every run-time numeric check the binary performs; `main` exits nonzero
unless this holds. -/
def allChecks : Bool := boxChecks && twoStateChecks && literalChecks

/-- The validation summary the binary prints. -/
def checksReport : String :=
  let verdict : Bool → String := fun b => if b then "pass" else "FAIL"
  "compiled-evaluator validation\n"
    ++ "  particle in a box         = " ++ verdict boxChecks ++ "\n"
    ++ "  two-state system          = " ++ verdict twoStateChecks ++ "\n"
    ++ "  literals through dgemv    = " ++ verdict literalChecks ++ "\n"

/-! ### The native kernel on the evaluation path

`Num.matVec` is what `eval` reaches when it applies a linear map, and the `Float`
carrier overrides it with a single `dgemv`, which is `@[extern]`. So in the
compiled binary this runs in C, on a flat array of doubles, with no unit
information present, because the checker has already discharged all of it. -/

def twoStateReport : String :=
  let fmt : Option Float → String := fun
    | some x => toString x
    | none => "<stuck>"
  "two-state system: A = 1e-4 eV\n"
    ++ "  backend                 = " ++ blasBackend () ++ "\n"
    ++ "  <H> symmetric  eigenstate = "
       ++ fmt ((runIn [hamiltonian, statePlus] expectH).map (· / eV)) ++ " eV\n"
    ++ "  <H> antisymmetric         = "
       ++ fmt ((runIn [hamiltonian, stateMinus] expectH).map (· / eV)) ++ " eV\n"
    ++ "  via the curried function  = "
       ++ fmt ((runIn [hamiltonian, statePlus] applied).map (· / eV)) ++ " eV\n"
    ++ "  all numeric checks pass   = " ++ toString twoStateChecks ++ "\n"

end TwoState

end LambdaS.QM

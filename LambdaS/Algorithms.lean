import LambdaS.Examples
import LambdaS.Notation
import LambdaS.Dynamics

/-!
# Numeric algorithms, as a sanity check on the calculus

Λs is pure and total: no recursion, no conditionals, no mutable state. The
question this file answers is whether that leaves enough to write recognizable
numerical methods, or only formulas.

The answer is that **straight-line numerical methods transcribe directly**, and
their types are their specifications. A central difference has type
`(Q v → Q u) → Q v → Q v → Q (u/v)`: differentiate a position with respect to a
time and you get a velocity, by derivation rather than by comment. What is
missing is iteration: one Runge–Kutta step is expressible, a solver loop is not.

## What the checker is doing that a syntactic system could not

Unit equality here is decided by *arithmetic on exponent vectors*, not by
normalizing syntax. In the Runge–Kutta step below, the intermediate
`(h/2)·k₁` has unit `t · (y/t)`, and `add` demands it equal `y`. As exponent
vectors those are `t + (y − t)` and `y`, and the checker settles it by adding
rationals. There is no normalization pass, so there is nothing to get wrong.
-/

namespace LambdaS.Algorithms

open LambdaS.Examples

/-! ## Scopes

Two nested dimension binders and two nested unit binders. Inside the body the
innermost unit variable is de Bruijn `0` and the outer one is `1`; likewise for
dimensions. -/

/- The value's unit, `u`. -/
abbrev uU : UExp Base 2 := Term.ofVar 1
/- The argument's unit, `v`. -/
abbrev vU : UExp Base 2 := Term.ofVar 0
/- The bound on `u`, at the scope where its binder sits. -/
abbrev dU : DExp Dim 1 := Term.ofVar 0
/- The bound on `v`. -/
abbrev dV : DExp Dim 2 := Term.ofVar 0

/- Wrap a body in `Λδu. Λu:δu. Λδv. Λv:δv.` -/
abbrev poly (body : Tm Base Dim 2 2) : Term₀ :=
  .dlam (.ulam dU (.dlam (.ulam dV body)))

/- Instantiate both quantifiers. -/
abbrev at₂ (du : DExp Dim 0) (u : UExp Base 0) (dv : DExp Dim 0) (v : UExp Base 0)
    (e : Term₀) : Term₀ := .uapp (.dapp (.uapp (.dapp e du) u) dv) v

abbrev dLen : DExp Dim 0 := Term.ofBase Dim.length
abbrev dTime : DExp Dim 0 := Term.ofBase Dim.time

/-! ## Central difference

`f'(x) ≈ (f(x+h) − f(x−h)) / 2h`. Inside the three value binders, `%0` is `h`,
`%1` is `x`, `%2` is `f`. -/

def deriv : Term₀ :=
  poly ⟪ fn[.arrow (.Q vU) (.Q uU)] fn[.Q vU] fn[.Q vU]
           ((%2 ◃ (%1 + %0)) - (%2 ◃ (%1 - %0))) / (2 * %0) ⟫

/- **The type is the specification.** Differentiating a length with respect to
a time yields a velocity, and the checker derives that rather than being told. -/
#guard typeOf (at₂ dLen m dTime sec deriv)
    == some (.arrow (.arrow (.Q sec) (.Q m)) (.arrow (.Q sec) (.arrow (.Q sec) (.Q (Term.div m sec)))))

/- Instantiating at the wrong dimension is rejected: `metre` is not a time. -/
#guard (typeOf (at₂ dTime m dTime sec deriv)).isNone

/-! ## Simpson's rule

`∫ₐᵇ f ≈ ((b−a)/6)·(f(a) + 4·f((a+b)/2) + f(b))`. `%0` is `b`, `%1` is `a`,
`%2` is `f`. -/

def simpson : Term₀ :=
  poly ⟪ fn[.arrow (.Q vU) (.Q uU)] fn[.Q vU] fn[.Q vU]
           ((%0 - %1) / 6)
             * ((%2 ◃ %1) + 4 * (%2 ◃ ((%1 + %0) / 2)) + (%2 ◃ %0)) ⟫

/- Integrating a length over a time yields a length-times-time. -/
#guard typeOf (at₂ dLen m dTime sec simpson)
    == some (.arrow (.arrow (.Q sec) (.Q m)) (.arrow (.Q sec) (.arrow (.Q sec) (.Q (Term.mul m sec)))))

/-! ## One Runge–Kutta step

`y' = y + (h/6)(k₁ + 2k₂ + 2k₃ + k₄)` for `dy/dt = f(t,y)`. Binders, innermost
first: `%0` is `y`, `%1` is `t`, `%2` is `h`, `%3` is `f`.

This is where unit equality does real work. `k₁ : Q (y/t)`, so `(h/2)·k₁` has
unit `t·(y/t)`, and adding it to `y` requires the checker to see those as the
same exponent vector. -/

/- `Λδy. Λy:δy. Λδt. Λt:δt.`: note the value unit is bound first here, so
inside the body `uU` is the *state* unit and `vU` the *time* unit. -/
def rk4 : Term₀ :=
  poly ⟪ fn[.arrow (.Q vU) (.arrow (.Q uU) (.Q (Term.div uU vU)))]
         fn[.Q vU] fn[.Q vU] fn[.Q uU]
           %0 + (%2 / 6)
             * ( (%3 ◃ %1 ◃ %0)
               + 2 * (%3 ◃ (%1 + %2 / 2) ◃ (%0 + (%2 / 2) * (%3 ◃ %1 ◃ %0)))
               + 2 * (%3 ◃ (%1 + %2 / 2) ◃ (%0 + (%2 / 2) * (%3 ◃ (%1 + %2 / 2) ◃ (%0 + (%2 / 2) * (%3 ◃ %1 ◃ %0)))))
               + (%3 ◃ (%1 + %2) ◃ (%0 + %2 * (%3 ◃ (%1 + %2 / 2) ◃ (%0 + (%2 / 2) * (%3 ◃ (%1 + %2 / 2) ◃ (%0 + (%2 / 2) * (%3 ◃ %1 ◃ %0)))))))) ⟫

/- A step of an ODE on a velocity, driven by an acceleration, over a time,
returns a velocity. -/
#guard typeOf (at₂ (Term.div dLen dTime) (Term.div m sec) dTime sec rk4)
    == some (.arrow (.arrow (.Q sec) (.arrow (.Q (Term.div m sec)) (.Q (Term.div (Term.div m sec) sec))))
              (.arrow (.Q sec) (.arrow (.Q sec) (.arrow (.Q (Term.div m sec)) (.Q (Term.div m sec))))))

/-! ## Tolerances, where dimensioned types catch the common bug

An absolute tolerance has the unit of the quantity; a relative one is
dimensionless. Writing `|x − y| < 1e-6` with a bare literal is a type error, and
the fix the checker forces is the correct one. -/

abbrev tolCtx : Ctx Base Dim 0 0 := [.Q m, .Q m]

/- `x − y` carries the unit, so any tolerance compared against it must too. -/
#guard typeOfIn tolCtx ⟪ %0 - %1 ⟫ == some (.Q m)

/- `(x − y)/x` is dimensionless, so a bare numeric tolerance is correct here,
and only here. -/
#guard typeOfIn tolCtx ⟪ (%0 - %1) / %0 ⟫ == some (.Q 1)

/- Adding a dimensionless tolerance to a dimensioned difference is rejected. -/
#guard (typeOfIn tolCtx ⟪ (%0 - %1) + 1 ⟫).isNone

/-! ## Running them

Free fall: `s(t) = ½·g·t²` with `g = 9.81 m/s²`. A central difference is exact on
a quadratic and Simpson's rule is exact on a cubic, so both answers are exact and
the guards can be tight. -/

abbrev accel : UExp Base 0 := Term.div m (Term.mul sec sec)

/- `g = 9.81 m/s²`. -/
def gravity : Term₀ := .mul (.lit (981 / 100)) (.ucon accel)

/- `λ(t : Q s). ½·g·t²` -/
def freeFall : Term₀ := ⟪ fn[.Q sec] (1 / 2) * (gravity * %0 * %0) ⟫

#guard typeOf freeFall == some (.arrow (.Q sec) (.Q m))

abbrev derivMS : Term₀ := at₂ dLen m dTime sec deriv
abbrev simpsonMS : Term₀ := at₂ dLen m dTime sec simpson

def twoSec : Term₀ := .mul (.lit 2) (.ucon sec)
def zeroSec : Term₀ := .mul (.lit 0) (.ucon sec)
def milliSec : Term₀ := .mul (.lit (1 / 1000)) (.ucon sec)

/- `deriv[m][s] freeFall 2s 0.001s`: the speed after two seconds. -/
def speedAt2 : Term₀ := ⟪ derivMS ◃ freeFall ◃ twoSec ◃ milliSec ⟫

#guard typeOf speedAt2 == some (.Q (Term.div m sec))

/- `simpson[m][s] freeFall 0s 2s`: the integral of position over time. -/
def absementTo2 : Term₀ := ⟪ simpsonMS ◃ freeFall ◃ zeroSec ◃ twoSec ⟫

#guard typeOf absementTo2 == some (.Q (Term.mul m sec))

def run (e : Term₀) : Option Float :=
  match evalC (D := Dim) (fun _ _ => (1.0 : Float)) 10000 [] e with
  | some (.scalar x) => some x.mag
  | _ => none

def report : String :=
  let fmt : Option Float → String := fun
    | some x => toString x
    | none => "<stuck>"
  "numeric algorithms, free fall s(t) = g t^2 / 2\n"
    ++ "  central difference s'(2s) = " ++ fmt (run speedAt2) ++ " m/s   (exact: 19.62)\n"
    ++ "  Simpson int_0^2 s dt      = " ++ fmt (run absementTo2) ++ " m s   (exact: 13.08)\n"

#eval report

/-! ## Declared conversions, compiled

The conversion oracle below is not `fun _ _ => 1.0`: it is computed from the
declared magnitudes (metre `1`, foot `0.3048`, yard `0.9144`), the `Float`
shadow of the valuation `ψyd` that `LambdaS.Examples` proves satisfies the
declaration set. `evalC_convert_declared` is the theorem that the instrumented
evaluator multiplies by exactly the declared factor; this is that theorem's
number coming out of the compiled binary.

Two routes from yards to metres (direct, and through feet) print the same
number, which is `convChain_eq` and `yard_forced` made observable: the factors
are forced by the declarations, so there is no route to get wrong. -/

/-- The declared magnitude of each base unit, in metres (and SI mates). -/
def magB : Base → Float
  | .metre => 1
  | .foot => 0.3048
  | .yard => 0.9144
  | .kilogram => 1
  | .second => 1

/-- The magnitude of a compound unit: the product of its bases' declared
magnitudes, at their exponents. -/
def magF (w : UExp Base 0) : Float :=
  [Base.metre, .foot, .yard, .kilogram, .second].foldl
    (fun acc b => acc * Float.pow (magB b) (Num.ofRat (w.base b))) 1

/-- The conversion oracle the declarations determine: a ratio of magnitudes,
which is `conv` at the `Float` shadow of `ψyd`. -/
def cfDecl (u v : UExp Base 0) : Float := magF u / magF v

def hundredYards : Term₀ := .mul (.lit 100) (.ucon yd)

def inFeet : Term₀ := .convert hundredYards yd ft
def inMetres : Term₀ := .convert hundredYards yd m
def viaFeet : Term₀ := .convert (.convert hundredYards yd ft) ft m

#guard typeOf inFeet == some (.Q ft)
#guard typeOf inMetres == some (.Q m)
#guard typeOf viaFeet == some (.Q m)

def runDecl (e : Term₀) : Option Float :=
  match evalC (D := Dim) cfDecl 10000 [] e with
  | some (.scalar x) => some x.mag
  | _ => none

def reportDecl : String :=
  let fmt : Option Float → String := fun
    | some x => toString x
    | none => "<stuck>"
  "declared conversions: yard = 3 foot, foot = 0.3048 metre\n"
    ++ "  100 yd in ft          = " ++ fmt (runDecl inFeet) ++ " ft   (declared: 300)\n"
    ++ "  100 yd in m, direct   = " ++ fmt (runDecl inMetres) ++ " m    (declared: 91.44)\n"
    ++ "  100 yd in m, via ft   = " ++ fmt (runDecl viaFeet) ++ " m    (same: paths agree)\n"

#eval reportDecl

/- The yard-demo numbers, checked at build time. All three comparisons are
exact `Float` equalities and hold bit for bit: 100 yd converts to feet as
exactly `300.0`, the direct conversion to meters equals the literal `91.44`,
and the route through feet produces the same `Float` as the direct route. -/
#guard runDecl inFeet == some 300.0
#guard runDecl inMetres == some 91.44
#guard runDecl inMetres == runDecl viaFeet

/- Both methods are exact on this integrand, so the checks are tight. -/
#guard (run speedAt2).any (fun x => decide (Float.abs (x - 19.62) < 1e-9))
#guard (run absementTo2).any (fun x => decide (Float.abs (x - 13.08) < 1e-9))

end LambdaS.Algorithms

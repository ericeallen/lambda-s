/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.DeclareSolver

/-!
# Executable declaration checks at the semantic boundaries

These examples run `DeclSolver.check`, `DeclSolver.solve`, and
`DeclSolver.conversionExact` on small unit systems chosen to separate
consistency from global completeness and to exercise exact irrational output.
Each namespace sets up its own `UnitSys`:

* `Length`: feet and meters with no declaration are consistent but rejected as
  incomplete, and `foot = 0.3048 meter` (`link`) makes the system pass, as in
  Section 3 of our paper; a redundant reciprocal is accepted and a conflicting
  factor is rejected.
* `Root`: the dimensionless equation `u = 2/u` forces the factor `√2`, returned
  as radicand `2` and degree `2`.
* `Unsound`: a solvable declaration that equates independent dimensions is
  rejected.
* `Empty` and `DependentDimensions`: an empty unit system, and dimension rows
  that coincide.
* `RadicalChain`: a radical factor derived through a compound right-hand side;
  in an incomplete system, a determined factor is still extracted and an
  undetermined one is refused.
* `Nanometer`: the paper's wavefunction-amplitude example (`exactAmplitude`).

Each check is a `#guard`, and `allChecks` and `report` run the same
computations in the native executable, which exits nonzero on failure.
`Length.linkedFactor_returned` and `Root.rootFactor_returned` prove what the
solver returns; `Length.linkedFactor_correct` and `Root.rootFactor_correct`
prove the returned factor equal to the conversion factor in every satisfying
real valuation, independently of the solver's chosen free magnitudes.
-/
namespace LambdaS.DeclarationSolverExamples

open DeclSolver

namespace Length
local instance : UnitSys (Fin 2) (Fin 1) where
  dim _ := Term.ofBase 0

def foot : UExp (Fin 2) 0 := Term.ofBase 0
def meter : UExp (Fin 2) 0 := Term.ofBase 1
/-- `unit foot = 0.3048 meter`. -/
def link : Decl (Fin 2) := ⟨0, 381 / 1250, by norm_num, meter⟩
/-- `unit meter = (1250/381) foot`: redundant with `link`, and consistent. -/
def reciprocal : Decl (Fin 2) := ⟨1, 1250 / 381, by norm_num, foot⟩
/-- `unit foot = (1/3) meter`: conflicts with `link`. -/
def conflict : Decl (Fin 2) := ⟨0, 1 / 3, by norm_num, meter⟩
def noDeclarations : Fin 0 → Decl (Fin 2) := Fin.elim0

def disconnectedConsistent : Bool := (solve (Equiv.refl _) noDeclarations).isSome

def disconnectedRejected : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 1)) noDeclarations).isNone

def disconnectedFactorRejected : Bool :=
  (conversionExact (Equiv.refl _) noDeclarations foot meter).isNone

def linkedAccepted : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 1)) ![link]).isSome

def reciprocalAccepted : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 1)) ![link, reciprocal, link]).isSome

def conflictRejected : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 1)) ![link, conflict]).isNone

def exactLink : Bool :=
  (conversionExact (Equiv.refl _) ![link] foot meter).map
    (fun q => (q.radicand, q.degree)) == some (381 / 1250, 1)

def linkedFactor : ExactFactor := exactFactor ![link] ![1]

/-- `conversionExact` from foot to meter returns `linkedFactor`, the exact factor
built from the coefficient witness `![1]`. -/
theorem linkedFactor_returned :
    conversionExact (Equiv.refl _) ![link] foot meter = some linkedFactor := by
  have h : factorCoefficients (Equiv.refl (Fin 2)) ![link]
      (Term.div foot meter) = some ![1] := by
    have hr : List.finRange 1 = [0] := by decide
    simp [hr, factorCoefficients, RationalSolver.solve, RationalSolver.matrixRows,
      RationalSolver.solveRows, RationalSolver.Row.pivot, RationalSolver.reduceRows,
      RationalSolver.Row.reduce, RationalSolver.Row.backsub, Decl.ratio,
      link, foot, meter, Term.div, Term.ofBase]
    funext i
    fin_cases i
    norm_num [Function.update]
  simp only [conversionExact, h, Option.map_some, linkedFactor]

/-- The returned factor equals the foot-to-meter conversion factor in every
valuation satisfying `link`. -/
theorem linkedFactor_correct (V : Scaling (Fin 2) 0) (hV : Decl.Satisfies V link) :
    linkedFactor.value = conv V foot meter := by
  apply conversionExact_correct (Equiv.refl _) ![link] foot meter linkedFactor_returned V
  intro i
  fin_cases i
  exact hV
end Length

namespace Root
local instance : UnitSys (Fin 1) (Fin 0) where
  dim _ := Term.one

def unit : UExp (Fin 1) 0 := Term.ofBase 0
/-- A dimensionless generator satisfying u = 2/u has magnitude sqrt(2). -/
def selfDecl : Decl (Fin 1) := ⟨0, 2, by norm_num, Term.rpow unit (-1)⟩
def accepted : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 0)) ![selfDecl]).isSome

def exactRoot : Bool :=
  (conversionExact (Equiv.refl _) ![selfDecl] unit Term.one).map
    (fun q => (q.radicand, q.degree)) == some (2, 2)

def rootFactor : ExactFactor := exactFactor ![selfDecl] ![1 / 2]

/-- `conversionExact` from `unit` to the dimensionless unit returns `rootFactor`,
the exact factor built from the coefficient witness `![1/2]`. -/
theorem rootFactor_returned :
    conversionExact (Equiv.refl _) ![selfDecl] unit Term.one = some rootFactor := by
  have h : factorCoefficients (Equiv.refl (Fin 1)) ![selfDecl]
      (Term.div unit Term.one) = some ![1 / 2] := by
    have hr : List.finRange 1 = [0] := by decide
    simp [hr, factorCoefficients, RationalSolver.solve, RationalSolver.matrixRows,
      RationalSolver.solveRows, RationalSolver.Row.pivot, RationalSolver.reduceRows,
      RationalSolver.Row.reduce, RationalSolver.Row.backsub, Decl.ratio,
      selfDecl, unit, Term.div, Term.ofBase, Term.rpow, Term.one]
    funext i
    fin_cases i
    norm_num [Function.update]
  simp only [conversionExact, h, Option.map_some, rootFactor]

/-- The returned factor equals the conversion factor from `unit` to `1` in every
valuation satisfying `selfDecl`. -/
theorem rootFactor_correct (V : Scaling (Fin 1) 0) (hV : Decl.Satisfies V selfDecl) :
    rootFactor.value = conv V unit Term.one := by
  apply conversionExact_correct (Equiv.refl _) ![selfDecl] unit Term.one rootFactor_returned V
  intro i
  fin_cases i
  exact hV
end Root

namespace Unsound
local instance : UnitSys (Fin 2) (Fin 2) where
  dim b := Term.ofBase b
/-- The equations have a solution, but equating independent dimensions is illegal. -/
def rejected : Bool :=
  (solve (Equiv.refl _) ![Length.link]).isSome &&
  (check (Equiv.refl _) (Equiv.refl (Fin 2)) ![Length.link]).isNone
end Unsound

namespace Empty
local instance : UnitSys (Fin 0) (Fin 0) where
  dim := Fin.elim0

def accepted : Bool :=
  (check (Equiv.refl (Fin 0)) (Equiv.refl (Fin 0))
    (fun i : Fin 0 => i.elim0 : Fin 0 → Decl (Fin 0))).isSome
end Empty

namespace DependentDimensions
local instance : UnitSys (Fin 2) (Fin 2) where
  dim _ := Term.mul (Term.ofBase 0) (Term.ofBase 1)
/-- Both dimension rows coincide; a declaration still fixes the only unit ratio. -/
def accepted : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 2)) ![Length.link]).isSome
end DependentDimensions

namespace RadicalChain
/-! Three length units linked through a compound rational-power right-hand side,
so that the radical a conversion needs is derived rather than declared. -/
local instance : UnitSys (Fin 3) (Fin 1) where
  dim _ := Term.ofBase 0

def a : UExp (Fin 3) 0 := Term.ofBase 0
def b : UExp (Fin 3) 0 := Term.ofBase 1
def c : UExp (Fin 3) 0 := Term.ofBase 2
/-- The geometric mean of b and c. -/
def meanBC : UExp (Fin 3) 0 := Term.rpow (Term.mul b c) (1 / 2)
/-- a = 2 · (b·c)^(1/2). -/
def viaMean : Decl (Fin 3) := ⟨0, 2, by norm_num, meanBC⟩
/-- b = 2 · c. -/
def bToC : Decl (Fin 3) := ⟨1, 2, by norm_num, c⟩
/-- a = 3 · c, which contradicts the other two: they force a/c = 2^(3/2). -/
def conflict : Decl (Fin 3) := ⟨0, 3, by norm_num, c⟩

/-- Both declared ratios together span the kernel of `dim`. -/
def chainAccepted : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 1)) ![viaMean, bToC]).isSome

/-- log(a/c) = (3/2) log 2, cleared to log 8 / 2. -/
def exactAC : Bool :=
  (conversionExact (Equiv.refl _) ![viaMean, bToC] a c).map
    (fun q => (q.radicand, q.degree)) == some (8, 2)

/-- log(a/b) = (1/2) log 2. -/
def exactAB : Bool :=
  (conversionExact (Equiv.refl _) ![viaMean, bToC] a b).map
    (fun q => (q.radicand, q.degree)) == some (2, 2)

/-- The contradiction is decided exactly: 2 log 3 − log 8 = log (9/8) ≠ 0. -/
def conflictRejected : Bool :=
  (solve (Equiv.refl _) ![viaMean, bToC, conflict]).isNone

/-- With `viaMean` alone, `b/c` is undetermined, so the global check rejects the system. -/
def incompleteRejected : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 1)) ![viaMean]).isNone

/-- With `viaMean` alone, the factor from `a` to `meanBC`, which that declaration
fixes, is still extracted exactly: radicand `2`, degree `1`. -/
def determinedInIncomplete : Bool :=
  (conversionExact (Equiv.refl _) ![viaMean] a meanBC).map
    (fun q => (q.radicand, q.degree)) == some (2, 1)

/-- With `viaMean` alone, the undetermined factor from `a` to `c` is refused rather
than assigned the solver's free choice. -/
def undeterminedInIncomplete : Bool :=
  (conversionExact (Equiv.refl _) ![viaMean] a c).isNone

def allChecks : Bool :=
  chainAccepted && exactAC && exactAB && conflictRejected && incompleteRejected &&
  determinedInIncomplete && undeterminedInIncomplete
end RadicalChain

namespace Nanometer
/-! A one-dimensional wavefunction amplitude carries a half-power of inverse
length. A rational declared factor between nanometer and meter then yields a
radical factor between the amplitude units. Section 3 of our paper cites
`exactAmplitude`. -/
local instance : UnitSys (Fin 2) (Fin 1) where
  dim _ := Term.ofBase 0

def nm : UExp (Fin 2) 0 := Term.ofBase 0
def meter : UExp (Fin 2) 0 := Term.ofBase 1
/-- nm = 10^(-9) m. -/
def nmDecl : Decl (Fin 2) := ⟨0, 1 / 10 ^ 9, by norm_num, meter⟩

def accepted : Bool :=
  (check (Equiv.refl _) (Equiv.refl (Fin 1)) ![nmDecl]).isSome

/-- nm^(-1/2) to m^(-1/2) multiplies by 10^(9/2): radicand 10^9, degree 2. -/
def exactAmplitude : Bool :=
  (conversionExact (Equiv.refl _) ![nmDecl]
      (Term.rpow nm (-1 / 2)) (Term.rpow meter (-1 / 2))).map
    (fun q => (q.radicand, q.degree)) == some (10 ^ 9, 2)
end Nanometer

/-- All declaration regressions, also evaluated by the native artifact executable. -/
def allChecks : Bool :=
  Length.disconnectedConsistent && Length.disconnectedRejected &&
  Length.disconnectedFactorRejected && Length.linkedAccepted && Length.reciprocalAccepted &&
  Length.conflictRejected && Length.exactLink && Root.accepted && Root.exactRoot &&
  Unsound.rejected && Empty.accepted && DependentDimensions.accepted &&
  RadicalChain.allChecks && Nanometer.accepted && Nanometer.exactAmplitude

/-- A compact runtime reading identifying the declaration checks. -/
def report : String :=
  s!"declaration solver: disconnected={Length.disconnectedRejected}, linked={Length.linkedAccepted}, reciprocal={Length.reciprocalAccepted}, conflict={Length.conflictRejected}, unsound={Unsound.rejected}, exact rational={Length.exactLink}, exact sqrt2={Root.exactRoot}, empty={Empty.accepted}, dependent dimensions={DependentDimensions.accepted}, radical chain={RadicalChain.allChecks}, nm amplitude={Nanometer.exactAmplitude}; all={allChecks}"

#guard Length.disconnectedConsistent
#guard Length.disconnectedRejected
#guard Length.disconnectedFactorRejected
#guard Length.linkedAccepted
#guard Length.reciprocalAccepted
#guard Length.conflictRejected
#guard Length.exactLink
#guard Root.accepted
#guard Root.exactRoot
#guard Unsound.rejected
#guard Empty.accepted
#guard DependentDimensions.accepted
#guard RadicalChain.chainAccepted
#guard RadicalChain.exactAC
#guard RadicalChain.exactAB
#guard RadicalChain.conflictRejected
#guard RadicalChain.incompleteRejected
#guard RadicalChain.determinedInIncomplete
#guard RadicalChain.undeterminedInIncomplete
#guard Nanometer.accepted
#guard Nanometer.exactAmplitude
#guard allChecks

end LambdaS.DeclarationSolverExamples

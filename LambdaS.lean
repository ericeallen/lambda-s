/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Num
import LambdaS.Uom
import LambdaS.Space
import LambdaS.Map
import LambdaS.Unify
import LambdaS.Density
import LambdaS.Syntax
import LambdaS.Typing
import LambdaS.Notation
import LambdaS.Pi
import LambdaS.Scaling
import LambdaS.Dynamics
import LambdaS.Soundness
import LambdaS.Normalization
import LambdaS.Adequacy
import LambdaS.Erasure
import LambdaS.Parametricity
import LambdaS.Fundamental
import LambdaS.PiTheorem
import LambdaS.PiCoherent
import LambdaS.NonDefinability
import LambdaS.Ratio
import LambdaS.Definability
import LambdaS.Twist
import LambdaS.Conversion
import LambdaS.Declare
import LambdaS.DeclareSolver
import LambdaS.DeclarationSolverExamples
import LambdaS.Examples
import LambdaS.PiExamples
import LambdaS.QM
import LambdaS.Algorithms

/-!
# Λs: a calculus for units of measure with conversion

This is the root module; importing it imports the whole development. The
module list above follows the paper's order: syntax and typing, the checker,
the denotational semantics with both abstraction theorems, the ratio
calculus, the evaluator with its erasure, unit declarations, and the worked
examples. `THEOREMS.md` in the repository maps every identifier the paper
cites to its module.

## From the paper's long form: Mechanization notes

The paper's tag `long-form` carries this section in full; it is reproduced
here, converted to Markdown, so the documentation develops what the paper
now summarizes. Section references name the module that carries the
section; theorem references name the declaration.

The measured size of the Lean 4 [de Moura and Ullrich 2021] development is
recorded in the README by `scripts/count_lines.py`. It builds with no `sorry` (Lean's placeholder for an unproved
obligation) and no axioms beyond the three of Lean's
standard library (propositional extensionality, choice, and quotient
soundness; the check by Lean's kernel is
part of the build, and no result adds an
axiom). The compiled evaluator calls BLAS where the platform supplies it,
falling back to portable C loops elsewhere. The
examples of “Unit Declarations” (`Declare.lean`) through “Dimensioned Linear Algebra” (`Map.lean`) run as
build-time assertions; the two numerical demonstrations whose
arithmetic reaches the foreign-function interface are checked by the
compiled binary when it runs. In this section we report what made the
mechanization small, one thing it caught, and what a reader must trust
beyond the kernel.

**Exponent vectors make the metatheory linear algebra.**
The decision of “Units and Dimensions” (`Typing.lean`) propagates through every file.
Substitution of units is a linear map; simultaneous substitution, weakening,
and their composition laws are equalities of finite sums, proved by
reordering summation rather than by structural induction. The one genuinely
dimensional lemma in the soundness proof says that grounding, the
substitution of
ground units for a term's unit variables, commutes with taking dimensions.
It is a Fubini argument: an interchange of the order of a finite double sum. In his Coq development, Kennedy [2008] reports the
substitution lemma for his logical relation as “awkward (needs equality
coercions)”; the corresponding lemmas here are changes in the order of
summation, and the value-typing relation, being indexed by *syntax* (a
ground type) rather than by a metalanguage type, never needs such coercions. Where Foster and Wolff [2023] implement dimension normalization in ML
because their host type system cannot reduce
L·T⁻¹·T,
our equality is *definitional*: no datatype of unit expressions exists
anywhere in the mechanization (“Units and Dimensions” (`Typing.lean`)), so a unit
expression is its own normal form.

**Derivations as data collapse the trusted base.**
Making the typing judgment Type-valued and the checker
derivation-returning (“Statics” (`Typing.lean`)) follows the
intrinsically-typed tradition [Altenkirch and Reus 1999; Poulsen et al. 2018]; the technique is
standard, and what we report is what it bought in this development. It
deleted an entire class of theorems: checker soundness, elaboration
soundness (`elabConvert`, which elaborates the
e in v form, returns the core term *with* its
derivation), and every “reconstruct the derivation”
lemma. Derivation uniqueness came free from
the theorem “Completeness” (`check_eq`, `Typing.lean`), and with it the right to define semantics
by recursion on derivations while stating side conditions on terms.

**An environment-passing normalizer avoids Kripke structure.**
The ratio normalizer of “Accumulated Ratios, and a Decidable Diagnostic” (`Twist.lean`) must interpret a binder
whose body lives at a larger unit scope. The standard treatment indexes the
model by scopes and quantifies over extensions, a Kripke structure with
unit scopes as the worlds; instead the normalizer holds
the scope fixed and reads the program's unit variables through an
environment, so binders extend the environment and nothing is ever weakened.
The two lemmas this rests on are the pullback laws of the scaling algebra,
which read a scaling through a substitution: the pulled-back scaling scales
a unit exactly as the original scales its substituted image. One law is
immediate from the definitions; the other is again an interchange of the
order of summation.

**What the composition laws caught.**
One defect in the development was found neither by examples, nor by the
worked physics computations, nor by inspection. It was found during the
metatheory the type-soundness proof rests on, when the composition law for
substitutions failed to hold. Our substitution on types, under a nested
quantifier, substituted for the *bound* variable instead of the outer
one: de Bruijn's classic capture error, in the one function the scope
indexing could not protect, because both variables inhabit the same scope.
Every test passed; weakening had the matching defect, and the two canceled
in the round-trip lemma we had proved! The failure of the composition law
pointed at the exact clause. We record this as evidence for a practice:
prove the full set of algebraic laws of a binding structure, because a
subset can hold by cancellation of matching defects, as our round-trip
lemma did. The repaired functions are derived from a single parallel
substitution with proved composition and identity laws, and the incident is
preserved in the artifact as a regression test.

**Numbers, twice.**
The semantic carrier is a type class with two instances. At ℝ it
is noncomputable, and it is the object of the theorems. At `Float`
it is compiled, calling BLAS through Lean's FFI where the platform supplies
it, on unboxed arrays; “Dimensioned Linear Algebra” (`Map.lean`)'s rank-one structure is why
the arrays can be unboxed. The class carries almost no laws, deliberately:
`Float`
satisfies neither associativity nor the field axioms, so any law strong
enough to be useful would exclude the instance that runs. The
carrier-generic theorems (type soundness, strong normalization, erasure)
therefore hold of the compiled evaluator and constrain its units, array extents,
and control flow; the theorems that pin down *which number* comes out
(adequacy, the theorem “Declared factors reach the compiled evaluator” (`one_yard_in_meters`, `Erasure.lean`), drift independence)
are stated at the ℝ instance. The binary's printed numbers are
checked by assertion instead. The yard report's 300 and 91.44 are
checked at build
time, in exact arithmetic where the declarations live and in `Float`
where the binary computes; the FFI-reaching reports are checked by the
binary itself when it runs.

**The carrier boundary.**
The abstraction and adequacy theorems use real arithmetic, not a proof
that floating-point evaluation equals it. Rounding affects defined operations.
For negative bases and non-integer exponents, `Float.pow` returns NaN,
whereas `Real.rpow` uses the real part of the principal complex power,
|x|^qcos(qπ). The carriers also choose different totalizations for division
by zero and logarithms. The covariance identity in `Fundamental.lean`
concerns the real operation; it is not a theorem about the compiled number.
The binary checks selected boundary cases, including these differing
power conventions, at startup.
We claim no IEEE
conformance, and a claim would say little: the
standard [IEEE 2019] requires correct rounding of the field
operations but only recommends it for `pow`, log, and exp,
so conformance pins down nothing about the accuracy of exactly the
operations at issue.

**The trusted base, enumerated.**
A reader who believes a theorem of the paper trusts the Lean kernel and
the three standard axioms. A reader who believes the number the compiled
binary prints trusts, in addition: Lean's code generator and runtime;
`Float` arithmetic, whose operations are opaque primitives with no
formal semantics; and three C stubs behind the FFI (a dot product, a
matrix-vector product, and a probe that reports which backend is linked).
The stubs are proved about their Lean fallback bodies and
assumed to agree with the C; floating-point reordering makes that
assumption approximate rather than exact. Everything upstream of the final
number (the checker, the consistency criterion, the semantics, both
abstraction theorems, the drift analysis) is kernel-checked and involves
none of this.
-/

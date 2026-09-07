/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Syntax

/-!
# Typing for Λs, and a checker proved correct against it

Two things live here, and the point is that only one of them can be wrong:

* `HasTy`, the **declarative** typing relation: what it *means* for a term to
  have a type;
* `check`, an **executable** decision procedure that returns the derivation.

Because `check` returns a derivation rather than a type, soundness is not a
theorem. There is nothing for it to say: a checker that cannot produce a type
without producing its justification cannot accept an ill-typed term. That
deletes the usual half of the correctness statement, and with it the usual place
for a refinement gap to hide.

What remains is `check_eq`, and it is stated more sharply than completeness
normally is: the checker finds not merely *a* derivation of a well-typed term
but *the* one it was given. Since `check Δ Γ e` is a single value, uniqueness of
derivations follows at once, and `HasTy` is a `Subsingleton`.

`HasTy` is `Type`-valued rather than `Prop`-valued, so that a derivation may be
eliminated into `Type`, which is what a denotation of terms requires. By the
`Subsingleton` instance nothing is lost by this: the data a derivation carries
is determined by the judgment it proves.

## Where the units bite

Five rules do the work, and each corresponds to something argued for in the
design:

* `add` requires the two units to be **equal**. This is where dimensional errors
  are caught.
* `pow` is **primitive**, with no side condition. It is not definable from the
  field operations, because the closure of the arguments under arithmetic is
  the subgroup they generate and rational powers escape it. Over ℚ exponents it
  is *total*, so `√` of a volume is well-typed here and is a type error in F#,
  and `pow 0 e : Q 1` is fine, denoting `x^0 = 1`. The rule mirrors the unit
  grammar, which has had `u^q` all along.
* `idx` reads the unit **out of the space**. `V[i]? = some u` is Λs in one
  hypothesis: the unit of a component is determined by its index.
* `uapp` **substitutes** a unit expression for a unit variable, and checks that
  the expression has the **declared dimension**. Because unit expressions are
  exponent vectors, substitution is a linear map and equality needs no
  normalization pass.
* `convert` requires the two units to have the same dimension. Decidable, so the
  trusted core checks it rather than delegating to an elaborator.
* `mcons` requires each row of a matrix literal to carry exactly `w / δ_V(i)`:
  the rank-one law of `LambdaS.Map`, checked at the introduction rather than
  merely preserved by the eliminations. The annotations on `mnil` (its column
  space) and `mcons` (its output unit) are what keep the rules syntax-directed:
  a zero-row matrix determines no width, and a row over the empty space
  determines no output unit.

## Two contexts

Typing carries a dimension context `Δ` alongside the usual `Γ`. `Δ` records the
declared dimension of each unit variable in scope, which is what `dimOf` needs
to give a total answer under a binder, and hence what makes `convert` usable in
polymorphic code. `∀u. τ` is `∀δ. ∀u:δ. τ`, so an "unbounded" unit variable is
bounded by a dimension *variable*: `dimOf` reports it, and it matches nothing
concrete, which is exactly the rejection an unbounded quantifier should give.

## Why completeness is available

The calculus is explicitly typed (lambdas are annotated, `Λu.e` and `e[μ]` are
written rather than inferred), so typing is syntax-directed and types are
*unique*. `infer` therefore returns **the** type or nothing, with no
most-general-type caveat, and `infer_complete` holds. Inferring the `Λu` and
`[μ]` instead would require let-generalization and hence the abelian-group
unification in `LambdaS.Unify`, where the guarantee weakens from uniqueness to
principality.
-/

/-!
## From the paper's long form: The Calculus

The paper's tag `long-form` carries this section in full; it is reproduced
here, converted to Markdown, so the documentation develops what the paper
now summarizes. Section references name the module that carries the
section; theorem references name the declaration.

In this section, we present the syntax and statics of Λs. The design is
governed by a single decision from which nearly everything else follows: units
and dimensions are not syntax trees but *exponent vectors*, and every
operation on them is linear algebra.

### Units and Dimensions

Fix a finite set B of *base units* (say, meter,
foot, kilogram, second) and a finite set D
of *base dimensions* (say, Length, Mass,
Time). The pair is a parameter of the calculus, as the class table
is a parameter of Featherweight Java [Igarashi et al. 2001]: introducing a new
base unit is module structure, not computation. “Unit Declarations” (`Declare.lean`)
gives the declaration forms: the primary-unit declarations that supply
this parameter, and the factor declarations that contribute constraints
with semantic content. A *unit
expression* over k unit variables is a pair of finitely supported maps
(i.e., nonzero at only finitely many arguments)

    u  =  ( u_base : B → ℚ,  u_var : {0,…,k-1} → ℚ ),

read as the formal product
∏_b b^(u_base(b)) · ∏_i u_i^(u_var(i)).
The unit variables u_i exist for polymorphism: each is bound by a
unit abstraction Λu:d (“Types and Terms” in this module), and a
term polymorphic in a unit reads its unit arguments through them.
Multiplication of units is pointwise addition of vectors, division is
subtraction, and the q-th power is scalar multiplication by
q ∈ ℚ. Dimension expressions are the same structure over D and
j dimension variables. For example, writing a vector by its nonzero entries,
and writing u and v for the unit variables at indices
0 and 1 under two binders:

    m = (m ↦ 1)  m/s = (m ↦ 1, s ↦ -1)
     u · v = (u ↦ 1, v ↦ 1)  kg·m/s² = (kg ↦ 1, m ↦ 1, s ↦ -2)
     u^(3/2) = (u ↦ 3/2)

Note that u · v has every base entry zero: a product
of two abstract units mentions no base unit. Dimension expressions
look the same over D: Length is the vector
(Length ↦ 1), and the dimension of a velocity is
Length/Time = (Length ↦ 1, Time ↦ -1). Two decisions here
bear emphasis.

First, *exponents are rational*, not integral. In Kennedy's
calculus [Kennedy 1997] the units form the free abelian group on the
base units, with integer exponents; here they form the free
ℚ-vector space on the same generators (see note 1).
The difference propagates everywhere downstream: the group is *divisible*,
every unit having an `n`-th root for nonzero `n` (`Uom.rpow_nth_root`),
so √(·) of a dimensioned quantity is well-typed
(√(m²) = m) where systems with integer
exponents must reject it; and consistency of unit declarations is
consistency of a linear system over a *field*, solved by Gaussian
elimination rather than Smith normal form, the integer-matrix analogue of
diagonalization (“Unit Declarations” (`Declare.lean`)).
Neither follows from torsion-freeness, which the free abelian group of
[Kennedy 1997] has too (see note 1). Quantities with genuinely fractional dimension,
such as the half-densities of geometric quantization (see note 2),
come for free.

> **Note 1.** Precisely: the
> units over B with k variables in scope form the free ℚ-vector
> space on B ⊔ {0,…,k-1}, written multiplicatively. It is
> torsion-free (written multiplicatively: uⁿ = 1 forces u = 1 for
> nonzero n), which `LambdaS.Map` uses to put the Cholesky factor in the
> dimensionless space, but so is a free abelian group over ℤ, so this is
> not a difference the rational exponents make. Nor is it what makes
> “ratio equal to one” mean “units equal”: that is cancellation, and holds
> in any group (`Definability.div_eq_one_iff`).

> **Note 2.** A probability
> density on a line measured in Length carries dimension
> Length⁻¹, so that its integral over an interval is
> dimensionless; the half-densities of geometric quantization carry
> Length^(-1/2), so that the product of two of them is a density.

Second, *units and dimensions are related by a homomorphism, not a
convention*. A *unit system* assigns each base unit a dimension,
dim : B → ℚ^D (an exponent vector over the base dimensions
for each base unit), and the map extends linearly to all unit expressions.
Note that dim is total: it is supplied for every base unit as part of
the calculus's parameters, alongside B and D, and the declarations of
“Unit Declarations” (`Declare.lean`) add
magnitudes, never dimensions. We say two units are *interchangeable*
when they
have the same dimension; we write dim_Δ(u) for the dimension of u
under a context Δ assigning dimensions to unit variables, and
u ∼_Δ v for dim_Δ(u) = dim_Δ(v). Nothing
restricts a dimension to one unit: meter, foot, and
yard are three units of Length, which is precisely the
situation conversion exists to serve, and precisely the situation that
systems tracking only dimensions, or one unit system at a
time [Foster and Wolff 2023], cannot express. The two-level design
follows the object-oriented lineage [Allen et al. 2004].

Note that the vectors are not a restriction of the unit syntax but its
entirety: because the group is *free* on the base units and the unit
variables in scope, every algebraic combination (u · v
for two bound
variables, m/s, u^(3/2) · kg)
denotes a
vector, and the operations of the unit grammar in Figure 1 of the paper (the `UExp`, `DExp`, `Ty`, and `Tm` inductives of `Syntax.lean`) are
total functions on vectors (pointwise addition, subtraction, scaling). A type
such as Q u · v under
Λu:d₁. Λv:d₂ is as well-formed as
Q m; the artifact checks
Λu:Length. Λv:Time.  λ x:Q u·v. x at the type written.
The spellings u · v and
v · u differ as expressions, but the
grammar's operations are evaluated when the expression is formed, so the two
spellings denote one vector, exactly as 2+2 and 4 denote one number.
There is nothing to normalize. Nothing remains to compare
except finitely many rationals: where a syntactic treatment must prove that
m · s · m⁻¹ normalizes to
s, here the two are the same vector, and equality of units is
decided by comparing their entries.

### Types and Terms

*(Figure omitted here; see Figure 1 of the paper (the `UExp`, `DExp`, `Ty`, and `Tm` inductives of `Syntax.lean`). Its caption: Syntax of Λs. Types and terms are indexed by the number of
enclosing dimension binders j and unit binders k; unit and dimension
variables are de Bruijn indices into those
scopes [de Bruijn 1972]. Function application
e e and linear-map application e ⊙ e are distinct term forms, as in
the artifact. Unit and dimension expressions satisfy the laws of a
ℚ-vector space written multiplicatively, by construction: each is
represented as its exponent vector.)*

The types and terms of Λs appear in Figure 1 of the paper (the `UExp`, `DExp`, `Ty`, and `Tm` inductives of `Syntax.lean`). When
describing Λs we use the following metavariables:

- Unit expressions: u, v, w; dimension expressions: d; spaces
  (lists of unit expressions): u⃗, w⃗.

- Types: τ, σ; terms: e; rational literals: q; naturals: n, i.

- Contexts: Γ (types of term variables), Δ (dimensions of
  unit variables); derivations: 𝒟.

- Valuations: V; rescalings: ψ.

A quantity
type Q u classifies scalars carrying unit u; Vec u⃗
classifies vectors whose i-th component carries unit u_i (the units vary
per component, following Hart [1995]); and
Lin u⃗ w⃗ classifies linear maps from
Vec u⃗ to Vec w⃗, which denote matrices.
We call a per-component unit assignment such as u⃗ a *space*;
Vec and Lin carry their spaces as type indices.
Both come with introduction and elimination forms. A vector is built by
consing scalars onto the empty vector, each cons extending the space by the
new component's unit. For example, the artifact's state space pairs a
position in m with a momentum in
kg·m/s, and the literal
1.3·1_m :: 21·1_(kg·m/s) :: ⟨⟩ has type
Vec [m, kg·m/s]
(`stateVec`). A matrix is built by rows. The rowless matrix
⟨⟩_(u⃗) carries its domain space, so a matrix with no
rows still has a well-defined width, and e ::_w e' adds a row
whose output unit is w (an annotation, because a row over the empty domain space determines no
output unit; eliding it at nonempty domains would split the rule and
still need it in the empty case, so the uniform annotation is the
parsimonious choice); rule T-MCons of Figure 2 of the paper (the constructors of `HasTy`)
demands the row inhabit Vec (w/u⃗), entry j at w/u_j.
That premise is Hart's factorization (“Dimensioned Linear Algebra” (`Map.lean`)) checked at
the introduction form: a matrix whose entries do not factor as row unit over
column unit cannot be written down. The eliminations are indexing e.i,
map application e ⊙ e, and composition e ∘ e: given
x : Vec [m, kg·m/s],
indexing gives x.0 : Q m and
x.1 : Q kg·m/s, and x.2 is a type
error.
Well-scopedness is a type index: types and terms carry the number of
enclosing dimension and unit binders, so ill-scoped unit and dimension syntax
is unrepresentable and unit and dimension substitution has nowhere to go
wrong; value variables are plain de Bruijn naturals, checked against Γ
by the typing relation. (“Mechanization notes” (`LambdaS.lean`)
reports the defect we found anyway, in the one place indexing could not
reach.)

The two quantifiers deserve comment, because their interaction is the
calculus's answer to a question every polymorphic unit system faces: what
does an *unbounded* unit variable mean? In Λs there is no such
thing. Unit abstraction is always bounded by a dimension,
∀u:d. τ, and unbounded quantification is recovered as
∀δ. ∀u:δ. τ: a unit variable bounded by a
dimension *variable*. The bound is what makes
conversion usable in polymorphic code. Under
Λu:Length, the body may
convert  u meter, because the checker can see that
u and meter share a dimension. Under
∀δ. ∀u:δ, no concrete unit matches
δ,
so conversion out of u can target only expressions of dimension
δ: the variable itself, other variables bounded by the same
δ, and their products with dimensionless units. In particular the
generic caster

    Λδ. Λu:δ. Λv:δ.  λ x:Q u. convert x u v

is well-typed (`caster`), and it is a term the two
abstraction theorems of “The Price of Conversion” (`Fundamental.lean`) separate: a coherent
rescaling assigns u and v the one factor its
dimension rescaling gives δ, leaving the caster invariant, while
independent factors move it. Converting to a *concrete* unit is still
rejected, as an unbounded variable demands, and because coherence
forces every variable bounded by δ to rescale together, the free
theorems of “The Price of Conversion” (`Fundamental.lean`) keep their full strength
there. Instantiation
is written e [u] for the unit quantifier and e {d} for the dimension
quantifier: the bracket and the brace mark which quantifier is being
eliminated, and the two are distinct term constructors.

The arithmetic rules carry the unit discipline. Multiplication and division
are total: any two quantities may be multiplied or divided, and the result
carries the product or quotient of their units (T-Mul,
T-Div in Figure 2 of the paper (the constructors of `HasTy`)). Addition demands its operands at
*equal* units, not merely interchangeable ones: adding meters to feet is
a type error, and convert is how the programmer says it was
intended (the value of requiring exact unit matching was first
made clear to the author by Guy L. Steele Jr., who pointed out that it
helps a programmer manage the imprecisions and finite bounds of
floating-point computation). Powers at constant rational exponents are primitive:
(·)^q : Q u → Q u^q, with no side condition, and we write
√[n]e for e^(1/n). Not every power is
definable from the field operations (no term built from +, ·,
and / computes a square root: “Dimensional Analysis” (`PiTheorem.lean`) proves
Q u² → Q u
uninhabited by arithmetic terms), and the rule
accepts every unit, since scaling an exponent vector by q always yields
a unit. For example, √(m³) is a quantity at
m^(3/2) (see note 3). Finally log and
exp demand dimensionless arguments (T-Log, T-Exp), which
is the type-theoretic face of the base-measure problem: a dimensioned
quantity has no scale-invariant logarithm, so log of a probability density
is rejected while log of a ratio of densities is accepted.

> **Note 3.** What is a quantity of dimension
> Length^(1/2)? We do not know either, but the type system has no
> reason to prejudge the question: quantum mechanics already uses
> Length^(-1/2),
> and rejecting √(m²) to forbid the unfamiliar
> √m would get the priority backwards.

Measurements are compound, not primitive: a literal is dimensionless
(q : Q 1) and a unit constant is one of its unit
(1_u : Q u), so the velocity every tutorial opens with is their
product. For example, 5 · 1_(m/s) : Q m/s: rule T-Mul gives it unit
1 · m/s, which *is* the vector
m/s. Why is the constant 1_u rather than u
alone, written directly as a term? Two reasons, one for the checker and one
for the theory. First, units live in types, and the typing rules compare
them by vector equality; if unit expressions were also terms, type indices
would mention terms, and deciding Q u = Q v would require evaluating
terms. The stratification is what keeps the statics a first-order decidable
theory. Second, and more important for the paper, 1_u names a
semantic decision that a bare u would hide: the term denotes the
*number one*, the unit measured in itself, in every unit system, and a
denotation that never rescales is exactly what parametricity must exclude.
Confining that decision to one constructor gives the theory a single site to
tax: the parametric fragment of “The Price of Conversion” (`Fundamental.lean`) bans exactly
this constructor, the drift analysis of “Accumulated Ratios, and a Decidable Diagnostic” (`Twist.lean`) declines
it as the one construct outside the theory itself, and everything else in
the term grammar rescales.

Larger formulas assemble the same way. The world-record 100-meter sprint is the quotient

    (100 · 1_m)  /  (9.58 · 1_s)  :  Q m/s,

where the numerator has type Q m, the denominator has type
Q s, T-Div assigns the quotient the vector with 1 at
m and -1 at s, and the magnitude is
100/9.58 ≈ 10.44. The artifact checks this idiom as `velocity`
in `Examples.lean`: a literal-times-constant quotient assigned
Q m/s. A surface syntax would write 5 m/s
and elaborate to exactly this.

Conversion itself is a checked primitive, rule T-Cvt of
Figure 2 of the paper (the constructors of `HasTy`). The term carries its source unit u as well as its
target v: the compiled evaluator (“Dynamics” (`Normalization.lean`)) must recover
the conversion factor from the term and its environment alone, and the target
does not determine the source. We envision a surface syntax in which the
programmer writes e in v and never writes u; the core
carries it, and the one inference this asks for is already discharged in
the artifact. Its elaborator (`elabConvert`) runs the checker of
“Statics” in this module on e, reads u off the derived type Q u,
and returns the annotated core term together with its typing derivation,
so an in cannot produce a term the checker would reject.
Elaboration succeeds exactly when e is a scalar whose unit shares the
target's dimension (`elabConvert_isSome`), and the inferred u
is unique because the checker computes at most one type
(the theorem “Completeness” (`check_eq`)).
T-Cvt is the only rule in Λs that can observe a unit, and
“The Price of Conversion” (`Fundamental.lean`) states what that observation costs.

### Statics

*(Figure omitted here; see Figure 2 of the paper (the constructors of `HasTy`). Its caption: Typing: the full rule set, transcribed from the artifact's
`HasTy`. Γ^(↑) and Δ^(↑) weaken a context
past a new binder: each index in the context is shifted so that it refers to
the same variable in the extended scope. In T-Idx, the premise
u⃗_i = u abbreviates a successful bounds-checked lookup, as in the
artifact. In T-Con, u ranges over all unit expressions,
variables included. (u, u⃗) prepends a component to a space, and in
T-MCons, w/u⃗ is the pointwise quotient, entry j at
w/u_j.)*

The typing judgment Δ;Γ ⊢ e : τ carries a dimension
context Δ (the declared dimension of each unit variable in scope)
alongside the usual Γ; the rules appear in Figure 2 of the paper (the constructors of `HasTy`),
they are syntax-directed, and types are unique. We highlight what the
artifact makes of this, because the
arrangement is unusual and we recommend it. The checker does not return a
type; it returns a *derivation*:

    def check : {j k : ℕ} → (Δ : DCtx D j k) → (Γ : Ctx B D j k) → (e : Tm B D j k) →
        Option (Σ τ : Ty B D j k, HasTy Δ Γ e τ)

The result is a dependent pair: a type τ together with a derivation
that e has type τ under Δ and Γ. The checker returns
evidence, not a boolean. With derivations as data, the usual checker soundness
theorem (anything the checker accepts is well-typed) is not a theorem. There
is nothing for it to say: a checker that cannot produce a type without
producing the derivation that justifies it cannot accept an ill-typed
term. (Type soundness, that a well-typed term evaluates to a value of its
type, is a theorem about the dynamics, with real content, and
“Dynamics” (`Normalization.lean`) proves it.)
What remains is the only direction with content, and
the theorem “Completeness” (`check_eq`) states it in a form stronger than completeness
usually takes:

**Theorem (Completeness; `check_eq`).** For every derivation 𝒟 of Δ;Γ ⊢ e : τ,
check Δ Γ e = some (τ, 𝒟).

Note that nothing is handed to the checker: the theorem quantifies over an
arbitrary derivation 𝒟 of the judgment and asserts that
check returns exactly the pair (τ, 𝒟). Since
check Δ Γ e is a single value, an immediate corollary
is that any two derivations of the same judgment are equal: typing
derivations are unique. Uniqueness is not
a curiosity. It is what licenses speaking of *the* denotation of a term
in “The Price of Conversion” (`Fundamental.lean`), where the semantics is defined by recursion
on derivations, and it is what lets the syntactic side conditions of the
abstraction theorems be predicates on terms rather than on derivations.
Decidability of typing falls out: the checker is a decision procedure, proved
sound by its type and complete by the theorem “Completeness” (`check_eq`).
-/

namespace LambdaS

variable {B D : Type} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]
variable [UnitSys B D]

/-- The declarative typing relation, over a dimension context `Δ` and a value
context `Γ`. -/
inductive HasTy : {j k : ℕ} → DCtx D j k → Ctx B D j k → Tm B D j k → Ty B D j k → Type where
  | var {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {n τ} :
      Γ[n]? = some τ → HasTy Δ Γ (.var n) τ
  | lam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {τ e σ} :
      HasTy Δ (τ :: Γ) e σ → HasTy Δ Γ (.lam τ e) (.arrow τ σ)
  | app {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f a τ σ} :
      HasTy Δ Γ f (.arrow τ σ) → HasTy Δ Γ a τ → HasTy Δ Γ (.app f a) σ
  | lit {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {q} : HasTy Δ Γ (.lit q) (.Q 1)
  | ucon {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {u} : HasTy Δ Γ (.ucon u) (.Q u)
  | mul {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {a b u v} :
      HasTy Δ Γ a (.Q u) → HasTy Δ Γ b (.Q v) → HasTy Δ Γ (.mul a b) (.Q (Term.mul u v))
  | div {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {a b u v} :
      HasTy Δ Γ a (.Q u) → HasTy Δ Γ b (.Q v) → HasTy Δ Γ (.div a b) (.Q (Term.div u v))
  /-- Addition demands equal units. The rule that catches the errors.

  Equal, not merely same-dimension: adding meters to feet is a type error, and
  `convert` is how you say you meant it. -/
  | add {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {a b u} :
      HasTy Δ Γ a (.Q u) → HasTy Δ Γ b (.Q u) → HasTy Δ Γ (.add a b) (.Q u)
  /-- Constant rational powers are primitive and total: the exponent acts on
  the unit exactly as the unit grammar's `u^q` does. -/
  | pow {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {q : ℚ} {e u} :
      HasTy Δ Γ e (.Q u) → HasTy Δ Γ (.pow q e) (.Q (Term.rpow u q))
  /-- The unit of a component is read out of the space. -/
  | idx {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e V i u} :
      HasTy Δ Γ e (.vec V) → V[i]? = some u → HasTy Δ Γ (.idx e i) (.Q u)
  /-- **Row extraction**, the elimination form for `Lin`. Row `i` of a map at
  `Lin V W` is a vector over `w / δ_V(·)` for `w = δ_W(i)`: precisely the row
  `mcons` consumes, so intro and elim meet definitionally. Without this rule
  `Lin` has introduction forms and no elimination form, and no closed term can
  read an entry out of a matrix it did not itself build. -/
  | mrow {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e V W i w} :
      HasTy Δ Γ e (.lin V W) → W[i]? = some w →
      HasTy Δ Γ (.mrow e i) (.vec (V.map fun u => Term.div w u))
  | mapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f x V W} :
      HasTy Δ Γ f (.lin V W) → HasTy Δ Γ x (.vec V) → HasTy Δ Γ (.mapp f x) (.vec W)
  | comp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f g U V W} :
      HasTy Δ Γ f (.lin V W) → HasTy Δ Γ g (.lin U V) → HasTy Δ Γ (.comp f g) (.lin U W)
  /-- The empty vector lives at the empty space. -/
  | vnil {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} : HasTy Δ Γ .vnil (.vec [])
  /-- Consing a scalar onto a vector extends the space by the scalar's unit:
  the introduction rule dual to `idx`. -/
  | vcons {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e v u V} :
      HasTy Δ Γ e (.Q u) → HasTy Δ Γ v (.vec V) →
      HasTy Δ Γ (.vcons e v) (.vec (u :: V))
  /-- The zero-row matrix at the annotated column space. The annotation is what
  gives a rowless matrix a well-defined width. -/
  | mnil {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {V} : HasTy Δ Γ (.mnil V) (.lin V [])
  /-- Consing a row onto a matrix. The row is a vector whose component `i`
  carries `w / δ_V(i)`, which is Hart's rank-one condition enforced at the
  introduction rather than merely preserved by the eliminations. -/
  | mcons {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {w r M V W} :
      HasTy Δ Γ r (.vec (V.map fun u => Term.div w u)) → HasTy Δ Γ M (.lin V W) →
      HasTy Δ Γ (.mcons w r M) (.lin V (w :: W))
  /-- `log` demands a dimensionless argument. This is the rule that makes the
  base-measure problem static: a probability density over a space with measure
  `μ` carries `μ⁻¹`, so `log p` is rejected, while `log (p/q)` for two densities
  of equal weight is fine because the ratio lands at `1`. -/
  | log {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e} :
      HasTy Δ Γ e (.Q 1) → HasTy Δ Γ (.log e) (.Q 1)
  | exp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e} :
      HasTy Δ Γ e (.Q 1) → HasTy Δ Γ (.exp e) (.Q 1)
  /-- Unit abstraction, `Λu:d. e`. Both contexts move: `Δ` records the bound
  variable's declared dimension, and `Γ` is weakened so the variable is
  genuinely fresh: nothing already in scope can mention it. -/
  | ulam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {d e τ} :
      HasTy (Δ.cons d) Γ.weaken e τ → HasTy Δ Γ (.ulam d e) (.all d τ)
  /-- Unit application. The instantiating expression must have the **declared
  dimension**: the check that makes bounded quantification mean something. -/
  | uapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f d τ σ} :
      HasTy Δ Γ f (.all d τ) → dimOf Δ σ = d → HasTy Δ Γ (.uapp f σ) (τ.subst σ)
  /-- Dimension abstraction, `Λδ. e`. -/
  | dlam {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e τ} :
      HasTy Δ.weakenDim Γ.weakenDim e τ → HasTy Δ Γ (.dlam e) (.allDim τ)
  /-- Dimension application, `e{d}`. Unconstrained: any dimension may be
  supplied, which is what makes `∀δ. ∀u:δ. τ` genuinely unbounded. -/
  | dapp {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {f τ} {d : DExp D j} :
      HasTy Δ Γ f (.allDim τ) → HasTy Δ Γ (.dapp f d) (τ.substDim d)
  /-- **Conversion.** Only between units of the same dimension, and `Δ` is what
  lets that be decided under a binder. -/
  | convert {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e u v} :
      HasTy Δ Γ e (.Q u) → SameDim Δ u v → HasTy Δ Γ (.convert e u v) (.Q v)

/-- **T-MCons enforces the model's entry units.** The row `T-MCons` accepts at
codomain unit `w` carries, at component `i`, the unit `w / δ_V(i)`, which is
entry `(0, i)` of the resulting matrix at `Lin V (w :: W)` (`linEntry`) and,
through `entry_toSpace`, the model's `entry`: reading a component out of the
row lands at exactly the unit Hart's form assigns it. -/
def HasTy.mcons_entry {j k} {Δ : DCtx D j k} {Γ : Ctx B D j k} {w r : _} {V : Sp B k}
    (W : Sp B k) (dr : HasTy Δ Γ r (.vec (V.map fun u => Term.div w u))) (i : Fin V.length) :
    HasTy Δ Γ (.idx r i) (.Q (linEntry V (w :: W) ⟨0, Nat.succ_pos _⟩ i)) :=
  .idx dr (by simp [linEntry])

section Check

/-- The checker. Syntax-directed, total, executable, and it returns the
**derivation**, not merely the type.

That is the whole of soundness. A separate "anything the checker accepts is
well-typed" theorem would have to reconstruct a derivation the checker had
already built and thrown away; here there is nothing to reconstruct and nothing
to prove. What remains (`check_eq`) is the only direction with content: that
the checker never rejects a term the rules accept, and indeed finds the very
derivation it was given. -/
def check : {j k : ℕ} → (Δ : DCtx D j k) → (Γ : Ctx B D j k) → (e : Tm B D j k) →
    Option (Σ τ : Ty B D j k, HasTy Δ Γ e τ)
  | _, _, _, Γ, .var n =>
      match h : Γ[n]? with
      | some τ => some ⟨τ, .var h⟩
      | none => none
  | _, _, Δ, Γ, .lam τ e => (check Δ (τ :: Γ) e).map fun ⟨_, d⟩ => ⟨_, .lam d⟩
  | _, _, Δ, Γ, .app f a =>
      match check Δ Γ f, check Δ Γ a with
      | some ⟨.arrow τ _, df⟩, some ⟨τ', da⟩ =>
          if h : τ' = τ then some ⟨_, .app df (h ▸ da)⟩ else none
      | _, _ => none
  | _, _, _, _, .lit _ => some ⟨_, .lit⟩
  | _, _, _, _, .ucon _ => some ⟨_, .ucon⟩
  | _, _, Δ, Γ, .mul a b =>
      match check Δ Γ a, check Δ Γ b with
      | some ⟨.Q _, da⟩, some ⟨.Q _, db⟩ => some ⟨_, .mul da db⟩
      | _, _ => none
  | _, _, Δ, Γ, .div a b =>
      match check Δ Γ a, check Δ Γ b with
      | some ⟨.Q _, da⟩, some ⟨.Q _, db⟩ => some ⟨_, .div da db⟩
      | _, _ => none
  | _, _, Δ, Γ, .add a b =>
      match check Δ Γ a, check Δ Γ b with
      | some ⟨.Q u, da⟩, some ⟨.Q v, db⟩ =>
          if h : u = v then some ⟨_, .add (h ▸ da) db⟩ else none
      | _, _ => none
  | _, _, Δ, Γ, .pow _ e =>
      match check Δ Γ e with
      | some ⟨.Q _, d⟩ => some ⟨_, .pow d⟩
      | _ => none
  | _, _, Δ, Γ, .idx e i =>
      match check Δ Γ e with
      | some ⟨.vec V, d⟩ =>
          match hv : V[i]? with
          | some _ => some ⟨_, .idx d hv⟩
          | none => none
      | _ => none
  | _, _, Δ, Γ, .mrow e i =>
      match check Δ Γ e with
      | some ⟨.lin _ W, d⟩ =>
          match hw : W[i]? with
          | some _ => some ⟨_, .mrow d hw⟩
          | none => none
      | _ => none
  | _, _, Δ, Γ, .mapp f x =>
      match check Δ Γ f, check Δ Γ x with
      | some ⟨.lin V _, df⟩, some ⟨.vec V', dx⟩ =>
          if h : V' = V then some ⟨_, .mapp df (h ▸ dx)⟩ else none
      | _, _ => none
  | _, _, Δ, Γ, .comp f g =>
      match check Δ Γ f, check Δ Γ g with
      | some ⟨.lin V _, df⟩, some ⟨.lin _ V', dg⟩ =>
          if h : V' = V then some ⟨_, .comp df (h ▸ dg)⟩ else none
      | _, _ => none
  | _, _, _, _, .vnil => some ⟨_, .vnil⟩
  | _, _, Δ, Γ, .vcons e v =>
      match check Δ Γ e, check Δ Γ v with
      | some ⟨.Q _, de⟩, some ⟨.vec _, dv⟩ => some ⟨_, .vcons de dv⟩
      | _, _ => none
  | _, _, _, _, .mnil _ => some ⟨_, .mnil⟩
  | _, _, Δ, Γ, .mcons w r M =>
      match check Δ Γ r, check Δ Γ M with
      | some ⟨.vec Vr, dr⟩, some ⟨.lin V _, dM⟩ =>
          if h : Vr = V.map (fun u => Term.div w u) then some ⟨_, .mcons (h ▸ dr) dM⟩
          else none
      | _, _ => none
  | _, _, Δ, Γ, .log e =>
      match check Δ Γ e with
      | some ⟨.Q u, d⟩ => if h : u = 1 then some ⟨_, .log (h ▸ d)⟩ else none
      | _ => none
  | _, _, Δ, Γ, .exp e =>
      match check Δ Γ e with
      | some ⟨.Q u, d⟩ => if h : u = 1 then some ⟨_, .exp (h ▸ d)⟩ else none
      | _ => none
  | _, _, Δ, Γ, .ulam _ e => (check (Δ.cons _) Γ.weaken e).map fun ⟨_, d⟩ => ⟨_, .ulam d⟩
  | _, _, Δ, Γ, .uapp f σ =>
      match check Δ Γ f with
      | some ⟨.all d _, df⟩ =>
          if h : dimOf Δ σ = d then some ⟨_, .uapp df h⟩ else none
      | _ => none
  | _, _, Δ, Γ, .dlam e => (check Δ.weakenDim Γ.weakenDim e).map fun ⟨_, d⟩ => ⟨_, .dlam d⟩
  | _, _, Δ, Γ, .dapp f _ =>
      match check Δ Γ f with
      | some ⟨.allDim _, df⟩ => some ⟨_, .dapp df⟩
      | _ => none
  | _, _, Δ, Γ, .convert e u v =>
      match check Δ Γ e with
      | some ⟨.Q u', d⟩ =>
          if h : u' = u then
            if hs : SameDim Δ u v then some ⟨_, .convert (h ▸ d) hs⟩ else none
          else none
      | _ => none

/-- The type the checker assigns, when one is wanted without its derivation. -/
def infer {j k : ℕ} (Δ : DCtx D j k) (Γ : Ctx B D j k) (e : Tm B D j k) :
    Option (Ty B D j k) := (check Δ Γ e).map Sigma.fst

/-- **Completeness.** Everything the rules accept, the checker finds, at
exactly that type, and returning *that very derivation*.

The equation is stated against the given `d` rather than against some derivation
the checker happens to build, which is stronger than completeness usually is and
costs nothing: the proof is the same induction. Two things fall out. First,
together with `check` returning its derivation, the equation is the whole
correctness statement, so soundness needs no theorem: the checker cannot
produce a type without producing
the derivation that justifies it. Second, since `check Δ Γ e` is one value,
any two derivations of the same judgment are equal. -/
theorem check_eq : ∀ {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ : Ty B D j k} (d : HasTy Δ Γ e τ), check Δ Γ e = some ⟨τ, d⟩ := by
  intro j k Δ Γ e τ d
  induction d with
  | var hn =>
    simp only [check]
    split
    · next x h => obtain rfl : x = _ := Option.some.inj (h.symm.trans hn); rfl
    · next h => exact absurd (h.symm.trans hn) (by simp)
  | lam _ ih => simp [check, ih]
  | app _ _ ihf iha => simp [check, ihf, iha]
  | lit => rfl
  | ucon => rfl
  | mul _ _ iha ihb => simp [check, iha, ihb]
  | div _ _ iha ihb => simp [check, iha, ihb]
  | add _ _ iha ihb => simp [check, iha, ihb]
  | pow _ ih => simp [check, ih]
  | idx _ hu ih =>
    simp only [check, ih]
    split
    · next x h => obtain rfl : x = _ := Option.some.inj (h.symm.trans hu); rfl
    · next h => exact absurd (h.symm.trans hu) (by simp)
  | mrow _ hw ih =>
    simp only [check, ih]
    split
    · next x h => obtain rfl : x = _ := Option.some.inj (h.symm.trans hw); rfl
    · next h => exact absurd (h.symm.trans hw) (by simp)
  | mapp _ _ ihf ihx => simp [check, ihf, ihx]
  | comp _ _ ihf ihg => simp [check, ihf, ihg]
  | vnil => rfl
  | vcons _ _ ihe ihv => simp [check, ihe, ihv]
  | mnil => rfl
  | mcons _ _ ihr ihM => simp [check, ihr, ihM]
  | log _ ih => simp [check, ih]
  | exp _ ih => simp [check, ih]
  | ulam _ ih => simp [check, ih]
  | uapp _ hd ihf => simp [check, ihf, hd]
  | dlam _ ih => simp [check, ih]
  | dapp _ ihf => simp [check, ihf]
  | convert _ hsd ih => simp [check, ih, hsd]

/-- **Derivations are unique.** A judgment is justified in at most one way, so
`HasTy` is a proposition in everything but its sort: it carries data only in
the sense that the data is determined.

This is what licenses speaking of *the* denotation of a term. Anything defined
by recursion over a derivation is thereby a function of the term alone, and no
theorem is needed to say so. It is also why making `HasTy` `Type`-valued costs
nothing in expressiveness: the elimination restriction that `Prop` would impose
is the only thing given up, and there was never a second derivation for it to
protect. -/
instance {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ : Ty B D j k} : Subsingleton (HasTy Δ Γ e τ) :=
  ⟨fun d₁ d₂ => by simpa using (check_eq d₁).symm.trans (check_eq d₂)⟩

/-- **Completeness**, stated for the type alone. -/
theorem infer_complete {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ : Ty B D j k} (d : HasTy Δ Γ e τ) : infer Δ Γ e = some τ := by
  simp [infer, check_eq d]

/-- **The checker decides typing exactly.** It accepts a term at a type
precisely when the rules derive it.

`Nonempty` because a derivation is data: what the judgment asserts is that one
*exists*, and that is a proposition even though the derivation is not. -/
theorem infer_eq_some_iff {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ : Ty B D j k} : infer Δ Γ e = some τ ↔ Nonempty (HasTy Δ Γ e τ) := by
  constructor
  · intro h
    obtain ⟨⟨_, d⟩, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨d⟩
  · rintro ⟨d⟩; exact infer_complete d

/-- Typing is decidable, as a corollary rather than a separate development. -/
instance {j k : ℕ} (Δ : DCtx D j k) (Γ : Ctx B D j k) (e : Tm B D j k) (τ : Ty B D j k) :
    Decidable (Nonempty (HasTy Δ Γ e τ)) :=
  decidable_of_iff (infer Δ Γ e = some τ) infer_eq_some_iff

/-- **Types are unique**, which is what makes `infer` return *the* type rather
than a most general one. -/
theorem HasTy.unique {j k : ℕ} {Δ : DCtx D j k} {Γ : Ctx B D j k} {e : Tm B D j k}
    {τ σ : Ty B D j k} (h₁ : HasTy Δ Γ e τ) (h₂ : HasTy Δ Γ e σ) : τ = σ := by
  have := infer_complete h₁
  have := infer_complete h₂
  simp_all

end Check

end LambdaS

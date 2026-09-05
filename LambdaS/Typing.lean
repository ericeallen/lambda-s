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
is determined by the judgement it proves.

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

The paper's tag `long-form` carries this section in full; preserved here,
lightly de-TeXed, so the documentation develops what the paper now
summarizes.

 sectionThe Calculus]


In this section, we present the syntax and statics of Λs. The design is
governed by a single decision from which nearly everything else follows: units
and dimensions are not syntax trees but **exponent vectors], and every
operation on them is linear algebra.

 subsectionUnits and Dimensions]


Fix a finite set B of **base units] (say, meter],
foot], kilogram], second]) and a finite set D
of **base dimensions] (say, Length], Mass],
Time]). The pair is a parameter of the calculus, as the class table
is a parameter of Featherweight Java [cite: igarashi2001]: introducing a new
base unit is module structure, not computation. Section [ref: sec:declarations]
gives the declaration forms: the primary-unit declarations that supply
this parameter, and the factor declarations that contribute constraints
with semantic content. A **unit
expression] over k unit variables is a pair of finitely supported maps
(i.e., nonzero at only finitely many arguments)
 [
u  =   bigl( u_base]] : B  to ℚ,  
              u_var]] :  0, dots,k-1 ]  to ℚ  bigr),
 ]
read as the formal product
 prod_b b^ u_base]](b)]  cdot  prod_i u]_i^ u_var]](i)].
The unit variables u]_i exist for polymorphism: each is bound by a
unit abstraction  Lambdau]:]d (Section [ref: sec:syntax]), and a
term polymorphic in a unit reads its unit arguments through them.
Multiplication of units is pointwise addition of vectors, division is
subtraction, and the q-th power is scalar multiplication by
q  in ℚ. Dimension expressions are the same structure over D and
j dimension variables. For example, writing a vector by its nonzero entries,
and writing u] and v] for the unit variables at indices
0 and 1 under two binders:
 [
@]r@  =  ]l@ qquad qquad]r@  =  ]l@]]
m] & (m]  mapsto 1) &
m]/s] & (m]  mapsto 1,  s]  mapsto -1)  [2pt]
u]  cdot v] & (u]  mapsto 1,  v]  mapsto 1) &
kg] cdotm]/s]^2 &
  (kg]  mapsto 1,  m]  mapsto 1,  s]  mapsto -2)  [2pt]
u]^3/2] & (u]  mapsto 3/2)

 ]
Note that u]  cdot v] has every base entry zero: a product
of two abstract units mentions no base unit. Dimension expressions
look the same over D: Length] is the vector
(Length]  mapsto 1), and the dimension of a velocity is
Length]/Time] =
(Length]  mapsto 1,  Time]  mapsto -1). Two decisions here
bear emphasis.

First, **exponents are rational], not integral. In Kennedy's
calculus [cite: kennedy1997] the units form the free abelian group on the
base units, with integer exponents; here they form the free
ℚ-vector space on the same generators [footnote: Precisely: the
units over B with k variables in scope form the free ℚ-vector
space on B  sqcup  0, dots,k-1 ], written multiplicatively. Every
ℚ-vector space is torsion-free (written multiplicatively:
u^n = 1 forces u = 1 for nonzero n), and torsion-freeness is what makes
``ratio equal to one'' mean ``units equal'' (Section [ref: sec:twist]).].
The difference propagates everywhere downstream: the group is torsion-free,
so a ratio of units equals the dimensionless unit 1 (the empty exponent
vector) exactly when the two units are equal (Section [ref: sec:twist]);
consistency of unit declarations is consistency of a linear
system over ℚ, solved by Gaussian elimination rather than Smith
normal form, the integer-matrix analogue of diagonalization
(Section [ref: sec:declarations]); and  sqrt cdot] of a
dimensioned quantity is well-typed
( smash sqrtm]^2]] = m]) where systems with integer
exponents must reject it. Quantities with genuinely fractional dimension,
such as the half-densities of geometric quantization, [footnote: A probability
density on a line measured in Length] carries dimension
Length]^-1], so that its integral over an interval is
dimensionless; the half-densities of geometric quantization carry
Length]^-1/2], so that the product of two of them is a density.]
come for free.

Second, **units and dimensions are related by a homomorphism, not a
convention]. A **unit system] assigns each base unit a dimension,
 dimOf : B  to ℚ^D (an exponent vector over the base dimensions
for each base unit), and the map extends linearly to all unit expressions.
Note that  dimOf is total: it is supplied for every base unit as part of
the calculus's parameters, alongside B and D, and the declarations of
Section [ref: sec:declarations] add
magnitudes, never dimensions. We say two units are **interchangeable]
when they
have the same dimension; we write  dimOf_ Delta(u) for the dimension of u
under a context  Delta assigning dimensions to unit variables, and
u  sim_ Delta v for  dimOf_ Delta(u) =  dimOf_ Delta(v). Nothing
restricts a dimension to one unit: meter], foot], and
yard] are three units of Length], which is precisely the
situation conversion exists to serve, and precisely the situation that
systems tracking only dimensions, or one unit system at a
time [cite: fosterwolff2023], cannot express. The two-level design
follows the object-oriented lineage [cite: allen2004].

Note that the vectors are not a restriction of the unit syntax but its
entirety: because the group is **free] on the base units and the unit
variables in scope, every algebraic combination (u]  cdot v]
for two bound
variables, m]/s], u]^3/2]  cdot kg])
denotes a
vector, and the operations in Figure [ref: fig:syntax]'s unit grammar are
total functions on vectors (pointwise addition, subtraction, scaling). A type
such as  Qu]  cdot v]] under
 Lambdau]:]d_1.  Lambdav]:]d_2 is as well-formed as
 Qm]]; the artifact checks
 Lambdau]:]Length].  Lambdav]:]Time]. 
 lambda x:] Qu] cdotv]]. x at the type written.
The spellings u]  cdot v] and
v]  cdot u] differ as expressions, but the
grammar's operations are evaluated when the expression is formed, so the two
spellings denote one vector, exactly as 2+2 and 4 denote one number.
There is nothing to normalize. Nothing remains to compare
except finitely many rationals: where a syntactic treatment must prove that
m]  cdot s]  cdot m]^-1] normalizes to
s], here the two are the same vector, and equality of units is
decided by comparing their entries.

 subsectionTypes and Terms]



 [
@]l@ quad]r@ ]c@ ]l@ qquad]l@]]
 textunits] & u, v & ::= & 1  mid b  mid u]_i  mid u  cdot v  mid
  u / v  mid u^q] & b  in B;  u]_i  text a unit variable];  q  in ℚ  
 textdimensions] & d & ::= & 1  mid D  mid  delta_i  mid d  cdot d  mid
  d / d  mid d^q] &  textlikewise over ] D  
 textspaces] &  vecu],  vecw] & ::= & [ ]  mid u,  vecu] &
   textper-component unit lists]  [4pt]
 texttypes] &  tau & ::= &  Qu] &  textquantity at unit ] u  
& &  mid &  tau  to  tau &  textfunction]  
& &  mid & Vec]  vecu] &  textvector with per-component units]  
& &  mid & Lin]  vecu]  vecw] &  textlinear map]  
& &  mid &  uallu]]d] tau &  textunit abstraction, bounded by a dimension]  
& &  mid &  dall delta] tau &  textdimension abstraction]  [2pt]
 textterms] & e & ::= & x  mid  lambda x:] tau. e  mid e e &   
& &  mid & q  mid 1]_u &  textrational literal (at unit ] 1 text); unit constant]  
& &  mid & e  cdot e  mid e / e  mid e + e  mid e^q] &  textarithmetic; constant rational power]  
& &  mid &  log e  mid  exp e &  textat unit ] 1  text only]  
& &  mid & e.i  mid e  odot e  mid e  circ e &  textindexing; map application; composition]  
& &  mid &  langle rangle  mid e  mathbin::] e &  textvector literals: empty; cons]  
& &  mid &  langle rangle_ vecu]]  mid e  mathbin::]_w] e &  textmatrix literals: rowless at ]  vecu] text; row cons at ] w  
& &  mid &  Lambda u]:]d. e  mid e [u] &  textunit abstraction and application]  
& &  mid &  Lambda delta. e  mid e  d ] &  textdimension abstraction and application]  
& &  mid &  cvte]u]v] &  textconversion]  

 ]
 captionSyntax of Λs. Types and terms are indexed by the number of
enclosing dimension binders j and unit binders k; unit and dimension
variables are de Bruijn indices into those
scopes [cite: debruijn1972]. Function application
e e and linear-map application e  odot e are distinct term forms, as in
the artifact. Unit and dimension expressions satisfy the laws of a
ℚ-vector space written multiplicatively, by construction: each is
represented as its exponent vector.]



The types and terms of Λs appear in Figure [ref: fig:syntax]. When
describing Λs we use the following metavariables:

 item Unit expressions: u, v, w; dimension expressions: d; spaces
  (lists of unit expressions):  vecu],  vecw].
 item Types:  tau,  sigma; terms: e; rational literals: q; naturals: n, i.
 item Contexts:  Gamma (types of term variables),  Delta (dimensions of
  unit variables); derivations:  mathcalD].
 item Valuations: V; rescalings:  psi.


A quantity
type  Qu] classifies scalars carrying unit u; Vec]  vecu]
classifies vectors whose i-th component carries unit u_i (the units vary
per component, following [cite: hart1995]); and
Lin]  vecu]  vecw] classifies linear maps from
Vec]  vecu] to Vec]  vecw], which denote matrices.
We call a per-component unit assignment such as  vecu] a **space];
Vec] and Lin] carry their spaces as type indices.
Both come with introduction and elimination forms. A vector is built by
consing scalars onto the empty vector, each cons extending the space by the
new component's unit. For example, the artifact's state space pairs a
position in m] with a momentum in
kg] cdotm]/s], and the literal
1.3 cdot1]_m]]  mathbin::]
21 cdot1]_kg] cdotm]/s]]  mathbin::]
 langle rangle has type
Vec] [m], kg] cdotm]/s]]
(`stateVec]). A matrix is built by rows. The rowless matrix
 langle rangle_ vecu]] carries its domain space, so a matrix with no
rows still has a well-defined width, and e  mathbin::]_w] e' adds a row
whose output unit is w (an annotation, because a row over the empty domain space determines no
output unit; eliding it at nonempty domains would split the rule and
still need it in the empty case, so the uniform annotation is the
parsimonious choice); rule  ftruleT-MCons] of Figure [ref: fig:typing]
demands the row inhabit Vec] (w/ vecu]), entry j at w/u_j.
That premise is Hart's factorization (Section [ref: sec:hart]) checked at
the introduction form: a matrix whose entries do not factor as row unit over
column unit cannot be written down. The eliminations are indexing e.i,
map application e  odot e, and composition e  circ e: given
x : Vec] [m], kg] cdotm]/s]],
indexing gives x.0 :  Qm]] and
x.1 :  Qkg] cdotm]/s]], and x.2 is a type
error.
Well-scopedness is a type index: types and terms carry the number of
enclosing dimension and unit binders, so ill-scoped unit and dimension syntax
is unrepresentable and unit and dimension substitution has nowhere to go
wrong; value variables are plain de Bruijn naturals, checked against  Gamma
by the typing relation. (Section [ref: sec:mechanization]
reports the defect we found anyway, in the one place indexing could not
reach.)

The two quantifiers deserve comment, because their interaction is the
calculus's answer to a question every polymorphic unit system faces: what
does an **unbounded] unit variable mean? In Λs there is no such
thing. Unit abstraction is always bounded by a dimension,
 uallu]]d] tau, and unbounded quantification is recovered as
 dall delta] uallu]] delta] tau: a unit variable bounded by a
dimension **variable]. The bound is what makes
conversion usable in polymorphic code. Under
 Lambdau]:]Length], the body may
 cvt !]u]]meter]], because the checker can see that
u] and meter] share a dimension. Under
 forall delta.  forallu]:] delta, no concrete unit matches
 delta,
so conversion out of u] can target only expressions of dimension
 delta: the variable itself, other variables bounded by the same
 delta, and their products with dimensionless units. In particular the
generic caster
 [
 Lambda delta.  Lambdau]:] delta.  Lambdav]:] delta. 
 lambda x:] Qu]].  cvtx]u]]v]]
 ]
is well-typed (`caster]), and it is a term the two
abstraction theorems of Section [ref: sec:semantics] separate: a coherent
rescaling assigns u] and v] the one factor its
dimension rescaling gives  delta, leaving the caster invariant, while
independent factors move it. Converting to a **concrete] unit is still
rejected, as an unbounded variable demands, and because coherence
forces every variable bounded by  delta to rescale together, the free
theorems of Section [ref: sec:semantics] keep their full strength
there. Instantiation
is written e [u] for the unit quantifier and e  d ] for the dimension
quantifier: the bracket and the brace mark which quantifier is being
eliminated, and the two are distinct term constructors.

The arithmetic rules carry the unit discipline. Multiplication and division
are total: any two quantities may be multiplied or divided, and the result
carries the product or quotient of their units ( ftruleT-Mul],
 ftruleT-Div] in Figure [ref: fig:typing]). Addition demands its operands at
**equal] units, not merely interchangeable ones: adding meters to feet is
a type error, and convert] is how the programmer says it was
intended. [footnote: The value of requiring exact unit matching was first
made clear to the author by Guy L. Steele Jr., who pointed out that it
helps a programmer manage the imprecisions and finite bounds of
floating-point computation.] Powers at constant rational exponents are primitive:
( cdot)^q] :  Qu]  to  Qu^q]], with no side condition, and we write
 sqrt[n]e] for e^1/n]. Not every power is
definable from the field operations (no term built from +,  cdot,
and / computes a square root: Section [ref: sec:pi] proves
 Qu^2]  to  Qu]
uninhabited by arithmetic terms), and the rule
accepts every unit, since scaling an exponent vector by q always yields
a unit. For example,  sqrtm]^3] is a quantity at
m]^3/2]. [footnote: What is a quantity of dimension
Length]^1/2]? We do not know either, but the type system has no
reason to prejudge the question: quantum mechanics already uses
Length]^-1/2],
and rejecting  sqrtm]^2] to forbid the unfamiliar
 sqrtm]] would get the priority backwards.] Finally  log and
 exp demand dimensionless arguments ( ftruleT-Log],  ftruleT-Exp]), which
is the type-theoretic face of the base-measure problem: a dimensioned
quantity has no scale-invariant logarithm, so  log of a probability density
is rejected while  log of a ratio of densities is accepted.

Measurements are compound, not primitive: a literal is dimensionless
(q :  Q1]) and a unit constant is one of its unit
(1]_u :  Qu]), so the velocity every tutorial opens with is their
product. For example, 5  cdot 1]_m]/s]] :
 Qm]/s]]: rule  ftruleT-Mul] gives it unit
1  cdot m]/s], which **is] the vector
m]/s]. Why is the constant 1]_u rather than u
alone, written directly as a term? Two reasons, one for the checker and one
for the theory. First, units live in types, and the typing rules compare
them by vector equality; if unit expressions were also terms, type indices
would mention terms, and deciding  Qu] =  Qv] would require evaluating
terms. The stratification is what keeps the statics a first-order decidable
theory. Second, and more important for this paper, 1]_u names a
semantic decision that a bare u would hide: the term denotes the
**number one], the unit measured in itself, in every unit system, and a
denotation that never rescales is exactly what parametricity must exclude.
Confining that decision to one constructor gives the theory a single site to
tax: the parametric fragment of Section [ref: sec:semantics] bans exactly
this constructor, the drift analysis of Section [ref: sec:twist] declines
it as the one construct outside the theory itself, and everything else in
the term grammar rescales.

Larger formulas assemble the same way. The world-record 100-meter sprint is the quotient
 [
(100  cdot 1]_m]])  /  (9.58  cdot 1]_s]])
 :   Qm]/s]],
 ]
where the numerator has type  Qm]], the denominator has type
 Qs]],  ftruleT-Div] assigns the quotient the vector with 1 at
m] and -1 at s], and the magnitude is
100/9.58  approx 10.44. The artifact checks this idiom as `velocity]
in `Examples.lean]: a literal-times-constant quotient assigned
 Qm]/s]]. A surface syntax would write 5 m]/s]
and elaborate to exactly this.

Conversion itself is a checked primitive, rule  ftruleT-Cvt] of
Figure [ref: fig:typing]. The term carries its source unit u as well as its
target v: the compiled evaluator (Section [ref: sec:dynamics]) must recover
the conversion factor from the term and its environment alone, and the target
does not determine the source. We envision a surface syntax in which the
programmer writes e in] v and never writes u; the core
carries it, and the one inference this asks for is already discharged in
the artifact. Its elaborator (`elabConvert]) runs the checker of
Section [ref: sec:statics] on e, reads u off the derived type  Qu],
and returns the annotated core term together with its typing derivation,
so an in] cannot produce a term the checker would reject.
Elaboration succeeds exactly when e is a scalar whose unit shares the
target's dimension (`elabConvert_isSome]), and the inferred u
is unique because the checker computes at most one type
(Theorem [ref: thm:completeness]).
 ftruleT-Cvt] is the only rule in Λs that can observe a unit, and
Section [ref: sec:semantics] states what that observation costs.

 subsectionStatics]




 inferrule[T-Var] Gamma(x) =  tau] Delta; Gamma  vdash x :  tau]
 and
 inferrule[T-Lam] Delta; Gamma, x:] tau  vdash e :  sigma]
   Delta; Gamma  vdash  lambda x:] tau. e :  tau  to  sigma]
 and
 inferrule[T-App] Delta; Gamma  vdash e_1 :  tau  to  sigma   
   Delta; Gamma  vdash e_2 :  tau] Delta; Gamma  vdash e_1 e_2 :  sigma]
 and
 inferrule[T-Lit] ] Delta; Gamma  vdash q :  Q1]]
 and
 inferrule[T-Con] ] Delta; Gamma  vdash 1]_u :  Qu]]
 and
 inferrule[T-Mul] Delta; Gamma  vdash e_1 :  Qu]   
   Delta; Gamma  vdash e_2 :  Qv]]
   Delta; Gamma  vdash e_1  cdot e_2 :  Qu v]]
 and
 inferrule[T-Div] Delta; Gamma  vdash e_1 :  Qu]   
   Delta; Gamma  vdash e_2 :  Qv]]
   Delta; Gamma  vdash e_1 / e_2 :  Qu/v]]
 and
 inferrule[T-Add] Delta; Gamma  vdash e_1 :  Qu]   
   Delta; Gamma  vdash e_2 :  Qu]]
   Delta; Gamma  vdash e_1 + e_2 :  Qu]]
 and
 inferrule[T-Pow] Delta; Gamma  vdash e :  Qu]]
   Delta; Gamma  vdash e^q] :  Qu^q]]]
 and
 inferrule[T-VNil] ] Delta; Gamma  vdash  langle rangle : Vec] [ ]]
 and
 inferrule[T-VCons] Delta; Gamma  vdash e_1 :  Qu]   
   Delta; Gamma  vdash e_2 : Vec]  vecu]]
   Delta; Gamma  vdash e_1  mathbin::] e_2 : Vec] (u,  vecu])]
 and
 inferrule[T-MNil] ] Delta; Gamma  vdash  langle rangle_ vecu]] :
  Lin]  vecu] [ ]]
 and
 inferrule[T-MCons] Delta; Gamma  vdash e_1 : Vec] (w/ vecu])   
   Delta; Gamma  vdash e_2 : Lin]  vecu]  vecw]]
   Delta; Gamma  vdash e_1  mathbin::]_w] e_2 :
  Lin]  vecu] (w,  vecw])]
 and
 inferrule[T-Idx] Delta; Gamma  vdash e : Vec]  vecu]   
   vecu]_i = u] Delta; Gamma  vdash e.i :  Qu]]
 and
 inferrule[T-Mapp] Delta; Gamma  vdash e_1 : Lin]  vecu]  vecw]   
   Delta; Gamma  vdash e_2 : Vec]  vecu]]
   Delta; Gamma  vdash e_1  odot e_2 : Vec]  vecw]]
 and
 inferrule[T-Comp] Delta; Gamma  vdash e_1 : Lin]  vecv]  vecw]   
   Delta; Gamma  vdash e_2 : Lin]  vecu]  vecv]]
   Delta; Gamma  vdash e_1  circ e_2 : Lin]  vecu]  vecw]]
 and
 inferrule[T-Log] Delta; Gamma  vdash e :  Q1]]
   Delta; Gamma  vdash  log e :  Q1]]
 and
 inferrule[T-Exp] Delta; Gamma  vdash e :  Q1]]
   Delta; Gamma  vdash  exp e :  Q1]]
 and
 inferrule[T-ULam] Delta, u]:]d; Gamma^ uparrow]  vdash e :  tau]
   Delta; Gamma  vdash  Lambdau]:]d. e :  uallu]]d] tau]
 and
 inferrule[T-UApp] Delta; Gamma  vdash e :  uallu]]d] tau   
   dimOf_ Delta(w) = d]
   Delta; Gamma  vdash e [w] :  tau[u]  mapsto w]]
 and
 inferrule[T-DLam] Delta^ uparrow]; Gamma^ uparrow]  vdash e :  tau]
   Delta; Gamma  vdash  Lambda delta. e :  dall delta] tau]
 and
 inferrule[T-DApp] Delta; Gamma  vdash e :  dall delta] tau]
   Delta; Gamma  vdash e  d ] :  tau[ delta  mapsto d]]
 and
 inferrule[T-Cvt] Delta; Gamma  vdash e :  Qu]    u  sim_ Delta v]
   Delta; Gamma  vdash  cvte]u]v] :  Qv]]

 captionTyping: the full rule set, transcribed from the artifact's
 textsfHasTy].  Gamma^ uparrow] and  Delta^ uparrow] weaken a context
past a new binder: each index in the context is shifted so that it refers to
the same variable in the extended scope. In  ftruleT-Idx], the premise
 vecu]_i = u abbreviates a successful bounds-checked lookup, as in the
artifact. In  ftruleT-Con], u ranges over all unit expressions,
variables included. (u,  vecu]) prepends a component to a space, and in
 ftruleT-MCons], w/ vecu] is the pointwise quotient, entry j at
w/u_j.]



The typing judgment  Delta; Gamma  vdash e :  tau carries a dimension
context  Delta (the declared dimension of each unit variable in scope)
alongside the usual  Gamma; the rules appear in Figure [ref: fig:typing],
they are syntax-directed, and types are unique. We highlight what the
artifact makes of this, because the
arrangement is unusual and we recommend it. The checker does not return a
type; it returns a **derivation]:
 small
 textttdef check :  j k :  mathbbN] ]  to ( Delta : DCtx D j k)  to
( Gamma : Ctx B D j k)  to (e : Tm B D j k)  to]  
 texttt phantomdef check ::] Option ( Sigma  tau : Ty B D j k,
HasTy  Delta  Gamma e  tau)]

The result is a dependent pair: a type  tau together with a derivation
that e has type  tau under  Delta and  Gamma. The checker returns
evidence, not a boolean. With derivations as data, the usual checker soundness
theorem (anything the checker accepts is well-typed) is not a theorem. There
is nothing for it to say: a checker that cannot produce a type without
producing the derivation that justifies it cannot accept an ill-typed
term. (Type soundness, that a well-typed term evaluates to a value of its
type, is a theorem about the dynamics, with real content, and
Section [ref: sec:dynamics] proves it.)
What remains is the only direction with content, and
Theorem [ref: thm:completeness] states it in a form stronger than completeness
usually takes:


For every derivation  mathcalD] of  Delta; Gamma  vdash e :  tau,
check]  Delta  Gamma e = some] ( tau,  mathcalD]).


Note that nothing is handed to the checker: the theorem quantifies over an
arbitrary derivation  mathcalD] of the judgment and asserts that
check] returns exactly the pair ( tau,  mathcalD]). Since
check]  Delta  Gamma e is a single value, an immediate corollary
is that any two derivations of the same judgment are equal: typing
derivations are unique. Uniqueness is not
a curiosity. It is what licenses speaking of **the] denotation of a term
in Section [ref: sec:semantics], where the semantics is defined by recursion
on derivations, and it is what lets the syntactic side conditions of the
abstraction theorems be predicates on terms rather than on derivations.
Decidability of typing falls out: the checker is a decision procedure, proved
sound by its type and complete by Theorem [ref: thm:completeness].

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

  Equal, not merely same-dimension: adding metres to feet is a type error, and
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
any two derivations of the same judgement are equal. -/
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

/-- **Derivations are unique.** A judgement is justified in at most one way, so
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

`Nonempty` because a derivation is data: what the judgement asserts is that one
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

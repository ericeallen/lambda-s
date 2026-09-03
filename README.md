# Λs: a calculus of units of measure with conversion

Λs is a typed lambda calculus in which **conversion between units of the same
dimension is a primitive**, and the price of admitting it is characterized
exactly. This repository is the full mechanization: statics, dynamics,
denotational semantics, two abstraction theorems, adequacy, erasure, and the
Pi theorem of dimensional analysis, in Lean 4.

The theoretical literature on units, beginning with Kennedy, obtains
parametricity theorems for calculi in which no operation can observe a unit.
The practical literature provides conversion, which is what programmers ask
of units, and no invariance theory, because conversion breaks the
parametricity such theories rest on. Λs has both. Every parametric term is
invariant under the rescalings that respect dimension, and a first-order
program with nonzero denotation is invariant under *all* rescalings precisely
when its accumulated conversion ratio is trivial: a decidable condition,
which the development turns into a compiler diagnostic.

The development is about eleven thousand lines and stays that small because of
one representational decision: units and dimensions are exponent vectors over
ℚ, so substitution is a linear map, every substitution lemma is a
reordering of finite sums, and no normalization pass over unit syntax exists
anywhere in the system.

## Status

| | |
|---|---|
| Lean | 4.33.0 (pinned in `lean-toolchain`) |
| mathlib | pinned in `lake-manifest.json` |
| `sorry` / `admit` | none |
| theorem and lemma declarations | 406 |
| axioms | `propext`, `Classical.choice`, `Quot.sound` |

`Examples.lean`, `QM.lean`, and `Algorithms.lean` run the checker, the
drift analysis, and the evaluator **at build time** through `#guard`; if a
stated result were different, the library would not compile. The two
numerical demonstrations whose arithmetic reaches the FFI are checked by
the compiled binary instead, and CI asserts its output.

## Build

Prerequisites: [elan](https://github.com/leanprover/elan) (which installs
the pinned Lean toolchain on first use) and a C compiler.

```sh
lake exe cache get     # fetch prebuilt mathlib oleans (multi-GB, needs network)
lake build             # build the library and check every proof
lake exe lambdas       # print the worked reports with their numeric self-checks
```

`lake exe cache get` is the slow step; with the cache in place, a full
build of this library takes a few minutes on a laptop. The BLAS shim in
`c/` links against Accelerate on macOS (via the Command Line Tools SDK; if
your Mac has only Xcode, adjust `moreLinkArgs` in `lakefile.lean`) and
falls back to portable C loops elsewhere; no separate BLAS installation is
required.

## What is in here

**The algebra.** `Uom` defines a unit as a ℚ-valued exponent vector and
proves the group laws. `Scaling` gives rescalings and the pullback laws that
make substitution commute with them. `Unify` is unification modulo the
equational theory of abelian groups, so inference has principal solutions.
`Space`, `Map`, and `Density` give dimensioned vectors, Hart-style
rank-one matrices, and densities.

**Statics.** `Syntax` gives types and terms, scope-indexed so ill-scoped
syntax is unrepresentable. `Typing` gives both the declarative judgment
`HasTy` and the checker, and the checker *returns derivations*: soundness
holds by construction, and completeness and decidability are proved.
`Notation` makes programs readable.

**Dynamics.** `Dynamics` is a definitional interpreter instrumented with
units. `Soundness` is type soundness, and `Normalization` is strong
normalization by Tait reducibility on type skeletons, so the fuel a
definitional interpreter carries is produced by a theorem rather than
assumed.

**Semantics.** `Parametricity` builds the logical relation, `Fundamental`
proves both abstraction theorems and that coherence is the exact price of
conversion. `Adequacy` joins the declaration oracle to the evaluator, and
`Erasure` strips units and every dynamic check from run-time values without
moving the numbers.

**Conversion.** `Conversion` gives the operator, `Declare` the consistency
criterion for declaration sets, proved in both directions in exact rational
arithmetic, `Ratio` the
first-order syntax of accumulated ratios, and `Twist` the drift analysis and
its decision procedure.

**Dimensional analysis.** `Pi` and `PiTheorem` derive Buckingham's counting
as a corollary of parametricity, including the bridge from the term-level
multiplicative scaling law to the log-coordinate Pi theorem (positivity is
the hypothesis the logarithm needs). `Definability` and `NonDefinability`
prove that roots must be primitive.

**Programs.** `Examples`, `QM`, and `Algorithms` are the worked examples,
including the yard/foot/metre declarations end to end and the pendulum.

Each module carries a header docstring explaining what it is for and why it
exists; those are the intended entry points for a reader, and the groups
above are the intended reading order.

## Theorem index

`THEOREMS.md` maps every artifact identifier the accompanying paper cites
to its Lean name, file, and line.

## Auditing the trust base

```sh
lake env lean scripts/Audit.lean
```

prints the axiom dependencies of every theorem the paper cites. CI builds
the library, greps the sources for `sorry`, fails if any audited theorem
depends on more than the three standard axioms, and runs the compiled
binary, asserting its numeric self-checks and the declared-conversion
report.

## License

Apache-2.0; see `LICENSE`.

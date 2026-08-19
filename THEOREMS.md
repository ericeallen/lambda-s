# Theorem index

Every theorem stated in the paper, with the Lean name that proves it.
Line numbers are for the commit that carries this file.

| Paper theorem | Section | Lean name | Location |
|---|---|---|---|
| Completeness | calculus | `LambdaS.check_eq` | [`LambdaS/Typing.lean:234`](LambdaS/Typing.lean#L234) |
| Consistency, necessity | declarations | `LambdaS.dependency_forces` | [`LambdaS/Declare.lean:172`](LambdaS/Declare.lean#L172) |
| Unit soundness | dynamics | `LambdaS.unit_soundness_total` | [`LambdaS/Normalization.lean:550`](LambdaS/Normalization.lean#L550) |
| Abstraction, convert-free | semantics | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:788`](LambdaS/Fundamental.lean#L788) |
| Abstraction, coherent | semantics | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:696`](LambdaS/Fundamental.lean#L696) |
| The price is exact | semantics | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:889`](LambdaS/Fundamental.lean#L889) |
| The scaling law, twisted | twist | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:168`](LambdaS/Twist.lean#L168) |
| Decidability | twist | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:392`](LambdaS/Twist.lean#L392) |
| Decidability (diagnostic) | twist | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:718`](LambdaS/Twist.lean#L718) |
| Declared factors reach the machine | erasure | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:701`](LambdaS/Adequacy.lean#L701) |
| Erasure (simulation) | erasure | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:178`](LambdaS/Erasure.lean#L178) |
| Erasure (correctness) | erasure | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:345`](LambdaS/Erasure.lean#L345) |
| Pi | pi | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:87`](LambdaS/PiTheorem.lean#L87) |
| Pi (invariance) | pi | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:114`](LambdaS/PiTheorem.lean#L114) |
| Pi (counting) | pi | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:137`](LambdaS/PiTheorem.lean#L137) |
| Pi (equivalence) | pi | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:177`](LambdaS/PiTheorem.lean#L177) |

## Reproducing the worked examples

`lake exe lambdas` prints the yard/foot/metre report: 300 ft and 91.44 m,
computed by both the declaration oracle and the compiled evaluator, which
is the chain from a declaration to a number that `LambdaS.evalC_convert_declared`
asserts. The `#guard` commands in `LambdaS/Examples.lean`, `LambdaS/QM.lean`,
and `LambdaS/Algorithms.lean` run at build time.

# Theorem index

Every artifact identifier the accompanying paper cites, with its Lean name
and location. Line numbers are for the commit that carries this file.
`scripts/Audit.lean` prints the axiom dependencies of the theorems below;
CI fails if any depends on more than `propext`, `Classical.choice`, and
`Quot.sound`.

## The calculus and its checker

| Paper claim | Lean name | Location |
|---|---|---|
| Typing rules (Figure 2) | `LambdaS.HasTy` | [`LambdaS/Typing.lean:75`](LambdaS/Typing.lean#L75) |
| Completeness; derivations unique | `LambdaS.check_eq` | [`LambdaS/Typing.lean:235`](LambdaS/Typing.lean#L235) |
| The velocity idiom | `LambdaS.Examples.velocity` | [`LambdaS/Examples.lean:91`](LambdaS/Examples.lean#L91) |

## Unit declarations

| Paper claim | Lean name | Location |
|---|---|---|
| Consistency, necessity (log form) | `LambdaS.dependency_forces` | [`LambdaS/Declare.lean:180`](LambdaS/Declare.lean#L180) |
| Consistency, necessity (product form) | `LambdaS.dependency_forces_mul` | [`LambdaS/Declare.lean:211`](LambdaS/Declare.lean#L211) |
| Consistency, sufficiency | `LambdaS.dependency_sufficient` | [`LambdaS/Declare.lean:292`](LambdaS/Declare.lean#L292) |
| Consistency characterized (log form) | `LambdaS.consistent_iff_dependencies` | [`LambdaS/Declare.lean:320`](LambdaS/Declare.lean#L320) |
| Consistency characterized (Theorem 3.1) | `LambdaS.consistent_iff_dependencies_mul` | [`LambdaS/Declare.lean:334`](LambdaS/Declare.lean#L334) |
| Redundant factor forced | `LambdaS.factor_chain_consistent` | [`LambdaS/Declare.lean:398`](LambdaS/Declare.lean#L398) |
| One-dimension well-formedness | `LambdaS.Decl.Sound` | [`LambdaS/Declare.lean:133`](LambdaS/Declare.lean#L133) |
| The yard set is satisfiable | `LambdaS.Examples.yard_satisfiable` | [`LambdaS/Examples.lean:520`](LambdaS/Examples.lean#L520) |
| The mistyped yard set is refuted | `LambdaS.Examples.yard_conflict` | [`LambdaS/Examples.lean:474`](LambdaS/Examples.lean#L474) |
| The redundant factor is forced | `LambdaS.Examples.yard_forced` | [`LambdaS/Examples.lean:462`](LambdaS/Examples.lean#L462) |

## Dynamics

| Paper claim | Lean name | Location |
|---|---|---|
| Unit soundness (Theorem 4.1) | `LambdaS.unit_soundness_total` | [`LambdaS/Normalization.lean:550`](LambdaS/Normalization.lean#L550) |
| Totality at every type | `LambdaS.eval_total` | [`LambdaS/Normalization.lean:533`](LambdaS/Normalization.lean#L533) |
| Fuel accounting, checked by the binary | `LambdaS.QM.twoStateChecks` | [`LambdaS/QM.lean:312`](LambdaS/QM.lean#L312) |

## Denotational semantics and abstraction

| Paper claim | Lean name | Location |
|---|---|---|
| Convert-free terms ignore the valuation | `LambdaS.den_eq_of_convertFree` | [`LambdaS/Fundamental.lean:677`](LambdaS/Fundamental.lean#L677) |
| Valuation independence at higher type | `LambdaS.den_indep` | [`LambdaS/Fundamental.lean:614`](LambdaS/Fundamental.lean#L614) |
| Abstraction, convert-free (Theorem 5.1) | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:788`](LambdaS/Fundamental.lean#L788) |
| Abstraction, coherent (Theorem 5.2) | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:696`](LambdaS/Fundamental.lean#L696) |
| Theorem 5.2 at a moving rescaling | `LambdaS.Examples.fundamental_at_moving_rescale` | [`LambdaS/Examples.lean:747`](LambdaS/Examples.lean#L747) |
| The price is exact (Theorem 5.3) | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:889`](LambdaS/Fundamental.lean#L889) |

## Accumulated ratios and the drift diagnostic

| Paper claim | Lean name | Location |
|---|---|---|
| The scaling law, twisted (Theorem 6.1) | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:169`](LambdaS/Twist.lean#L169) |
| Invariance iff trivial ratio | `LambdaS.Twist.invariant_iff` | [`LambdaS/Twist.lean:368`](LambdaS/Twist.lean#L368) |
| Decidability (Theorem 6.2) | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:392`](LambdaS/Twist.lean#L392) |
| The diagnostic's specification | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:719`](LambdaS/Twist.lean#L719) |
| Branch comparison at `+` | `LambdaS.Tw.scalarEq` | [`LambdaS/Twist.lean:612`](LambdaS/Twist.lean#L612) |
| Reassociated conversions accepted | `LambdaS.Examples.addAssoc` | [`LambdaS/Examples.lean:678`](LambdaS/Examples.lean#L678) |
| Drift-free programs are declaration-independent | `LambdaS.evalC_indep_of_driftFree` | [`LambdaS/Twist.lean:769`](LambdaS/Twist.lean#L769) |

## Adequacy and erasure

| Paper claim | Lean name | Location |
|---|---|---|
| Adequacy at the declared factors | `LambdaS.eval_adeq` | [`LambdaS/Adequacy.lean:333`](LambdaS/Adequacy.lean#L333) |
| Declared factors reach the compiled evaluator (Theorem 7.1) | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:701`](LambdaS/Adequacy.lean#L701) |
| Erasure simulation, no typing hypothesis (Theorem 7.2) | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:179`](LambdaS/Erasure.lean#L179) |
| Erasure correctness | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:346`](LambdaS/Erasure.lean#L346) |
| The erased evaluator computes the denotation | `LambdaS.eeval_den` | [`LambdaS/Erasure.lean:358`](LambdaS/Erasure.lean#L358) |
| One yard is three feet, at the evaluator | `LambdaS.Examples.one_yard_is_three_feet` | [`LambdaS/Examples.lean:528`](LambdaS/Examples.lean#L528) |
| One yard is 0.9144 meters, both routes | `LambdaS.Examples.one_yard_in_metres` | [`LambdaS/Examples.lean:539`](LambdaS/Examples.lean#L539) |

## Dimensional analysis

| Paper claim | Lean name | Location |
|---|---|---|
| Square root not definable by arithmetic | `LambdaS.NonDef.sqrt_not_definable` | [`LambdaS/NonDefinability.lean:142`](LambdaS/NonDefinability.lean#L142) |
| No seed for Newton's method | `LambdaS.NonDef.no_newton_seed` | [`LambdaS/NonDefinability.lean:150`](LambdaS/NonDefinability.lean#L150) |
| The multiplicative scale law (definition) | `LambdaS.Pi.MulScaleLaw` | [`LambdaS/PiTheorem.lean:215`](LambdaS/PiTheorem.lean#L215) |
| Term-level multiplicative scale law | `LambdaS.Pi.den_mulScaleLaw` | [`LambdaS/PiTheorem.lean:369`](LambdaS/PiTheorem.lean#L369) |
| Log transport, positivity hypothesis | `LambdaS.Pi.scaleLaw_of_mulScaleLaw` | [`LambdaS/PiTheorem.lean:244`](LambdaS/PiTheorem.lean#L244) |
| Pi (Theorem 8.1) | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:87`](LambdaS/PiTheorem.lean#L87) |
| Pi, multiplicative coordinates | `LambdaS.Pi.mulScaleLaw_factorization` | [`LambdaS/PiTheorem.lean:268`](LambdaS/PiTheorem.lean#L268) |
| Invariants are the dimensionless monomials | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:114`](LambdaS/PiTheorem.lean#L114) |
| Buckingham's counting | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:137`](LambdaS/PiTheorem.lean#L137) |
| The factorization is an equivalence | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:177`](LambdaS/PiTheorem.lean#L177) |
| The pendulum signature | `LambdaS.Pi.pendulum` | [`LambdaS/Pi.lean:128`](LambdaS/Pi.lean#L128) |
| The pendulum solution exhibited | `LambdaS.Pi.pendulum_period_solution` | [`LambdaS/Pi.lean:156`](LambdaS/Pi.lean#L156) |
| The pendulum ignores its mass | `LambdaS.Pi.pendulum_mass_absent` | [`LambdaS/PiTheorem.lean:393`](LambdaS/PiTheorem.lean#L393) |
| A once-appearing base unit forces a zero exponent | `LambdaS.Pi.solution_eq_zero_of_appears_once` | [`LambdaS/Pi.lean:113`](LambdaS/Pi.lean#L113) |

## Dimensioned linear algebra

| Paper claim | Lean name | Location |
|---|---|---|
| Rank-one units (Theorem 9.1) | `LambdaS.entry_rank_one` | [`LambdaS/Map.lean:51`](LambdaS/Map.lean#L51) |
| Composition entry units | `LambdaS.entry_comp` | [`LambdaS/Map.lean:62`](LambdaS/Map.lean#L62) |
| Endomorphism diagonals dimensionless | `LambdaS.entry_id_diag` | [`LambdaS/Map.lean:89`](LambdaS/Map.lean#L89) |
| Permutation products dimensionless | `LambdaS.entry_perm_prod` | [`LambdaS/Map.lean:77`](LambdaS/Map.lean#L77) |
| Eigenvalue unit identity | `LambdaS.eigenvalue_uom` | [`LambdaS/Map.lean:119`](LambdaS/Map.lean#L119) |
| Dual-map entries symmetric | `LambdaS.entry_dual_symm` | [`LambdaS/Map.lean:126`](LambdaS/Map.lean#L126) |
| Weighted norms dimensionless | `LambdaS.weighted_norm_dimensionless` | [`LambdaS/Map.lean:131`](LambdaS/Map.lean#L131) |
| Cholesky factors dimensionless | `LambdaS.cholesky_factor_dimensionless` | [`LambdaS/Map.lean:141`](LambdaS/Map.lean#L141) |
| Uniform spaces are scaled dimensionless spaces | `LambdaS.Space.uniform_iff_scale_triv` | [`LambdaS/Space.lean:86`](LambdaS/Space.lean#L86) |
| SVD entries share one unit | `LambdaS.svd_entry_const` | [`LambdaS/Map.lean:157`](LambdaS/Map.lean#L157) |
| Self-dual spaces are dimensionless | `LambdaS.transpose_comp_direct_iff` | [`LambdaS/Map.lean:171`](LambdaS/Map.lean#L171) |
| Uniform spaces carry a canonical metric | `LambdaS.uniform_canonical_metric` | [`LambdaS/Map.lean:184`](LambdaS/Map.lean#L184) |

## Reproducing the worked examples

`lake exe lambdas` prints the declared-conversion report (100 yards as
300 ft, as 91.44 m directly, and as 91.44 m through feet: path independence
made observable), followed by the quantum-mechanics and free-fall reports
with their numeric self-checks. The same three yard numbers are asserted at
build time by `#guard`s in `LambdaS/Algorithms.lean`; the `#guard`s there
and in `LambdaS/Examples.lean` and `LambdaS/QM.lean` run the checker, the
drift analysis, and the evaluator during `lake build`, so a wrong stated
result would fail the build.

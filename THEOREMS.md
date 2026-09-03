# Theorem index

Every artifact identifier the accompanying paper cites, with its Lean name
and location. Line numbers are for the commit that carries this file.
`scripts/Audit.lean` prints the axiom dependencies of the theorems below;
CI fails if any depends on more than `propext`, `Classical.choice`, and
`Quot.sound`.

## The calculus and its checker

| Paper claim | Lean name | Location |
|---|---|---|
| Typing rules (Figure 2) | `LambdaS.HasTy` | [`LambdaS/Typing.lean:80`](LambdaS/Typing.lean#L80) |
| Completeness; derivations unique | `LambdaS.check_eq` | [`LambdaS/Typing.lean:240`](LambdaS/Typing.lean#L240) |
| The generic caster is well-typed | `LambdaS.Examples.caster` | [`LambdaS/Examples.lean:726`](LambdaS/Examples.lean#L726) |
| The velocity idiom | `LambdaS.Examples.velocity` | [`LambdaS/Examples.lean:96`](LambdaS/Examples.lean#L96) |

## Unit declarations

| Paper claim | Lean name | Location |
|---|---|---|
| Consistency, necessity (log form) | `LambdaS.dependency_forces` | [`LambdaS/Declare.lean:185`](LambdaS/Declare.lean#L185) |
| Consistency, necessity (product form) | `LambdaS.dependency_forces_mul` | [`LambdaS/Declare.lean:216`](LambdaS/Declare.lean#L216) |
| Consistency, sufficiency | `LambdaS.dependency_sufficient` | [`LambdaS/Declare.lean:258`](LambdaS/Declare.lean#L258) |
| Consistency characterized (log form) | `LambdaS.consistent_iff_dependencies` | [`LambdaS/Declare.lean:286`](LambdaS/Declare.lean#L286) |
| Consistency characterized (Theorem 3.1) | `LambdaS.consistent_iff_dependencies_mul` | [`LambdaS/Declare.lean:300`](LambdaS/Declare.lean#L300) |
| Redundant factor forced | `LambdaS.factor_chain_consistent` | [`LambdaS/Declare.lean:364`](LambdaS/Declare.lean#L364) |
| One-dimension well-formedness | `LambdaS.Decl.Sound` | [`LambdaS/Declare.lean:138`](LambdaS/Declare.lean#L138) |
| The yard set is satisfiable | `LambdaS.Examples.yard_satisfiable` | [`LambdaS/Examples.lean:525`](LambdaS/Examples.lean#L525) |
| The mistyped yard set is refuted | `LambdaS.Examples.yard_conflict` | [`LambdaS/Examples.lean:479`](LambdaS/Examples.lean#L479) |
| The redundant factor is forced | `LambdaS.Examples.yard_forced` | [`LambdaS/Examples.lean:467`](LambdaS/Examples.lean#L467) |

## Dynamics

| Paper claim | Lean name | Location |
|---|---|---|
| Unit soundness (Theorem 4.1) | `LambdaS.unit_soundness_total` | [`LambdaS/Normalization.lean:555`](LambdaS/Normalization.lean#L555) |
| Totality at every type | `LambdaS.eval_total` | [`LambdaS/Normalization.lean:538`](LambdaS/Normalization.lean#L538) |
| Fuel accounting, checked by the binary | `LambdaS.QM.twoStateChecks` | [`LambdaS/QM.lean:317`](LambdaS/QM.lean#L317) |

## Denotational semantics and abstraction

| Paper claim | Lean name | Location |
|---|---|---|
| Convert-free terms ignore the valuation | `LambdaS.den_eq_of_convertFree` | [`LambdaS/Fundamental.lean:687`](LambdaS/Fundamental.lean#L687) |
| Valuation independence at higher type | `LambdaS.den_indep` | [`LambdaS/Fundamental.lean:624`](LambdaS/Fundamental.lean#L624) |
| Abstraction, convert-free (Theorem 5.1) | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:800`](LambdaS/Fundamental.lean#L800) |
| Abstraction, coherent (Theorem 5.2) | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:706`](LambdaS/Fundamental.lean#L706) |
| Theorem 5.2 at a moving rescaling | `LambdaS.Examples.fundamental_at_moving_rescale` | [`LambdaS/Examples.lean:804`](LambdaS/Examples.lean#L804) |
| The root scaling identity, all reals, positive factor | `LambdaS.mul_rpow_of_pos_left` | [`LambdaS/Parametricity.lean:359`](LambdaS/Parametricity.lean#L359) |
| The abstraction theorem at a root term | `LambdaS.sqrt_scales` | [`LambdaS/Fundamental.lean:1047`](LambdaS/Fundamental.lean#L1047) |
| The price is exact (Theorem 5.3) | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:903`](LambdaS/Fundamental.lean#L903) |
| Coherent equals factoring through dimension | `LambdaS.Scaling.coherent_iff_factors` | [`LambdaS/Conversion.lean:447`](LambdaS/Conversion.lean#L447) |

## Accumulated ratios and the drift diagnostic

| Paper claim | Lean name | Location |
|---|---|---|
| The scaling law, twisted (Theorem 6.1) | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:174`](LambdaS/Twist.lean#L174) |
| Invariance iff trivial ratio | `LambdaS.Twist.invariant_iff` | [`LambdaS/Twist.lean:373`](LambdaS/Twist.lean#L373) |
| Decidability (Theorem 6.2) | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:397`](LambdaS/Twist.lean#L397) |
| The diagnostic's specification | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:728`](LambdaS/Twist.lean#L728) |
| Branch comparison at `+` | `LambdaS.Tw.scalarEq` | [`LambdaS/Twist.lean:621`](LambdaS/Twist.lean#L621) |
| Reassociated conversions accepted | `LambdaS.Examples.addAssoc` | [`LambdaS/Examples.lean:683`](LambdaS/Examples.lean#L683) |
| Drift-free programs are declaration-independent | `LambdaS.evalC_indep_of_driftFree` | [`LambdaS/Twist.lean:778`](LambdaS/Twist.lean#L778) |

## Adequacy and erasure

| Paper claim | Lean name | Location |
|---|---|---|
| Adequacy at the declared factors | `LambdaS.eval_adeq` | [`LambdaS/Adequacy.lean:338`](LambdaS/Adequacy.lean#L338) |
| Declared factors reach the compiled evaluator (Theorem 7.1) | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:706`](LambdaS/Adequacy.lean#L706) |
| Erasure simulation, no typing hypothesis (Theorem 7.2) | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:184`](LambdaS/Erasure.lean#L184) |
| Erasure correctness | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:351`](LambdaS/Erasure.lean#L351) |
| The erased evaluator computes the denotation | `LambdaS.eeval_den` | [`LambdaS/Erasure.lean:363`](LambdaS/Erasure.lean#L363) |
| One yard is three feet, at the evaluator | `LambdaS.Examples.one_yard_is_three_feet` | [`LambdaS/Examples.lean:533`](LambdaS/Examples.lean#L533) |
| One yard is 0.9144 meters, both routes | `LambdaS.Examples.one_yard_in_metres` | [`LambdaS/Examples.lean:544`](LambdaS/Examples.lean#L544) |

## Dimensional analysis

| Paper claim | Lean name | Location |
|---|---|---|
| Square root not definable by arithmetic | `LambdaS.NonDef.sqrt_not_definable` | [`LambdaS/NonDefinability.lean:147`](LambdaS/NonDefinability.lean#L147) |
| The reflection into the arithmetic grammar | `LambdaS.NonDef.arith_of_hasTy` | [`LambdaS/NonDefinability.lean:200`](LambdaS/NonDefinability.lean#L200) |
| Square root not definable, at the term grammar | `LambdaS.NonDef.sqrt_not_definable_tm` | [`LambdaS/NonDefinability.lean:245`](LambdaS/NonDefinability.lean#L245) |
| No seed for Newton's method | `LambdaS.NonDef.no_newton_seed` | [`LambdaS/NonDefinability.lean:155`](LambdaS/NonDefinability.lean#L155) |
| No seed, at the term grammar | `LambdaS.NonDef.no_newton_seed_tm` | [`LambdaS/NonDefinability.lean:256`](LambdaS/NonDefinability.lean#L256) |
| The multiplicative scale law (definition) | `LambdaS.Pi.MulScaleLaw` | [`LambdaS/PiTheorem.lean:220`](LambdaS/PiTheorem.lean#L220) |
| Term-level multiplicative scale law | `LambdaS.Pi.den_mulScaleLaw` | [`LambdaS/PiTheorem.lean:374`](LambdaS/PiTheorem.lean#L374) |
| Log transport, positivity hypothesis | `LambdaS.Pi.scaleLaw_of_mulScaleLaw` | [`LambdaS/PiTheorem.lean:249`](LambdaS/PiTheorem.lean#L249) |
| Pi (Theorem 8.1) | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:92`](LambdaS/PiTheorem.lean#L92) |
| Pi, multiplicative coordinates | `LambdaS.Pi.mulScaleLaw_factorization` | [`LambdaS/PiTheorem.lean:273`](LambdaS/PiTheorem.lean#L273) |
| Invariants are the dimensionless monomials | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:119`](LambdaS/PiTheorem.lean#L119) |
| Buckingham's counting | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:142`](LambdaS/PiTheorem.lean#L142) |
| The factorization is an equivalence | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:182`](LambdaS/PiTheorem.lean#L182) |
| The pendulum signature | `LambdaS.Pi.pendulum` | [`LambdaS/Pi.lean:133`](LambdaS/Pi.lean#L133) |
| The pendulum solution exhibited | `LambdaS.Pi.pendulum_period_solution` | [`LambdaS/Pi.lean:161`](LambdaS/Pi.lean#L161) |
| The pendulum ignores its mass | `LambdaS.Pi.pendulum_mass_absent` | [`LambdaS/PiTheorem.lean:398`](LambdaS/PiTheorem.lean#L398) |
| A once-appearing base unit forces a zero exponent | `LambdaS.Pi.solution_eq_zero_of_appears_once` | [`LambdaS/Pi.lean:118`](LambdaS/Pi.lean#L118) |

## Dimensioned linear algebra

| Paper claim | Lean name | Location |
|---|---|---|
| Rank-one units (Theorem 9.1) | `LambdaS.entry_rank_one` | [`LambdaS/Map.lean:56`](LambdaS/Map.lean#L56) |
| Composition entry units | `LambdaS.entry_comp` | [`LambdaS/Map.lean:67`](LambdaS/Map.lean#L67) |
| Endomorphism diagonals dimensionless | `LambdaS.entry_id_diag` | [`LambdaS/Map.lean:94`](LambdaS/Map.lean#L94) |
| Permutation products dimensionless | `LambdaS.entry_perm_prod` | [`LambdaS/Map.lean:82`](LambdaS/Map.lean#L82) |
| Eigenvalue unit identity | `LambdaS.eigenvalue_uom` | [`LambdaS/Map.lean:124`](LambdaS/Map.lean#L124) |
| Dual-map entries symmetric | `LambdaS.entry_dual_symm` | [`LambdaS/Map.lean:131`](LambdaS/Map.lean#L131) |
| Weighted norms dimensionless | `LambdaS.weighted_norm_dimensionless` | [`LambdaS/Map.lean:136`](LambdaS/Map.lean#L136) |
| Cholesky factors dimensionless | `LambdaS.cholesky_factor_dimensionless` | [`LambdaS/Map.lean:146`](LambdaS/Map.lean#L146) |
| Uniform spaces are scaled dimensionless spaces | `LambdaS.Space.uniform_iff_scale_triv` | [`LambdaS/Space.lean:91`](LambdaS/Space.lean#L91) |
| SVD entries share one unit | `LambdaS.svd_entry_const` | [`LambdaS/Map.lean:162`](LambdaS/Map.lean#L162) |
| Self-dual spaces are dimensionless | `LambdaS.transpose_comp_direct_iff` | [`LambdaS/Map.lean:176`](LambdaS/Map.lean#L176) |
| Uniform spaces carry a canonical metric | `LambdaS.uniform_canonical_metric` | [`LambdaS/Map.lean:189`](LambdaS/Map.lean#L189) |

## Reproducing the worked examples

`lake exe lambdas` prints the declared-conversion report (100 yards as
300 ft, as 91.44 m directly, and as 91.44 m through feet: path independence
made observable), followed by the quantum-mechanics and free-fall reports
with their numeric self-checks. The same three yard numbers are asserted at
build time by `#guard`s in `LambdaS/Algorithms.lean`; the `#guard`s there
and in `LambdaS/Examples.lean` and `LambdaS/QM.lean` run the checker, the
drift analysis, and the evaluator during `lake build`, so a wrong stated
result would fail the build.

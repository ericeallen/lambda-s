# Theorem index

Every artifact identifier the accompanying paper cites, with its Lean name
and location. Line numbers are for the commit that carries this file.
`scripts/Audit.lean` prints the axiom dependencies of the theorems below;
CI fails if any depends on more than `propext`, `Classical.choice`, and
`Quot.sound`.

## The calculus and its checker

| Paper claim | Lean name | Location |
|---|---|---|
| Typing rules (Figure 2) | `LambdaS.HasTy` | [`LambdaS/Typing.lean:88`](LambdaS/Typing.lean#L88) |
| Completeness; derivations unique | `LambdaS.check_eq` | [`LambdaS/Typing.lean:276`](LambdaS/Typing.lean#L276) |
| The generic caster is well-typed | `LambdaS.Examples.caster` | [`LambdaS/Examples.lean:727`](LambdaS/Examples.lean#L727) |
| The velocity idiom | `LambdaS.Examples.velocity` | [`LambdaS/Examples.lean:96`](LambdaS/Examples.lean#L96) |
| Surface `in` elaborates by running the checker | `LambdaS.elabConvert` | [`LambdaS/Notation.lean:106`](LambdaS/Notation.lean#L106) |
| Elaboration succeeds iff scalar of the target's dimension | `LambdaS.elabConvert_isSome` | [`LambdaS/Notation.lean:119`](LambdaS/Notation.lean#L119) |
| The state-vector literal | `LambdaS.Examples.stateVec` | [`LambdaS/Examples.lean:827`](LambdaS/Examples.lean#L827) |
| A matrix literal, rank-one checked at introduction | `LambdaS.Examples.toTime` | [`LambdaS/Examples.lean:849`](LambdaS/Examples.lean#L849) |

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
| The yard set is satisfiable | `LambdaS.Examples.yard_satisfiable` | [`LambdaS/Examples.lean:526`](LambdaS/Examples.lean#L526) |
| The mistyped yard set is refuted | `LambdaS.Examples.yard_conflict` | [`LambdaS/Examples.lean:480`](LambdaS/Examples.lean#L480) |
| The redundant factor is forced | `LambdaS.Examples.yard_forced` | [`LambdaS/Examples.lean:468`](LambdaS/Examples.lean#L468) |

## Dynamics

| Paper claim | Lean name | Location |
|---|---|---|
| Unit soundness (Theorem 4.1) | `LambdaS.unit_soundness_total` | [`LambdaS/Normalization.lean:621`](LambdaS/Normalization.lean#L621) |
| Matrix literals evaluate to matrices at their spaces | `LambdaS.lin_soundness_total` | [`LambdaS/Normalization.lean:634`](LambdaS/Normalization.lean#L634) |
| Totality at every type | `LambdaS.eval_total` | [`LambdaS/Normalization.lean:604`](LambdaS/Normalization.lean#L604) |
| Fuel accounting, checked by the binary | `LambdaS.QM.twoStateChecks` | [`LambdaS/QM.lean:368`](LambdaS/QM.lean#L368) |

## Denotational semantics and abstraction

| Paper claim | Lean name | Location |
|---|---|---|
| Convert-free terms ignore the valuation | `LambdaS.den_eq_of_convertFree` | [`LambdaS/Fundamental.lean:727`](LambdaS/Fundamental.lean#L727) |
| Valuation independence at higher type | `LambdaS.den_indep` | [`LambdaS/Fundamental.lean:649`](LambdaS/Fundamental.lean#L649) |
| Abstraction, convert-free (Theorem 5.1) | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:879`](LambdaS/Fundamental.lean#L879) |
| Abstraction, coherent (Theorem 5.2) | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:746`](LambdaS/Fundamental.lean#L746) |
| Theorem 5.2 at a moving rescaling | `LambdaS.Examples.fundamental_at_moving_rescale` | [`LambdaS/Examples.lean:805`](LambdaS/Examples.lean#L805) |
| The root scaling identity, all reals, positive factor | `LambdaS.mul_rpow_of_pos_left` | [`LambdaS/Parametricity.lean:364`](LambdaS/Parametricity.lean#L364) |
| The abstraction theorem at a root term | `LambdaS.sqrt_scales` | [`LambdaS/Fundamental.lean:1176`](LambdaS/Fundamental.lean#L1176) |
| The price is exact (Theorem 5.3) | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:1021`](LambdaS/Fundamental.lean#L1021) |
| Coherent equals factoring through dimension | `LambdaS.Scaling.coherent_iff_factors` | [`LambdaS/Conversion.lean:450`](LambdaS/Conversion.lean#L450) |

## Accumulated ratios and the drift diagnostic

| Paper claim | Lean name | Location |
|---|---|---|
| Shapes (Figure 5) | `LambdaS.Shape` | [`LambdaS/Ratio.lean:56`](LambdaS/Ratio.lean#L56) |
| Ratio expressions (Figure 5) | `LambdaS.Tw` | [`LambdaS/Ratio.lean:140`](LambdaS/Ratio.lean#L140) |
| Semantic ratios (Figure 5) | `LambdaS.SemTw` | [`LambdaS/Ratio.lean:213`](LambdaS/Ratio.lean#L213) |
| Ratio evaluation (Figure 5) | `LambdaS.Tw.eval` | [`LambdaS/Ratio.lean:237`](LambdaS/Ratio.lean#L237) |
| The scaling law, twisted (Theorem 6.1) | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:248`](LambdaS/Twist.lean#L248) |
| Invariance iff trivial ratio | `LambdaS.Twist.invariant_iff` | [`LambdaS/Twist.lean:556`](LambdaS/Twist.lean#L556) |
| Decidability (Theorem 6.2) | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:580`](LambdaS/Twist.lean#L580) |
| The diagnostic's specification | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:1163`](LambdaS/Twist.lean#L1163) |
| Branch comparison at `+` | `LambdaS.Tw.scalarEq` | [`LambdaS/Twist.lean:929`](LambdaS/Twist.lean#L929) |
| Reassociated conversions accepted | `LambdaS.Examples.addAssoc` | [`LambdaS/Examples.lean:684`](LambdaS/Examples.lean#L684) |
| Drift-free programs are declaration-independent | `LambdaS.evalC_indep_of_driftFree` | [`LambdaS/Twist.lean:1215`](LambdaS/Twist.lean#L1215) |

| The ballistics case study (four verdicts) | `LambdaS.Examples.Ballistics` | [`LambdaS/Examples.lean:1011`](LambdaS/Examples.lean#L1011) |

## Adequacy and erasure

| Paper claim | Lean name | Location |
|---|---|---|
| Adequacy at the declared factors | `LambdaS.eval_adeq` | [`LambdaS/Adequacy.lean:338`](LambdaS/Adequacy.lean#L338) |
| Declared factors reach the compiled evaluator (Theorem 7.1) | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:782`](LambdaS/Adequacy.lean#L782) |
| Erasure simulation, no typing hypothesis (Theorem 7.2) | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:198`](LambdaS/Erasure.lean#L198) |
| Erasure correctness | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:387`](LambdaS/Erasure.lean#L387) |
| The erased evaluator computes the denotation | `LambdaS.eeval_den` | [`LambdaS/Erasure.lean:399`](LambdaS/Erasure.lean#L399) |
| One yard is three feet, at the evaluator | `LambdaS.Examples.one_yard_is_three_feet` | [`LambdaS/Examples.lean:534`](LambdaS/Examples.lean#L534) |
| One yard is 0.9144 meters, both routes | `LambdaS.Examples.one_yard_in_metres` | [`LambdaS/Examples.lean:545`](LambdaS/Examples.lean#L545) |

## Dimensional analysis

| Paper claim | Lean name | Location |
|---|---|---|
| Conversion not definable convert-free | `LambdaS.NonDef.convert_not_definable` | [`LambdaS/NonDefinability.lean:338`](LambdaS/NonDefinability.lean#L338) |
| Square root not definable by arithmetic | `LambdaS.NonDef.sqrt_not_definable` | [`LambdaS/NonDefinability.lean:147`](LambdaS/NonDefinability.lean#L147) |
| The reflection into the arithmetic grammar | `LambdaS.NonDef.arith_of_hasTy` | [`LambdaS/NonDefinability.lean:200`](LambdaS/NonDefinability.lean#L200) |
| Square root not definable, at the term grammar | `LambdaS.NonDef.sqrt_not_definable_tm` | [`LambdaS/NonDefinability.lean:245`](LambdaS/NonDefinability.lean#L245) |
| No seed for Newton's method | `LambdaS.NonDef.no_newton_seed` | [`LambdaS/NonDefinability.lean:155`](LambdaS/NonDefinability.lean#L155) |
| No seed, at the term grammar | `LambdaS.NonDef.no_newton_seed_tm` | [`LambdaS/NonDefinability.lean:256`](LambdaS/NonDefinability.lean#L256) |
| The multiplicative scale law (definition) | `LambdaS.Pi.MulScaleLaw` | [`LambdaS/PiTheorem.lean:220`](LambdaS/PiTheorem.lean#L220) |
| Term-level multiplicative scale law | `LambdaS.Pi.den_mulScaleLaw` | [`LambdaS/PiTheorem.lean:375`](LambdaS/PiTheorem.lean#L375) |
| Log transport, positivity hypothesis | `LambdaS.Pi.scaleLaw_of_mulScaleLaw` | [`LambdaS/PiTheorem.lean:249`](LambdaS/PiTheorem.lean#L249) |
| Pi (Theorem 8.1) | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:92`](LambdaS/PiTheorem.lean#L92) |
| Pi, multiplicative coordinates | `LambdaS.Pi.mulScaleLaw_factorization` | [`LambdaS/PiTheorem.lean:273`](LambdaS/PiTheorem.lean#L273) |
| Invariants are the dimensionless monomials | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:119`](LambdaS/PiTheorem.lean#L119) |
| Buckingham's counting | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:142`](LambdaS/PiTheorem.lean#L142) |
| The factorization is an equivalence | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:182`](LambdaS/PiTheorem.lean#L182) |
| The pendulum signature | `LambdaS.Pi.pendulum` | [`LambdaS/Pi.lean:133`](LambdaS/Pi.lean#L133) |
| The pendulum solution exhibited | `LambdaS.Pi.pendulum_period_solution` | [`LambdaS/Pi.lean:161`](LambdaS/Pi.lean#L161) |
| The pendulum ignores its mass | `LambdaS.Pi.pendulum_mass_absent` | [`LambdaS/PiTheorem.lean:399`](LambdaS/PiTheorem.lean#L399) |
| A once-appearing base unit forces zero in every invariant | `LambdaS.Pi.eq_zero_of_appears_once` | [`LambdaS/Pi.lean:101`](LambdaS/Pi.lean#L101) |
| A once-appearing base unit forces a zero exponent | `LambdaS.Pi.solution_eq_zero_of_appears_once` | [`LambdaS/Pi.lean:118`](LambdaS/Pi.lean#L118) |

## Dimensioned linear algebra

| Paper claim | Lean name | Location |
|---|---|---|
| Entry units (definition) | `LambdaS.entry` | [`LambdaS/Map.lean:44`](LambdaS/Map.lean#L44) |
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

## The quantum-mechanics appendix

| Paper claim | Lean name | Location |
|---|---|---|
| The ground-state energy is an energy | `LambdaS.QM.groundEnergy` | [`LambdaS/QM.lean:87`](LambdaS/QM.lean#L87) |
| The uncertainty product is dimensionless | `LambdaS.QM.uncertainty` | [`LambdaS/QM.lean:113`](LambdaS/QM.lean#L113) |
| The amplitude carries m^(-1/2) | `LambdaS.QM.amplitude` | [`LambdaS/QM.lean:122`](LambdaS/QM.lean#L122) |
| The squared amplitude is a density | `LambdaS.QM.density` | [`LambdaS/QM.lean:134`](LambdaS/QM.lean#L134) |
| Density times length is dimensionless | `LambdaS.QM.probability` | [`LambdaS/QM.lean:140`](LambdaS/QM.lean#L140) |
| The expectation of the Hamiltonian is an energy | `LambdaS.QM.expectH` | [`LambdaS/QM.lean:237`](LambdaS/QM.lean#L237) |
| The state literal, parametric | `LambdaS.QM.statePlusTm` | [`LambdaS/QM.lean:281`](LambdaS/QM.lean#L281) |
| The Hamiltonian literal, not parametric | `LambdaS.QM.hamiltonianTm` | [`LambdaS/QM.lean:290`](LambdaS/QM.lean#L290) |
| The phase is dimensionless; `exp` accepts it | `LambdaS.QM.phase` | [`LambdaS/QM.lean:333`](LambdaS/QM.lean#L333) |
| The expectation as a curried function | `LambdaS.QM.expectation` | [`LambdaS/QM.lean:350`](LambdaS/QM.lean#L350) |

## Reproducing the worked examples

`lake exe lambdas` prints the declared-conversion report (100 yards as
300 ft, as 91.44 m directly, and as 91.44 m through feet: path independence
made observable), followed by the quantum-mechanics and free-fall reports
with their numeric self-checks. The same three yard numbers are asserted at
build time by `#guard`s in `LambdaS/Algorithms.lean`; the `#guard`s there
and in `LambdaS/Examples.lean` and `LambdaS/QM.lean` run the checker, the
drift analysis, and the evaluator during `lake build`, so a wrong stated
result would fail the build.

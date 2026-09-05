# Theorem index

Every artifact identifier the accompanying paper cites, with its Lean name
and location. Line numbers are for the commit that carries this file.
`scripts/Audit.lean` prints the axiom dependencies of the theorems below;
CI fails if any depends on more than `propext`, `Classical.choice`, and
`Quot.sound`.

## The calculus and its checker

| Paper claim | Lean name | Location |
|---|---|---|
| Typing rules (Figure 2) | `LambdaS.HasTy` | [`LambdaS/Typing.lean:564`](LambdaS/Typing.lean#L564) |
| Completeness; derivations unique | `LambdaS.check_eq` | [`LambdaS/Typing.lean:752`](LambdaS/Typing.lean#L752) |
| The generic caster is well-typed | `LambdaS.Examples.caster` | [`LambdaS/Examples.lean:924`](LambdaS/Examples.lean#L924) |
| The velocity idiom | `LambdaS.Examples.velocity` | [`LambdaS/Examples.lean:96`](LambdaS/Examples.lean#L96) |
| Surface `in` elaborates by running the checker | `LambdaS.elabConvert` | [`LambdaS/Notation.lean:106`](LambdaS/Notation.lean#L106) |
| Elaboration succeeds iff scalar of the target's dimension | `LambdaS.elabConvert_isSome` | [`LambdaS/Notation.lean:119`](LambdaS/Notation.lean#L119) |
| The state-vector literal | `LambdaS.Examples.stateVec` | [`LambdaS/Examples.lean:1087`](LambdaS/Examples.lean#L1087) |
| A matrix literal, rank-one checked at introduction | `LambdaS.Examples.toTime` | [`LambdaS/Examples.lean:1109`](LambdaS/Examples.lean#L1109) |

## Unit declarations

| Paper claim | Lean name | Location |
|---|---|---|
| Consistency, necessity (log form) | `LambdaS.dependency_forces` | [`LambdaS/Declare.lean:366`](LambdaS/Declare.lean#L366) |
| Consistency, necessity (product form) | `LambdaS.dependency_forces_mul` | [`LambdaS/Declare.lean:397`](LambdaS/Declare.lean#L397) |
| Consistency, sufficiency | `LambdaS.dependency_sufficient` | [`LambdaS/Declare.lean:439`](LambdaS/Declare.lean#L439) |
| Consistency characterized (log form) | `LambdaS.consistent_iff_dependencies` | [`LambdaS/Declare.lean:467`](LambdaS/Declare.lean#L467) |
| Consistency characterized (Theorem 3.1) | `LambdaS.consistent_iff_dependencies_mul` | [`LambdaS/Declare.lean:481`](LambdaS/Declare.lean#L481) |
| Redundant factor forced | `LambdaS.factor_chain_consistent` | [`LambdaS/Declare.lean:545`](LambdaS/Declare.lean#L545) |
| One-dimension well-formedness | `LambdaS.Decl.Sound` | [`LambdaS/Declare.lean:319`](LambdaS/Declare.lean#L319) |
| The yard set is satisfiable | `LambdaS.Examples.yard_satisfiable` | [`LambdaS/Examples.lean:578`](LambdaS/Examples.lean#L578) |
| A benign declaration cycle is satisfiable | `LambdaS.Examples.cycle_satisfiable` | [`LambdaS/Examples.lean:608`](LambdaS/Examples.lean#L608) |
| Dimension abbreviations elaborate by scoping alone | `LambdaS.DimAbbrev.elabDimDefs` | [`LambdaS/Declare.lean:589`](LambdaS/Declare.lean#L589) |
| Primary units: the declaration determines the dimension | `LambdaS.DimAbbrev.elabPrimary` | [`LambdaS/Declare.lean:600`](LambdaS/Declare.lean#L600) |
| The cyclic dimension pair, rejected at its second line | `LambdaS.Examples.dimCycle` | [`LambdaS/Examples.lean:509`](LambdaS/Examples.lean#L509) |
| A vicious declaration cycle is rejected | `LambdaS.Examples.cycle_conflict` | [`LambdaS/Examples.lean:614`](LambdaS/Examples.lean#L614) |
| The mistyped yard set is refuted | `LambdaS.Examples.yard_conflict` | [`LambdaS/Examples.lean:480`](LambdaS/Examples.lean#L480) |
| One yard per foot denotes 1, at yd/ft | `LambdaS.Algorithms.ydPerFt` | [`LambdaS/Algorithms.lean:242`](LambdaS/Algorithms.lean#L242) |
| Converted to unit 1, the declared 3 appears | `LambdaS.Algorithms.ydPerFtIn1` | [`LambdaS/Algorithms.lean:251`](LambdaS/Algorithms.lean#L251) |
| The redundant factor is forced | `LambdaS.Examples.yard_forced` | [`LambdaS/Examples.lean:468`](LambdaS/Examples.lean#L468) |

## Dynamics

| Paper claim | Lean name | Location |
|---|---|---|
| Preservation: a produced value has the predicted type | `LambdaS.eval_sound` | [`LambdaS/Soundness.lean:214`](LambdaS/Soundness.lean#L214) |
| Unit soundness (Theorem 4.1) | `LambdaS.unit_soundness_total` | [`LambdaS/Normalization.lean:716`](LambdaS/Normalization.lean#L716) |
| Matrix literals evaluate to matrices at their spaces | `LambdaS.lin_soundness_total` | [`LambdaS/Normalization.lean:729`](LambdaS/Normalization.lean#L729) |
| Totality at every type | `LambdaS.eval_total` | [`LambdaS/Normalization.lean:699`](LambdaS/Normalization.lean#L699) |
| Fuel accounting, checked by the binary | `LambdaS.QM.twoStateChecks` | [`LambdaS/QM.lean:378`](LambdaS/QM.lean#L378) |

## Denotational semantics and abstraction

| Paper claim | Lean name | Location |
|---|---|---|
| Convert-free terms ignore the valuation | `LambdaS.den_eq_of_convertFree` | [`LambdaS/Fundamental.lean:934`](LambdaS/Fundamental.lean#L934) |
| Valuation independence at higher type | `LambdaS.den_indep` | [`LambdaS/Fundamental.lean:856`](LambdaS/Fundamental.lean#L856) |
| Abstraction, convert-free (Theorem 5.1) | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:1086`](LambdaS/Fundamental.lean#L1086) |
| Abstraction, coherent (Theorem 5.2) | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:953`](LambdaS/Fundamental.lean#L953) |
| Theorem 5.2 at a moving rescaling | `LambdaS.Examples.fundamental_at_moving_rescale` | [`LambdaS/Examples.lean:1065`](LambdaS/Examples.lean#L1065) |
| The root scaling identity, all reals, positive factor | `LambdaS.mul_rpow_of_pos_left` | [`LambdaS/Parametricity.lean:364`](LambdaS/Parametricity.lean#L364) |
| The abstraction theorem at a root term | `LambdaS.sqrt_scales` | [`LambdaS/Fundamental.lean:1383`](LambdaS/Fundamental.lean#L1383) |
| The price is exact (Theorem 5.3) | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:1228`](LambdaS/Fundamental.lean#L1228) |
| Coherent equals factoring through dimension | `LambdaS.Scaling.coherent_iff_factors` | [`LambdaS/Conversion.lean:450`](LambdaS/Conversion.lean#L450) |

## Accumulated ratios and the drift diagnostic

| Paper claim | Lean name | Location |
|---|---|---|
| Shapes (Figure 3) | `LambdaS.Shape` | [`LambdaS/Ratio.lean:200`](LambdaS/Ratio.lean#L200) |
| Ratio expressions (Figure 3) | `LambdaS.Tw` | [`LambdaS/Ratio.lean:290`](LambdaS/Ratio.lean#L290) |
| Semantic ratios (Figure 3) | `LambdaS.SemTw` | [`LambdaS/Ratio.lean:491`](LambdaS/Ratio.lean#L491) |
| Ratio evaluation (Figure 3) | `LambdaS.Tw.eval` | [`LambdaS/Ratio.lean:515`](LambdaS/Ratio.lean#L515) |
| The scaling law, twisted (Theorem 6.1) | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:627`](LambdaS/Twist.lean#L627) |
| Invariance iff trivial ratio | `LambdaS.Twist.invariant_iff` | [`LambdaS/Twist.lean:964`](LambdaS/Twist.lean#L964) |
| Decidability (Theorem 6.2) | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:988`](LambdaS/Twist.lean#L988) |
| The diagnostic's specification | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:1674`](LambdaS/Twist.lean#L1674) |
| Branch comparison at `+` | `LambdaS.Tw.scalarEq` | [`LambdaS/Twist.lean:1350`](LambdaS/Twist.lean#L1350) |
| Reassociated conversions accepted | `LambdaS.Examples.addAssoc` | [`LambdaS/Examples.lean:881`](LambdaS/Examples.lean#L881) |
| Drift-free programs are declaration-independent | `LambdaS.evalC_indep_of_driftFree` | [`LambdaS/Twist.lean:1746`](LambdaS/Twist.lean#L1746) |

| The ballistics case study (four verdicts) | `LambdaS.Examples.Ballistics` | [`LambdaS/Examples.lean:1297`](LambdaS/Examples.lean#L1297) |

| Sum of two converted inputs, accepted at m/ft | `LambdaS.Examples.addTwoVars` | [`LambdaS/Examples.lean:779`](LambdaS/Examples.lean#L779) |
| Genuinely drifting sum, declined | `LambdaS.Examples.addMixed` | [`LambdaS/Examples.lean:793`](LambdaS/Examples.lean#L793) |
| A visible application analyzes as its redex | `LambdaS.Examples.betaShared` | [`LambdaS/Examples.lean:848`](LambdaS/Examples.lean#L848) |
| Polymorphic round trip, drift-free uninstantiated | `LambdaS.Examples.casterRound` | [`LambdaS/Examples.lean:990`](LambdaS/Examples.lean#L990) |
| Leading lambda binders analyzed as inputs | `LambdaS.unitDriftLam` | [`LambdaS/Twist.lean:1697`](LambdaS/Twist.lean#L1697) |
| Comparison exact for atom-free ratios (iff) | `LambdaS.Tw.scalarEq_iff_eval_eq` | [`LambdaS/Twist.lean:1466`](LambdaS/Twist.lean#L1466) |

| log of a round-trip ratio, accepted at drift 1 | `LambdaS.Examples.logRoundTrip` | [`LambdaS/Examples.lean:821`](LambdaS/Examples.lean#L821) |
| log of a drifting argument, declined | `LambdaS.Examples.logDrifting` | [`LambdaS/Examples.lean:834`](LambdaS/Examples.lean#L834) |

## Adequacy and erasure

| Paper claim | Lean name | Location |
|---|---|---|
| Adequacy at the declared factors | `LambdaS.eval_adeq` | [`LambdaS/Adequacy.lean:338`](LambdaS/Adequacy.lean#L338) |
| Declared factors reach the compiled evaluator (Theorem 7.1) | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:782`](LambdaS/Adequacy.lean#L782) |
| Erasure simulation, no typing hypothesis (Theorem 7.2) | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:293`](LambdaS/Erasure.lean#L293) |
| Erasure correctness | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:482`](LambdaS/Erasure.lean#L482) |
| The erased evaluator computes the denotation | `LambdaS.eeval_den` | [`LambdaS/Erasure.lean:494`](LambdaS/Erasure.lean#L494) |
| One yard is three feet, at the evaluator | `LambdaS.Examples.one_yard_is_three_feet` | [`LambdaS/Examples.lean:632`](LambdaS/Examples.lean#L632) |
| One yard is 0.9144 meters, both routes | `LambdaS.Examples.one_yard_in_metres` | [`LambdaS/Examples.lean:643`](LambdaS/Examples.lean#L643) |

## Dimensional analysis

| Paper claim | Lean name | Location |
|---|---|---|
| Conversion not definable convert-free | `LambdaS.NonDef.convert_not_definable` | [`LambdaS/NonDefinability.lean:406`](LambdaS/NonDefinability.lean#L406) |
| Square root not definable by arithmetic | `LambdaS.NonDef.sqrt_not_definable` | [`LambdaS/NonDefinability.lean:215`](LambdaS/NonDefinability.lean#L215) |
| The reflection into the arithmetic grammar | `LambdaS.NonDef.arith_of_hasTy` | [`LambdaS/NonDefinability.lean:268`](LambdaS/NonDefinability.lean#L268) |
| Square root not definable, at the term grammar | `LambdaS.NonDef.sqrt_not_definable_tm` | [`LambdaS/NonDefinability.lean:313`](LambdaS/NonDefinability.lean#L313) |
| No seed for Newton's method | `LambdaS.NonDef.no_newton_seed` | [`LambdaS/NonDefinability.lean:223`](LambdaS/NonDefinability.lean#L223) |
| No seed, at the term grammar | `LambdaS.NonDef.no_newton_seed_tm` | [`LambdaS/NonDefinability.lean:324`](LambdaS/NonDefinability.lean#L324) |
| The multiplicative scale law (definition) | `LambdaS.Pi.MulScaleLaw` | [`LambdaS/PiTheorem.lean:413`](LambdaS/PiTheorem.lean#L413) |
| Term-level multiplicative scale law | `LambdaS.Pi.den_mulScaleLaw` | [`LambdaS/PiTheorem.lean:808`](LambdaS/PiTheorem.lean#L808) |
| Log transport, positivity hypothesis | `LambdaS.Pi.scaleLaw_of_mulScaleLaw` | [`LambdaS/PiTheorem.lean:670`](LambdaS/PiTheorem.lean#L670) |
| Pi (Theorem 8.1) | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:278`](LambdaS/PiTheorem.lean#L278) |
| Pi, multiplicative coordinates | `LambdaS.Pi.mulScaleLaw_factorization` | [`LambdaS/PiTheorem.lean:522`](LambdaS/PiTheorem.lean#L522) |
| Invariants are the dimensionless monomials | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:305`](LambdaS/PiTheorem.lean#L305) |
| Buckingham's counting | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:328`](LambdaS/PiTheorem.lean#L328) |
| The factorization is an equivalence | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:368`](LambdaS/PiTheorem.lean#L368) |
| The pendulum signature | `LambdaS.Pi.pendulum` | [`LambdaS/Pi.lean:137`](LambdaS/Pi.lean#L137) |
| The pendulum solution exhibited | `LambdaS.Pi.pendulum_period_solution` | [`LambdaS/Pi.lean:165`](LambdaS/Pi.lean#L165) |
| The pendulum ignores its mass | `LambdaS.Pi.pendulum_mass_absent` | [`LambdaS/PiTheorem.lean:834`](LambdaS/PiTheorem.lean#L834) |
| A once-appearing base unit forces zero in every invariant | `LambdaS.Pi.eq_zero_of_appears_once` | [`LambdaS/Pi.lean:105`](LambdaS/Pi.lean#L105) |
| A once-appearing base unit forces a zero exponent | `LambdaS.Pi.solution_eq_zero_of_appears_once` | [`LambdaS/Pi.lean:122`](LambdaS/Pi.lean#L122) |

| Signed equivalence, multiplicative coordinates | `LambdaS.Pi.piEquivSigned` | [`LambdaS/PiTheorem.lean:476`](LambdaS/PiTheorem.lean#L476) |
| Unsolvable signatures admit only zero | `LambdaS.Pi.mulScaleLaw_eq_zero_of_unsolvable` | [`LambdaS/PiTheorem.lean:615`](LambdaS/PiTheorem.lean#L615) |
| The solvability dichotomy | `LambdaS.Pi.mulScaleLaw_dichotomy` | [`LambdaS/PiTheorem.lean:643`](LambdaS/PiTheorem.lean#L643) |

## Dimensioned linear algebra

| Paper claim | Lean name | Location |
|---|---|---|
| Entry units (definition) | `LambdaS.entry` | [`LambdaS/Map.lean:170`](LambdaS/Map.lean#L170) |
| Rank-one units (Theorem 9.1) | `LambdaS.entry_rank_one` | [`LambdaS/Map.lean:182`](LambdaS/Map.lean#L182) |
| Composition entry units | `LambdaS.entry_comp` | [`LambdaS/Map.lean:193`](LambdaS/Map.lean#L193) |
| Endomorphism diagonals dimensionless | `LambdaS.entry_id_diag` | [`LambdaS/Map.lean:220`](LambdaS/Map.lean#L220) |
| Permutation products dimensionless | `LambdaS.entry_perm_prod` | [`LambdaS/Map.lean:208`](LambdaS/Map.lean#L208) |
| Eigenvalue unit identity | `LambdaS.eigenvalue_uom` | [`LambdaS/Map.lean:250`](LambdaS/Map.lean#L250) |
| Dual-map entries symmetric | `LambdaS.entry_dual_symm` | [`LambdaS/Map.lean:257`](LambdaS/Map.lean#L257) |
| Weighted norms dimensionless | `LambdaS.weighted_norm_dimensionless` | [`LambdaS/Map.lean:262`](LambdaS/Map.lean#L262) |
| Cholesky factors dimensionless | `LambdaS.cholesky_factor_dimensionless` | [`LambdaS/Map.lean:272`](LambdaS/Map.lean#L272) |
| Uniform spaces are scaled dimensionless spaces | `LambdaS.Space.uniform_iff_scale_triv` | [`LambdaS/Space.lean:91`](LambdaS/Space.lean#L91) |
| SVD entries share one unit | `LambdaS.svd_entry_const` | [`LambdaS/Map.lean:288`](LambdaS/Map.lean#L288) |
| Self-dual spaces are dimensionless | `LambdaS.transpose_comp_direct_iff` | [`LambdaS/Map.lean:302`](LambdaS/Map.lean#L302) |
| Uniform spaces carry a canonical metric | `LambdaS.uniform_canonical_metric` | [`LambdaS/Map.lean:315`](LambdaS/Map.lean#L315) |

## The quantum-mechanics appendix

| Paper claim | Lean name | Location |
|---|---|---|
| The ground-state energy is an energy | `LambdaS.QM.groundEnergy` | [`LambdaS/QM.lean:97`](LambdaS/QM.lean#L97) |
| The uncertainty product is dimensionless | `LambdaS.QM.uncertainty` | [`LambdaS/QM.lean:123`](LambdaS/QM.lean#L123) |
| The amplitude carries m^(-1/2) | `LambdaS.QM.amplitude` | [`LambdaS/QM.lean:132`](LambdaS/QM.lean#L132) |
| The squared amplitude is a density | `LambdaS.QM.density` | [`LambdaS/QM.lean:144`](LambdaS/QM.lean#L144) |
| Density times length is dimensionless | `LambdaS.QM.probability` | [`LambdaS/QM.lean:150`](LambdaS/QM.lean#L150) |
| The expectation of the Hamiltonian is an energy | `LambdaS.QM.expectH` | [`LambdaS/QM.lean:247`](LambdaS/QM.lean#L247) |
| The state literal, parametric | `LambdaS.QM.statePlusTm` | [`LambdaS/QM.lean:291`](LambdaS/QM.lean#L291) |
| The Hamiltonian literal, not parametric | `LambdaS.QM.hamiltonianTm` | [`LambdaS/QM.lean:300`](LambdaS/QM.lean#L300) |
| The phase is dimensionless; `exp` accepts it | `LambdaS.QM.phase` | [`LambdaS/QM.lean:343`](LambdaS/QM.lean#L343) |
| The expectation as a curried function | `LambdaS.QM.expectation` | [`LambdaS/QM.lean:360`](LambdaS/QM.lean#L360) |

## Reproducing the worked examples

`lake exe lambdas` prints the declared-conversion report (100 yards as
300 ft, as 91.44 m directly, and as 91.44 m through feet: path independence
made observable), followed by the quantum-mechanics and free-fall reports
with their numeric self-checks. The same three yard numbers are asserted at
build time by `#guard`s in `LambdaS/Algorithms.lean`; the `#guard`s there
and in `LambdaS/Examples.lean` and `LambdaS/QM.lean` run the checker, the
drift analysis, and the evaluator during `lake build`, so a wrong stated
result would fail the build.

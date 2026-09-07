# Theorem index

Every artifact identifier the accompanying paper cites, and the supporting
results behind them, with Lean name and location. Line numbers are for the commit that carries this file.
`scripts/Audit.lean` prints the axiom dependencies of every declaration below
(`scripts/verify_theorems_index.py` fails if one is missing from it); CI fails
if any depends on more than `propext`, `Classical.choice`, and `Quot.sound`.

## The calculus and its checker

| Paper claim | Lean name | Location |
|---|---|---|
| Typing rules (Figure 2) | `LambdaS.HasTy` | [`LambdaS/Typing.lean:445`](LambdaS/Typing.lean#L445) |
| Completeness; derivations unique | `LambdaS.check_eq` | [`LambdaS/Typing.lean:673`](LambdaS/Typing.lean#L673) |
| The generic caster is well-typed | `LambdaS.Examples.caster` | [`LambdaS/Examples.lean:1006`](LambdaS/Examples.lean#L1006) |
| The velocity idiom | `LambdaS.Examples.velocity` | [`LambdaS/Examples.lean:97`](LambdaS/Examples.lean#L97) |
| Surface `in` elaborates by running the checker | `LambdaS.elabConvert` | [`LambdaS/Notation.lean:110`](LambdaS/Notation.lean#L110) |
| Elaboration succeeds iff scalar of the target's dimension | `LambdaS.elabConvert_isSome` | [`LambdaS/Notation.lean:123`](LambdaS/Notation.lean#L123) |
| The state-vector literal | `LambdaS.Examples.stateVec` | [`LambdaS/Examples.lean:1169`](LambdaS/Examples.lean#L1169) |
| A matrix literal, rank-one checked at introduction | `LambdaS.Examples.toTime` | [`LambdaS/Examples.lean:1191`](LambdaS/Examples.lean#L1191) |

## Unit declarations

| Paper claim | Lean name | Location |
|---|---|---|
| Consistency, necessity (log form) | `LambdaS.dependency_forces` | [`LambdaS/Declare.lean:361`](LambdaS/Declare.lean#L361) |
| Consistency, necessity (product form) | `LambdaS.dependency_forces_mul` | [`LambdaS/Declare.lean:392`](LambdaS/Declare.lean#L392) |
| Consistency, sufficiency | `LambdaS.dependency_sufficient` | [`LambdaS/Declare.lean:434`](LambdaS/Declare.lean#L434) |
| Consistency characterized (log form) | `LambdaS.consistent_iff_dependencies` | [`LambdaS/Declare.lean:462`](LambdaS/Declare.lean#L462) |
| Consistency characterized (Theorem 3.1) | `LambdaS.consistent_iff_dependencies_mul` | [`LambdaS/Declare.lean:476`](LambdaS/Declare.lean#L476) |
| Redundant factor forced | `LambdaS.factor_chain_consistent` | [`LambdaS/Declare.lean:540`](LambdaS/Declare.lean#L540) |
| One-dimension well-formedness | `LambdaS.Decl.Sound` | [`LambdaS/Declare.lean:314`](LambdaS/Declare.lean#L314) |
| The yard set is satisfiable | `LambdaS.Examples.yard_satisfiable` | [`LambdaS/Examples.lean:582`](LambdaS/Examples.lean#L582) |
| A benign declaration cycle is satisfiable | `LambdaS.Examples.cycle_satisfiable` | [`LambdaS/Examples.lean:612`](LambdaS/Examples.lean#L612) |
| Dimension abbreviations elaborate by scoping alone | `LambdaS.DimAbbrev.elabDimDefs` | [`LambdaS/Declare.lean:584`](LambdaS/Declare.lean#L584) |
| Primary units: the declaration determines the dimension | `LambdaS.DimAbbrev.elabPrimary` | [`LambdaS/Declare.lean:595`](LambdaS/Declare.lean#L595) |
| The cyclic dimension pair, rejected at its second line | `LambdaS.Examples.dimCycle` | [`LambdaS/Examples.lean:511`](LambdaS/Examples.lean#L511) |
| A vicious declaration cycle is rejected | `LambdaS.Examples.cycle_conflict` | [`LambdaS/Examples.lean:618`](LambdaS/Examples.lean#L618) |
| The mistyped yard set is refuted | `LambdaS.Examples.yard_conflict` | [`LambdaS/Examples.lean:481`](LambdaS/Examples.lean#L481) |
| One yard per foot denotes 1, at yd/ft | `LambdaS.Algorithms.ydPerFt` | [`LambdaS/Algorithms.lean:245`](LambdaS/Algorithms.lean#L245) |
| Converted to unit 1, the declared 3 appears | `LambdaS.Algorithms.ydPerFtIn1` | [`LambdaS/Algorithms.lean:254`](LambdaS/Algorithms.lean#L254) |
| Converting one operand first, the same 3 | `LambdaS.Algorithms.ydPerFtViaFt` | [`LambdaS/Algorithms.lean:266`](LambdaS/Algorithms.lean#L266) |
| The redundant factor is forced | `LambdaS.Examples.yard_forced` | [`LambdaS/Examples.lean:469`](LambdaS/Examples.lean#L469) |

## Dynamics

| Paper claim | Lean name | Location |
|---|---|---|
| Preservation: a produced value has the predicted type | `LambdaS.eval_sound` | [`LambdaS/Soundness.lean:214`](LambdaS/Soundness.lean#L214) |
| Unit soundness (Theorem 4.1) | `LambdaS.unit_soundness_total` | [`LambdaS/Normalization.lean:774`](LambdaS/Normalization.lean#L774) |
| Matrix literals evaluate to matrices at their spaces | `LambdaS.lin_soundness_total` | [`LambdaS/Normalization.lean:787`](LambdaS/Normalization.lean#L787) |
| Totality at every type | `LambdaS.eval_total` | [`LambdaS/Normalization.lean:759`](LambdaS/Normalization.lean#L759) |
| Fuel accounting, checked by the binary | `LambdaS.QM.twoStateChecks` | [`LambdaS/QM.lean:382`](LambdaS/QM.lean#L382) |

## Denotational semantics and abstraction

| Paper claim | Lean name | Location |
|---|---|---|
| Convert-free terms ignore the valuation | `LambdaS.den_eq_of_convertFree` | [`LambdaS/Fundamental.lean:950`](LambdaS/Fundamental.lean#L950) |
| Valuation independence at higher type | `LambdaS.den_indep` | [`LambdaS/Fundamental.lean:860`](LambdaS/Fundamental.lean#L860) |
| Abstraction, convert-free (Theorem 5.1) | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:1119`](LambdaS/Fundamental.lean#L1119) |
| Abstraction, coherent (Theorem 5.2) | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:969`](LambdaS/Fundamental.lean#L969) |
| Theorem 5.2 at a moving rescaling | `LambdaS.Examples.fundamental_at_moving_rescale` | [`LambdaS/Examples.lean:1147`](LambdaS/Examples.lean#L1147) |
| The root scaling identity, all reals, positive factor | `LambdaS.mul_rpow_of_pos_left` | [`LambdaS/Parametricity.lean:379`](LambdaS/Parametricity.lean#L379) |
| The abstraction theorem at a root term | `LambdaS.sqrt_scales` | [`LambdaS/Fundamental.lean:1433`](LambdaS/Fundamental.lean#L1433) |
| The price is exact (Theorem 5.3) | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:1278`](LambdaS/Fundamental.lean#L1278) |
| Coherent equals factoring through dimension | `LambdaS.Scaling.coherent_iff_factors` | [`LambdaS/Conversion.lean:454`](LambdaS/Conversion.lean#L454) |

## Accumulated ratios and the drift diagnostic

| Paper claim | Lean name | Location |
|---|---|---|
| Shapes | `LambdaS.Shape` | [`LambdaS/Ratio.lean:57`](LambdaS/Ratio.lean#L57) |
| Ratio expressions | `LambdaS.Tw` | [`LambdaS/Ratio.lean:147`](LambdaS/Ratio.lean#L147) |
| Semantic ratios | `LambdaS.SemTw` | [`LambdaS/Ratio.lean:348`](LambdaS/Ratio.lean#L348) |
| Ratio evaluation | `LambdaS.Tw.eval` | [`LambdaS/Ratio.lean:372`](LambdaS/Ratio.lean#L372) |
| The scaling law, twisted (two parameters) | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:623`](LambdaS/Twist.lean#L623) |
| The twisted law at first order | `LambdaS.Twist.law` | [`LambdaS/Twist.lean:957`](LambdaS/Twist.lean#L957) |
| The drift law (both parameters) | `LambdaS.unitDrift_law` | [`LambdaS/Twist.lean:2088`](LambdaS/Twist.lean#L2088) |
| Declared magnitudes enter through the drift alone | `LambdaS.den_comp_of_drift` | [`LambdaS/Twist.lean:2101`](LambdaS/Twist.lean#L2101) |
| Drift 1 is declaration independence, open programs at any unit | `LambdaS.den_indep_of_driftFree` | [`LambdaS/Twist.lean:2115`](LambdaS/Twist.lean#L2115) |
| Drift 1 gives the unrestricted scaling law | `LambdaS.scaleLaw_of_driftFree` | [`LambdaS/Twist.lean:2130`](LambdaS/Twist.lean#L2130) |
| Drift 1 gives the scaling law at a matrix result | `LambdaS.scaleLaw_lin_of_driftFree` | [`LambdaS/Twist.lean:1959`](LambdaS/Twist.lean#L1959) |
| The same over an arbitrary context | `LambdaS.scaleLaw_lin_of_driftFree_gen` | [`LambdaS/Twist.lean:1927`](LambdaS/Twist.lean#L1927) |
| Invariance iff trivial ratio (Theorem 6.1) | `LambdaS.Twist.invariant_iff` | [`LambdaS/Twist.lean:1050`](LambdaS/Twist.lean#L1050) |
| Decidability | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:1083`](LambdaS/Twist.lean#L1083) |
| The diagnostic's specification (Theorem 6.1) | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:1991`](LambdaS/Twist.lean#L1991) |
| Branch comparison at `+` (on normal forms) | `LambdaS.Tw.normEq` | [`LambdaS/Twist.lean:1578`](LambdaS/Twist.lean#L1578) |
| Branch comparison, flat form | `LambdaS.Tw.scalarEq` | [`LambdaS/Twist.lean:1445`](LambdaS/Twist.lean#L1445) |
| The β-normalizer for ratios | `LambdaS.Tw.norm` | [`LambdaS/Ratio.lean:503`](LambdaS/Ratio.lean#L503) |
| Normalization preserves evaluation | `LambdaS.Tw.eval_norm` | [`LambdaS/Ratio.lean:809`](LambdaS/Ratio.lean#L809) |
| Reassociated conversions accepted | `LambdaS.Examples.addAssoc` | [`LambdaS/Examples.lean:963`](LambdaS/Examples.lean#L963) |
| Drift-free closed programs are declaration-independent at the evaluator | `LambdaS.evalC_indep_of_driftFree` | [`LambdaS/Twist.lean:2143`](LambdaS/Twist.lean#L2143) |
| The ballistics case study (four verdicts) | `LambdaS.Examples.Ballistics` | [`LambdaS/Examples.lean:1426`](LambdaS/Examples.lean#L1426) |
| Sum of two converted inputs, accepted at m/ft | `LambdaS.Examples.addTwoVars` | [`LambdaS/Examples.lean:822`](LambdaS/Examples.lean#L822) |
| Genuinely drifting sum, declined | `LambdaS.Examples.addMixed` | [`LambdaS/Examples.lean:837`](LambdaS/Examples.lean#L837) |
| Agreeing sum through an internal abstraction, accepted | `LambdaS.Examples.hoSum` | [`LambdaS/Examples.lean:884`](LambdaS/Examples.lean#L884) |
| A visible application analyzes as its redex | `LambdaS.Examples.betaShared` | [`LambdaS/Examples.lean:928`](LambdaS/Examples.lean#L928) |
| Polymorphic round trip, drift-free uninstantiated | `LambdaS.Examples.casterRound` | [`LambdaS/Examples.lean:1072`](LambdaS/Examples.lean#L1072) |
| Leading lambda binders analyzed as inputs | `LambdaS.unitDriftLam` | [`LambdaS/Twist.lean:2014`](LambdaS/Twist.lean#L2014) |
| The stripped kernel is analyzed as an open term | `LambdaS.unitDriftLam_eq_unitDrift` | [`LambdaS/Twist.lean:2034`](LambdaS/Twist.lean#L2034) |
| The diagnostic through a leading abstraction, exact | `LambdaS.unitDriftLam_spec` | [`LambdaS/Twist.lean:2048`](LambdaS/Twist.lean#L2048) |
| Comparison exact for atom-free ratios (iff) | `LambdaS.Tw.normEq_iff_eval_eq` | [`LambdaS/Twist.lean:1612`](LambdaS/Twist.lean#L1612) |
| Flat comparison exact for atom-free ratios (iff) | `LambdaS.Tw.scalarEq_iff_eval_eq` | [`LambdaS/Twist.lean:1563`](LambdaS/Twist.lean#L1563) |
| log of a round-trip ratio, accepted at drift 1 | `LambdaS.Examples.logRoundTrip` | [`LambdaS/Examples.lean:901`](LambdaS/Examples.lean#L901) |
| log of a drifting argument, declined | `LambdaS.Examples.logDrifting` | [`LambdaS/Examples.lean:914`](LambdaS/Examples.lean#L914) |

## Adequacy and erasure

| Paper claim | Lean name | Location |
|---|---|---|
| Adequacy at the declared factors | `LambdaS.eval_adeq` | [`LambdaS/Adequacy.lean:338`](LambdaS/Adequacy.lean#L338) |
| Declared factors reach the compiled evaluator (Theorem 7.1) | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:841`](LambdaS/Adequacy.lean#L841) |
| Erasure simulation, no typing hypothesis (Theorem 7.2) | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:297`](LambdaS/Erasure.lean#L297) |
| Erasure correctness | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:511`](LambdaS/Erasure.lean#L511) |
| The erased evaluator computes the denotation | `LambdaS.eeval_den` | [`LambdaS/Erasure.lean:523`](LambdaS/Erasure.lean#L523) |
| One yard is three feet, at the evaluator | `LambdaS.Examples.one_yard_is_three_feet` | [`LambdaS/Examples.lean:638`](LambdaS/Examples.lean#L638) |
| One yard is 0.9144 meters, directly | `LambdaS.Examples.one_yard_in_meters` | [`LambdaS/Examples.lean:649`](LambdaS/Examples.lean#L649) |
| One yard is 0.9144 meters, through feet | `LambdaS.Examples.one_yard_in_meters_via_feet` | [`LambdaS/Examples.lean:664`](LambdaS/Examples.lean#L664) |
| The two routes agree at the evaluator | `LambdaS.Examples.yard_routes_agree` | [`LambdaS/Examples.lean:687`](LambdaS/Examples.lean#L687) |

## Dimensional analysis

| Paper claim | Lean name | Location |
|---|---|---|
| Conversion not definable convert-free | `LambdaS.NonDef.convert_not_definable` | [`LambdaS/NonDefinability.lean:418`](LambdaS/NonDefinability.lean#L418) |
| Square root not definable by arithmetic | `LambdaS.NonDef.sqrt_not_definable` | [`LambdaS/NonDefinability.lean:227`](LambdaS/NonDefinability.lean#L227) |
| The reflection into the arithmetic grammar | `LambdaS.NonDef.arith_of_hasTy` | [`LambdaS/NonDefinability.lean:280`](LambdaS/NonDefinability.lean#L280) |
| Square root not definable, at the term grammar | `LambdaS.NonDef.sqrt_not_definable_tm` | [`LambdaS/NonDefinability.lean:325`](LambdaS/NonDefinability.lean#L325) |
| No seed for Newton's method | `LambdaS.NonDef.no_newton_seed` | [`LambdaS/NonDefinability.lean:235`](LambdaS/NonDefinability.lean#L235) |
| No seed, at the term grammar | `LambdaS.NonDef.no_newton_seed_tm` | [`LambdaS/NonDefinability.lean:336`](LambdaS/NonDefinability.lean#L336) |
| The multiplicative scale law (definition) | `LambdaS.Pi.MulScaleLaw` | [`LambdaS/PiTheorem.lean:408`](LambdaS/PiTheorem.lean#L408) |
| Term-level multiplicative scale law | `LambdaS.Pi.den_mulScaleLaw` | [`LambdaS/PiTheorem.lean:803`](LambdaS/PiTheorem.lean#L803) |
| Term-level scale law from drift 1 | `LambdaS.Pi.den_mulScaleLaw_driftFree` | [`LambdaS/PiTheorem.lean:826`](LambdaS/PiTheorem.lean#L826) |
| Log transport, positivity hypothesis | `LambdaS.Pi.scaleLaw_of_mulScaleLaw` | [`LambdaS/PiTheorem.lean:665`](LambdaS/PiTheorem.lean#L665) |
| Pi, the factorization | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:273`](LambdaS/PiTheorem.lean#L273) |
| Pi, multiplicative coordinates | `LambdaS.Pi.mulScaleLaw_factorization` | [`LambdaS/PiTheorem.lean:517`](LambdaS/PiTheorem.lean#L517) |
| Invariants are the dimensionless monomials | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:300`](LambdaS/PiTheorem.lean#L300) |
| Buckingham's counting (Theorem 8.1) | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:323`](LambdaS/PiTheorem.lean#L323) |
| The factorization is an equivalence | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:363`](LambdaS/PiTheorem.lean#L363) |
| The pendulum signature | `LambdaS.Pi.pendulum` | [`LambdaS/Pi.lean:138`](LambdaS/Pi.lean#L138) |
| The pendulum solution exhibited | `LambdaS.Pi.pendulum_period_solution` | [`LambdaS/Pi.lean:167`](LambdaS/Pi.lean#L167) |
| The pendulum ignores its mass, both halves | `LambdaS.Pi.pendulum_mass_absent` | [`LambdaS/PiTheorem.lean:851`](LambdaS/PiTheorem.lean#L851) |
| Mass is absent from every solution | `LambdaS.Pi.pendulum_period_independent_of_mass` | [`LambdaS/Pi.lean:156`](LambdaS/Pi.lean#L156) |
| Mass is absent from every dimensionless group | `LambdaS.Pi.pendulum_mass_drops_out` | [`LambdaS/Pi.lean:150`](LambdaS/Pi.lean#L150) |
| A once-appearing base unit forces zero in every invariant | `LambdaS.Pi.eq_zero_of_appears_once` | [`LambdaS/Pi.lean:106`](LambdaS/Pi.lean#L106) |
| A once-appearing base unit forces a zero exponent | `LambdaS.Pi.solution_eq_zero_of_appears_once` | [`LambdaS/Pi.lean:123`](LambdaS/Pi.lean#L123) |
| Signed equivalence, multiplicative coordinates | `LambdaS.Pi.piEquivSigned` | [`LambdaS/PiTheorem.lean:471`](LambdaS/PiTheorem.lean#L471) |
| Unsolvable signatures admit only zero | `LambdaS.Pi.mulScaleLaw_eq_zero_of_unsolvable` | [`LambdaS/PiTheorem.lean:610`](LambdaS/PiTheorem.lean#L610) |
| The solvability dichotomy (Theorem 8.1) | `LambdaS.Pi.mulScaleLaw_dichotomy` | [`LambdaS/PiTheorem.lean:638`](LambdaS/PiTheorem.lean#L638) |

## Dimensioned linear algebra

| Paper claim | Lean name | Location |
|---|---|---|
| Entry units (definition) | `LambdaS.entry` | [`LambdaS/Map.lean:162`](LambdaS/Map.lean#L162) |
| The calculus's entry units are the model's | `LambdaS.entry_toSpace` | [`LambdaS/Syntax.lean:352`](LambdaS/Syntax.lean#L352) |
| T-MCons enforces the model's entry units | `LambdaS.HasTy.mcons_entry` | [`LambdaS/Typing.lean:540`](LambdaS/Typing.lean#L540) |
| Rank-one units (Theorem 9.1) | `LambdaS.entry_rank_one` | [`LambdaS/Map.lean:174`](LambdaS/Map.lean#L174) |
| Composition entry units | `LambdaS.entry_comp` | [`LambdaS/Map.lean:185`](LambdaS/Map.lean#L185) |
| Endomorphism diagonals dimensionless | `LambdaS.entry_id_diag` | [`LambdaS/Map.lean:212`](LambdaS/Map.lean#L212) |
| Permutation products dimensionless | `LambdaS.entry_perm_prod` | [`LambdaS/Map.lean:200`](LambdaS/Map.lean#L200) |
| Eigenvalue unit identity | `LambdaS.eigenvalue_uom` | [`LambdaS/Map.lean:242`](LambdaS/Map.lean#L242) |
| Dual-map entries symmetric | `LambdaS.entry_dual_symm` | [`LambdaS/Map.lean:249`](LambdaS/Map.lean#L249) |
| Weighted norms dimensionless | `LambdaS.weighted_norm_dimensionless` | [`LambdaS/Map.lean:254`](LambdaS/Map.lean#L254) |
| Cholesky factors dimensionless | `LambdaS.cholesky_factor_dimensionless` | [`LambdaS/Map.lean:264`](LambdaS/Map.lean#L264) |
| Uniform spaces are scaled dimensionless spaces | `LambdaS.Space.uniform_iff_scale_triv` | [`LambdaS/Space.lean:91`](LambdaS/Space.lean#L91) |
| SVD entries share one unit | `LambdaS.svd_entry_const` | [`LambdaS/Map.lean:280`](LambdaS/Map.lean#L280) |
| Self-dual spaces are dimensionless | `LambdaS.transpose_comp_direct_iff` | [`LambdaS/Map.lean:294`](LambdaS/Map.lean#L294) |
| Uniform spaces carry a canonical metric | `LambdaS.uniform_canonical_metric` | [`LambdaS/Map.lean:307`](LambdaS/Map.lean#L307) |

## The quantum-mechanics example

| Paper claim | Lean name | Location |
|---|---|---|
| The ground-state energy is an energy | `LambdaS.QM.groundEnergy` | [`LambdaS/QM.lean:97`](LambdaS/QM.lean#L97) |
| The uncertainty product is dimensionless | `LambdaS.QM.uncertainty` | [`LambdaS/QM.lean:123`](LambdaS/QM.lean#L123) |
| The amplitude carries m^(-1/2) | `LambdaS.QM.amplitude` | [`LambdaS/QM.lean:132`](LambdaS/QM.lean#L132) |
| The squared amplitude is a density | `LambdaS.QM.density` | [`LambdaS/QM.lean:144`](LambdaS/QM.lean#L144) |
| Density times length is dimensionless | `LambdaS.QM.probability` | [`LambdaS/QM.lean:150`](LambdaS/QM.lean#L150) |
| The expectation of the Hamiltonian is an energy | `LambdaS.QM.expectH` | [`LambdaS/QM.lean:251`](LambdaS/QM.lean#L251) |
| The state literal, parametric | `LambdaS.QM.statePlusTm` | [`LambdaS/QM.lean:295`](LambdaS/QM.lean#L295) |
| The Hamiltonian literal, not parametric | `LambdaS.QM.hamiltonianTm` | [`LambdaS/QM.lean:304`](LambdaS/QM.lean#L304) |
| The phase is dimensionless; `exp` accepts it | `LambdaS.QM.phase` | [`LambdaS/QM.lean:347`](LambdaS/QM.lean#L347) |
| The expectation as a curried function | `LambdaS.QM.expectation` | [`LambdaS/QM.lean:364`](LambdaS/QM.lean#L364) |

## Reproducing the worked examples

`lake exe lambdas` prints the particle-in-a-box report, the free-fall
report, the declared-conversion report (100 yards as 300 ft, as 91.44 m
directly, and as 91.44 m through feet: path independence made observable),
the two-state report with its numeric self-checks, and the compiled-evaluator
validation lines CI asserts. The same three yard numbers are asserted at
build time by `#guard`s in `LambdaS/Algorithms.lean`; the `#guard`s there
and in `LambdaS/Examples.lean` and `LambdaS/QM.lean` run the checker, the
drift analysis, and the evaluator during `lake build`, so a wrong stated
result would fail the build.

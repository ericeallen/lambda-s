# Theorem index

Every artifact identifier the accompanying paper cites, and the supporting
results behind them, with Lean name and location. Line numbers are for the commit that carries this file.
`scripts/Audit.lean` prints the axiom dependencies of every declaration below
(`scripts/verify_theorems_index.py` fails if one is missing from it); CI fails
if any depends on more than `propext`, `Classical.choice`, and `Quot.sound`.

## The calculus and its checker

| Paper claim | Lean name | Location |
|---|---|---|
| Typing rules (Figure 2) | `LambdaS.HasTy` | [`LambdaS/Typing.lean:435`](LambdaS/Typing.lean#L435) |
| Completeness; derivations unique | `LambdaS.check_eq` | [`LambdaS/Typing.lean:664`](LambdaS/Typing.lean#L664) |
| The generic caster is well-typed | `LambdaS.Examples.caster` | [`LambdaS/Examples.lean:1011`](LambdaS/Examples.lean#L1011) |
| The velocity idiom | `LambdaS.Examples.velocity` | [`LambdaS/Examples.lean:97`](LambdaS/Examples.lean#L97) |
| Surface `in` elaborates by running the checker | `LambdaS.elabConvert` | [`LambdaS/Notation.lean:110`](LambdaS/Notation.lean#L110) |
| Elaboration succeeds iff scalar of the target's dimension | `LambdaS.elabConvert_isSome` | [`LambdaS/Notation.lean:123`](LambdaS/Notation.lean#L123) |
| The state-vector literal | `LambdaS.Examples.stateVec` | [`LambdaS/Examples.lean:1174`](LambdaS/Examples.lean#L1174) |
| A matrix literal, rank-one checked at introduction | `LambdaS.Examples.toTime` | [`LambdaS/Examples.lean:1196`](LambdaS/Examples.lean#L1196) |

## Operational semantics

| Paper claim | Lean name | Location |
|---|---|---|
| Instrumented evaluation rules | `LambdaS.eval` | [`LambdaS/Dynamics.lean:125`](LambdaS/Dynamics.lean#L125) |
| Numeric operations supplied by the carrier | `LambdaS.Num` | [`LambdaS/Num.lean:94`](LambdaS/Num.lean#L94) |

## Unit declarations

| Paper claim | Lean name | Location |
|---|---|---|
| Consistency, necessity (log form) | `LambdaS.dependency_forces` | [`LambdaS/Declare.lean:364`](LambdaS/Declare.lean#L364) |
| Consistency, necessity (product form) | `LambdaS.dependency_forces_mul` | [`LambdaS/Declare.lean:395`](LambdaS/Declare.lean#L395) |
| Consistency, sufficiency | `LambdaS.dependency_sufficient` | [`LambdaS/Declare.lean:437`](LambdaS/Declare.lean#L437) |
| Consistency characterized (log form) | `LambdaS.consistent_iff_dependencies` | [`LambdaS/Declare.lean:465`](LambdaS/Declare.lean#L465) |
| Consistency characterized (Theorem 3.1) | `LambdaS.consistent_iff_dependencies_mul` | [`LambdaS/Declare.lean:479`](LambdaS/Declare.lean#L479) |
| Redundant factor forced | `LambdaS.factor_chain_consistent` | [`LambdaS/Declare.lean:543`](LambdaS/Declare.lean#L543) |
| One-dimension well-formedness | `LambdaS.Decl.Sound` | [`LambdaS/Declare.lean:316`](LambdaS/Declare.lean#L316) |
| The yard set is satisfiable | `LambdaS.Examples.yard_satisfiable` | [`LambdaS/Examples.lean:584`](LambdaS/Examples.lean#L584) |
| A benign declaration cycle is satisfiable | `LambdaS.Examples.cycle_satisfiable` | [`LambdaS/Examples.lean:614`](LambdaS/Examples.lean#L614) |
| Dimension abbreviations elaborate by scoping alone | `LambdaS.DimAbbrev.elabDimDefs` | [`LambdaS/Declare.lean:587`](LambdaS/Declare.lean#L587) |
| Primary units: the declaration determines the dimension | `LambdaS.DimAbbrev.elabPrimary` | [`LambdaS/Declare.lean:598`](LambdaS/Declare.lean#L598) |
| The cyclic dimension pair, rejected at its second line | `LambdaS.Examples.dimCycle` | [`LambdaS/Examples.lean:513`](LambdaS/Examples.lean#L513) |
| A vicious declaration cycle is rejected | `LambdaS.Examples.cycle_conflict` | [`LambdaS/Examples.lean:620`](LambdaS/Examples.lean#L620) |
| The mistyped yard set is refuted | `LambdaS.Examples.yard_conflict` | [`LambdaS/Examples.lean:483`](LambdaS/Examples.lean#L483) |
| One yard per foot denotes 1, at yd/ft | `LambdaS.Algorithms.ydPerFt` | [`LambdaS/Algorithms.lean:249`](LambdaS/Algorithms.lean#L249) |
| Converted to unit 1, the declared 3 appears | `LambdaS.Algorithms.ydPerFtIn1` | [`LambdaS/Algorithms.lean:258`](LambdaS/Algorithms.lean#L258) |
| Converting one operand first, the same 3 | `LambdaS.Algorithms.ydPerFtViaFt` | [`LambdaS/Algorithms.lean:271`](LambdaS/Algorithms.lean#L271) |
| The redundant factor is forced | `LambdaS.Examples.yard_forced` | [`LambdaS/Examples.lean:471`](LambdaS/Examples.lean#L471) |

## Dynamics

| Paper claim | Lean name | Location |
|---|---|---|
| Preservation: a produced value has the predicted type | `LambdaS.eval_sound` | [`LambdaS/Soundness.lean:214`](LambdaS/Soundness.lean#L214) |
| Unit soundness (Theorem 4.1) | `LambdaS.unit_soundness_total` | [`LambdaS/Normalization.lean:769`](LambdaS/Normalization.lean#L769) |
| Matrix literals evaluate to matrices at their spaces | `LambdaS.lin_soundness_total` | [`LambdaS/Normalization.lean:782`](LambdaS/Normalization.lean#L782) |
| Totality at every type | `LambdaS.eval_total` | [`LambdaS/Normalization.lean:754`](LambdaS/Normalization.lean#L754) |
| Fuel accounting, checked by the binary | `LambdaS.QM.twoStateChecks` | [`LambdaS/QM.lean:386`](LambdaS/QM.lean#L386) |

## Denotational semantics and abstraction

| Paper claim | Lean name | Location |
|---|---|---|
| Convert-free terms ignore the valuation | `LambdaS.den_eq_of_convertFree` | [`LambdaS/Fundamental.lean:958`](LambdaS/Fundamental.lean#L958) |
| Valuation independence at higher type | `LambdaS.den_indep` | [`LambdaS/Fundamental.lean:868`](LambdaS/Fundamental.lean#L868) |
| Abstraction, convert-free (Theorem 5.1) | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:1127`](LambdaS/Fundamental.lean#L1127) |
| Abstraction, coherent (Theorem 5.2) | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:977`](LambdaS/Fundamental.lean#L977) |
| Theorem 5.2 at a moving rescaling | `LambdaS.Examples.fundamental_at_moving_rescale` | [`LambdaS/Examples.lean:1152`](LambdaS/Examples.lean#L1152) |
| The root scaling identity, all reals, positive factor | `LambdaS.mul_rpow_of_pos_left` | [`LambdaS/Parametricity.lean:380`](LambdaS/Parametricity.lean#L380) |
| The abstraction theorem at a root term | `LambdaS.sqrt_scales` | [`LambdaS/Fundamental.lean:1441`](LambdaS/Fundamental.lean#L1441) |
| The price is exact (Theorem 5.3) | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:1286`](LambdaS/Fundamental.lean#L1286) |
| Coherent equals factoring through dimension | `LambdaS.Scaling.coherent_iff_factors` | [`LambdaS/Conversion.lean:452`](LambdaS/Conversion.lean#L452) |

## Accumulated ratios and the drift diagnostic

| Paper claim | Lean name | Location |
|---|---|---|
| Shapes | `LambdaS.Shape` | [`LambdaS/Ratio.lean:62`](LambdaS/Ratio.lean#L62) |
| Ratio expressions | `LambdaS.Tw` | [`LambdaS/Ratio.lean:152`](LambdaS/Ratio.lean#L152) |
| Semantic ratios | `LambdaS.SemTw` | [`LambdaS/Ratio.lean:353`](LambdaS/Ratio.lean#L353) |
| Ratio evaluation | `LambdaS.Tw.eval` | [`LambdaS/Ratio.lean:377`](LambdaS/Ratio.lean#L377) |
| The scaling law, twisted (two parameters) | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:625`](LambdaS/Twist.lean#L625) |
| The twisted law at first order | `LambdaS.Twist.law` | [`LambdaS/Twist.lean:959`](LambdaS/Twist.lean#L959) |
| The drift law (both parameters) | `LambdaS.unitDrift_law` | [`LambdaS/Twist.lean:2102`](LambdaS/Twist.lean#L2102) |
| Declared magnitudes enter through the drift alone | `LambdaS.den_comp_of_drift` | [`LambdaS/Twist.lean:2115`](LambdaS/Twist.lean#L2115) |
| Drift 1 is declaration independence, open programs at any unit | `LambdaS.den_indep_of_driftFree` | [`LambdaS/Twist.lean:2129`](LambdaS/Twist.lean#L2129) |
| Drift 1 gives the unrestricted scaling law | `LambdaS.scaleLaw_of_driftFree` | [`LambdaS/Twist.lean:2144`](LambdaS/Twist.lean#L2144) |
| Drift 1 gives the scaling law at a matrix result | `LambdaS.scaleLaw_lin_of_driftFree` | [`LambdaS/Twist.lean:1973`](LambdaS/Twist.lean#L1973) |
| The same over an arbitrary context | `LambdaS.scaleLaw_lin_of_driftFree_gen` | [`LambdaS/Twist.lean:1941`](LambdaS/Twist.lean#L1941) |
| Invariance iff trivial ratio (Theorem 6.1) | `LambdaS.Twist.invariant_iff` | [`LambdaS/Twist.lean:1052`](LambdaS/Twist.lean#L1052) |
| Decidability | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:1085`](LambdaS/Twist.lean#L1085) |
| The diagnostic's specification (Theorem 6.1) | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:2005`](LambdaS/Twist.lean#L2005) |
| Branch comparison at `+` (on normal forms) | `LambdaS.Tw.normEq` | [`LambdaS/Twist.lean:1588`](LambdaS/Twist.lean#L1588) |
| Branch comparison, flat form | `LambdaS.Tw.scalarEq` | [`LambdaS/Twist.lean:1450`](LambdaS/Twist.lean#L1450) |
| The β-normalizer for ratios | `LambdaS.Tw.norm` | [`LambdaS/Ratio.lean:512`](LambdaS/Ratio.lean#L512) |
| Normalization preserves evaluation | `LambdaS.Tw.eval_norm` | [`LambdaS/Ratio.lean:818`](LambdaS/Ratio.lean#L818) |
| Reassociated conversions accepted | `LambdaS.Examples.addAssoc` | [`LambdaS/Examples.lean:968`](LambdaS/Examples.lean#L968) |
| Drift-free closed programs are declaration-independent at the evaluator | `LambdaS.evalC_indep_of_driftFree` | [`LambdaS/Twist.lean:2157`](LambdaS/Twist.lean#L2157) |
| The ballistics case study (four verdicts) | `LambdaS.Examples.Ballistics` | [`LambdaS/Examples.lean:1431`](LambdaS/Examples.lean#L1431) |
| Sum of two converted inputs, accepted at m/ft | `LambdaS.Examples.addTwoVars` | [`LambdaS/Examples.lean:824`](LambdaS/Examples.lean#L824) |
| Genuinely drifting sum, declined | `LambdaS.Examples.addMixed` | [`LambdaS/Examples.lean:840`](LambdaS/Examples.lean#L840) |
| Agreeing sum through an internal abstraction, accepted | `LambdaS.Examples.hoSum` | [`LambdaS/Examples.lean:889`](LambdaS/Examples.lean#L889) |
| A visible application analyzes as its redex | `LambdaS.Examples.betaShared` | [`LambdaS/Examples.lean:933`](LambdaS/Examples.lean#L933) |
| Polymorphic round trip, drift-free uninstantiated | `LambdaS.Examples.casterRound` | [`LambdaS/Examples.lean:1077`](LambdaS/Examples.lean#L1077) |
| Leading lambda binders analyzed as inputs | `LambdaS.unitDriftLam` | [`LambdaS/Twist.lean:2028`](LambdaS/Twist.lean#L2028) |
| The stripped kernel is analyzed as an open term | `LambdaS.unitDriftLam_eq_unitDrift` | [`LambdaS/Twist.lean:2048`](LambdaS/Twist.lean#L2048) |
| The diagnostic through a leading abstraction, exact | `LambdaS.unitDriftLam_spec` | [`LambdaS/Twist.lean:2062`](LambdaS/Twist.lean#L2062) |
| Comparison exact for atom-free ratios (iff) | `LambdaS.Tw.normEq_iff_eval_eq` | [`LambdaS/Twist.lean:1624`](LambdaS/Twist.lean#L1624) |
| Flat comparison exact for atom-free ratios (iff) | `LambdaS.Tw.scalarEq_iff_eval_eq` | [`LambdaS/Twist.lean:1570`](LambdaS/Twist.lean#L1570) |
| log of a round-trip ratio, accepted at drift 1 | `LambdaS.Examples.logRoundTrip` | [`LambdaS/Examples.lean:906`](LambdaS/Examples.lean#L906) |
| log of a drifting argument, declined | `LambdaS.Examples.logDrifting` | [`LambdaS/Examples.lean:919`](LambdaS/Examples.lean#L919) |

## Adequacy and erasure

| Paper claim | Lean name | Location |
|---|---|---|
| Adequacy at the declared factors | `LambdaS.eval_adeq` | [`LambdaS/Adequacy.lean:341`](LambdaS/Adequacy.lean#L341) |
| Declared factors reach the real-valued evaluator (Theorem 7.1) | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:844`](LambdaS/Adequacy.lean#L844) |
| Erasure (Theorem 7.2) | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:510`](LambdaS/Erasure.lean#L510) |
| The simulation behind it, no typing hypothesis | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:296`](LambdaS/Erasure.lean#L296) |
| The erased evaluator computes the denotation, at `ℝ` | `LambdaS.eeval_den` | [`LambdaS/Erasure.lean:523`](LambdaS/Erasure.lean#L523) |
| One yard is three feet, at the evaluator | `LambdaS.Examples.one_yard_is_three_feet` | [`LambdaS/Examples.lean:640`](LambdaS/Examples.lean#L640) |
| One yard is 0.9144 meters, directly | `LambdaS.Examples.one_yard_in_meters` | [`LambdaS/Examples.lean:651`](LambdaS/Examples.lean#L651) |
| One yard is 0.9144 meters, through feet | `LambdaS.Examples.one_yard_in_meters_via_feet` | [`LambdaS/Examples.lean:666`](LambdaS/Examples.lean#L666) |
| The two routes agree at the evaluator | `LambdaS.Examples.yard_routes_agree` | [`LambdaS/Examples.lean:689`](LambdaS/Examples.lean#L689) |

## Dimensional analysis

| Paper claim | Lean name | Location |
|---|---|---|
| Conversion not definable convert-free | `LambdaS.NonDef.convert_not_definable` | [`LambdaS/NonDefinability.lean:410`](LambdaS/NonDefinability.lean#L410) |
| Square root not definable by arithmetic | `LambdaS.NonDef.sqrt_not_definable` | [`LambdaS/NonDefinability.lean:219`](LambdaS/NonDefinability.lean#L219) |
| The reflection into the arithmetic grammar | `LambdaS.NonDef.arith_of_hasTy` | [`LambdaS/NonDefinability.lean:272`](LambdaS/NonDefinability.lean#L272) |
| Square root not definable, at the term grammar | `LambdaS.NonDef.sqrt_not_definable_tm` | [`LambdaS/NonDefinability.lean:317`](LambdaS/NonDefinability.lean#L317) |
| No seed for Newton's method | `LambdaS.NonDef.no_newton_seed` | [`LambdaS/NonDefinability.lean:227`](LambdaS/NonDefinability.lean#L227) |
| No seed, at the term grammar | `LambdaS.NonDef.no_newton_seed_tm` | [`LambdaS/NonDefinability.lean:328`](LambdaS/NonDefinability.lean#L328) |
| The multiplicative scale law (definition) | `LambdaS.Pi.MulScaleLaw` | [`LambdaS/PiTheorem.lean:492`](LambdaS/PiTheorem.lean#L492) |
| Term-level multiplicative scale law | `LambdaS.Pi.den_mulScaleLaw` | [`LambdaS/PiTheorem.lean:902`](LambdaS/PiTheorem.lean#L902) |
| Term-level scale law from drift 1 | `LambdaS.Pi.den_mulScaleLaw_driftFree` | [`LambdaS/PiTheorem.lean:925`](LambdaS/PiTheorem.lean#L925) |
| Log transport, positivity hypothesis | `LambdaS.Pi.scaleLaw_of_mulScaleLaw` | [`LambdaS/PiTheorem.lean:764`](LambdaS/PiTheorem.lean#L764) |
| Pi, the factorization | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:279`](LambdaS/PiTheorem.lean#L279) |
| Pi, multiplicative coordinates | `LambdaS.Pi.mulScaleLaw_factorization` | [`LambdaS/PiTheorem.lean:602`](LambdaS/PiTheorem.lean#L602) |
| Invariants are the dimensionless monomials | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:307`](LambdaS/PiTheorem.lean#L307) |
| Buckingham's counting (Theorem 8.1) | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:331`](LambdaS/PiTheorem.lean#L331) |
| The factorization is an equivalence | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:447`](LambdaS/PiTheorem.lean#L447) |
| The pendulum signature | `LambdaS.Pi.pendulum` | [`LambdaS/Pi.lean:137`](LambdaS/Pi.lean#L137) |
| The pendulum solution exhibited | `LambdaS.Pi.pendulum_period_solution` | [`LambdaS/Pi.lean:166`](LambdaS/Pi.lean#L166) |
| The pendulum ignores its mass, both halves | `LambdaS.Pi.pendulum_mass_absent` | [`LambdaS/PiTheorem.lean:950`](LambdaS/PiTheorem.lean#L950) |
| Mass is absent from every solution | `LambdaS.Pi.pendulum_period_independent_of_mass` | [`LambdaS/Pi.lean:155`](LambdaS/Pi.lean#L155) |
| Mass is absent from every dimensionless group | `LambdaS.Pi.pendulum_mass_drops_out` | [`LambdaS/Pi.lean:149`](LambdaS/Pi.lean#L149) |
| A once-appearing base unit forces zero in every invariant | `LambdaS.Pi.eq_zero_of_appears_once` | [`LambdaS/Pi.lean:105`](LambdaS/Pi.lean#L105) |
| A once-appearing base unit forces a zero exponent | `LambdaS.Pi.solution_eq_zero_of_appears_once` | [`LambdaS/Pi.lean:122`](LambdaS/Pi.lean#L122) |
| Signed equivalence, multiplicative coordinates | `LambdaS.Pi.piEquivSigned` | [`LambdaS/PiTheorem.lean:555`](LambdaS/PiTheorem.lean#L555) |
| Unsolvable signatures admit only zero | `LambdaS.Pi.mulScaleLaw_eq_zero_of_unsolvable` | [`LambdaS/PiTheorem.lean:709`](LambdaS/PiTheorem.lean#L709) |
| The solvability dichotomy (Theorem 8.1) | `LambdaS.Pi.mulScaleLaw_dichotomy` | [`LambdaS/PiTheorem.lean:737`](LambdaS/PiTheorem.lean#L737) |

## Dimensioned linear algebra

| Paper claim | Lean name | Location |
|---|---|---|
| Entry units (definition) | `LambdaS.entry` | [`LambdaS/Map.lean:162`](LambdaS/Map.lean#L162) |
| The calculus's entry units are the model's | `LambdaS.entry_toSpace` | [`LambdaS/Syntax.lean:355`](LambdaS/Syntax.lean#L355) |
| T-MCons enforces the model's entry units | `LambdaS.HasTy.mcons_entry` | [`LambdaS/Typing.lean:531`](LambdaS/Typing.lean#L531) |
| Rank-one units (Theorem 9.1) | `LambdaS.entry_rank_one` | [`LambdaS/Map.lean:174`](LambdaS/Map.lean#L174) |
| Composition entry units | `LambdaS.entry_comp` | [`LambdaS/Map.lean:185`](LambdaS/Map.lean#L185) |
| Endomorphism diagonals dimensionless | `LambdaS.entry_id_diag` | [`LambdaS/Map.lean:212`](LambdaS/Map.lean#L212) |
| Permutation products dimensionless | `LambdaS.entry_perm_prod` | [`LambdaS/Map.lean:200`](LambdaS/Map.lean#L200) |
| Eigenvalue unit identity | `LambdaS.eigenvalue_uom` | [`LambdaS/Map.lean:241`](LambdaS/Map.lean#L241) |
| Dual-map entries symmetric | `LambdaS.entry_dual_symm` | [`LambdaS/Map.lean:248`](LambdaS/Map.lean#L248) |
| Weighted norms dimensionless | `LambdaS.weighted_norm_dimensionless` | [`LambdaS/Map.lean:253`](LambdaS/Map.lean#L253) |
| Cholesky factors dimensionless | `LambdaS.cholesky_factor_dimensionless` | [`LambdaS/Map.lean:263`](LambdaS/Map.lean#L263) |
| Uniform spaces are scaled dimensionless spaces | `LambdaS.Space.uniform_iff_scale_triv` | [`LambdaS/Space.lean:91`](LambdaS/Space.lean#L91) |
| SVD entries share one unit | `LambdaS.svd_entry_const` | [`LambdaS/Map.lean:279`](LambdaS/Map.lean#L279) |
| Self-dual spaces are dimensionless | `LambdaS.transpose_comp_direct_iff` | [`LambdaS/Map.lean:293`](LambdaS/Map.lean#L293) |
| Uniform metric entries carry unit u⁻² | `LambdaS.uniform_canonical_metric` | [`LambdaS/Map.lean:308`](LambdaS/Map.lean#L308) |

## The quantum-mechanics example

| Paper claim | Lean name | Location |
|---|---|---|
| The ground-state energy is an energy | `LambdaS.QM.groundEnergy` | [`LambdaS/QM.lean:99`](LambdaS/QM.lean#L99) |
| The uncertainty product is dimensionless | `LambdaS.QM.uncertainty` | [`LambdaS/QM.lean:125`](LambdaS/QM.lean#L125) |
| The amplitude carries m^(-1/2) | `LambdaS.QM.amplitude` | [`LambdaS/QM.lean:134`](LambdaS/QM.lean#L134) |
| The squared amplitude is a density | `LambdaS.QM.density` | [`LambdaS/QM.lean:146`](LambdaS/QM.lean#L146) |
| Density times length is dimensionless | `LambdaS.QM.probability` | [`LambdaS/QM.lean:152`](LambdaS/QM.lean#L152) |
| The expectation of the Hamiltonian is an energy | `LambdaS.QM.expectH` | [`LambdaS/QM.lean:255`](LambdaS/QM.lean#L255) |
| The state literal, parametric | `LambdaS.QM.statePlusTm` | [`LambdaS/QM.lean:299`](LambdaS/QM.lean#L299) |
| The Hamiltonian literal, not parametric | `LambdaS.QM.hamiltonianTm` | [`LambdaS/QM.lean:308`](LambdaS/QM.lean#L308) |
| The phase is dimensionless; `exp` accepts it | `LambdaS.QM.phase` | [`LambdaS/QM.lean:351`](LambdaS/QM.lean#L351) |
| The expectation as a curried function | `LambdaS.QM.expectation` | [`LambdaS/QM.lean:368`](LambdaS/QM.lean#L368) |

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

## Pi arity descent

| Paper claim | Lean name | Location |
|---|---|---|
| Rational dimensionless coordinates | `LambdaS.Pi.piCoordinates` | [`LambdaS/PiTheorem.lean:358`](LambdaS/PiTheorem.lean#L358) |
| Arbitrary invariants descend to n minus rank coordinates | `LambdaS.Pi.invariant_descends` | [`LambdaS/PiTheorem.lean:412`](LambdaS/PiTheorem.lean#L412) |
| Signed Buckingham factorization at reduced arity | `LambdaS.Pi.mulScaleLaw_factorization_reduced` | [`LambdaS/PiTheorem.lean:629`](LambdaS/PiTheorem.lean#L629) |

## Dimension-level Pi theorem with conversion

| Paper claim | Lean name | Location |
|---|---|---|
| Only same-dimension oracle entries affect evaluation | `LambdaS.eval_congr_sameDim` | [`LambdaS/PiCoherent.lean:39`](LambdaS/PiCoherent.lean#L39) |
| Coherent valuation changes preserve scalar denotation | `LambdaS.den_eq_of_coherent` | [`LambdaS/PiCoherent.lean:92`](LambdaS/PiCoherent.lean#L92) |
| Converting programs obey the dimension-level scaling law | `LambdaS.Pi.den_mulScaleLaw_coherent` | [`LambdaS/PiCoherent.lean:135`](LambdaS/PiCoherent.lean#L135) |
| Converting programs factor through n minus dimension-rank groups | `LambdaS.Pi.den_pi_coherent` | [`LambdaS/PiCoherent.lean:159`](LambdaS/PiCoherent.lean#L159) |

## Executable declaration solving and determinacy

| Paper claim | Lean name | Location |
|---|---|---|
| Executable rational elimination | `LambdaS.RationalSolver.solve` | [`LambdaS/RationalSolver.lean:197`](LambdaS/RationalSolver.lean#L197) |
| Rational solver soundness | `LambdaS.RationalSolver.solve_sound` | [`LambdaS/RationalSolver.lean:206`](LambdaS/RationalSolver.lean#L206) |
| Rational solver completeness | `LambdaS.RationalSolver.solve_isSome_iff` | [`LambdaS/RationalSolver.lean:211`](LambdaS/RationalSolver.lean#L211) |
| Solvability reflects through exact log interpretation | `LambdaS.RationalSolver.solvable_map_iff` | [`LambdaS/RationalSolver.lean:291`](LambdaS/RationalSolver.lean#L291) |
| Executable exact logarithmic equality | `LambdaS.LogFactor.isZero_iff` | [`LambdaS/LogFactor.lean:84`](LambdaS/LogFactor.lean#L84) |
| Exact factor semantics is injective | `LambdaS.LogFactor.interpret_injective` | [`LambdaS/LogFactor.lean:207`](LambdaS/LogFactor.lean#L207) |
| Inspectable radical output is exact | `LambdaS.LogFactor.radical_exp` | [`LambdaS/LogFactor.lean:75`](LambdaS/LogFactor.lean#L75) |
| Semantic determinacy is span membership | `LambdaS.Decl.determined_iff_coefficients` | [`LambdaS/Determinacy.lean:114`](LambdaS/Determinacy.lean#L114) |
| Global completeness decides all legal factors | `LambdaS.DeclarationComplete.check_iff_all_conversions_determined` | [`LambdaS/DeclarationComplete.lean:129`](LambdaS/DeclarationComplete.lean#L129) |
| Executable declaration consistency is exact | `LambdaS.DeclSolver.solve_isSome_iff` | [`LambdaS/DeclareSolver.lean:127`](LambdaS/DeclareSolver.lean#L127) |
| Computed declaration solutions satisfy valuations | `LambdaS.DeclSolver.solve_sound` | [`LambdaS/DeclareSolver.lean:116`](LambdaS/DeclareSolver.lean#L116) |
| Factor lookup decides determinacy | `LambdaS.DeclSolver.conversion_isSome_iff` | [`LambdaS/DeclareSolver.lean:185`](LambdaS/DeclareSolver.lean#L185) |
| Extracted radical agrees with every satisfying valuation | `LambdaS.DeclSolver.conversionExact_correct` | [`LambdaS/DeclareSolver.lean:234`](LambdaS/DeclareSolver.lean#L234) |
| Full declaration checker sound and complete | `LambdaS.DeclSolver.check_isSome_iff` | [`LambdaS/DeclareSolver.lean:283`](LambdaS/DeclareSolver.lean#L283) |
| Checked systems supply every legal conversion | `LambdaS.DeclSolver.Checked.conversionExact_isSome` | [`LambdaS/DeclareSolver.lean:300`](LambdaS/DeclareSolver.lean#L300) |
| Rational factor actually computed | `LambdaS.DeclarationSolverExamples.Length.linkedFactor_returned` | [`LambdaS/DeclarationSolverExamples.lean:54`](LambdaS/DeclarationSolverExamples.lean#L54) |
| Computed rational factor semantic correctness | `LambdaS.DeclarationSolverExamples.Length.linkedFactor_correct` | [`LambdaS/DeclarationSolverExamples.lean:68`](LambdaS/DeclarationSolverExamples.lean#L68) |
| Irrational factor actually computed | `LambdaS.DeclarationSolverExamples.Root.rootFactor_returned` | [`LambdaS/DeclarationSolverExamples.lean:92`](LambdaS/DeclarationSolverExamples.lean#L92) |
| Computed irrational factor semantic correctness | `LambdaS.DeclarationSolverExamples.Root.rootFactor_correct` | [`LambdaS/DeclarationSolverExamples.lean:106`](LambdaS/DeclarationSolverExamples.lean#L106) |

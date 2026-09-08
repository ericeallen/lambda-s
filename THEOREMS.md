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
| The generic caster is well-typed | `LambdaS.Examples.caster` | [`LambdaS/Examples.lean:1010`](LambdaS/Examples.lean#L1010) |
| The velocity idiom | `LambdaS.Examples.velocity` | [`LambdaS/Examples.lean:97`](LambdaS/Examples.lean#L97) |
| Surface `in` elaborates by running the checker | `LambdaS.elabConvert` | [`LambdaS/Notation.lean:110`](LambdaS/Notation.lean#L110) |
| Elaboration succeeds iff scalar of the target's dimension | `LambdaS.elabConvert_isSome` | [`LambdaS/Notation.lean:123`](LambdaS/Notation.lean#L123) |
| The state-vector literal | `LambdaS.Examples.stateVec` | [`LambdaS/Examples.lean:1173`](LambdaS/Examples.lean#L1173) |
| A matrix literal, rank-one checked at introduction | `LambdaS.Examples.toTime` | [`LambdaS/Examples.lean:1195`](LambdaS/Examples.lean#L1195) |

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
| The yard set is satisfiable | `LambdaS.Examples.yard_satisfiable` | [`LambdaS/Examples.lean:584`](LambdaS/Examples.lean#L584) |
| A benign declaration cycle is satisfiable | `LambdaS.Examples.cycle_satisfiable` | [`LambdaS/Examples.lean:614`](LambdaS/Examples.lean#L614) |
| Dimension abbreviations elaborate by scoping alone | `LambdaS.DimAbbrev.elabDimDefs` | [`LambdaS/Declare.lean:584`](LambdaS/Declare.lean#L584) |
| Primary units: the declaration determines the dimension | `LambdaS.DimAbbrev.elabPrimary` | [`LambdaS/Declare.lean:595`](LambdaS/Declare.lean#L595) |
| The cyclic dimension pair, rejected at its second line | `LambdaS.Examples.dimCycle` | [`LambdaS/Examples.lean:513`](LambdaS/Examples.lean#L513) |
| A vicious declaration cycle is rejected | `LambdaS.Examples.cycle_conflict` | [`LambdaS/Examples.lean:620`](LambdaS/Examples.lean#L620) |
| The mistyped yard set is refuted | `LambdaS.Examples.yard_conflict` | [`LambdaS/Examples.lean:483`](LambdaS/Examples.lean#L483) |
| One yard per foot denotes 1, at yd/ft | `LambdaS.Algorithms.ydPerFt` | [`LambdaS/Algorithms.lean:245`](LambdaS/Algorithms.lean#L245) |
| Converted to unit 1, the declared 3 appears | `LambdaS.Algorithms.ydPerFtIn1` | [`LambdaS/Algorithms.lean:254`](LambdaS/Algorithms.lean#L254) |
| Converting one operand first, the same 3 | `LambdaS.Algorithms.ydPerFtViaFt` | [`LambdaS/Algorithms.lean:266`](LambdaS/Algorithms.lean#L266) |
| The redundant factor is forced | `LambdaS.Examples.yard_forced` | [`LambdaS/Examples.lean:471`](LambdaS/Examples.lean#L471) |

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
| Convert-free terms ignore the valuation | `LambdaS.den_eq_of_convertFree` | [`LambdaS/Fundamental.lean:947`](LambdaS/Fundamental.lean#L947) |
| Valuation independence at higher type | `LambdaS.den_indep` | [`LambdaS/Fundamental.lean:857`](LambdaS/Fundamental.lean#L857) |
| Abstraction, convert-free (Theorem 5.1) | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:1116`](LambdaS/Fundamental.lean#L1116) |
| Abstraction, coherent (Theorem 5.2) | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:966`](LambdaS/Fundamental.lean#L966) |
| Theorem 5.2 at a moving rescaling | `LambdaS.Examples.fundamental_at_moving_rescale` | [`LambdaS/Examples.lean:1151`](LambdaS/Examples.lean#L1151) |
| The root scaling identity, all reals, positive factor | `LambdaS.mul_rpow_of_pos_left` | [`LambdaS/Parametricity.lean:379`](LambdaS/Parametricity.lean#L379) |
| The abstraction theorem at a root term | `LambdaS.sqrt_scales` | [`LambdaS/Fundamental.lean:1430`](LambdaS/Fundamental.lean#L1430) |
| The price is exact (Theorem 5.3) | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:1275`](LambdaS/Fundamental.lean#L1275) |
| Coherent equals factoring through dimension | `LambdaS.Scaling.coherent_iff_factors` | [`LambdaS/Conversion.lean:454`](LambdaS/Conversion.lean#L454) |

## Accumulated ratios and the drift diagnostic

| Paper claim | Lean name | Location |
|---|---|---|
| Shapes | `LambdaS.Shape` | [`LambdaS/Ratio.lean:57`](LambdaS/Ratio.lean#L57) |
| Ratio expressions | `LambdaS.Tw` | [`LambdaS/Ratio.lean:147`](LambdaS/Ratio.lean#L147) |
| Semantic ratios | `LambdaS.SemTw` | [`LambdaS/Ratio.lean:348`](LambdaS/Ratio.lean#L348) |
| Ratio evaluation | `LambdaS.Tw.eval` | [`LambdaS/Ratio.lean:372`](LambdaS/Ratio.lean#L372) |
| The scaling law, twisted (two parameters) | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:630`](LambdaS/Twist.lean#L630) |
| The twisted law at first order | `LambdaS.Twist.law` | [`LambdaS/Twist.lean:964`](LambdaS/Twist.lean#L964) |
| The drift law (both parameters) | `LambdaS.unitDrift_law` | [`LambdaS/Twist.lean:2097`](LambdaS/Twist.lean#L2097) |
| Declared magnitudes enter through the drift alone | `LambdaS.den_comp_of_drift` | [`LambdaS/Twist.lean:2110`](LambdaS/Twist.lean#L2110) |
| Drift 1 is declaration independence, open programs at any unit | `LambdaS.den_indep_of_driftFree` | [`LambdaS/Twist.lean:2124`](LambdaS/Twist.lean#L2124) |
| Drift 1 gives the unrestricted scaling law | `LambdaS.scaleLaw_of_driftFree` | [`LambdaS/Twist.lean:2139`](LambdaS/Twist.lean#L2139) |
| Drift 1 gives the scaling law at a matrix result | `LambdaS.scaleLaw_lin_of_driftFree` | [`LambdaS/Twist.lean:1968`](LambdaS/Twist.lean#L1968) |
| The same over an arbitrary context | `LambdaS.scaleLaw_lin_of_driftFree_gen` | [`LambdaS/Twist.lean:1936`](LambdaS/Twist.lean#L1936) |
| Invariance iff trivial ratio (Theorem 6.1) | `LambdaS.Twist.invariant_iff` | [`LambdaS/Twist.lean:1057`](LambdaS/Twist.lean#L1057) |
| Decidability | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:1090`](LambdaS/Twist.lean#L1090) |
| The diagnostic's specification (Theorem 6.1) | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:2000`](LambdaS/Twist.lean#L2000) |
| Branch comparison at `+` (on normal forms) | `LambdaS.Tw.normEq` | [`LambdaS/Twist.lean:1587`](LambdaS/Twist.lean#L1587) |
| Branch comparison, flat form | `LambdaS.Tw.scalarEq` | [`LambdaS/Twist.lean:1454`](LambdaS/Twist.lean#L1454) |
| The β-normalizer for ratios | `LambdaS.Tw.norm` | [`LambdaS/Ratio.lean:503`](LambdaS/Ratio.lean#L503) |
| Normalization preserves evaluation | `LambdaS.Tw.eval_norm` | [`LambdaS/Ratio.lean:809`](LambdaS/Ratio.lean#L809) |
| Reassociated conversions accepted | `LambdaS.Examples.addAssoc` | [`LambdaS/Examples.lean:967`](LambdaS/Examples.lean#L967) |
| Drift-free closed programs are declaration-independent at the evaluator | `LambdaS.evalC_indep_of_driftFree` | [`LambdaS/Twist.lean:2152`](LambdaS/Twist.lean#L2152) |
| The ballistics case study (four verdicts) | `LambdaS.Examples.Ballistics` | [`LambdaS/Examples.lean:1430`](LambdaS/Examples.lean#L1430) |
| Sum of two converted inputs, accepted at m/ft | `LambdaS.Examples.addTwoVars` | [`LambdaS/Examples.lean:824`](LambdaS/Examples.lean#L824) |
| Genuinely drifting sum, declined | `LambdaS.Examples.addMixed` | [`LambdaS/Examples.lean:839`](LambdaS/Examples.lean#L839) |
| Agreeing sum through an internal abstraction, accepted | `LambdaS.Examples.hoSum` | [`LambdaS/Examples.lean:888`](LambdaS/Examples.lean#L888) |
| A visible application analyzes as its redex | `LambdaS.Examples.betaShared` | [`LambdaS/Examples.lean:932`](LambdaS/Examples.lean#L932) |
| Polymorphic round trip, drift-free uninstantiated | `LambdaS.Examples.casterRound` | [`LambdaS/Examples.lean:1076`](LambdaS/Examples.lean#L1076) |
| Leading lambda binders analyzed as inputs | `LambdaS.unitDriftLam` | [`LambdaS/Twist.lean:2023`](LambdaS/Twist.lean#L2023) |
| The stripped kernel is analyzed as an open term | `LambdaS.unitDriftLam_eq_unitDrift` | [`LambdaS/Twist.lean:2043`](LambdaS/Twist.lean#L2043) |
| The diagnostic through a leading abstraction, exact | `LambdaS.unitDriftLam_spec` | [`LambdaS/Twist.lean:2057`](LambdaS/Twist.lean#L2057) |
| Comparison exact for atom-free ratios (iff) | `LambdaS.Tw.normEq_iff_eval_eq` | [`LambdaS/Twist.lean:1621`](LambdaS/Twist.lean#L1621) |
| Flat comparison exact for atom-free ratios (iff) | `LambdaS.Tw.scalarEq_iff_eval_eq` | [`LambdaS/Twist.lean:1572`](LambdaS/Twist.lean#L1572) |
| log of a round-trip ratio, accepted at drift 1 | `LambdaS.Examples.logRoundTrip` | [`LambdaS/Examples.lean:905`](LambdaS/Examples.lean#L905) |
| log of a drifting argument, declined | `LambdaS.Examples.logDrifting` | [`LambdaS/Examples.lean:918`](LambdaS/Examples.lean#L918) |

## Adequacy and erasure

| Paper claim | Lean name | Location |
|---|---|---|
| Adequacy at the declared factors | `LambdaS.eval_adeq` | [`LambdaS/Adequacy.lean:338`](LambdaS/Adequacy.lean#L338) |
| Declared factors reach the compiled evaluator (Theorem 7.1) | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:841`](LambdaS/Adequacy.lean#L841) |
| Erasure simulation, no typing hypothesis (Theorem 7.2) | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:297`](LambdaS/Erasure.lean#L297) |
| Erasure correctness | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:511`](LambdaS/Erasure.lean#L511) |
| The erased evaluator computes the denotation | `LambdaS.eeval_den` | [`LambdaS/Erasure.lean:523`](LambdaS/Erasure.lean#L523) |
| One yard is three feet, at the evaluator | `LambdaS.Examples.one_yard_is_three_feet` | [`LambdaS/Examples.lean:640`](LambdaS/Examples.lean#L640) |
| One yard is 0.9144 meters, directly | `LambdaS.Examples.one_yard_in_meters` | [`LambdaS/Examples.lean:651`](LambdaS/Examples.lean#L651) |
| One yard is 0.9144 meters, through feet | `LambdaS.Examples.one_yard_in_meters_via_feet` | [`LambdaS/Examples.lean:666`](LambdaS/Examples.lean#L666) |
| The two routes agree at the evaluator | `LambdaS.Examples.yard_routes_agree` | [`LambdaS/Examples.lean:689`](LambdaS/Examples.lean#L689) |

## Dimensional analysis

| Paper claim | Lean name | Location |
|---|---|---|
| Conversion not definable convert-free | `LambdaS.NonDef.convert_not_definable` | [`LambdaS/NonDefinability.lean:418`](LambdaS/NonDefinability.lean#L418) |
| Square root not definable by arithmetic | `LambdaS.NonDef.sqrt_not_definable` | [`LambdaS/NonDefinability.lean:227`](LambdaS/NonDefinability.lean#L227) |
| The reflection into the arithmetic grammar | `LambdaS.NonDef.arith_of_hasTy` | [`LambdaS/NonDefinability.lean:280`](LambdaS/NonDefinability.lean#L280) |
| Square root not definable, at the term grammar | `LambdaS.NonDef.sqrt_not_definable_tm` | [`LambdaS/NonDefinability.lean:325`](LambdaS/NonDefinability.lean#L325) |
| No seed for Newton's method | `LambdaS.NonDef.no_newton_seed` | [`LambdaS/NonDefinability.lean:235`](LambdaS/NonDefinability.lean#L235) |
| No seed, at the term grammar | `LambdaS.NonDef.no_newton_seed_tm` | [`LambdaS/NonDefinability.lean:336`](LambdaS/NonDefinability.lean#L336) |
| The multiplicative scale law (definition) | `LambdaS.Pi.MulScaleLaw` | [`LambdaS/PiTheorem.lean:487`](LambdaS/PiTheorem.lean#L487) |
| Term-level multiplicative scale law | `LambdaS.Pi.den_mulScaleLaw` | [`LambdaS/PiTheorem.lean:897`](LambdaS/PiTheorem.lean#L897) |
| Term-level scale law from drift 1 | `LambdaS.Pi.den_mulScaleLaw_driftFree` | [`LambdaS/PiTheorem.lean:920`](LambdaS/PiTheorem.lean#L920) |
| Log transport, positivity hypothesis | `LambdaS.Pi.scaleLaw_of_mulScaleLaw` | [`LambdaS/PiTheorem.lean:759`](LambdaS/PiTheorem.lean#L759) |
| Pi, the factorization | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:274`](LambdaS/PiTheorem.lean#L274) |
| Pi, multiplicative coordinates | `LambdaS.Pi.mulScaleLaw_factorization` | [`LambdaS/PiTheorem.lean:597`](LambdaS/PiTheorem.lean#L597) |
| Invariants are the dimensionless monomials | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:302`](LambdaS/PiTheorem.lean#L302) |
| Buckingham's counting (Theorem 8.1) | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:326`](LambdaS/PiTheorem.lean#L326) |
| The factorization is an equivalence | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:442`](LambdaS/PiTheorem.lean#L442) |
| The pendulum signature | `LambdaS.Pi.pendulum` | [`LambdaS/Pi.lean:138`](LambdaS/Pi.lean#L138) |
| The pendulum solution exhibited | `LambdaS.Pi.pendulum_period_solution` | [`LambdaS/Pi.lean:167`](LambdaS/Pi.lean#L167) |
| The pendulum ignores its mass, both halves | `LambdaS.Pi.pendulum_mass_absent` | [`LambdaS/PiTheorem.lean:945`](LambdaS/PiTheorem.lean#L945) |
| Mass is absent from every solution | `LambdaS.Pi.pendulum_period_independent_of_mass` | [`LambdaS/Pi.lean:156`](LambdaS/Pi.lean#L156) |
| Mass is absent from every dimensionless group | `LambdaS.Pi.pendulum_mass_drops_out` | [`LambdaS/Pi.lean:150`](LambdaS/Pi.lean#L150) |
| A once-appearing base unit forces zero in every invariant | `LambdaS.Pi.eq_zero_of_appears_once` | [`LambdaS/Pi.lean:106`](LambdaS/Pi.lean#L106) |
| A once-appearing base unit forces a zero exponent | `LambdaS.Pi.solution_eq_zero_of_appears_once` | [`LambdaS/Pi.lean:123`](LambdaS/Pi.lean#L123) |
| Signed equivalence, multiplicative coordinates | `LambdaS.Pi.piEquivSigned` | [`LambdaS/PiTheorem.lean:550`](LambdaS/PiTheorem.lean#L550) |
| Unsolvable signatures admit only zero | `LambdaS.Pi.mulScaleLaw_eq_zero_of_unsolvable` | [`LambdaS/PiTheorem.lean:704`](LambdaS/PiTheorem.lean#L704) |
| The solvability dichotomy (Theorem 8.1) | `LambdaS.Pi.mulScaleLaw_dichotomy` | [`LambdaS/PiTheorem.lean:732`](LambdaS/PiTheorem.lean#L732) |

## Dimensioned linear algebra

| Paper claim | Lean name | Location |
|---|---|---|
| Entry units (definition) | `LambdaS.entry` | [`LambdaS/Map.lean:164`](LambdaS/Map.lean#L164) |
| The calculus's entry units are the model's | `LambdaS.entry_toSpace` | [`LambdaS/Syntax.lean:352`](LambdaS/Syntax.lean#L352) |
| T-MCons enforces the model's entry units | `LambdaS.HasTy.mcons_entry` | [`LambdaS/Typing.lean:540`](LambdaS/Typing.lean#L540) |
| Rank-one units (Theorem 9.1) | `LambdaS.entry_rank_one` | [`LambdaS/Map.lean:176`](LambdaS/Map.lean#L176) |
| Composition entry units | `LambdaS.entry_comp` | [`LambdaS/Map.lean:187`](LambdaS/Map.lean#L187) |
| Endomorphism diagonals dimensionless | `LambdaS.entry_id_diag` | [`LambdaS/Map.lean:214`](LambdaS/Map.lean#L214) |
| Permutation products dimensionless | `LambdaS.entry_perm_prod` | [`LambdaS/Map.lean:202`](LambdaS/Map.lean#L202) |
| Eigenvalue unit identity | `LambdaS.eigenvalue_uom` | [`LambdaS/Map.lean:244`](LambdaS/Map.lean#L244) |
| Dual-map entries symmetric | `LambdaS.entry_dual_symm` | [`LambdaS/Map.lean:251`](LambdaS/Map.lean#L251) |
| Weighted norms dimensionless | `LambdaS.weighted_norm_dimensionless` | [`LambdaS/Map.lean:256`](LambdaS/Map.lean#L256) |
| Cholesky factors dimensionless | `LambdaS.cholesky_factor_dimensionless` | [`LambdaS/Map.lean:266`](LambdaS/Map.lean#L266) |
| Uniform spaces are scaled dimensionless spaces | `LambdaS.Space.uniform_iff_scale_triv` | [`LambdaS/Space.lean:91`](LambdaS/Space.lean#L91) |
| SVD entries share one unit | `LambdaS.svd_entry_const` | [`LambdaS/Map.lean:282`](LambdaS/Map.lean#L282) |
| Self-dual spaces are dimensionless | `LambdaS.transpose_comp_direct_iff` | [`LambdaS/Map.lean:296`](LambdaS/Map.lean#L296) |
| Uniform spaces carry a canonical metric | `LambdaS.uniform_canonical_metric` | [`LambdaS/Map.lean:309`](LambdaS/Map.lean#L309) |

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

## Pi arity descent

| Paper claim | Lean name | Location |
|---|---|---|
| Rational dimensionless coordinates | `LambdaS.Pi.piCoordinates` | [`LambdaS/PiTheorem.lean:353`](LambdaS/PiTheorem.lean#L353) |
| Arbitrary invariants descend to n minus rank coordinates | `LambdaS.Pi.invariant_descends` | [`LambdaS/PiTheorem.lean:407`](LambdaS/PiTheorem.lean#L407) |
| Signed Buckingham factorization at reduced arity | `LambdaS.Pi.mulScaleLaw_factorization_reduced` | [`LambdaS/PiTheorem.lean:624`](LambdaS/PiTheorem.lean#L624) |

## Dimension-level Pi theorem with conversion

| Paper claim | Lean name | Location |
|---|---|---|
| Only same-dimension oracle entries affect evaluation | `LambdaS.eval_congr_sameDim` | [`LambdaS/PiCoherent.lean:39`](LambdaS/PiCoherent.lean#L39) |
| Coherent valuation changes preserve scalar denotation | `LambdaS.den_eq_of_coherent` | [`LambdaS/PiCoherent.lean:92`](LambdaS/PiCoherent.lean#L92) |
| Converting programs obey the dimension-level scaling law | `LambdaS.Pi.den_mulScaleLaw_coherent` | [`LambdaS/PiCoherent.lean:135`](LambdaS/PiCoherent.lean#L135) |
| Converting programs factor through n minus dimension-rank groups | `LambdaS.Pi.den_pi_coherent` | [`LambdaS/PiCoherent.lean:159`](LambdaS/PiCoherent.lean#L159) |

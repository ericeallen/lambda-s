# Theorem index

Every declaration the paper cites, and the supporting
results behind them, with Lean name and location. Line numbers are for the commit that carries this file.
`scripts/Audit.lean` prints the axiom dependencies of every declaration below
(`scripts/verify_theorems_index.py` fails if one is missing from it); CI fails
if any depends on more than `propext`, `Classical.choice`, and `Quot.sound`.

## The calculus and its checker

| Paper claim | Lean name | Location |
|---|---|---|
| Typing rules (Figure 2) | `LambdaS.HasTy` | [`LambdaS/Typing.lean:430`](LambdaS/Typing.lean#L430) |
| Completeness; derivations unique | `LambdaS.check_eq` | [`LambdaS/Typing.lean:659`](LambdaS/Typing.lean#L659) |
| Triangularization preserves ground solution sets | `LambdaS.System.solves_triangulate_iff` | [`LambdaS/Unify.lean:339`](LambdaS/Unify.lean#L339) |
| The generic caster is well-typed | `LambdaS.Examples.caster` | [`LambdaS/Examples.lean:1017`](LambdaS/Examples.lean#L1017) |
| The velocity idiom | `LambdaS.Examples.velocity` | [`LambdaS/Examples.lean:99`](LambdaS/Examples.lean#L99) |
| Surface `in` elaborates by running the checker | `LambdaS.elabConvert` | [`LambdaS/Notation.lean:112`](LambdaS/Notation.lean#L112) |
| Elaboration succeeds iff scalar of the target's dimension | `LambdaS.elabConvert_isSome` | [`LambdaS/Notation.lean:125`](LambdaS/Notation.lean#L125) |
| The state-vector literal | `LambdaS.Examples.stateVec` | [`LambdaS/Examples.lean:1180`](LambdaS/Examples.lean#L1180) |
| A matrix literal, rank-one checked at introduction | `LambdaS.Examples.toTime` | [`LambdaS/Examples.lean:1202`](LambdaS/Examples.lean#L1202) |

## Operational semantics

| Paper claim | Lean name | Location |
|---|---|---|
| Instrumented evaluation rules | `LambdaS.eval` | [`LambdaS/Dynamics.lean:126`](LambdaS/Dynamics.lean#L126) |
| Numeric operations supplied by the carrier | `LambdaS.Num` | [`LambdaS/Num.lean:95`](LambdaS/Num.lean#L95) |

## Unit declarations

| Paper claim | Lean name | Location |
|---|---|---|
| Consistency, necessity (log form) | `LambdaS.dependency_forces` | [`LambdaS/Declare.lean:374`](LambdaS/Declare.lean#L374) |
| Consistency, necessity (product form) | `LambdaS.dependency_forces_mul` | [`LambdaS/Declare.lean:405`](LambdaS/Declare.lean#L405) |
| Consistency, sufficiency | `LambdaS.dependency_sufficient` | [`LambdaS/Declare.lean:447`](LambdaS/Declare.lean#L447) |
| Consistency characterized (log form) | `LambdaS.consistent_iff_dependencies` | [`LambdaS/Declare.lean:475`](LambdaS/Declare.lean#L475) |
| Consistency characterized (Theorem 3.1) | `LambdaS.consistent_iff_dependencies_mul` | [`LambdaS/Declare.lean:489`](LambdaS/Declare.lean#L489) |
| Redundant factor forced | `LambdaS.factor_chain_consistent` | [`LambdaS/Declare.lean:556`](LambdaS/Declare.lean#L556) |
| One-dimension well-formedness | `LambdaS.Decl.Sound` | [`LambdaS/Declare.lean:326`](LambdaS/Declare.lean#L326) |
| The yard set is satisfiable | `LambdaS.Examples.yard_satisfiable` | [`LambdaS/Examples.lean:589`](LambdaS/Examples.lean#L589) |
| A benign declaration cycle is satisfiable | `LambdaS.Examples.cycle_satisfiable` | [`LambdaS/Examples.lean:619`](LambdaS/Examples.lean#L619) |
| Dimension abbreviations elaborate by scoping alone | `LambdaS.DimAbbrev.elabDimDefs` | [`LambdaS/Declare.lean:600`](LambdaS/Declare.lean#L600) |
| Primary units: the declaration determines the dimension | `LambdaS.DimAbbrev.elabPrimary` | [`LambdaS/Declare.lean:612`](LambdaS/Declare.lean#L612) |
| The cyclic dimension pair, rejected at its second line | `LambdaS.Examples.dimCycle` | [`LambdaS/Examples.lean:518`](LambdaS/Examples.lean#L518) |
| A vicious declaration cycle is rejected | `LambdaS.Examples.cycle_conflict` | [`LambdaS/Examples.lean:625`](LambdaS/Examples.lean#L625) |
| The mistyped yard set is refuted | `LambdaS.Examples.yard_conflict` | [`LambdaS/Examples.lean:488`](LambdaS/Examples.lean#L488) |
| One yard per foot denotes 1, at yd/ft | `LambdaS.Algorithms.ydPerFt` | [`LambdaS/Algorithms.lean:250`](LambdaS/Algorithms.lean#L250) |
| Converted to unit 1, the declared 3 appears | `LambdaS.Algorithms.ydPerFtIn1` | [`LambdaS/Algorithms.lean:259`](LambdaS/Algorithms.lean#L259) |
| Converting one operand first, the same 3 | `LambdaS.Algorithms.ydPerFtViaFt` | [`LambdaS/Algorithms.lean:272`](LambdaS/Algorithms.lean#L272) |
| The redundant factor is forced | `LambdaS.Examples.yard_forced` | [`LambdaS/Examples.lean:476`](LambdaS/Examples.lean#L476) |

## Dynamics

| Paper claim | Lean name | Location |
|---|---|---|
| Preservation: a produced value has the predicted type | `LambdaS.eval_sound` | [`LambdaS/Soundness.lean:218`](LambdaS/Soundness.lean#L218) |
| Unit soundness (Theorem 4.1) | `LambdaS.unit_soundness_total` | [`LambdaS/Normalization.lean:776`](LambdaS/Normalization.lean#L776) |
| Every closed well-typed term evaluates at some fuel | `LambdaS.eval_terminates` | [`LambdaS/Normalization.lean:747`](LambdaS/Normalization.lean#L747) |
| Every larger fuel bound returns the same value | `LambdaS.eval_mono` | [`LambdaS/Normalization.lean:128`](LambdaS/Normalization.lean#L128) |
| Closed terms of linear-map type evaluate to matrices at their spaces | `LambdaS.lin_soundness_total` | [`LambdaS/Normalization.lean:789`](LambdaS/Normalization.lean#L789) |
| Totality at every type | `LambdaS.eval_total` | [`LambdaS/Normalization.lean:761`](LambdaS/Normalization.lean#L761) |
| Fuel accounting, checked by the binary | `LambdaS.QM.twoStateChecks` | [`LambdaS/QM.lean:387`](LambdaS/QM.lean#L387) |

## Denotational semantics and abstraction

| Paper claim | Lean name | Location |
|---|---|---|
| Convert-free terms ignore the valuation | `LambdaS.den_eq_of_convertFree` | [`LambdaS/Fundamental.lean:959`](LambdaS/Fundamental.lean#L959) |
| Valuation independence at higher type | `LambdaS.den_indep` | [`LambdaS/Fundamental.lean:869`](LambdaS/Fundamental.lean#L869) |
| Abstraction, convert-free (Theorem 5.1) | `LambdaS.fundamental_free` | [`LambdaS/Fundamental.lean:1128`](LambdaS/Fundamental.lean#L1128) |
| The coherent logical relation | `LambdaS.RelCo` | [`LambdaS/Fundamental.lean:429`](LambdaS/Fundamental.lean#L429) |
| The convert-free logical relation | `LambdaS.Rel` | [`LambdaS/Parametricity.lean:171`](LambdaS/Parametricity.lean#L171) |
| Abstraction, coherent (Theorem 5.2) | `LambdaS.fundamental` | [`LambdaS/Fundamental.lean:978`](LambdaS/Fundamental.lean#L978) |
| Theorem 5.2 at a moving rescaling | `LambdaS.Examples.fundamental_at_moving_rescale` | [`LambdaS/Examples.lean:1158`](LambdaS/Examples.lean#L1158) |
| The root scaling identity, all reals, positive factor | `LambdaS.mul_rpow_of_pos_left` | [`LambdaS/Parametricity.lean:381`](LambdaS/Parametricity.lean#L381) |
| The abstraction theorem at a root term | `LambdaS.sqrt_scales` | [`LambdaS/Fundamental.lean:1440`](LambdaS/Fundamental.lean#L1440) |
| Single-conversion invariance (Theorem 5.3) | `LambdaS.cvt_rel_iff_coherent` | [`LambdaS/Fundamental.lean:1287`](LambdaS/Fundamental.lean#L1287) |
| Coherent iff every single conversion is invariant | `LambdaS.coherent_iff_cvt_invariant` | [`LambdaS/Fundamental.lean:1484`](LambdaS/Fundamental.lean#L1484) |
| Coherent equals factoring through dimension | `LambdaS.Scaling.coherent_iff_factors` | [`LambdaS/Conversion.lean:450`](LambdaS/Conversion.lean#L450) |
| One base unit per dimension makes every rescaling coherent | `LambdaS.Scaling.coherent_of_dim_equiv` | [`LambdaS/Conversion.lean:464`](LambdaS/Conversion.lean#L464) |

## Accumulated ratios and the drift diagnostic

| Paper claim | Lean name | Location |
|---|---|---|
| Shapes | `LambdaS.Shape` | [`LambdaS/Ratio.lean:62`](LambdaS/Ratio.lean#L62) |
| Ratio expressions | `LambdaS.Tw` | [`LambdaS/Ratio.lean:153`](LambdaS/Ratio.lean#L153) |
| Semantic ratios | `LambdaS.SemTw` | [`LambdaS/Ratio.lean:355`](LambdaS/Ratio.lean#L355) |
| Ratio evaluation | `LambdaS.Tw.eval` | [`LambdaS/Ratio.lean:379`](LambdaS/Ratio.lean#L379) |
| The scaling law, twisted (two parameters) | `LambdaS.Twist.scaling` | [`LambdaS/Twist.lean:631`](LambdaS/Twist.lean#L631) |
| The twisted law at first order | `LambdaS.Twist.law` | [`LambdaS/Twist.lean:966`](LambdaS/Twist.lean#L966) |
| The drift law (both parameters) | `LambdaS.unitDrift_law` | [`LambdaS/Twist.lean:2253`](LambdaS/Twist.lean#L2253) |
| Declared magnitudes enter through the drift alone | `LambdaS.den_comp_of_drift` | [`LambdaS/Twist.lean:2266`](LambdaS/Twist.lean#L2266) |
| Drift 1 is declaration independence, open programs at any unit | `LambdaS.den_indep_of_driftFree` | [`LambdaS/Twist.lean:2280`](LambdaS/Twist.lean#L2280) |
| Drift 1 gives the unrestricted scaling law | `LambdaS.scaleLaw_of_driftFree` | [`LambdaS/Twist.lean:2295`](LambdaS/Twist.lean#L2295) |
| Drift 1 gives the scaling law at a matrix result | `LambdaS.scaleLaw_lin_of_driftFree` | [`LambdaS/Twist.lean:2029`](LambdaS/Twist.lean#L2029) |
| The same over an arbitrary context | `LambdaS.scaleLaw_lin_of_driftFree_gen` | [`LambdaS/Twist.lean:1997`](LambdaS/Twist.lean#L1997) |
| The drift diagnostic over an arbitrary context and a matrix result | `LambdaS.unitDriftGen` | [`LambdaS/Twist.lean:1944`](LambdaS/Twist.lean#L1944) |
| Drift 1 gives the scaling law at a vector result, per component | `LambdaS.scaleLaw_vec_of_driftFree` | [`LambdaS/Twist.lean:2125`](LambdaS/Twist.lean#L2125) |
| The same over an arbitrary context | `LambdaS.scaleLaw_vec_of_driftFree_gen` | [`LambdaS/Twist.lean:2097`](LambdaS/Twist.lean#L2097) |
| The drift diagnostic over an arbitrary context and a vector result | `LambdaS.unitDriftVecGen` | [`LambdaS/Twist.lean:2057`](LambdaS/Twist.lean#L2057) |
| Invariance iff trivial ratio (Theorem 6.1) | `LambdaS.Twist.invariant_iff` | [`LambdaS/Twist.lean:1077`](LambdaS/Twist.lean#L1077) |
| Decidability | `LambdaS.Tw.nfOne_eq_one_iff` | [`LambdaS/Twist.lean:1111`](LambdaS/Twist.lean#L1111) |
| The diagnostic's specification | `LambdaS.unitDrift_spec` | [`LambdaS/Twist.lean:2156`](LambdaS/Twist.lean#L2156) |
| Branch comparison at `+` | `LambdaS.Tw.normEq` | [`LambdaS/Twist.lean:1618`](LambdaS/Twist.lean#L1618) |
| Fuel-free open scalar normal form | `LambdaS.Tw.openNF` | [`LambdaS/RatioCompare.lean:129`](LambdaS/RatioCompare.lean#L129) |
| Open normal form preserves evaluation | `LambdaS.Tw.openNF_correct` | [`LambdaS/RatioCompare.lean:145`](LambdaS/RatioCompare.lean#L145) |
| Open normal forms exact at first-order contexts | `LambdaS.Tw.openNF_eq_iff` | [`LambdaS/RatioCompare.lean:186`](LambdaS/RatioCompare.lean#L186) |
| Branch comparison exact at first-order contexts | `LambdaS.Tw.normEq_firstOrder_iff` | [`LambdaS/Twist.lean:1634`](LambdaS/Twist.lean#L1634) |
| Accepts every comparison the bounded reducer accepts | `LambdaS.Tw.normEq_of_legacy` | [`LambdaS/Twist.lean:1644`](LambdaS/Twist.lean#L1644) |
| Open higher-order composition regression (kernel) | `LambdaS.RatioCompareExamples.open_composition_correct` | [`LambdaS/RatioCompareExamples.lean:67`](LambdaS/RatioCompareExamples.lean#L67) |
| Branch comparison, flat form | `LambdaS.Tw.scalarEq` | [`LambdaS/Twist.lean:1480`](LambdaS/Twist.lean#L1480) |
| Bounded reducer (fallback for function and unit-family inputs) | `LambdaS.Tw.norm` | [`LambdaS/Ratio.lean:518`](LambdaS/Ratio.lean#L518) |
| Bounded reduction preserves evaluation | `LambdaS.Tw.eval_norm` | [`LambdaS/Ratio.lean:824`](LambdaS/Ratio.lean#L824) |
| Reassociated conversions accepted | `LambdaS.Examples.addAssoc` | [`LambdaS/Examples.lean:974`](LambdaS/Examples.lean#L974) |
| Drift-free closed dimensionless programs are declaration-independent at the evaluator | `LambdaS.evalC_indep_of_driftFree` | [`LambdaS/Twist.lean:2308`](LambdaS/Twist.lean#L2308) |
| The ballistics case study (four verdicts) | `LambdaS.Examples.Ballistics` | [`LambdaS/Examples.lean:1553`](LambdaS/Examples.lean#L1553) |
| Sum of two converted inputs, accepted at m/ft | `LambdaS.Examples.addTwoVars` | [`LambdaS/Examples.lean:829`](LambdaS/Examples.lean#L829) |
| Genuinely drifting sum, declined | `LambdaS.Examples.addMixed` | [`LambdaS/Examples.lean:846`](LambdaS/Examples.lean#L846) |
| Agreeing sum through an internal abstraction, accepted | `LambdaS.Examples.hoSum` | [`LambdaS/Examples.lean:895`](LambdaS/Examples.lean#L895) |
| A visible application analyzes as its redex | `LambdaS.Examples.betaShared` | [`LambdaS/Examples.lean:939`](LambdaS/Examples.lean#L939) |
| Polymorphic round trip, drift-free uninstantiated | `LambdaS.Examples.casterRound` | [`LambdaS/Examples.lean:1083`](LambdaS/Examples.lean#L1083) |
| Leading lambda binders analyzed as inputs | `LambdaS.unitDriftLam` | [`LambdaS/Twist.lean:2179`](LambdaS/Twist.lean#L2179) |
| The stripped kernel is analyzed as an open term | `LambdaS.unitDriftLam_eq_unitDrift` | [`LambdaS/Twist.lean:2199`](LambdaS/Twist.lean#L2199) |
| The diagnostic through a leading abstraction, exact | `LambdaS.unitDriftLam_spec` | [`LambdaS/Twist.lean:2213`](LambdaS/Twist.lean#L2213) |
| Comparison exact for atom-free ratios (iff) | `LambdaS.Tw.normEq_iff_eval_eq` | [`LambdaS/Twist.lean:1676`](LambdaS/Twist.lean#L1676) |
| Flat comparison exact for atom-free ratios (iff) | `LambdaS.Tw.scalarEq_iff_eval_eq` | [`LambdaS/Twist.lean:1599`](LambdaS/Twist.lean#L1599) |
| log of a round-trip ratio, accepted at drift 1 | `LambdaS.Examples.logRoundTrip` | [`LambdaS/Examples.lean:912`](LambdaS/Examples.lean#L912) |
| log of a drifting argument, declined | `LambdaS.Examples.logDrifting` | [`LambdaS/Examples.lean:925`](LambdaS/Examples.lean#L925) |

## Adequacy and erasure

| Paper claim | Lean name | Location |
|---|---|---|
| Adequacy at the declared factors | `LambdaS.eval_adeq` | [`LambdaS/Adequacy.lean:342`](LambdaS/Adequacy.lean#L342) |
| Declared factors reach the real-valued evaluator (Theorem 7.1) | `LambdaS.evalC_convert_declared` | [`LambdaS/Adequacy.lean:845`](LambdaS/Adequacy.lean#L845) |
| Adequacy: the real-arithmetic evaluator computes the denotation | `LambdaS.evalC_eq_den` | [`LambdaS/Adequacy.lean:832`](LambdaS/Adequacy.lean#L832) |
| Erasure (Theorem 7.2) | `LambdaS.erasure_correct` | [`LambdaS/Erasure.lean:510`](LambdaS/Erasure.lean#L510) |
| The simulation behind it, no typing hypothesis | `LambdaS.eeval_erase` | [`LambdaS/Erasure.lean:296`](LambdaS/Erasure.lean#L296) |
| The erased evaluator computes the denotation, at `ℝ` | `LambdaS.eeval_den` | [`LambdaS/Erasure.lean:523`](LambdaS/Erasure.lean#L523) |
| One yard is three feet, at the evaluator | `LambdaS.Examples.one_yard_is_three_feet` | [`LambdaS/Examples.lean:645`](LambdaS/Examples.lean#L645) |
| One yard is 0.9144 meters, directly | `LambdaS.Examples.one_yard_in_meters` | [`LambdaS/Examples.lean:656`](LambdaS/Examples.lean#L656) |
| One yard is 0.9144 meters, through feet | `LambdaS.Examples.one_yard_in_meters_via_feet` | [`LambdaS/Examples.lean:671`](LambdaS/Examples.lean#L671) |
| The two routes agree at the evaluator | `LambdaS.Examples.yard_routes_agree` | [`LambdaS/Examples.lean:694`](LambdaS/Examples.lean#L694) |

## Dimensional analysis

| Paper claim | Lean name | Location |
|---|---|---|
| Conversion not definable convert-free | `LambdaS.NonDef.convert_not_definable` | [`LambdaS/NonDefinability.lean:412`](LambdaS/NonDefinability.lean#L412) |
| Square root not definable by arithmetic | `LambdaS.NonDef.sqrt_not_definable` | [`LambdaS/NonDefinability.lean:220`](LambdaS/NonDefinability.lean#L220) |
| The reflection into the arithmetic grammar | `LambdaS.NonDef.arith_of_hasTy` | [`LambdaS/NonDefinability.lean:273`](LambdaS/NonDefinability.lean#L273) |
| Square root not definable, at the term grammar | `LambdaS.NonDef.sqrt_not_definable_tm` | [`LambdaS/NonDefinability.lean:318`](LambdaS/NonDefinability.lean#L318) |
| No seed for Newton's method | `LambdaS.NonDef.no_newton_seed` | [`LambdaS/NonDefinability.lean:228`](LambdaS/NonDefinability.lean#L228) |
| No seed, at the term grammar | `LambdaS.NonDef.no_newton_seed_tm` | [`LambdaS/NonDefinability.lean:329`](LambdaS/NonDefinability.lean#L329) |
| The multiplicative scale law (definition) | `LambdaS.Pi.MulScaleLaw` | [`LambdaS/PiTheorem.lean:493`](LambdaS/PiTheorem.lean#L493) |
| Term-level multiplicative scale law | `LambdaS.Pi.den_mulScaleLaw` | [`LambdaS/PiTheorem.lean:903`](LambdaS/PiTheorem.lean#L903) |
| Term-level scale law from drift 1 | `LambdaS.Pi.den_mulScaleLaw_driftFree` | [`LambdaS/PiTheorem.lean:926`](LambdaS/PiTheorem.lean#L926) |
| Log transport, positivity hypothesis | `LambdaS.Pi.scaleLaw_of_mulScaleLaw` | [`LambdaS/PiTheorem.lean:765`](LambdaS/PiTheorem.lean#L765) |
| Pi, the factorization | `LambdaS.Pi.pi_theorem` | [`LambdaS/PiTheorem.lean:279`](LambdaS/PiTheorem.lean#L279) |
| Pi, multiplicative coordinates | `LambdaS.Pi.mulScaleLaw_factorization` | [`LambdaS/PiTheorem.lean:603`](LambdaS/PiTheorem.lean#L603) |
| Invariants are the dimensionless monomials | `LambdaS.Pi.invariant_iff_dimensionless` | [`LambdaS/PiTheorem.lean:307`](LambdaS/PiTheorem.lean#L307) |
| Buckingham's counting | `LambdaS.Pi.pi_count` | [`LambdaS/PiTheorem.lean:331`](LambdaS/PiTheorem.lean#L331) |
| The factorization is an equivalence | `LambdaS.Pi.piEquiv` | [`LambdaS/PiTheorem.lean:447`](LambdaS/PiTheorem.lean#L447) |
| The pendulum signature | `LambdaS.Pi.pendulum` | [`LambdaS/Pi.lean:139`](LambdaS/Pi.lean#L139) |
| The pendulum solution exhibited | `LambdaS.Pi.pendulum_period_solution` | [`LambdaS/Pi.lean:168`](LambdaS/Pi.lean#L168) |
| The pendulum ignores its mass, both halves | `LambdaS.Pi.pendulum_mass_absent` | [`LambdaS/PiTheorem.lean:954`](LambdaS/PiTheorem.lean#L954) |
| Mass is absent from every solution | `LambdaS.Pi.pendulum_period_independent_of_mass` | [`LambdaS/Pi.lean:157`](LambdaS/Pi.lean#L157) |
| Mass is absent from every dimensionless group | `LambdaS.Pi.pendulum_mass_drops_out` | [`LambdaS/Pi.lean:151`](LambdaS/Pi.lean#L151) |
| A once-appearing base unit forces zero in every invariant | `LambdaS.Pi.eq_zero_of_appears_once` | [`LambdaS/Pi.lean:107`](LambdaS/Pi.lean#L107) |
| A once-appearing base unit forces a zero exponent | `LambdaS.Pi.solution_eq_zero_of_appears_once` | [`LambdaS/Pi.lean:124`](LambdaS/Pi.lean#L124) |
| Signed equivalence, multiplicative coordinates | `LambdaS.Pi.piEquivSigned` | [`LambdaS/PiTheorem.lean:556`](LambdaS/PiTheorem.lean#L556) |
| Unsolvable signatures admit only zero | `LambdaS.Pi.mulScaleLaw_eq_zero_of_unsolvable` | [`LambdaS/PiTheorem.lean:710`](LambdaS/PiTheorem.lean#L710) |
| The solvability dichotomy over scaling laws | `LambdaS.Pi.mulScaleLaw_dichotomy` | [`LambdaS/PiTheorem.lean:738`](LambdaS/PiTheorem.lean#L738) |

## Dimensioned linear algebra

| Paper claim | Lean name | Location |
|---|---|---|
| Entry units (definition) | `LambdaS.entry` | [`LambdaS/Map.lean:163`](LambdaS/Map.lean#L163) |
| The calculus's entry units are the model's | `LambdaS.entry_toSpace` | [`LambdaS/Syntax.lean:355`](LambdaS/Syntax.lean#L355) |
| T-MCons enforces the model's entry units | `LambdaS.HasTy.mcons_entry` | [`LambdaS/Typing.lean:526`](LambdaS/Typing.lean#L526) |
| Rank-one units | `LambdaS.entry_rank_one` | [`LambdaS/Map.lean:175`](LambdaS/Map.lean#L175) |
| Composition entry units | `LambdaS.entry_comp` | [`LambdaS/Map.lean:186`](LambdaS/Map.lean#L186) |
| Endomorphism diagonals dimensionless | `LambdaS.entry_id_diag` | [`LambdaS/Map.lean:210`](LambdaS/Map.lean#L210) |
| Permutation products dimensionless | `LambdaS.entry_perm_prod` | [`LambdaS/Map.lean:201`](LambdaS/Map.lean#L201) |
| Eigenvalue unit identity | `LambdaS.eigenvalue_uom` | [`LambdaS/Map.lean:238`](LambdaS/Map.lean#L238) |
| Dual-map entries symmetric | `LambdaS.entry_dual_symm` | [`LambdaS/Map.lean:245`](LambdaS/Map.lean#L245) |
| Weighted norms dimensionless | `LambdaS.weighted_norm_dimensionless` | [`LambdaS/Map.lean:250`](LambdaS/Map.lean#L250) |
| Cholesky factors dimensionless | `LambdaS.cholesky_factor_dimensionless` | [`LambdaS/Map.lean:260`](LambdaS/Map.lean#L260) |
| Uniform spaces are scaled dimensionless spaces | `LambdaS.Space.uniform_iff_scale_triv` | [`LambdaS/Space.lean:91`](LambdaS/Space.lean#L91) |
| SVD entries share one unit | `LambdaS.svd_entry_const` | [`LambdaS/Map.lean:276`](LambdaS/Map.lean#L276) |
| Self-dual spaces are dimensionless | `LambdaS.transpose_comp_direct_iff` | [`LambdaS/Map.lean:290`](LambdaS/Map.lean#L290) |
| Uniform metric entries carry unit u⁻² | `LambdaS.uniform_canonical_metric` | [`LambdaS/Map.lean:305`](LambdaS/Map.lean#L305) |
| A fixed absolute tolerance, not parametric | `LambdaS.Examples.stopAbsolute` | [`LambdaS/Examples.lean:1819`](LambdaS/Examples.lean#L1819) |
| One Jacobi sweep, typed at the uniform space | `LambdaS.Examples.sweep` | [`LambdaS/Examples.lean:1775`](LambdaS/Examples.lean#L1775) |
| A transpose assembled from row extractions | `LambdaS.Examples.fromTimeT` | [`LambdaS/Examples.lean:1266`](LambdaS/Examples.lean#L1266) |
| Trace of a dimensioned endomorphism, at unit 1 | `LambdaS.Examples.traceTm` | [`LambdaS/Examples.lean:1307`](LambdaS/Examples.lean#L1307) |
| Determinant of a dimensioned endomorphism, at unit 1 | `LambdaS.Examples.detTm` | [`LambdaS/Examples.lean:1311`](LambdaS/Examples.lean#L1311) |
| Cofactor inverse, typed as an endomorphism | `LambdaS.Examples.invTm` | [`LambdaS/Examples.lean:1321`](LambdaS/Examples.lean#L1321) |

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
| The expectation as a curried function | `LambdaS.QM.expectation` | [`LambdaS/QM.lean:369`](LambdaS/QM.lean#L369) |

## Pi arity descent

| Paper claim | Lean name | Location |
|---|---|---|
| Rational dimensionless coordinates | `LambdaS.Pi.piCoordinates` | [`LambdaS/PiTheorem.lean:358`](LambdaS/PiTheorem.lean#L358) |
| Arbitrary invariants descend to n minus rank coordinates | `LambdaS.Pi.invariant_descends` | [`LambdaS/PiTheorem.lean:412`](LambdaS/PiTheorem.lean#L412) |
| Signed Buckingham factorization at reduced arity | `LambdaS.Pi.mulScaleLaw_factorization_reduced` | [`LambdaS/PiTheorem.lean:630`](LambdaS/PiTheorem.lean#L630) |

## Dimension-level Pi theorem with conversion

| Paper claim | Lean name | Location |
|---|---|---|
| Only same-dimension oracle entries affect evaluation | `LambdaS.eval_congr_sameDim` | [`LambdaS/PiCoherent.lean:42`](LambdaS/PiCoherent.lean#L42) |
| Coherent valuation changes preserve scalar denotation | `LambdaS.den_eq_of_coherent` | [`LambdaS/PiCoherent.lean:95`](LambdaS/PiCoherent.lean#L95) |
| Converting programs obey the dimension-level scaling law | `LambdaS.Pi.den_mulScaleLaw_coherent` | [`LambdaS/PiCoherent.lean:138`](LambdaS/PiCoherent.lean#L138) |
| The declined sum still obeys the dimension-level law | `LambdaS.Examples.addMixed_coherent` | [`LambdaS/PiExamples.lean:25`](LambdaS/PiExamples.lean#L25) |
| Converting programs factor through n minus dimension-rank groups | `LambdaS.Pi.den_pi_coherent` | [`LambdaS/PiCoherent.lean:163`](LambdaS/PiCoherent.lean#L163) |
| Pi for programs with conversion, as a dichotomy (Theorem 8.1) | `LambdaS.Pi.den_pi_coherent_dichotomy` | [`LambdaS/PiCoherent.lean:183`](LambdaS/PiCoherent.lean#L183) |

## Executable declaration solving and determinacy

| Paper claim | Lean name | Location |
|---|---|---|
| Executable rational elimination | `LambdaS.RationalSolver.solve` | [`LambdaS/RationalSolver.lean:218`](LambdaS/RationalSolver.lean#L218) |
| Rational solver soundness | `LambdaS.RationalSolver.solve_sound` | [`LambdaS/RationalSolver.lean:227`](LambdaS/RationalSolver.lean#L227) |
| Rational solver completeness | `LambdaS.RationalSolver.solve_isSome_iff` | [`LambdaS/RationalSolver.lean:232`](LambdaS/RationalSolver.lean#L232) |
| Solvability reflects through exact log interpretation | `LambdaS.RationalSolver.solvable_map_iff` | [`LambdaS/RationalSolver.lean:312`](LambdaS/RationalSolver.lean#L312) |
| Executable exact logarithmic equality | `LambdaS.LogFactor.isZero_iff` | [`LambdaS/LogFactor.lean:110`](LambdaS/LogFactor.lean#L110) |
| Exact factor semantics is injective | `LambdaS.LogFactor.interpret_injective` | [`LambdaS/LogFactor.lean:237`](LambdaS/LogFactor.lean#L237) |
| Inspectable radical output is exact | `LambdaS.LogFactor.radical_exp` | [`LambdaS/LogFactor.lean:99`](LambdaS/LogFactor.lean#L99) |
| Semantic determinacy is span membership | `LambdaS.Decl.determined_iff_coefficients` | [`LambdaS/Determinacy.lean:147`](LambdaS/Determinacy.lean#L147) |
| Global completeness decides all legal factors | `LambdaS.DeclarationComplete.check_iff_all_conversions_determined` | [`LambdaS/DeclarationComplete.lean:154`](LambdaS/DeclarationComplete.lean#L154) |
| Executable declaration consistency is exact | `LambdaS.DeclSolver.solve_isSome_iff` | [`LambdaS/DeclareSolver.lean:140`](LambdaS/DeclareSolver.lean#L140) |
| Computed declaration solutions satisfy valuations | `LambdaS.DeclSolver.solve_sound` | [`LambdaS/DeclareSolver.lean:129`](LambdaS/DeclareSolver.lean#L129) |
| Factor lookup decides determinacy | `LambdaS.DeclSolver.conversion_isSome_iff` | [`LambdaS/DeclareSolver.lean:200`](LambdaS/DeclareSolver.lean#L200) |
| Extracted radical agrees with every satisfying valuation | `LambdaS.DeclSolver.conversionExact_correct` | [`LambdaS/DeclareSolver.lean:253`](LambdaS/DeclareSolver.lean#L253) |
| Amplitude conversion nm^(-1/2) to m^(-1/2) extracts radicand 10^9, degree 2 | `LambdaS.DeclarationSolverExamples.Nanometer.exactAmplitude` | [`LambdaS/DeclarationSolverExamples.lean:246`](LambdaS/DeclarationSolverExamples.lean#L246) |
| Executable declaration checking, sound and complete (Theorem 3.2) | `LambdaS.DeclSolver.check_isSome_iff` | [`LambdaS/DeclareSolver.lean:315`](LambdaS/DeclareSolver.lean#L315) |
| Checked systems supply every legal conversion | `LambdaS.DeclSolver.Checked.conversionExact_isSome` | [`LambdaS/DeclareSolver.lean:332`](LambdaS/DeclareSolver.lean#L332) |
| Rational factor actually computed | `LambdaS.DeclarationSolverExamples.Length.linkedFactor_returned` | [`LambdaS/DeclarationSolverExamples.lean:81`](LambdaS/DeclarationSolverExamples.lean#L81) |
| Computed rational factor semantic correctness | `LambdaS.DeclarationSolverExamples.Length.linkedFactor_correct` | [`LambdaS/DeclarationSolverExamples.lean:97`](LambdaS/DeclarationSolverExamples.lean#L97) |
| Irrational factor actually computed | `LambdaS.DeclarationSolverExamples.Root.rootFactor_returned` | [`LambdaS/DeclarationSolverExamples.lean:123`](LambdaS/DeclarationSolverExamples.lean#L123) |
| Computed irrational factor semantic correctness | `LambdaS.DeclarationSolverExamples.Root.rootFactor_correct` | [`LambdaS/DeclarationSolverExamples.lean:139`](LambdaS/DeclarationSolverExamples.lean#L139) |

## Reproducing the worked examples

`lake exe lambdas` prints the particle-in-a-box report, the free-fall
report, the declared-conversion report (100 yards as 300 ft, as 91.44 m
directly, and as 91.44 m through feet: path independence made observable),
the two-state report with its numeric self-checks, the compiled-evaluator
validation lines, and one summary line each for the declaration-solver and
Jacobi batteries. It exits nonzero if any check fails, and CI asserts the
output. The same three yard numbers are asserted at build time by `#guard`s
in `LambdaS/Algorithms.lean`; the `#guard`s there and in
`LambdaS/Examples.lean`, `LambdaS/QM.lean`,
`LambdaS/RatioCompareExamples.lean`, and
`LambdaS/DeclarationSolverExamples.lean` run the checker, the drift
analysis, the evaluator, and the declaration solver during `lake build`, so
a wrong stated result would fail the build.

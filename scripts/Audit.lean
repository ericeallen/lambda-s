/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS

/-!
# Trust base audit

Prints the axiom dependencies of every declaration `THEOREMS.md` indexes
(every artifact identifier the paper cites, and the supporting results behind
them), grouped by module. The intended output mentions only `propext`,
`Classical.choice`, and `Quot.sound`; any occurrence of `sorryAx` is a
failure, and CI greps for it. `scripts/verify_theorems_index.py` fails when an
indexed declaration is missing from this file, so the list cannot drift from
the index.

Run with `lake env lean scripts/Audit.lean`.
-/

-- Typing
#print axioms LambdaS.check_eq
#print axioms LambdaS.HasTy
#print axioms LambdaS.elabConvert
#print axioms LambdaS.elabConvert_isSome

-- Conversion
#print axioms LambdaS.Scaling.coherent_iff_factors

-- Declare
#print axioms LambdaS.dependency_forces
#print axioms LambdaS.dependency_forces_mul
#print axioms LambdaS.dependency_sufficient
#print axioms LambdaS.consistent_iff_dependencies
#print axioms LambdaS.consistent_iff_dependencies_mul
#print axioms LambdaS.factor_chain_consistent
#print axioms LambdaS.Decl.Sound
#print axioms LambdaS.DimAbbrev.elabDimDefs
#print axioms LambdaS.DimAbbrev.elabPrimary

-- Normalization
#print axioms LambdaS.unit_soundness_total
#print axioms LambdaS.eval_total
#print axioms LambdaS.lin_soundness_total
#print axioms LambdaS.eval_sound

-- Fundamental
#print axioms LambdaS.fundamental_free
#print axioms LambdaS.fundamental
#print axioms LambdaS.cvt_rel_iff_coherent
#print axioms LambdaS.den_eq_of_convertFree
#print axioms LambdaS.den_indep
#print axioms LambdaS.sqrt_scales
#print axioms LambdaS.mul_rpow_of_pos_left

-- Twist
#print axioms LambdaS.Twist.scaling
#print axioms LambdaS.Twist.invariant_iff
#print axioms LambdaS.Tw.nfOne_eq_one_iff
#print axioms LambdaS.unitDrift_spec
#print axioms LambdaS.evalC_indep_of_driftFree
#print axioms LambdaS.Shape
#print axioms LambdaS.Tw
#print axioms LambdaS.SemTw
#print axioms LambdaS.Tw.eval
#print axioms LambdaS.Tw.scalarEq
#print axioms LambdaS.Tw.scalarEq_iff_eval_eq
#print axioms LambdaS.Tw.norm
#print axioms LambdaS.Tw.eval_norm
#print axioms LambdaS.Tw.normEq
#print axioms LambdaS.Tw.normEq_iff_eval_eq
#print axioms LambdaS.unitDriftLam
#print axioms LambdaS.unitDriftLam_eq_unitDrift
#print axioms LambdaS.unitDriftLam_spec
#print axioms LambdaS.Twist.law
#print axioms LambdaS.unitDrift_law
#print axioms LambdaS.den_comp_of_drift
#print axioms LambdaS.den_indep_of_driftFree
#print axioms LambdaS.scaleLaw_of_driftFree

-- Adequacy and Erasure
#print axioms LambdaS.eval_adeq
#print axioms LambdaS.evalC_convert_declared
#print axioms LambdaS.eeval_erase
#print axioms LambdaS.erasure_correct
#print axioms LambdaS.eeval_den

-- NonDefinability
#print axioms LambdaS.NonDef.convert_not_definable
#print axioms LambdaS.NonDef.sqrt_not_definable
#print axioms LambdaS.NonDef.no_newton_seed
#print axioms LambdaS.NonDef.arith_of_hasTy
#print axioms LambdaS.NonDef.sqrt_not_definable_tm
#print axioms LambdaS.NonDef.no_newton_seed_tm

-- Pi and PiTheorem
#print axioms LambdaS.Pi.pi_theorem
#print axioms LambdaS.Pi.invariant_iff_dimensionless
#print axioms LambdaS.Pi.pi_count
#print axioms LambdaS.Pi.piEquiv
#print axioms LambdaS.Pi.scaleLaw_of_mulScaleLaw
#print axioms LambdaS.Pi.piEquivSigned
#print axioms LambdaS.Pi.expScaleLaw_of_mulScaleLaw
#print axioms LambdaS.Pi.mulScaleLaw_factorization
#print axioms LambdaS.Pi.mulScaleLaw_factorization_pos
#print axioms LambdaS.Pi.mulScaleLaw_eq_zero_of_unsolvable
#print axioms LambdaS.Pi.mulScaleLaw_dichotomy
#print axioms LambdaS.Pi.den_mulScaleLaw
#print axioms LambdaS.Pi.den_mulScaleLaw_driftFree
#print axioms LambdaS.Pi.pendulum_mass_absent
#print axioms LambdaS.Pi.solution_eq_zero_of_appears_once
#print axioms LambdaS.Pi.MulScaleLaw
#print axioms LambdaS.Pi.pendulum
#print axioms LambdaS.Pi.pendulum_period_solution
#print axioms LambdaS.Pi.eq_zero_of_appears_once
#print axioms LambdaS.Pi.pendulum_mass_drops_out
#print axioms LambdaS.Pi.pendulum_period_independent_of_mass

-- Space and Map (Hart's taxonomy)
#print axioms LambdaS.Space.uniform_iff_scale_triv
#print axioms LambdaS.entry_rank_one
#print axioms LambdaS.entry_comp
#print axioms LambdaS.entry_id_diag
#print axioms LambdaS.entry_perm_prod
#print axioms LambdaS.eigenvalue_uom
#print axioms LambdaS.entry_dual_symm
#print axioms LambdaS.weighted_norm_dimensionless
#print axioms LambdaS.cholesky_factor_dimensionless
#print axioms LambdaS.svd_entry_const
#print axioms LambdaS.transpose_comp_direct_iff
#print axioms LambdaS.uniform_canonical_metric
#print axioms LambdaS.entry
#print axioms LambdaS.entry_toSpace
#print axioms LambdaS.HasTy.mcons_entry

-- Examples
#print axioms LambdaS.Examples.yard_satisfiable
#print axioms LambdaS.Examples.yard_conflict
#print axioms LambdaS.Examples.yard_forced
#print axioms LambdaS.Examples.one_yard_is_three_feet
#print axioms LambdaS.Examples.one_yard_in_meters
#print axioms LambdaS.Examples.fundamental_at_moving_rescale
#print axioms LambdaS.Examples.one_yard_in_meters_via_feet
#print axioms LambdaS.Examples.yard_routes_agree
#print axioms LambdaS.Examples.cycle_satisfiable
#print axioms LambdaS.Examples.cycle_conflict
#print axioms LambdaS.Examples.dimCycle
#print axioms LambdaS.Examples.caster
#print axioms LambdaS.Examples.casterRound
#print axioms LambdaS.Examples.velocity
#print axioms LambdaS.Examples.stateVec
#print axioms LambdaS.Examples.toTime
#print axioms LambdaS.Examples.addAssoc
#print axioms LambdaS.Examples.addTwoVars
#print axioms LambdaS.Examples.addMixed
#print axioms LambdaS.Examples.hoSum
#print axioms LambdaS.Examples.betaShared
#print axioms LambdaS.Examples.logRoundTrip
#print axioms LambdaS.Examples.logDrifting

-- QM and Algorithms (the worked programs)
#print axioms LambdaS.QM.groundEnergy
#print axioms LambdaS.QM.uncertainty
#print axioms LambdaS.QM.amplitude
#print axioms LambdaS.QM.density
#print axioms LambdaS.QM.probability
#print axioms LambdaS.QM.expectH
#print axioms LambdaS.QM.statePlusTm
#print axioms LambdaS.QM.hamiltonianTm
#print axioms LambdaS.QM.phase
#print axioms LambdaS.QM.expectation
#print axioms LambdaS.QM.twoStateChecks
#print axioms LambdaS.Algorithms.ydPerFt
#print axioms LambdaS.Algorithms.ydPerFtIn1
#print axioms LambdaS.Algorithms.ydPerFtViaFt

import LambdaS

/-!
# Trust base audit

Prints the axiom dependencies of every theorem the paper cites, plus the
worked examples and taxonomy results backing them, grouped by module. The
intended
output mentions only `propext`, `Classical.choice`, and `Quot.sound`; any
occurrence of `sorryAx` is a failure, and CI greps for it.

Run with `lake env lean scripts/Audit.lean`.
-/

-- Typing
#print axioms LambdaS.check_eq

-- Conversion
#print axioms LambdaS.Scaling.coherent_iff_factors

-- Declare
#print axioms LambdaS.dependency_forces
#print axioms LambdaS.dependency_forces_mul
#print axioms LambdaS.dependency_sufficient
#print axioms LambdaS.consistent_iff_dependencies
#print axioms LambdaS.consistent_iff_dependencies_mul
#print axioms LambdaS.factor_chain_consistent

-- Normalization
#print axioms LambdaS.unit_soundness_total
#print axioms LambdaS.eval_total

-- Fundamental
#print axioms LambdaS.fundamental_free
#print axioms LambdaS.fundamental
#print axioms LambdaS.cvt_rel_iff_coherent
#print axioms LambdaS.den_eq_of_convertFree
#print axioms LambdaS.den_indep

-- Twist
#print axioms LambdaS.Twist.scaling
#print axioms LambdaS.Twist.invariant_iff
#print axioms LambdaS.Tw.nfOne_eq_one_iff
#print axioms LambdaS.unitDrift_spec
#print axioms LambdaS.evalC_indep_of_driftFree

-- Adequacy and Erasure
#print axioms LambdaS.eval_adeq
#print axioms LambdaS.evalC_convert_declared
#print axioms LambdaS.eeval_erase
#print axioms LambdaS.erasure_correct
#print axioms LambdaS.eeval_den

-- NonDefinability
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
#print axioms LambdaS.Pi.mulScaleLaw_factorization
#print axioms LambdaS.Pi.den_mulScaleLaw
#print axioms LambdaS.Pi.pendulum_mass_absent
#print axioms LambdaS.Pi.solution_eq_zero_of_appears_once

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

-- Examples
#print axioms LambdaS.Examples.yard_satisfiable
#print axioms LambdaS.Examples.yard_conflict
#print axioms LambdaS.Examples.yard_forced
#print axioms LambdaS.Examples.one_yard_is_three_feet
#print axioms LambdaS.Examples.one_yard_in_metres
#print axioms LambdaS.Examples.fundamental_at_moving_rescale

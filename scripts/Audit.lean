import LambdaS

/-!
# Trust base audit

Prints the axiom dependencies of the theorems the paper states. The intended
output mentions only `propext`, `Classical.choice`, and `Quot.sound`; any
occurrence of `sorryAx` is a failure, and CI greps for it.

Run with `lake env lean scripts/Audit.lean`.
-/

#print axioms LambdaS.check_eq
#print axioms LambdaS.dependency_forces
#print axioms LambdaS.unit_soundness_total
#print axioms LambdaS.fundamental_free
#print axioms LambdaS.fundamental
#print axioms LambdaS.cvt_rel_iff_coherent
#print axioms LambdaS.Twist.scaling
#print axioms LambdaS.Tw.nfOne_eq_one_iff
#print axioms LambdaS.unitDrift_spec
#print axioms LambdaS.evalC_convert_declared
#print axioms LambdaS.eeval_erase
#print axioms LambdaS.erasure_correct
#print axioms LambdaS.Pi.pi_theorem
#print axioms LambdaS.Pi.invariant_iff_dimensionless
#print axioms LambdaS.Pi.pi_count
#print axioms LambdaS.Pi.piEquiv
#print axioms LambdaS.eval_total
#print axioms LambdaS.eval_adeq
#print axioms LambdaS.eeval_den
#print axioms LambdaS.den_eq_of_convertFree
#print axioms LambdaS.den_indep
#print axioms LambdaS.NonDef.sqrt_not_definable
#print axioms LambdaS.NonDef.no_newton_seed
#print axioms LambdaS.Twist.invariant_iff
#print axioms LambdaS.evalC_indep_of_driftFree
#print axioms LambdaS.factor_chain_consistent
#print axioms LambdaS.Examples.yard_satisfiable
#print axioms LambdaS.Examples.yard_conflict
#print axioms LambdaS.Examples.yard_forced
#print axioms LambdaS.Examples.one_yard_is_three_feet
#print axioms LambdaS.Examples.one_yard_in_metres
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
#print axioms LambdaS.Pi.pendulum_mass_absent
#print axioms LambdaS.Pi.solution_eq_zero_of_appears_once

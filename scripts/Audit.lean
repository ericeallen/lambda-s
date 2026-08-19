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

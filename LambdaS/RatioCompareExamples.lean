/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Twist

/-!
# Regression predictions and checks for fuel-free ratio comparison

Predictions recorded before execution: internal higher-order composition computes
its expected unit; independent scalar inputs remain distinct; beta-equivalent
open terms agree; unit binders and vector/matrix projections preserve results.
Unknown function/family contexts are tested separately against the legacy
comparison. They retain the legacy bounded comparison, including acceptance when
substitution creates another redex; no new completeness claim is made there.
-/

namespace LambdaS.RatioCompareExamples

private abbrev B := Fin 1
private def u : UExp B 0 := ⟨fun _ => 1, Fin.elim0⟩
private abbrev S := Shape.scalar
private abbrev F := Shape.arrow S S

/-- Function composition doubles the number of applications. -/
private def twice {Θ : List Shape} : Tw B 0 Θ (.arrow F F) :=
  .lam (.lam (.app (.var 1 rfl) (.app (.var 1 rfl) (.var 0 rfl))))

/-- At depth n the function applies its multiplier 2^n times. -/
private def composed (n : Nat) {Θ : List Shape} : Tw B 0 Θ F :=
  match n with
  | 0 => .lam (.mul (.var 0 rfl) (.unit u))
  | n + 1 => .app twice (composed n)

/-- Closed scalar result after 256 internally composed function applications. -/
private def deepClosed : Tw B 0 [] S := .app (composed 8) (.unit 1)
#guard Tw.normEq deepClosed (.unit (Term.rpow u 256))
#guard !Tw.normEq deepClosed (.unit (Term.rpow u 255))

private def x : Tw B 0 [S, S] S := .var 0 rfl
private def y : Tw B 0 [S, S] S := .var 1 rfl
#guard !Tw.normEq x y
#guard Tw.normEq (.app (.lam (.var 0 rfl)) x) x
#guard Tw.normEq (.app (composed 6) x) (.mul x (.unit (Term.rpow u 64)))
#guard !Tw.normEq (.app (composed 6) x) (.mul y (.unit (Term.rpow u 64)))
#guard Tw.normEq (.div (.mul x y) x) y
#guard Tw.normEq (.qpow (.qpow x (1/3)) 3) x

/-- A unit binder passes its instantiation through an internal function. -/
private def unitFamily : Tw B 0 [S, S] (.bind S) :=
  .ulam (.app (.lam (.mul (.var 0 rfl) (.unit (Term.ofVar 0)))) (.var 0 rfl))
#guard Tw.normEq (.uapp unitFamily u) (.mul x (.unit u))

private def v : Tw B 0 [.vec 2, .mat 2 2] (.vec 2) := .var 0 rfl
private def M : Tw B 0 [.vec 2, .mat 2 2] (.mat 2 2) := .var 1 rfl
#guard !Tw.normEq (.proj v 0) (.proj v 1)
#guard Tw.normEq (.proj (.app (.lam (.var 0 rfl)) v) 1) (.proj v 1)
#guard Tw.normEq (.proj (.row (.app (.lam (.var 0 rfl)) M) 1) 0)
  (.proj (.row M 1) 0)
#guard !Tw.normEq (.proj (.row M 0) 1) (.proj (.row M 1) 0)
#guard Tw.normEq (.proj (.veccons x (.veccons y .vecnil)) 1) y
#guard Tw.normEq (.proj (.row (.matcons (.veccons x .vecnil) .matnil) 0) 0) x

/-- A kernel-checked instance of the new exactness theorem, with unrestricted
internal higher-order syntax and arbitrary unknown scalar inputs. -/
theorem open_composition_correct (ψ : Scaling B 0) (ρ : TwEnv [S, S]) :
    Tw.eval ψ (.app (composed 3) x) ρ =
      Tw.eval ψ (.mul x (.unit (Term.rpow u 8))) ρ :=
  Tw.normEq_sound _ _ (by decide +kernel) ψ ρ

/-- Free unit variables and fresh scalar coordinates occupy disjoint slots. -/
private def scopedInput : Tw B 2 [S] S := .var 0 rfl
#guard !Tw.normEq scopedInput (.unit (Term.ofVar 0))
#guard !Tw.normEq (.unit (Term.ofVar 0) : Tw B 2 [S] S) (.unit (Term.ofVar 1))
#guard Tw.normEq (.uapp (.ulam (.mul (.var 0 rfl) (.unit (Term.ofVar 0))))
    (Term.ofVar 1)) (.mul scopedInput (.unit (Term.ofVar 1)))

/-- An internal unit family is passed through a higher-order identity function. -/
private def passedFamily : Tw B 0 [S, S] (.bind S) :=
  .app (.lam (.var 0 rfl)) unitFamily
#guard Tw.normEq (.uapp passedFamily u) (.mul x (.unit u))

/-! ## Explicit higher-order boundary and prior-acceptance comparison -/

private def unknownApplication : Tw B 0 [F, S] S := .app (.var 0 rfl) (.var 1 rfl)
#guard Tw.normEq unknownApplication unknownApplication
#guard Tw.normEq (.div unknownApplication unknownApplication) (.unit 1)
#guard !Tw.normEq unknownApplication (.var 1 rfl)
#guard Tw.normEq (.app (.lam (.var 0 rfl)) unknownApplication) unknownApplication

/-- A substitution-created redex in a context containing an unknown function.
The unknown function need not occur: selection is by context, not liveness. -/
private def higherOrderBoundary : Tw B 0 [F, S] S :=
  .app (.lam (.app (.var 0 rfl) (.var 2 rfl))) (.lam (.var 0 rfl))
private def higherOrderInput : Tw B 0 [F, S] S := .var 1 rfl
-- Both the legacy comparison and the retained higher-order fallback accept.
#guard Tw.scalarEq higherOrderBoundary.norm higherOrderInput.norm
#guard Tw.normEq higherOrderBoundary higherOrderInput
-- The kernel independently confirms that the compared terms are equivalent.
theorem higherOrderBoundary_equal (ψ : Scaling B 0) (ρ : TwEnv [F, S]) :
    Tw.eval ψ higherOrderBoundary ρ = Tw.eval ψ higherOrderInput ρ := by
  rfl

/-- A composed conversion ratio weakened into an unused arrow-valued context,
matching the substitution-created-redex mechanism of `Examples.hoSum`. -/
private def weakenedComposition : Tw B 0 [F] S :=
  (.app (composed 2) (.unit 1) : Tw B 0 [] S).weakenR
#guard Tw.scalarEq weakenedComposition.norm (Tw.unit (Term.rpow u 4) : Tw B 0 [F] S).norm
#guard Tw.normEq weakenedComposition (.unit (Term.rpow u 4))

private def unknownFamily : Tw B 0 [.bind S] S := .uapp (.var 0 rfl) u
#guard Tw.normEq unknownFamily unknownFamily
#guard Tw.normEq (.uapp (.ulam (.uapp (.var 0 rfl) (Term.ofVar 0))) u) unknownFamily
#guard !Tw.normEq unknownFamily (.unit 1)

end LambdaS.RatioCompareExamples

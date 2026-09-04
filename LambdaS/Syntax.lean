/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Map
import LambdaS.Unify

/-!
# Syntax of Λs

Kennedy's Λu attaches units to scalars. Λs distributes them over an index type,
so the primitive is a **space** and scalars are the one-point case.

## Representation choices

Three, all forced by wanting a *decidable* checker rather than chosen for
elegance.

**Unit expressions are exponent vectors, not trees.** A unit expression with `k`
unit variables in scope is a `Term B (Fin k)`: the very structure
`LambdaS.Unify` solves systems over. Units form a free abelian group, so a
normal form *is* an exponent vector, and equality is vector equality with no
normalization pass to write or verify. `m * s / m` and `s` are literally the
same object.

**Scope is a type index.** `Ty B D j k` and `Tm B D j k` carry the numbers of
enclosing `∀δ` and `∀u:d` binders, so well-scopedness is a typing invariant
rather than a side condition, and substitution has nowhere to go wrong.

**A space is the list of units its components carry.** This is `LambdaS.Space`
at a finite index type, written structurally: a space *is* its unit
assignment. Ordering is the indexing: `[m, s]` and `[s, m]` are isomorphic but
not equal, because a linear map's entry `(j,i)` carries `δ_W(j)/δ_V(i)` and
identifying them would let a matrix's columns permute silently.

## Explicit typing, and why it matters here

`Λu.e` and `e[μ]` are **written, not inferred**, exactly as in Kennedy's Λu. So
the checker needs substitution and decidable equality but never unification,
types stay unique, and `infer` is provably complete as well as sound. The
unification development in `LambdaS.Unify` is for a future *inference* engine,
where let-generalization forces it; nothing here depends on it.
-/

namespace LambdaS

variable {B : Type}

/-! ## Unit expressions -/

/-- A unit expression with `k` unit variables in scope. -/
abbrev UExp (B : Type) (k : ℕ) := Term B (Fin k)

namespace Term

variable {V : Type}

@[ext] theorem ext' {s t : Term B V} (hb : s.base = t.base) (hv : s.vars = t.vars) :
    s = t := by cases s; cases t; simp_all

instance [Fintype B] [DecidableEq B] [Fintype V] [DecidableEq V] :
    DecidableEq (Term B V) := fun s t =>
  decidable_of_iff (s.base = t.base ∧ s.vars = t.vars)
    ⟨fun ⟨hb, hv⟩ => ext' hb hv, fun h => by subst h; exact ⟨rfl, rfl⟩⟩

/-- The trivial unit. -/
def one : Term B V := ⟨fun _ => 0, fun _ => 0⟩

instance : One (Term B V) := ⟨one⟩

/-- Unit multiplication: exponents add. -/
def mul (s t : Term B V) : Term B V :=
  ⟨fun b => s.base b + t.base b, fun v => s.vars v + t.vars v⟩

/-- Unit inverse: exponents negate. -/
def inv (t : Term B V) : Term B V := ⟨fun b => -t.base b, fun v => -t.vars v⟩

/-- Unit division. -/
def div (s t : Term B V) : Term B V :=
  ⟨fun b => s.base b - t.base b, fun v => s.vars v - t.vars v⟩

/-- Rational powers. Total: every unit expression has an `n`-th root. -/
def rpow (t : Term B V) (q : ℚ) : Term B V :=
  ⟨fun b => q * t.base b, fun v => q * t.vars v⟩

@[simp] theorem one_base (b : B) : (1 : Term B V).base b = 0 := rfl
@[simp] theorem one_vars (v : V) : (1 : Term B V).vars v = 0 := rfl
@[simp] theorem mul_base (s t : Term B V) (b : B) :
    (mul s t).base b = s.base b + t.base b := rfl
@[simp] theorem mul_vars (s t : Term B V) (v : V) :
    (mul s t).vars v = s.vars v + t.vars v := rfl
@[simp] theorem inv_base (t : Term B V) (b : B) : (inv t).base b = -t.base b := rfl
@[simp] theorem inv_vars (t : Term B V) (v : V) : (inv t).vars v = -t.vars v := rfl
@[simp] theorem div_base (s t : Term B V) (b : B) :
    (div s t).base b = s.base b - t.base b := rfl
@[simp] theorem div_vars (s t : Term B V) (v : V) :
    (div s t).vars v = s.vars v - t.vars v := rfl
@[simp] theorem rpow_base (t : Term B V) (q : ℚ) (b : B) :
    (rpow t q).base b = q * t.base b := rfl
@[simp] theorem rpow_vars (t : Term B V) (q : ℚ) (v : V) :
    (rpow t q).vars v = q * t.vars v := rfl

/-- A base unit as a unit expression. -/
def ofBase [DecidableEq B] (b₀ : B) : Term B V :=
  ⟨fun b => if b = b₀ then 1 else 0, fun _ => 0⟩

/-- A unit variable as a unit expression. -/
def ofVar [DecidableEq V] (v₀ : V) : Term B V :=
  ⟨fun _ => 0, fun v => if v = v₀ then 1 else 0⟩

end Term

namespace UExp

variable {k : ℕ}

/-- Substitute `σ` for de Bruijn unit variable `0`, discharging one binder.

Linear in the exponents, because substitution into an element of a free abelian
group *is* a linear map. -/
def subst (t : UExp B (k + 1)) (σ : UExp B k) : UExp B k :=
  ⟨fun b => t.base b + t.vars 0 * σ.base b,
   fun i => t.vars i.succ + t.vars 0 * σ.vars i⟩

/-- Introduce a fresh unit variable, unused. -/
def weaken (t : UExp B k) : UExp B (k + 1) :=
  ⟨t.base, fun i => Fin.cases 0 (fun j => t.vars j) i⟩

/-- Substituting into a weakened expression changes nothing: the fresh
variable was unused. -/
@[simp] theorem subst_weaken (t : UExp B k) (σ : UExp B k) : subst (weaken t) σ = t := by
  ext b <;> simp [subst, weaken]

end UExp


/-! ## Simultaneous substitution

Single-variable substitution is not closed under going beneath a binder: pushing
`σ` into `∀u. τ` must shift `σ` past the new variable *and* leave the bound one
alone. The standard fix is to define everything from a **simultaneous**
substitution, and to define single substitution and weakening as instances of it.

Λs gets that cheaply. Simultaneous substitution is a linear map on exponent
vectors, so its identity, composition and homomorphism laws are `Finset`
arithmetic rather than structural inductions. Only the walk over types is
structural, and there the sole interesting case is the quantifier. -/

/-- Substitute a unit expression for every unit variable at once. -/
def substU {k k₀ : ℕ} (η : Fin k → UExp B k₀) (u : UExp B k) : UExp B k₀ :=
  ⟨fun b => u.base b + ∑ i, u.vars i * (η i).base b,
   fun v => ∑ i, u.vars i * (η i).vars v⟩

@[simp] theorem substU_base {k k₀ : ℕ} (η : Fin k → UExp B k₀) (u : UExp B k) (b : B) :
    (substU η u).base b = u.base b + ∑ i, u.vars i * (η i).base b := rfl

@[simp] theorem substU_vars {k k₀ : ℕ} (η : Fin k → UExp B k₀) (u : UExp B k)
    (v : Fin k₀) : (substU η u).vars v = ∑ i, u.vars i * (η i).vars v := rfl

/-- The identity substitution. -/
def idU (B : Type) (k : ℕ) : Fin k → UExp B k := fun i => Term.ofVar i

/-- Extend a substitution under a binder: the bound variable maps to itself and
everything else is shifted past it. This clause is the whole content of the
de Bruijn discipline. -/
def liftU {k k₀ : ℕ} (η : Fin k → UExp B k₀) : Fin (k + 1) → UExp B (k₀ + 1) :=
  Fin.cases (Term.ofVar 0) fun i => (η i).weaken

@[simp] theorem substU_ofVar {k k₀ : ℕ} (η : Fin k → UExp B k₀) (i : Fin k) :
    substU η (Term.ofVar i) = η i := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_) <;>
    simp [Term.ofVar, Finset.sum_ite_eq']

@[simp] theorem substU_id {k : ℕ} (u : UExp B k) : substU (idU B k) u = u := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_) <;>
    simp [idU, Term.ofVar]

theorem weaken_ofVar {k : ℕ} (i : Fin k) :
    UExp.weaken (Term.ofVar i : UExp B k) = Term.ofVar i.succ := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_)
  · simp [UExp.weaken, Term.ofVar]
  · cases v using Fin.cases with
    | zero =>
      simp only [UExp.weaken, Term.ofVar, Fin.cases_zero]
      exact (if_neg (Ne.symm (Fin.succ_ne_zero i))).symm
    | succ j => simp [UExp.weaken, Term.ofVar, Fin.succ_inj]

@[simp] theorem liftU_id {k : ℕ} : liftU (idU B k) = idU B (k + 1) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [liftU, idU]
  | succ j => simp [liftU, idU, weaken_ofVar]

/-- The empty substitution, at the closed scope. -/
def nilU (B : Type) : Fin 0 → UExp B 0 := fun i => i.elim0

@[simp] theorem substU_nil (u : UExp B 0) : substU (nilU B) u = u := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_)
  · simp
  · exact v.elim0

@[simp] theorem map_substU_id {k : ℕ} (V : List (UExp B k)) :
    V.map (substU (idU B k)) = V := by
  induction V with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- Substitution is a homomorphism of the unit group, which is what lets a
typing rule that multiplies units survive it. -/
@[simp] theorem substU_one {k k₀ : ℕ} (η : Fin k → UExp B k₀) :
    substU η (1 : UExp B k) = 1 := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_) <;> simp

theorem substU_mul {k k₀ : ℕ} (η : Fin k → UExp B k₀) (u w : UExp B k) :
    substU η (Term.mul u w) = Term.mul (substU η u) (substU η w) := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_) <;>
    simp only [substU_base, substU_vars, Term.mul_base, Term.mul_vars, add_mul,
      Finset.sum_add_distrib]; ring

theorem substU_div {k k₀ : ℕ} (η : Fin k → UExp B k₀) (u w : UExp B k) :
    substU η (Term.div u w) = Term.div (substU η u) (substU η w) := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_) <;>
    simp only [substU_base, substU_vars, Term.div_base, Term.div_vars, sub_mul,
      Finset.sum_sub_distrib]; ring

theorem substU_rpow {k k₀ : ℕ} (η : Fin k → UExp B k₀) (u : UExp B k) (q : ℚ) :
    substU η (Term.rpow u q) = Term.rpow (substU η u) q := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_)
  · simp only [substU_base, Term.rpow_base, Term.rpow_vars, mul_add, Finset.mul_sum]
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun _ _ => by ring)
  · simp only [substU_vars, Term.rpow_vars, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Composition.** The lemma a substitution development usually pays for with a
structural induction; here both sides are linear maps. -/
theorem substU_comp {k k₁ k₂ : ℕ} (η₂ : Fin k₁ → UExp B k₂) (η₁ : Fin k → UExp B k₁)
    (u : UExp B k) :
    substU η₂ (substU η₁ u) = substU (fun i => substU η₂ (η₁ i)) u := by
  have key : ∀ g : Fin k₁ → ℚ,
      (∑ x, (∑ i, u.vars i * (η₁ i).vars x) * g x)
        = ∑ i, u.vars i * ∑ x, (η₁ i).vars x * g x := by
    intro g
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_)
  · simp only [substU_base, substU_vars, key, mul_add, Finset.sum_add_distrib]
    ring
  · simp only [substU_vars, key]

theorem substU_weaken {k k₀ : ℕ} (η : Fin k → UExp B k₀) (u : UExp B k) :
    substU (liftU η) u.weaken = (substU η u).weaken := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_)
  · simp only [substU_base, UExp.weaken, liftU, Fin.sum_univ_succ, Fin.cases_zero,
      Fin.cases_succ]
    simp [Term.ofVar]
  · cases v using Fin.cases with
    | zero =>
      simp only [substU_vars, UExp.weaken, liftU, Fin.sum_univ_succ, Fin.cases_zero,
        Fin.cases_succ]
      simp [Term.ofVar]
    | succ w =>
      simp only [substU_vars, UExp.weaken, liftU, Fin.sum_univ_succ, Fin.cases_zero,
        Fin.cases_succ]
      simp [Term.ofVar]

/-- Substituting into a weakened expression ignores whatever was put at index
zero: the weakened expression does not mention it. -/
theorem substU_weaken_cons {k k₀ : ℕ} (w : UExp B k₀) (ξ : Fin k → UExp B k₀)
    (t : UExp B k) : substU (Fin.cons w ξ) (UExp.weaken t) = substU ξ t := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_) <;>
    simp [UExp.weaken, Fin.sum_univ_succ]

theorem liftU_comp {k k₁ k₂ : ℕ} (η₂ : Fin k₁ → UExp B k₂) (η₁ : Fin k → UExp B k₁) :
    liftU (fun i => substU η₂ (η₁ i)) = fun i => substU (liftU η₂) (liftU η₁ i) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [liftU]
  | succ j => simp [liftU, substU_weaken]

/-! ## Spaces -/

/-- A **space** with `k` unit variables in scope: the list of units carried by
its components. The index type is `Fin V.length`, the assignment is `V.get`. -/
abbrev Sp (B : Type) (k : ℕ) := List (UExp B k)

namespace Sp

/-- The dual space carries reciprocal units. -/
def dual {k} (V : Sp B k) : Sp B k := V.map Term.inv

/-- Scaling a space by a unit. -/
def scale {k} (V : Sp B k) (d : UExp B k) : Sp B k := V.map (Term.mul · d)

/-- Substitute through a space. -/
def subst {k} (V : Sp B (k + 1)) (σ : UExp B k) : Sp B k := V.map (UExp.subst · σ)

/-- Weaken a space. -/
def weaken {k} (V : Sp B k) : Sp B (k + 1) := V.map UExp.weaken

@[simp] theorem subst_weaken {k} (V : Sp B k) (σ : UExp B k) :
    subst (weaken V) σ = V := by
  simp [subst, weaken, List.map_map, Function.comp_def]

end Sp

/-! ## Dimensions

A dimension expression has exactly the structure a unit expression does: the
dimension group is free abelian on base dimensions, just as the unit group is
free abelian on base units. So `DExp` *is* `UExp` at the dimension alphabet, and
every operation (multiplication, division, rational powers, substitution,
weakening, decidable equality) is reused rather than rebuilt.

`dimension Velocity = Length/Time` is therefore `Term.div`, an abbreviation with
nothing left to check. Unit definitions are the interesting case and live in
`LambdaS.Declare`, because `unit yard = 3 foot` declares a generator **and** an
equation, and equations can conflict.

## Why dimension *variables*

The alternative is two unit quantifiers, `∀u` and `∀u:d`. It does not work. An
unbounded `∀u` still has to say *something* about `u`'s dimension, and there is
no right answer: reporting the trivial dimension claims `u` is dimensionless, so
`convert x u 1` typechecks under a binder that promised nothing; reporting
"unknown" makes `dimOf` partial and threads `Option` through every dimension
lemma.

Abstracting the dimension is the answer, and it collapses the two quantifiers
into one:

  `∀u. τ`  ≡  `∀δ. ∀u:δ. τ`

Unbounded quantification is bounded quantification at a dimension variable.
`dimOf` stays total, `convert` under `∀u` is rejected because `δ` matches
nothing, and there is a single quantifier rule to state and prove.
-/

/-- A dimension expression with `j` dimension variables in scope. Literally a
unit expression over base dimensions: the two are the same free abelian group
construction, so `UExp`'s whole API applies. -/
abbrev DExp (D : Type) (j : ℕ) := UExp D j

/-- A **unit system**: the dimension each base unit measures.

`dim` need not be injective: `metre` and `foot` share a dimension, which is what
lets Λs avoid restricting compound units to one named unit per dimension. Nor
need it land on a generator: `joule` can be declared directly at
`Mass·Length²·Time⁻²` rather than needing a base dimension of its own, which is
what makes `dimension` definitions worth having.

Base units have **closed** dimensions: a generator's dimension cannot mention a
dimension variable, since those are bound by types. -/
class UnitSys (B D : Type) where
  /-- The dimension each base unit measures. -/
  dim : B → DExp D 0

/-- A **dimension context**: the declared dimension of each unit variable in
scope. `∀u:d. τ` extends it by `d`. -/
abbrev DCtx (D : Type) (j k : ℕ) := Fin k → DExp D j

namespace DCtx

variable {D : Type} {j k : ℕ}

/-- The empty context: a closed term has no unit variables in scope. -/
def nil (D : Type) : DCtx D 0 0 := fun i => i.elim0

/-- Extend under a unit binder. -/
def cons (d : DExp D j) (Δ : DCtx D j k) : DCtx D j (k + 1) := Fin.cases d Δ

/-- Extend under a dimension binder: every declared dimension is weakened into
the larger dimension scope. -/
def weakenDim (Δ : DCtx D j k) : DCtx D (j + 1) k := fun i => (Δ i).weaken

/-- Discharge a dimension binder. -/
def substDim (Δ : DCtx D (j + 1) k) (σ : DExp D j) : DCtx D j k :=
  fun i => (Δ i).subst σ

@[simp] theorem substDim_weakenDim (Δ : DCtx D j k) (σ : DExp D j) :
    substDim (weakenDim Δ) σ = Δ := by
  funext i; simp [substDim, weakenDim]

end DCtx

/-- The **dimension of a unit expression**, relative to a dimension context.

Linear in the exponent vector: a matrix product, with the naive "each base unit
has one base dimension" the special case where every column is a standard basis
vector. Base units contribute only to base dimensions; the dimension *variables*
of the result come entirely from the context. -/
def dimOf [Fintype B] [UnitSys B D] {j k} (Δ : DCtx D j k) (u : UExp B k) : DExp D j :=
  ⟨fun d => (∑ b, u.base b * (UnitSys.dim (D := D) b).base d)
          + ∑ i, u.vars i * (Δ i).base d,
   fun v => ∑ i, u.vars i * (Δ i).vars v⟩

/-- A unit variable has exactly its declared dimension. -/
@[simp] theorem dimOf_ofVar [Fintype B] [UnitSys B D] {j k} (Δ : DCtx D j k) (i : Fin k) :
    dimOf (D := D) Δ (Term.ofVar i : UExp B k) = Δ i := by
  refine Term.ext' (funext fun d => ?_) (funext fun v => ?_) <;>
    simp only [dimOf, Term.ofVar, zero_mul, Finset.sum_const_zero, zero_add] <;>
    · rw [Finset.sum_eq_single i] <;> simp_all

/-- Weakening the dimension context weakens the dimension. -/
@[simp] theorem dimOf_weakenDim [Fintype B] [UnitSys B D] {j k} (Δ : DCtx D j k)
    (u : UExp B k) :
    dimOf (D := D) Δ.weakenDim u = (dimOf (D := D) Δ u).weaken := by
  refine Term.ext' (funext fun d => ?_) (funext fun v => ?_)
  · simp [dimOf, DCtx.weakenDim, UExp.weaken]
  · refine Fin.cases ?_ (fun v => ?_) v <;>
      simp [dimOf, DCtx.weakenDim, UExp.weaken]

/-- A weakened unit has the dimension it had before the context grew. -/
@[simp] theorem dimOf_weaken_cons [Fintype B] [UnitSys B D] {j k} (Δ : DCtx D j k)
    (e : DExp D j) (u : UExp B k) :
    dimOf (D := D) (Δ.cons e) (UExp.weaken u) = dimOf (D := D) Δ u := by
  refine Term.ext' (funext fun d => ?_) (funext fun v => ?_) <;>
    simp [dimOf, DCtx.cons, UExp.weaken, Fin.sum_univ_succ]

/-- Substituting the shift is weakening. -/
@[simp] theorem substU_shift {k : ℕ} (t : UExp B k) :
    substU (fun i => Term.ofVar i.succ) t = t.weaken := by
  refine Term.ext' (funext fun b => ?_) (funext fun v => ?_)
  · simp [substU, UExp.weaken, Term.ofVar]
  · refine Fin.cases ?_ (fun v => ?_) v
    · simp only [substU, UExp.weaken, Term.ofVar, Fin.cases_zero]
      exact Finset.sum_eq_zero fun i _ => by simp [(Fin.succ_ne_zero i).symm]
    · simp [substU, UExp.weaken, Term.ofVar]

/-- Two units are **interchangeable** when they have the same dimension.

Note what is *not* here. Before dimension contexts this also demanded
`u.vars = v.vars`, a conservative stand-in for not knowing a unit variable's
dimension. With `Δ` supplying it the clause is gone, and `convert` works under a
bounded quantifier, which is what makes a dimension-typed quantity usable. -/
def SameDim [Fintype B] [UnitSys B D] {j k} (Δ : DCtx D j k) (u v : UExp B k) : Prop :=
  dimOf (D := D) Δ u = dimOf (D := D) Δ v

instance [Fintype B] [Fintype D] [DecidableEq D] [UnitSys B D] {j k}
    (Δ : DCtx D j k) (u v : UExp B k) : Decidable (SameDim Δ u v) := by
  unfold SameDim; infer_instance

/-! ## Types -/

/-- Types of Λs, indexed by the number of **dimension** variables and the number
of **unit** variables in scope.

Six formers, one unit quantifier. `∀u. τ` is not primitive: it is
`∀δ. ∀u:δ. τ`, and the free theorems that need a genuinely unconstrained unit
get one by abstracting its dimension. -/
inductive Ty (B D : Type) : ℕ → ℕ → Type where
  /-- A scalar quantity carrying a unit. The one-point space. -/
  | Q {j k} : UExp B k → Ty B D j k
  | arrow {j k} : Ty B D j k → Ty B D j k → Ty B D j k
  /-- A vector over a space. -/
  | vec {j k} : Sp B k → Ty B D j k
  /-- A linear map `V ⊸ W`. Entry `(j,i)` carries `δ_W(j) / δ_V(i)`, which is
  Hart's rank-one condition holding by construction. -/
  | lin {j k} : Sp B k → Sp B k → Ty B D j k
  /-- Unit polymorphism bounded by a dimension, `∀u:d. τ`. -/
  | all {j k} : DExp D j → Ty B D j (k + 1) → Ty B D j k
  /-- Dimension polymorphism, `∀δ. τ`. Together with `all` this is unbounded
  unit quantification. -/
  | allDim {j k} : Ty B D (j + 1) k → Ty B D j k

namespace Ty

variable {D : Type}

/-- Push a unit substitution and a dimension substitution through a type.

Every other substitution on types is an instance of this one. The quantifier
cases are the only interesting clauses, and they are where the earlier
definitions were wrong: going under `∀u:d` must map the *bound* variable to
itself and shift everything else past it, which is exactly `liftU`. -/
def ground : {j k j₀ k₀ : ℕ} → (Fin k → UExp B k₀) → (Fin j → DExp D j₀) →
    Ty B D j k → Ty B D j₀ k₀
  | _, _, _, _, η, _, .Q u => .Q (substU η u)
  | _, _, _, _, η, δ, .arrow a b => .arrow (ground η δ a) (ground η δ b)
  | _, _, _, _, η, _, .vec V => .vec (V.map (substU η))
  | _, _, _, _, η, _, .lin V W => .lin (V.map (substU η)) (W.map (substU η))
  | _, _, _, _, η, δ, .all d τ => .all (substU δ d) (ground (liftU η) δ τ)
  | _, _, _, _, η, δ, .allDim τ => .allDim (ground η (liftU δ) τ)

/-- Substitute a unit expression for the outermost **unit** variable. -/
def subst {j k} (τ : Ty B D j (k + 1)) (σ : UExp B k) : Ty B D j k :=
  ground (Fin.cons σ (idU B k)) (idU D j) τ

/-- Weaken into a larger **unit**-variable scope. -/
def weaken {j k} (τ : Ty B D j k) : Ty B D j (k + 1) :=
  ground (fun i => Term.ofVar i.succ) (idU D j) τ

/-- Substitute a dimension expression for the outermost **dimension** variable.
Units are untouched: a unit expression cannot mention a dimension variable. -/
def substDim {j k} (τ : Ty B D (j + 1) k) (σ : DExp D j) : Ty B D j k :=
  ground (idU B k) (Fin.cons σ (idU D j)) τ

/-- Weaken into a larger **dimension**-variable scope. -/
def weakenDim {j k} (τ : Ty B D j k) : Ty B D (j + 1) k :=
  ground (idU B k) (fun i => Term.ofVar i.succ) τ

/-- Grounding by the identity does nothing. -/
@[simp] theorem ground_id : ∀ {j k : ℕ} (τ : Ty B D j k),
    ground (idU B k) (idU D j) τ = τ := by
  intro j k τ
  induction τ with
  | Q u => simp [ground]
  | arrow a b iha ihb => simp [ground, iha, ihb]
  | vec V => simp [ground]
  | lin V W => simp [ground]
  | all d τ ih => simp [ground, liftU_id, ih]
  | allDim τ ih => simp [ground, liftU_id, ih]

/-- **Grounding composes.** Two substitutions in sequence are the substitution
that maps each variable through both. -/
theorem ground_comp : ∀ {j k j₁ k₁ j₂ k₂ : ℕ} (η₂ : Fin k₁ → UExp B k₂)
    (δ₂ : Fin j₁ → DExp D j₂) (η₁ : Fin k → UExp B k₁) (δ₁ : Fin j → DExp D j₁)
    (τ : Ty B D j k),
    ground η₂ δ₂ (ground η₁ δ₁ τ)
      = ground (fun i => substU η₂ (η₁ i)) (fun i => substU δ₂ (δ₁ i)) τ := by
  intro j k j₁ k₁ j₂ k₂ η₂ δ₂ η₁ δ₁ τ
  induction τ generalizing j₁ k₁ j₂ k₂ with
  | Q u => simp [ground, substU_comp]
  | arrow a b iha ihb => simp [ground, iha, ihb]
  | vec V => simp [ground, List.map_map, Function.comp_def, substU_comp]
  | lin V W => simp [ground, List.map_map, Function.comp_def, substU_comp]
  | all d τ ih => simp [ground, substU_comp, ih, liftU_comp]
  | allDim τ ih => simp [ground, ih, liftU_comp]

/-- Decidable equality, by structural recursion. Written by hand rather than
derived: the deriving handler cannot carry the `[Fintype B]` constraint that
`DecidableEq (UExp B k)` needs. -/
def decEq [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D] :
    {j k : ℕ} → (a b : Ty B D j k) → Decidable (a = b)
  | _, _, .Q u, .Q v => decidable_of_iff (u = v) (by simp)
  | _, _, .vec V, .vec W => decidable_of_iff (V = W) (by simp)
  | _, _, .lin V W, .lin V' W' => decidable_of_iff (V = V' ∧ W = W') (by simp)
  | _, _, .arrow a b, .arrow c d =>
      match decEq a c, decEq b d with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h1, _ => isFalse (fun h => by cases h; exact h1 rfl)
      | _, isFalse h2 => isFalse (fun h => by cases h; exact h2 rfl)
  | _, _, .allDim a, .allDim b =>
      match decEq a b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (fun he => by cases he; exact h rfl)
  | _, _, .all d a, .all e b =>
      if hde : d = e then
        match decEq a b with
        | isTrue h => isTrue (by subst hde; subst h; rfl)
        | isFalse h => isFalse (fun he => by cases he; exact h rfl)
      else isFalse (fun he => by cases he; exact hde rfl)
  | _, _, .Q _, .arrow _ _ | _, _, .Q _, .vec _
  | _, _, .Q _, .lin _ _ | _, _, .Q _, .all _ _
  | _, _, .Q _, .allDim _ | _, _, .arrow _ _, .Q _
  | _, _, .arrow _ _, .vec _ | _, _, .arrow _ _, .lin _ _
  | _, _, .arrow _ _, .all _ _ | _, _, .arrow _ _, .allDim _
  | _, _, .vec _, .Q _ | _, _, .vec _, .arrow _ _
  | _, _, .vec _, .lin _ _ | _, _, .vec _, .all _ _
  | _, _, .vec _, .allDim _ | _, _, .lin _ _, .Q _
  | _, _, .lin _ _, .arrow _ _ | _, _, .lin _ _, .vec _
  | _, _, .lin _ _, .all _ _ | _, _, .lin _ _, .allDim _
  | _, _, .all _ _, .Q _ | _, _, .all _ _, .arrow _ _
  | _, _, .all _ _, .vec _ | _, _, .all _ _, .lin _ _
  | _, _, .all _ _, .allDim _ | _, _, .allDim _, .Q _
  | _, _, .allDim _, .arrow _ _ | _, _, .allDim _, .vec _
  | _, _, .allDim _, .lin _ _ | _, _, .allDim _, .all _ _ =>
      isFalse (fun h => by cases h)

instance [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D] {j k : ℕ} :
    DecidableEq (Ty B D j k) := decEq

/-- Weakening then grounding by an extended environment ignores the extension:
the weakened type does not mention the new variable. This is what lets a context
captured outside a unit binder be reused inside it. -/
theorem ground_weaken {j k j₀ k₀ : ℕ} (η : Fin k → UExp B k₀)
    (δ : Fin j → DExp D j₀) (w : UExp B k₀) (σ : Ty B D j k) :
    ground (Fin.cons w η) δ (weaken σ) = ground η δ σ := by
  rw [weaken, ground_comp]
  congr 1
  · funext i; simp
  · funext i; simp [idU]

/-- **The quantifier case.** Grounding under a binder and then substituting the
instantiating unit is the same as grounding with the environment extended by it.

This is the lemma the `uapp` case of soundness turns on, and it is where the
corrected `liftU` earns its place. -/
theorem ground_liftU_subst {j k j₀ k₀ : ℕ} (η : Fin k → UExp B k₀)
    (δ : Fin j → DExp D j₀) (w : UExp B k₀) (τ : Ty B D j (k + 1)) :
    subst (ground (liftU η) δ τ) w = ground (Fin.cons w η) δ τ := by
  rw [subst, ground_comp]
  congr 1
  · funext i
    cases i using Fin.cases with
    | zero => simp [liftU]
    | succ m => simp [liftU, substU_weaken_cons]
  · funext i; simp

/-- The dimension analogue of `ground_weaken`. -/
theorem ground_weakenDim {j k j₀ k₀ : ℕ} (η : Fin k → UExp B k₀)
    (δ : Fin j → DExp D j₀) (w : DExp D j₀) (σ : Ty B D j k) :
    ground η (Fin.cons w δ) (weakenDim σ) = ground η δ σ := by
  rw [weakenDim, ground_comp]
  congr 1
  · funext i; simp [idU]
  · funext i; simp

/-- The dimension analogue of `ground_liftU_subst`. -/
theorem ground_liftD_substDim {j k j₀ k₀ : ℕ} (η : Fin k → UExp B k₀)
    (δ : Fin j → DExp D j₀) (w : DExp D j₀) (τ : Ty B D (j + 1) k) :
    substDim (ground η (liftU δ) τ) w = ground η (Fin.cons w δ) τ := by
  rw [substDim, ground_comp]
  congr 1
  · funext i; simp
  · funext i
    cases i using Fin.cases with
    | zero => simp [liftU]
    | succ m => simp [liftU, substU_weaken_cons]

/-- Grounding a single substitution: the same as grounding with the environment
extended by the grounded instantiation. This is what turns `uapp`'s result type
into something the closure's own environment can produce. -/
theorem ground_subst {j k j₀ k₀ : ℕ} (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀)
    (μ : UExp B k) (τ : Ty B D j (k + 1)) :
    ground η δ (subst τ μ) = ground (Fin.cons (substU η μ) η) δ τ := by
  rw [subst, ground_comp]
  congr 1
  · funext i
    cases i using Fin.cases with
    | zero => simp
    | succ m => simp [idU]
  · funext i; simp [idU]

/-- The dimension analogue. -/
theorem ground_substDim {j k j₀ k₀ : ℕ} (η : Fin k → UExp B k₀)
    (δ : Fin j → DExp D j₀) (d : DExp D j) (τ : Ty B D (j + 1) k) :
    ground η δ (substDim τ d) = ground η (Fin.cons (substU δ d) δ) τ := by
  rw [substDim, ground_comp]
  congr 1
  · funext i; simp [idU]
  · funext i
    cases i using Fin.cases with
    | zero => simp
    | succ m => simp [idU]


/-! ## The skeleton

Erase every unit and dimension and a type becomes a plain simple type. Nothing in
the calculus's *shape* depends on units, which is why substituting one leaves the
skeleton alone. That is what makes the normalization argument in
`LambdaS.Normalization` Tait's rather than Girard's. -/

/-- The size of a type's skeleton. -/
def skel : {j k : ℕ} → Ty B D j k → ℕ
  | _, _, .Q _ => 1
  | _, _, .vec _ => 1
  | _, _, .lin _ _ => 1
  | _, _, .arrow a b => skel a + skel b + 1
  | _, _, .all _ τ => skel τ + 1
  | _, _, .allDim τ => skel τ + 1

/-- **Substitution does not change the skeleton.** -/
@[simp] theorem skel_ground : ∀ {j k j₀ k₀ : ℕ} (η : Fin k → UExp B k₀)
    (δ : Fin j → DExp D j₀) (τ : Ty B D j k),
    skel (ground η δ τ) = skel τ := by
  intro j k j₀ k₀ η δ τ
  induction τ generalizing j₀ k₀ with
  | Q u => rfl
  | vec V => rfl
  | lin V W => rfl
  | arrow a b iha ihb => simp [ground, skel, iha, ihb]
  | all d τ ih => simp [ground, skel, ih]
  | allDim τ ih => simp [ground, skel, ih]

@[simp] theorem skel_subst {j k : ℕ} (τ : Ty B D j (k + 1)) (μ : UExp B k) :
    skel (subst τ μ) = skel τ := by simp [subst]

@[simp] theorem skel_substDim {j k : ℕ} (τ : Ty B D (j + 1) k) (d : DExp D j) :
    skel (substDim τ d) = skel τ := by simp [substDim]

/-- Substituting into a weakened type changes nothing. The type-level statement
that a unit binder binds a genuinely fresh variable.

With `subst` and `weaken` both built from `ground`, this is composition plus the
identity law rather than a structural induction of its own. -/
@[simp] theorem subst_weaken {j k} (τ : Ty B D j k) (σ : UExp B k) :
    subst (weaken τ) σ = τ := by
  rw [subst, weaken, ground_comp]
  have h₁ : (fun i => substU (Fin.cons σ (idU B k)) (Term.ofVar i.succ)) = idU B k := by
    funext i; simp [idU]
  have h₂ : (fun i => substU (idU D j) (idU D j i)) = idU D j := by funext i; simp
  rw [h₁, h₂, ground_id]

/-- The same for the dimension binder. -/
@[simp] theorem substDim_weakenDim {j k} (τ : Ty B D j k) (σ : DExp D j) :
    substDim (weakenDim τ) σ = τ := by
  rw [substDim, weakenDim, ground_comp]
  have h₁ : (fun i => substU (idU B k) (idU B k i)) = idU B k := by funext i; simp
  have h₂ : (fun i => substU (Fin.cons σ (idU D j)) (Term.ofVar i.succ)) = idU D j := by
    funext i; simp [idU]
  rw [h₁, h₂, ground_id]

end Ty

/-! ## Terms -/

/-- Terms of Λs, with de Bruijn indices for value variables and type indices for
the dimension- and unit-variable scopes. -/
inductive Tm (B D : Type) : ℕ → ℕ → Type where
  | var {j k} : ℕ → Tm B D j k
  | lam {j k} : Ty B D j k → Tm B D j k → Tm B D j k
  | app {j k} : Tm B D j k → Tm B D j k → Tm B D j k
  /-- Every literal is dimensionless. There is no unitless *type*, only `1`. -/
  | lit {j k} : ℚ → Tm B D j k
  /-- A unit constant, so `m : Q m`. This is what makes `1.3 m` work. -/
  | ucon {j k} : UExp B k → Tm B D j k
  | mul {j k} : Tm B D j k → Tm B D j k → Tm B D j k
  | div {j k} : Tm B D j k → Tm B D j k → Tm B D j k
  /-- Addition, where unit errors are caught. -/
  | add {j k} : Tm B D j k → Tm B D j k → Tm B D j k
  /-- The `n`-th root. Primitive, because it is not definable from the field
  operations; total over ℚ exponents. -/
  | root {j k} : ℕ → Tm B D j k → Tm B D j k
  | idx {j k} : Tm B D j k → ℕ → Tm B D j k
  | mapp {j k} : Tm B D j k → Tm B D j k → Tm B D j k
  | comp {j k} : Tm B D j k → Tm B D j k → Tm B D j k
  /-- The empty vector, at the empty space. -/
  | vnil {j k} : Tm B D j k
  /-- A scalar consed onto a vector: the vector introduction step. The unit of
  the new component is read off the scalar's type, so the constructor carries
  no annotation. -/
  | vcons {j k} : Tm B D j k → Tm B D j k → Tm B D j k
  /-- The zero-row matrix, carrying its column space. The annotation is the
  design point: a matrix with no rows still has a width, and nothing else
  could supply it. -/
  | mnil {j k} : Sp B k → Tm B D j k
  /-- A row consed onto a matrix: output unit `w`, a row (a vector term whose
  components carry `w / δ_V(i)`), and the rest of the matrix. The annotation
  `w` is needed because a row over an empty column space determines no output
  unit. -/
  | mcons {j k} : UExp B k → Tm B D j k → Tm B D j k → Tm B D j k
  /-- Logarithm. Requires a **dimensionless** argument, which is what makes the
  base-measure problem a type error: a probability density is not dimensionless,
  so `log p` does not typecheck. -/
  | log {j k} : Tm B D j k → Tm B D j k
  /-- Exponential. Also requires a dimensionless argument.

  This is what makes `exp (-i·E·t/ħ)` a *typed* statement: the phase of a
  quantum time evolution must be dimensionless, and the rule enforces it. -/
  | exp {j k} : Tm B D j k → Tm B D j k
  /-- Unit abstraction, `Λu:d. e`. -/
  | ulam {j k} : DExp D j → Tm B D j (k + 1) → Tm B D j k
  /-- Unit application, `e[μ]`. Checks that `μ` has the declared dimension. -/
  | uapp {j k} : Tm B D j k → UExp B k → Tm B D j k
  /-- Dimension abstraction, `Λδ. e`. -/
  | dlam {j k} : Tm B D (j + 1) k → Tm B D j k
  /-- Dimension application, `e{d}`. -/
  | dapp {j k} : Tm B D j k → DExp D j → Tm B D j k
  /-- Conversion, `e in v`, written `convert e u v` with the **source** unit `u`
  carried explicitly.

  A term constructor rather than sugar for a multiplication, so that the trusted
  core checks the dimensions and determines the factor. Under the elaboration
  alternative a wrong factor would still typecheck, putting the Mars Climate
  Orbiter failure outside the trusted boundary.

  This is the only form that can observe a unit, and so the only form that
  costs parametricity: a term containing it is scale-invariant for **coherent**
  scalings rather than for all of them. See `LambdaS.Conversion`. -/
  | convert {j k} : Tm B D j k → UExp B k → UExp B k → Tm B D j k

/-- A typing context. -/
abbrev Ctx (B D : Type) (j k : ℕ) := List (Ty B D j k)

namespace Ctx

/-- Weakening under a unit binder. -/
def weaken {B D j k} (Γ : Ctx B D j k) : Ctx B D j (k + 1) := Γ.map Ty.weaken

/-- Weakening under a dimension binder. -/
def weakenDim {B D j k} (Γ : Ctx B D j k) : Ctx B D (j + 1) k := Γ.map Ty.weakenDim

end Ctx

end LambdaS

import LambdaS.Uom

/-!
# Unification of units

Type inference for units is unification modulo the equational theory of abelian
groups. Kennedy showed this is decidable with principal solutions; this file is
the beginning of a mechanization of that, specialized to ℚ exponents.

## Why ℚ makes this linear algebra

Over ℤ the unit group is a lattice and solving requires Hermite or Smith normal
form. Over ℚ it is a vector space, and the whole problem becomes linear algebra
over a field.

Better, it **decomposes**. A unit term's variable coefficients are *scalars*
(`vars : V → ℚ`), not per-base vectors, so a single system of equations gives an
independent linear system for each base unit — all sharing the same coefficient
matrix. One elimination serves every base unit. That structural fact is built
into `Term` rather than proved about it, and `Term.solves_iff` below is where it
becomes visible.

## The algorithm

Gaussian elimination, with `Term.reduce` as the row operation. Two facts make it
work, and they are the whole content:

* reducing `u` against a pivot equation `t` **kills the pivot variable** in `u`
  (`reduce_pivot`);
* reducing **preserves the solution set**, given that the pivot equation itself
  holds (`solves_reduce_iff`).

Termination is structural: `triangulate` recurses on a list of equations whose
length strictly decreases, so there is no measure to invent and no well-founded
argument to discharge.

## Status

Proved here:

* the per-base decomposition (`Term.solves_iff`);
* single-equation elimination, **sound** (`Term.solves_elim`) and **principal**
  (`Term.elim_eq_of_solves` — any solution is *forced* to agree with it);
* row reduction kills the pivot and preserves solutions (`Term.reduce_pivot`,
  `Term.solves_reduce_iff`);
* multi-equation systems, with reduction preserving the solution set
  (`System.solves_reduceAll_iff`) and isolating the pivot
  (`System.reduceAll_pivot_zero`);
* triangularization, terminating structurally, preserving the solution set
  **exactly** — an `iff`, so nothing is lost and nothing gained
  (`System.solves_triangulate_iff`);
* the rigid residual case, decided by inspection with no search
  (`System.solves_of_no_vars`, `System.solves_of_pivot_none`).

Not proved here: the **constructor**. Forward elimination and back-substitution
are each verified, but they are not yet composed into a function
`System B V → Option (Assign B V)` returning a most general unifier, with a
proof that it does. Every ingredient is in place; the assembly is not. Until it
lands, `LambdaS.Map`'s results rest on an algebra whose solver is verified in
pieces rather than end to end.
-/

namespace LambdaS

/-- A unit term over base units `B` with unification variables `V`.

`base b` is the exponent of base unit `b`; `vars v` is the exponent of variable
`v`. A term denotes the formal product `∏ b^(base b) · ∏ v^(vars v)`.

Note the asymmetry that does all the work: `vars` is `V → ℚ`, not `V → B → ℚ`.
A variable stands for a whole unit, so it enters every base unit's equation with
the *same* scalar coefficient. -/
structure Term (B V : Type*) where
  base : B → ℚ
  vars : V → ℚ

namespace Term

variable {B V : Type*}

/-- An assignment sends each unification variable to a ground unit.

Reducible, so `Function.update` and the rest of the `Pi` API apply to it
directly — the same structurality choice made for `Space`. -/
abbrev Assign (B V : Type*) := V → Uom B

/-- Applying an assignment: exponents combine linearly. -/
def eval [Fintype V] (t : Term B V) (σ : Assign B V) : Uom B :=
  Uom.ofExp fun b => t.base b + ∑ v, t.vars v * Uom.exp (σ v) b

@[simp] theorem exp_eval [Fintype V] (t : Term B V) (σ : Assign B V) (b : B) :
    Uom.exp (t.eval σ) b = t.base b + ∑ v, t.vars v * Uom.exp (σ v) b := rfl

/-- An assignment *solves* a term when the term evaluates to the trivial unit —
i.e. when the equation it encodes holds. -/
def Solves [Fintype V] (σ : Assign B V) (t : Term B V) : Prop := t.eval σ = 1

/-- **Decomposition.** A single unit equation is equivalent to one independent
scalar equation per base unit, all sharing the coefficient vector `t.vars`.

This is the statement that unification over ℚ is `|B|` linear systems with a
common matrix, and hence one Gaussian elimination. -/
theorem solves_iff [Fintype V] (σ : Assign B V) (t : Term B V) :
    Solves σ t ↔ ∀ b, t.base b + ∑ v, t.vars v * Uom.exp (σ v) b = 0 := by
  constructor
  · intro h b
    have := congrFun h b
    simpa [Solves, eval, Uom.ofExp] using congrArg Multiplicative.toAdd this
  · intro h
    ext b
    simpa using h b

/-- **Rigid mismatch.** When no variable occurs, the equation is solvable exactly
when it already holds on the nose. This is the error case of unification, and it
is decidable pointwise. -/
theorem solves_of_no_vars [Fintype V] (t : Term B V) (hv : t.vars = fun _ => 0)
    (σ : Assign B V) : Solves σ t ↔ t.base = fun _ => 0 := by
  rw [solves_iff]
  constructor
  · intro h; funext b; simpa [hv] using h b
  · intro h b; simp [hv, h]

section Elim

variable [Fintype V] [DecidableEq V]

/-- **Elimination.** Given a variable `v₀` occurring with nonzero exponent, solve
the equation for it, taking the other variables' values as given.

This is the single step of the unification algorithm: `v₀` is determined by the
rest, so each step removes one variable. -/
def elim (t : Term B V) (v₀ : V) (rest : Assign B V) : Assign B V :=
  Function.update rest v₀ <| Uom.ofExp fun b =>
    -(t.base b + ∑ v ∈ Finset.univ.erase v₀, t.vars v * Uom.exp (rest v) b) / t.vars v₀

/-- Splitting the sum at `v₀`, the shape both proofs below need. -/
private theorem sum_split (t : Term B V) (v₀ : V) (σ : Assign B V) (b : B) :
    ∑ v, t.vars v * Uom.exp (σ v) b
      = t.vars v₀ * Uom.exp (σ v₀) b
        + ∑ v ∈ Finset.univ.erase v₀, t.vars v * Uom.exp (σ v) b := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v₀)]

/-- **Soundness of elimination.** The assignment it produces solves the equation. -/
theorem solves_elim (t : Term B V) (v₀ : V) (h : t.vars v₀ ≠ 0) (rest : Assign B V) :
    Solves (elim t v₀ rest) t := by
  rw [solves_iff]
  intro b
  have hupd : ∀ v ∈ Finset.univ.erase v₀,
      t.vars v * Uom.exp (elim t v₀ rest v) b = t.vars v * Uom.exp (rest v) b := by
    intro v hv
    rw [elim, Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  rw [sum_split t v₀ _ b, Finset.sum_congr rfl hupd]
  rw [elim, Function.update_self]
  simp only [Uom.exp_ofExp]
  field_simp
  ring

/-- **Principality.** Any solution is *forced* to agree with `elim` on `v₀`.

So the solution set is exactly `elim` applied to the free variables: `v₀` is
determined, and everything else is a parameter. That is what makes the solution
most general, and it is why unit inference has principal types. -/
theorem elim_eq_of_solves (t : Term B V) (v₀ : V) (h : t.vars v₀ ≠ 0)
    (τ : Assign B V) (hτ : Solves τ t) : τ = elim t v₀ τ := by
  funext v
  by_cases hv : v = v₀
  · subst hv
    rw [elim, Function.update_self]
    rw [solves_iff] at hτ
    ext b
    have hb := hτ b
    rw [sum_split t v τ b] at hb
    simp only [Uom.exp_ofExp]
    field_simp
    linarith [hb]
  · rw [elim, Function.update_of_ne hv]

end Elim

/-! ## Row reduction

The single operation from which multi-equation solving is built. -/

/-- Reduce `u` against pivot equation `t` on variable `v₀`: the row operation
`u ← u - (u[v₀]/t[v₀]) · t`. -/
def reduce (u t : Term B V) (v₀ : V) : Term B V where
  base := fun b => u.base b - (u.vars v₀ / t.vars v₀) * t.base b
  vars := fun v => u.vars v - (u.vars v₀ / t.vars v₀) * t.vars v

@[simp] theorem reduce_base (u t : Term B V) (v₀ : V) (b : B) :
    (u.reduce t v₀).base b = u.base b - (u.vars v₀ / t.vars v₀) * t.base b := rfl

@[simp] theorem reduce_vars (u t : Term B V) (v₀ : V) (v : V) :
    (u.reduce t v₀).vars v = u.vars v - (u.vars v₀ / t.vars v₀) * t.vars v := rfl

/-- **Reduction kills the pivot.** After reducing, `v₀` no longer occurs in `u`,
which is what makes the elimination make progress. -/
@[simp] theorem reduce_pivot (u t : Term B V) (v₀ : V) (h : t.vars v₀ ≠ 0) :
    (u.reduce t v₀).vars v₀ = 0 := by
  simp only [reduce_vars]
  field_simp
  ring

/-- **Reduction preserves solutions**, given that the pivot equation holds.

This is the correctness of Gaussian elimination, and everything below is an
induction over it. -/
theorem solves_reduce_iff [Fintype V] {σ : Assign B V} {u t : Term B V} {v₀ : V}
    (ht : Solves σ t) : Solves σ (u.reduce t v₀) ↔ Solves σ u := by
  rw [solves_iff] at ht ⊢
  rw [solves_iff]
  constructor
  · intro h b
    have hb := h b
    have htb := ht b
    simp only [reduce_base, reduce_vars, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      ← Finset.mul_sum] at hb
    linear_combination hb + (u.vars v₀ / t.vars v₀) * htb
  · intro h b
    have hb := h b
    have htb := ht b
    simp only [reduce_base, reduce_vars, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      ← Finset.mul_sum]
    linear_combination hb - (u.vars v₀ / t.vars v₀) * htb

end Term

/-! ## Systems -/

/-- A system of unit equations, each asserted to equal the trivial unit. -/
abbrev System (B V : Type*) := List (Term B V)

namespace System

variable {B V : Type*} [Fintype V]

/-- An assignment solves a system when it solves every equation in it. -/
def Solves (σ : Term.Assign B V) (sys : System B V) : Prop :=
  ∀ t ∈ sys, Term.Solves σ t

@[simp] theorem solves_nil (σ : Term.Assign B V) : Solves σ [] := by
  intro _ h; cases h

@[simp] theorem solves_cons (σ : Term.Assign B V) (t : Term B V) (sys : System B V) :
    Solves σ (t :: sys) ↔ Term.Solves σ t ∧ Solves σ sys := by
  constructor
  · intro h
    exact ⟨h t (List.mem_cons_self ..), fun u hu => h u (List.mem_cons_of_mem _ hu)⟩
  · rintro ⟨h1, h2⟩ u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h1
    · exact h2 u hu

/-- Reduce every equation of a system against a pivot. -/
def reduceAll (sys : System B V) (t : Term B V) (v₀ : V) : System B V :=
  sys.map (fun u => u.reduce t v₀)

/-- Reducing a whole system preserves its solution set, given the pivot holds. -/
theorem solves_reduceAll_iff {σ : Term.Assign B V} {sys : System B V}
    {t : Term B V} {v₀ : V} (ht : Term.Solves σ t) :
    Solves σ (sys.reduceAll t v₀) ↔ Solves σ sys := by
  induction sys with
  | nil => simp [reduceAll]
  | cons u rest ih =>
    simp only [reduceAll, List.map_cons, solves_cons] at *
    rw [Term.solves_reduce_iff ht, ih]

/-- After reduction the pivot variable is gone from every equation. -/
theorem reduceAll_pivot_zero {sys : System B V} {t : Term B V} {v₀ : V}
    (h : t.vars v₀ ≠ 0) : ∀ u ∈ sys.reduceAll t v₀, u.vars v₀ = 0 := by
  intro u hu
  simp only [reduceAll, List.mem_map] at hu
  obtain ⟨w, _, rfl⟩ := hu
  exact Term.reduce_pivot w t v₀ h

/-! ## Triangularization

Repeatedly pivot on the head equation, reducing the tail against it. Recursion is
on a list whose length strictly decreases, so **termination is structural** — no
measure to invent, no well-founded argument to discharge. -/

/-- Reduction preserves the number of equations — it is a row operation, not an
elimination of rows. This is what makes `triangulate` structurally decreasing. -/
@[simp] theorem length_reduceAll (sys : System B V) (t : Term B V) (v₀ : V) :
    (reduceAll sys t v₀).length = sys.length := List.length_map ..

/-- Choose a pivot variable for an equation: any variable occurring with nonzero
coefficient. Left abstract, since the choice affects only numerical conditioning,
never the solution set. -/
def Pivot (B V : Type*) := Term B V → Option V

/-- A pivot function is *faithful* when it finds a variable exactly when one
occurs. Correctness of elimination (`solves_triangulate_iff`) needs none of
this — the solution set is preserved whatever the pivot does. Faithfulness is
what makes elimination *terminate usefully*, by guaranteeing that a `none`
answer really does mean the equation has become rigid. -/
structure Faithful (p : Pivot B V) : Prop where
  /-- No pivot reported means no variable occurs. -/
  none_of : ∀ t, p t = none → t.vars = fun _ => 0
  /-- A reported pivot really has a nonzero coefficient. -/
  ne_zero : ∀ t v, p t = some v → t.vars v ≠ 0

/-- Gaussian elimination: pivot on each equation in turn, reducing all later
equations against it. -/
def triangulate (p : Pivot B V) : System B V → System B V
  | [] => []
  | t :: rest =>
    match p t with
    | some v₀ => t :: triangulate p (reduceAll rest t v₀)
    | none => t :: triangulate p rest
  termination_by sys => sys.length
  decreasing_by all_goals simp [reduceAll]

/-- **Correctness of triangularization.** It preserves the solution set exactly.

Together with `reduceAll_pivot_zero` this is Gaussian elimination: each pivot
variable is isolated in a single equation, and the solution set is untouched. -/
theorem solves_triangulate_iff (p : Pivot B V) {σ : Term.Assign B V} :
    ∀ sys : System B V, Solves σ (triangulate p sys) ↔ Solves σ sys
  | [] => by simp [triangulate]
  | t :: rest => by
    rw [triangulate]
    cases hp : p t with
    | some v₀ =>
      simp only [solves_cons]
      constructor
      · rintro ⟨ht, hrest⟩
        refine ⟨ht, ?_⟩
        rw [← solves_reduceAll_iff (v₀ := v₀) ht]
        exact (solves_triangulate_iff p _).mp hrest
      · rintro ⟨ht, hrest⟩
        refine ⟨ht, ?_⟩
        refine (solves_triangulate_iff p _).mpr ?_
        rw [solves_reduceAll_iff (v₀ := v₀) ht]
        exact hrest
    | none =>
      simp only [solves_cons]
      constructor
      · rintro ⟨ht, hrest⟩; exact ⟨ht, (solves_triangulate_iff p _).mp hrest⟩
      · rintro ⟨ht, hrest⟩; exact ⟨ht, (solves_triangulate_iff p _).mpr hrest⟩
  termination_by sys => sys.length
  decreasing_by all_goals simp [reduceAll]

/-! ## The terminal case, and decidability -/

/-- A system in which no variable occurs is solvable exactly when every base
exponent already vanishes.

This is the rigid-mismatch check, and it is the terminal case of elimination:
once triangularization has isolated every pivot variable, what remains are the
variable-free equations, and *those* decide solvability. -/
theorem solves_of_no_vars {sys : System B V} (hv : ∀ t ∈ sys, t.vars = fun _ => 0)
    (σ : Term.Assign B V) :
    Solves σ sys ↔ ∀ t ∈ sys, t.base = fun _ => 0 := by
  constructor
  · intro h t ht
    exact (Term.solves_of_no_vars t (hv t ht) σ).mp (h t ht)
  · intro h t ht
    exact (Term.solves_of_no_vars t (hv t ht) σ).mpr (h t ht)

/-- Solvability of a variable-free system does not depend on the assignment —
so the check is a decision procedure, not a search. -/
theorem no_vars_solves_iff_forall {sys : System B V}
    (hv : ∀ t ∈ sys, t.vars = fun _ => 0) (σ τ : Term.Assign B V) :
    Solves σ sys ↔ Solves τ sys := by
  rw [solves_of_no_vars hv σ, solves_of_no_vars hv τ]

/-- With a faithful pivot, an equation the pivot declines is genuinely rigid, and
its solvability is settled by inspecting its base exponents alone.

This is what closes the loop: elimination drives every equation either to a
pivot (which determines a variable, by `Term.elim_eq_of_solves`) or to a rigid
residual (which is decided here, with no search and no assignment). -/
theorem solves_of_pivot_none {p : Pivot B V} (hp : Faithful p)
    {t : Term B V} (h : p t = none) (σ : Term.Assign B V) :
    Term.Solves σ t ↔ t.base = fun _ => 0 :=
  Term.solves_of_no_vars t (hp.none_of t h) σ

end System

end LambdaS

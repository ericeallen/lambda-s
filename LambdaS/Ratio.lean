/-
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
-/
import LambdaS.Fundamental
import Mathlib.Algebra.Order.Positive.Field

/-!
# Conversion ratios as syntax

Concretely, `convert x m ft` contributes the ratio `m/ft`, and the round trip
`convert (convert x m ft) ft m` accumulates `(m/ft) · (ft/m) = 1`; this file
gives ratios like these a first-order syntax.

An earlier design, since deleted, carried a term's accumulated conversion ratio
as a *semantic* object: at arrow type the ratio was a Lean function space. That
works at first order and stops working at a unit binder, and the reason is worth
stating, because it is a familiar one.

A function space is higher-order abstract syntax for the ratio map, and HOAS
cannot be traversed or substituted into. Instantiating a unit variable is a
substitution, so `e[μ]` has nowhere to send the ratio of `e`; and the map is
contravariant at arrow type, so no covariant transport exists either. That is why
`TwistTy` at a quantifier is `PUnit`: not a choice, an obstruction.

The fix is to make ratios first-order, which is what this file does. Two things
fall out beyond fixing the quantifiers.

Substitution disappears rather than becoming structural: `Tw.uapp` **records**
the instantiating unit instead of performing it, and the interpretation does the
work. So there is no ratio-substitution lemma at all, and no transport.

And a first-order ratio is *inspectable*. With a function space you can define a
term's ratio but never decide whether it is trivial; with syntax you can, which
turns `Twist.invariant_iff` from a characterization into an algorithm: the
compiler diagnostic *"this program's conversions do not cancel, so its result
depends on the declared magnitudes"*.

## Shapes

Ratios are indexed by a `Shape` (the type's skeleton) rather than by the type.
That is not a simplification but an observation: the deleted semantic ratios
never inspected a type's units, only its structure, so type-indexing was buying
nothing. A
shape records where the ratio is a unit (`scalar`), where it is a map
(`arrow`), where it is a family of scalars (`vec` and `mat`, for spaces and
linear maps: the drift of a vector is a vector of drifts, and the drift of a
matrix is a matrix of drifts, indexed by component counts, which are
unit-blind), and where a unit binder was crossed (`bind`).
-/

namespace LambdaS

/-- The skeleton of a type, as far as conversion ratios can see. -/
inductive Shape where
  /-- A quantity: the ratio is a unit expression. -/
  | scalar : Shape
  /-- A function: the ratio maps ratios to ratios. -/
  | arrow : Shape → Shape → Shape
  /-- A space of the given length: one scalar ratio per component. -/
  | vec : ℕ → Shape
  /-- A linear map, by domain and codomain lengths: one scalar ratio per
  entry. -/
  | mat : ℕ → ℕ → Shape
  /-- Under a unit binder: the ratio lives one unit scope out. -/
  | bind : Shape → Shape
  deriving DecidableEq, Repr

variable {B D : Type}

/-- The shape of a type. Units are ignored; only the structure survives.

`@[reducible]` for the same reason `Ty.den` is: instance synthesis runs at
reducible transparency, and `SemTw (Ty.shape (.Q u))` has to resolve to the
positive-real carrier. -/
@[reducible] def Ty.shape : {j k : ℕ} → Ty B D j k → Shape
  | _, _, .Q _ => .scalar
  | _, _, .arrow a b => .arrow (Ty.shape a) (Ty.shape b)
  | _, _, .vec V => .vec V.length
  | _, _, .lin V W => .mat V.length W.length
  | _, _, .all _ τ => .bind (Ty.shape τ)
  | _, _, .allDim τ => Ty.shape τ

/-- The shapes of a context, one ratio variable per term variable. -/
def Ctx.shapes {j k : ℕ} (Γ : Ctx B D j k) : List Shape := Γ.map Ty.shape

@[simp] theorem Ctx.shapes_nil {j k : ℕ} :
    Ctx.shapes ([] : Ctx B D j k) = [] := rfl

@[simp] theorem Ctx.shapes_cons {j k : ℕ} (τ : Ty B D j k) (Γ : Ctx B D j k) :
    Ctx.shapes (τ :: Γ) = Ty.shape τ :: Ctx.shapes Γ := rfl

/-- A context lookup, read at the shapes. -/
theorem Ctx.shapes_getElem? {j k : ℕ} {Γ : Ctx B D j k} {n : ℕ}
    {τ : Ty B D j k} (h : Γ[n]? = some τ) :
    (Ctx.shapes Γ)[n]? = some (Ty.shape τ) := by
  simp [Ctx.shapes, h]

/-- **Shape is blind to units.** Grounding a type through unit and dimension
environments leaves its shape alone, which is why ratios need no transport: the
`Tw` indexed by a type is equally an index for every instantiation of it. The
space cases are `List.length_map`: lengths are unit-blind. -/
@[simp] theorem Ty.shape_ground : ∀ {j k : ℕ} (τ : Ty B D j k) {j₀ k₀ : ℕ}
    (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀),
    Ty.shape (Ty.ground η δ τ) = Ty.shape τ := by
  intro j k τ
  induction τ with
  | Q u => intro _ _ _ _; rfl
  | arrow a b iha ihb => intro _ _ η δ; simp only [Ty.ground, Ty.shape, iha, ihb]
  | vec V => intro _ _ _ _; simp only [Ty.ground, Ty.shape, List.length_map]
  | lin V W => intro _ _ _ _; simp only [Ty.ground, Ty.shape, List.length_map]
  | all d τ ih => intro _ _ η δ; simp only [Ty.ground, Ty.shape, ih]
  | allDim τ ih => intro _ _ η δ; simp only [Ty.ground, Ty.shape, ih]

@[simp] theorem Ty.shape_subst {j k : ℕ} (τ : Ty B D j (k + 1)) (μ : UExp B k) :
    Ty.shape (τ.subst μ) = Ty.shape τ := Ty.shape_ground _ _ _

@[simp] theorem Ty.shape_substDim {j k : ℕ} (τ : Ty B D (j + 1) k) (d : DExp D j) :
    Ty.shape (τ.substDim d) = Ty.shape τ := Ty.shape_ground _ _ _

@[simp] theorem Ty.shape_weaken {j k : ℕ} (τ : Ty B D j k) :
    Ty.shape (Ty.weaken τ) = Ty.shape τ := Ty.shape_ground _ _ _

@[simp] theorem Ty.shape_weakenDim {j k : ℕ} (τ : Ty B D j k) :
    Ty.shape (Ty.weakenDim τ) = Ty.shape τ := Ty.shape_ground _ _ _

@[simp] theorem Ctx.shapes_weaken {j k : ℕ} (Γ : Ctx B D j k) :
    Ctx.shapes Γ.weaken = Ctx.shapes Γ := by
  simp [Ctx.shapes, Ctx.weaken, List.map_map, Function.comp_def]

@[simp] theorem Ctx.shapes_weakenDim {j k : ℕ} (Γ : Ctx B D j k) :
    Ctx.shapes Γ.weakenDim = Ctx.shapes Γ := by
  simp [Ctx.shapes, Ctx.weakenDim, List.map_map, Function.comp_def]

/-! ## The syntax of ratios

A ratio is an open term over a context of ratio variables (one for each free
term variable) in the free abelian group generated by unit expressions, closed
under abstraction and application so that the analysis passes first order.

`uapp` records its instantiating unit rather than substituting it. That is what
makes the whole construction transport-free. -/

/-- **Conversion-ratio expressions.** -/
inductive Tw (B : Type) : ℕ → List Shape → Shape → Type where
  /-- The ratio of a free variable. -/
  | var {k Θ s} (n : ℕ) : Θ[n]? = some s → Tw B k Θ s
  /-- A constant ratio: a unit expression. `1` is the trivial ratio. -/
  | unit {k Θ} : UExp B k → Tw B k Θ .scalar
  /-- Multiplication multiplies ratios. -/
  | mul {k Θ} : Tw B k Θ .scalar → Tw B k Θ .scalar → Tw B k Θ .scalar
  /-- Division divides them. -/
  | div {k Θ} : Tw B k Θ .scalar → Tw B k Θ .scalar → Tw B k Θ .scalar
  /-- A constant rational power lifts a ratio to that power. This is what
  carries the analysis through `pow`: the scale factor of `e ^ q` is
  `ψ(u) ^ q`, so its drift is the drift of `e` to the `q`. -/
  | qpow {k Θ} : Tw B k Θ .scalar → ℚ → Tw B k Θ .scalar
  /-- Abstraction binds a ratio variable. This is the first-order replacement
  for the function space, and the whole point of the file. -/
  | lam {k Θ s t} : Tw B k (s :: Θ) t → Tw B k Θ (.arrow s t)
  /-- Application. -/
  | app {k Θ s t} : Tw B k Θ (.arrow s t) → Tw B k Θ s → Tw B k Θ t
  /-- The empty drift vector. -/
  | vecnil {k Θ} : Tw B k Θ (.vec 0)
  /-- Consing a scalar drift onto a drift vector. -/
  | veccons {k Θ n} : Tw B k Θ .scalar → Tw B k Θ (.vec n) → Tw B k Θ (.vec (n + 1))
  /-- Projecting a component out of a drift vector. -/
  | proj {k Θ n} : Tw B k Θ (.vec n) → Fin n → Tw B k Θ .scalar
  /-- The zero-row drift matrix, at any domain length. -/
  | matnil {k Θ n} : Tw B k Θ (.mat n 0)
  /-- Consing a row-drift vector onto a drift matrix. -/
  | matcons {k Θ n m} : Tw B k Θ (.vec n) → Tw B k Θ (.mat n m) → Tw B k Θ (.mat n (m + 1))
  /-- Reading a row-drift vector out of a drift matrix. -/
  | row {k Θ n m} : Tw B k Θ (.mat n m) → Fin m → Tw B k Θ (.vec n)
  /-- Under a unit binder the ratio lives at the larger unit scope. -/
  | ulam {k Θ s} : Tw B (k + 1) Θ s → Tw B k Θ (.bind s)
  /-- Unit instantiation is **recorded**, not performed. -/
  | uapp {k Θ s} : Tw B k Θ (.bind s) → UExp B k → Tw B k Θ s

/-- Retyping a ratio along an equality of shapes. Needed only at `uapp` and
`dapp`, where the result type is `τ.subst σ` and `Ty.shape_subst` is a theorem
rather than a definitional equality, and at a matrix row, whose space is a
`map` over the column space with `List.length_map` likewise a theorem. -/
def Tw.castShape {k : ℕ} {Θ : List Shape} {s s' : Shape} (h : s = s') :
    Tw B k Θ s → Tw B k Θ s' := fun t => h ▸ t

@[simp] theorem Tw.castShape_rfl {k : ℕ} {Θ : List Shape} {s : Shape}
    (t : Tw B k Θ s) : Tw.castShape rfl t = t := rfl

/-! ### Renaming and substitution

`uapp` records unit instantiation, so no unit-substitution is ever *forced*;
but a recorded β-redex (`app (lam t) s`, or `uapp (ulam t) μ`) is opaque to
the flat-form comparison, which costs completeness at the agreement checks.
These operations let the redexes that arise at construction be reduced on the
spot: a ratio-context renaming (for weakening a substituend under `lam`), a
unit-scope pullback (for carrying a substituend under `ulam`, and for
performing a recorded instantiation), and simultaneous substitution built
from the two. Each preserves evaluation, which is proved below the
interpreter. -/

/-- Lifting a ratio-context renaming under a binder. -/
def Tw.liftR (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => f n + 1

/-- A lifted renaming stays coherent with the shape contexts. -/
theorem Tw.liftR_ok {Θ Θ' : List Shape} {s₀ : Shape} (f : ℕ → ℕ)
    (hf : ∀ (n : ℕ) (s : Shape), Θ[n]? = some s → Θ'[f n]? = some s) :
    ∀ (n : ℕ) (s : Shape), (s₀ :: Θ)[n]? = some s → (s₀ :: Θ')[Tw.liftR f n]? = some s
  | 0, _, h => h
  | n + 1, s, h => by simpa [Tw.liftR] using hf n s (by simpa using h)

/-- Renaming the ratio context along a coherent index map. -/
def Tw.rename : {k : ℕ} → {Θ Θ' : List Shape} → (f : ℕ → ℕ) →
    (∀ (n : ℕ) (s : Shape), Θ[n]? = some s → Θ'[f n]? = some s) → {s : Shape} →
    Tw B k Θ s → Tw B k Θ' s
  | _, _, _, f, hf, _, .var n h => .var (f n) (hf n _ h)
  | _, _, _, _, _, _, .unit u => .unit u
  | _, _, _, f, hf, _, .mul a b => .mul (a.rename f hf) (b.rename f hf)
  | _, _, _, f, hf, _, .div a b => .div (a.rename f hf) (b.rename f hf)
  | _, _, _, f, hf, _, .qpow t q => .qpow (t.rename f hf) q
  | _, _, _, f, hf, _, .lam t => .lam (t.rename (Tw.liftR f) (Tw.liftR_ok f hf))
  | _, _, _, f, hf, _, .app g a => .app (g.rename f hf) (a.rename f hf)
  | _, _, _, _, _, _, .vecnil => .vecnil
  | _, _, _, f, hf, _, .veccons a v => .veccons (a.rename f hf) (v.rename f hf)
  | _, _, _, f, hf, _, .proj v i => .proj (v.rename f hf) i
  | _, _, _, _, _, _, .matnil => .matnil
  | _, _, _, f, hf, _, .matcons r M => .matcons (r.rename f hf) (M.rename f hf)
  | _, _, _, f, hf, _, .row M j => .row (M.rename f hf) j
  | _, _, _, f, hf, _, .ulam t => .ulam (t.rename f hf)
  | _, _, _, f, hf, _, .uapp t μ => .uapp (t.rename f hf) μ

/-- Weakening by a fresh ratio variable at position `0`. -/
def Tw.weakenR {k : ℕ} {Θ : List Shape} {s₀ s : Shape} (t : Tw B k Θ s) :
    Tw B k (s₀ :: Θ) s :=
  t.rename (· + 1) fun _ _ h => by simpa using h

/-- Pulling a ratio back along a unit substitution: every unit constant is
substituted, and a recorded instantiation records the substituted unit. The
syntactic face of `Scaling.pull`. -/
def Tw.pullU : {k k' : ℕ} → (η : Fin k → UExp B k') → {Θ : List Shape} →
    {s : Shape} → Tw B k Θ s → Tw B k' Θ s
  | _, _, _, _, _, .var n h => .var n h
  | _, _, η, _, _, .unit u => .unit (substU η u)
  | _, _, η, _, _, .mul a b => .mul (a.pullU η) (b.pullU η)
  | _, _, η, _, _, .div a b => .div (a.pullU η) (b.pullU η)
  | _, _, η, _, _, .qpow t q => .qpow (t.pullU η) q
  | _, _, η, _, _, .lam t => .lam (t.pullU η)
  | _, _, η, _, _, .app g a => .app (g.pullU η) (a.pullU η)
  | _, _, _, _, _, .vecnil => .vecnil
  | _, _, η, _, _, .veccons a v => .veccons (a.pullU η) (v.pullU η)
  | _, _, η, _, _, .proj v i => .proj (v.pullU η) i
  | _, _, _, _, _, .matnil => .matnil
  | _, _, η, _, _, .matcons r M => .matcons (r.pullU η) (M.pullU η)
  | _, _, η, _, _, .row M j => .row (M.pullU η) j
  | _, _, η, _, _, .ulam t => .ulam (t.pullU (liftU η))
  | _, _, η, _, _, .uapp t μ => .uapp (t.pullU η) (substU η μ)

/-- Weakening the unit scope by a fresh unit variable. -/
def Tw.uweaken {k : ℕ} {Θ : List Shape} {s : Shape} (t : Tw B k Θ s) :
    Tw B (k + 1) Θ s :=
  t.pullU fun i => Term.ofVar i.succ

/-- Lifting a simultaneous substitution under a binder: the bound variable
maps to itself and everything else is weakened past it. -/
def Tw.liftS {k : ℕ} {Θ Θ' : List Shape} {s₀ : Shape}
    (σ : ∀ (n : ℕ) (s : Shape), Θ[n]? = some s → Tw B k Θ' s) :
    ∀ (n : ℕ) (s : Shape), (s₀ :: Θ)[n]? = some s → Tw B k (s₀ :: Θ') s
  | 0, _, h => .var 0 (by simpa using h)
  | n + 1, s, h => (σ n s (by simpa using h)).weakenR

/-- Simultaneous substitution of ratios for ratio variables. Crossing `lam`
lifts the substitution; crossing `ulam` weakens every substituend's unit
scope. -/
def Tw.subst : {k : ℕ} → {Θ Θ' : List Shape} →
    (σ : ∀ (n : ℕ) (s : Shape), Θ[n]? = some s → Tw B k Θ' s) → {s : Shape} →
    Tw B k Θ s → Tw B k Θ' s
  | _, _, _, σ, _, .var n h => σ n _ h
  | _, _, _, _, _, .unit u => .unit u
  | _, _, _, σ, _, .mul a b => .mul (a.subst σ) (b.subst σ)
  | _, _, _, σ, _, .div a b => .div (a.subst σ) (b.subst σ)
  | _, _, _, σ, _, .qpow t q => .qpow (t.subst σ) q
  | _, _, _, σ, _, .lam t => .lam (t.subst (Tw.liftS σ))
  | _, _, _, σ, _, .app g a => .app (g.subst σ) (a.subst σ)
  | _, _, _, _, _, .vecnil => .vecnil
  | _, _, _, σ, _, .veccons a v => .veccons (a.subst σ) (v.subst σ)
  | _, _, _, σ, _, .proj v i => .proj (v.subst σ) i
  | _, _, _, _, _, .matnil => .matnil
  | _, _, _, σ, _, .matcons r M => .matcons (r.subst σ) (M.subst σ)
  | _, _, _, σ, _, .row M j => .row (M.subst σ) j
  | _, _, _, σ, _, .ulam t => .ulam (t.subst fun n s h => (σ n s h).uweaken)
  | _, _, _, σ, _, .uapp t μ => .uapp (t.subst σ) μ

/-- Substituting for the most recently bound ratio variable. -/
def Tw.subst0 {k : ℕ} {Θ : List Shape} {s₀ s : Shape}
    (t : Tw B k (s₀ :: Θ) s) (a : Tw B k Θ s₀) : Tw B k Θ s :=
  t.subst fun n _ h =>
    match n, h with
    | 0, h => Tw.castShape (Option.some.inj h) a
    | n + 1, h => .var n (by simpa using h)

/-- Application that β-reduces when the head is a literal abstraction, so
that a redex formed at construction is not left for the flat form to treat
as an opaque atom. -/
def Tw.appE {k : ℕ} {Θ : List Shape} {s t : Shape} :
    Tw B k Θ (.arrow s t) → Tw B k Θ s → Tw B k Θ t
  | .lam b, a => b.subst0 a
  | f, a => .app f a

/-- Unit instantiation that reduces when the head is a literal unit
abstraction, by performing the recorded substitution through `pullU`. -/
def Tw.uappE {k : ℕ} {Θ : List Shape} {s : Shape} :
    Tw B k Θ (.bind s) → UExp B k → Tw B k Θ s
  | .ulam t, μ => t.pullU (Fin.cons μ (idU B k))
  | t, μ => .uapp t μ

/-! ## What a ratio means -/

/-- The semantic ratio at scalar shape: a **positive** real. A definition of
its own so that the space shapes can be compositional in the scalar meaning:
change the scalar carrier and every shape follows.

Positivity is carried by the type rather than by a side relation: a ratio's
value is built from scale factors (positive) by multiplication, division and
rational powers (positivity-preserving), and the rational-power former is
sound only on positives, so the carrier says so. This is the semantic face of
the unit group having no zero. -/
@[reducible] def SemScalar : Type := { x : ℝ // 0 < x }

/-- Rational powers on positive scalars, via `Real.rpow`. -/
noncomputable def SemScalar.rpow (x : SemScalar) (q : ℝ) : SemScalar :=
  ⟨(x : ℝ) ^ q, Real.rpow_pos_of_pos x.2 q⟩

@[simp] theorem SemScalar.val_rpow (x : SemScalar) (q : ℝ) :
    (SemScalar.rpow x q : ℝ) = (x : ℝ) ^ q := rfl

@[simp] theorem SemScalar.val_div (x y : SemScalar) :
    ((x / y : SemScalar) : ℝ) = (x : ℝ) / (y : ℝ) := by
  rw [div_eq_mul_inv, Positive.val_mul, Positive.coe_inv, div_eq_mul_inv]

/-- The semantic ratio at each shape: a scale factor at a quantity, a map at a
function, a scale factor per component at a space, a scale factor per entry at
a linear map (entry `(j, i)` is row `j`, column `i`), a family at a unit
binder. -/
@[reducible] def SemTw : Shape → Type
  | .scalar => SemScalar
  | .arrow s t => SemTw s → SemTw t
  | .vec n => Fin n → SemScalar
  | .mat n m => Fin m → Fin n → SemScalar
  | .bind s => ℝ → SemTw s

/-- Semantic ratios for a ratio context. -/
@[reducible] def TwEnv : List Shape → Type
  | [] => PUnit
  | s :: Θ => SemTw s × TwEnv Θ

/-- Looking a ratio variable up. -/
def TwEnv.lookup : {Θ : List Shape} → {s : Shape} → (n : ℕ) → Θ[n]? = some s →
    TwEnv Θ → SemTw s
  | [], _, _, h, _ => absurd h (by simp)
  | _ :: _, _, 0, h, ρ => Option.some.inj h ▸ ρ.1
  | _ :: _, _, n + 1, h, ρ => TwEnv.lookup n (by simpa using h) ρ.2

variable [Fintype B]

/-- **The meaning of a ratio**, under a declared scaling. `uapp` is where the
recorded instantiation is finally performed: semantically, by reading the
family at the instantiating unit's magnitude. -/
noncomputable def Tw.eval : {k : ℕ} → Scaling B k → {Θ : List Shape} → {s : Shape} →
    Tw B k Θ s → TwEnv Θ → SemTw s
  | _, _, _, _, .var n h, ρ => TwEnv.lookup n h ρ
  | _, ψ, _, _, .unit u, _ => ⟨ψ.scale u, ψ.scale_pos u⟩
  | _, ψ, _, _, .mul a b, ρ => Tw.eval ψ a ρ * Tw.eval ψ b ρ
  | _, ψ, _, _, .div a b, ρ => Tw.eval ψ a ρ / Tw.eval ψ b ρ
  | _, ψ, _, _, .qpow t q, ρ => SemScalar.rpow (Tw.eval ψ t ρ) (q : ℝ)
  | _, ψ, _, _, .lam t, ρ => fun r => Tw.eval ψ t (r, ρ)
  | _, ψ, _, _, .app f a, ρ => (Tw.eval ψ f ρ) (Tw.eval ψ a ρ)
  | _, _, _, _, .vecnil, _ => fun i => i.elim0
  | _, ψ, _, _, .veccons a v, ρ => Fin.cons (Tw.eval ψ a ρ) (Tw.eval ψ v ρ)
  | _, ψ, _, _, .proj v i, ρ => Tw.eval ψ v ρ i
  | _, _, _, _, .matnil, _ => fun j => j.elim0
  | _, ψ, _, _, .matcons r M, ρ => Fin.cons (Tw.eval ψ r ρ) (Tw.eval ψ M ρ)
  | _, ψ, _, _, .row M j, ρ => Tw.eval ψ M ρ j
  | _, ψ, _, _, .ulam t, ρ => fun r => Tw.eval (ψ.cons r) t ρ
  | _, ψ, _, _, .uapp t μ, ρ => (Tw.eval ψ t ρ) (ψ.logScale μ)

/-- Evaluation commutes with retyping. -/
@[simp] theorem Tw.eval_castShape {k : ℕ} (ψ : Scaling B k) {Θ : List Shape}
    {s s' : Shape} (h : s = s') (t : Tw B k Θ s) (ρ : TwEnv Θ) :
    Tw.eval ψ (Tw.castShape h t) ρ = h ▸ Tw.eval ψ t ρ := by
  subst h; rfl

/-- Retyping along an equality of vector shapes reindexes the components and
changes nothing else. The equality in play is `List.length_map` at a matrix
row, where the row space is a `map` over the column space. -/
theorem Tw.eval_castShape_vec {k : ℕ} (ψ : Scaling B k) {Θ : List Shape}
    {n n' : ℕ} (h : Shape.vec n = Shape.vec n') (t : Tw B k Θ (.vec n))
    (ρ : TwEnv Θ) (i : Fin n') :
    Tw.eval ψ (Tw.castShape h t) ρ i
      = Tw.eval ψ t ρ (Fin.cast (Shape.vec.inj h).symm i) := by
  have hn : n = n' := Shape.vec.inj h
  subst hn
  rw [show Tw.castShape h t = t from eq_of_heq (eqRec_heq h t)]
  rfl

/-! ### Derived vector and matrix combinators

`vecOfFn` and `matOfFn` build literal drift vectors and matrices from
component functions. `projE` and `rowE` are `proj` and `row` that reduce on
literals, so that the syntactic comparison in the drift computation sees a
literal's components rather than an opaque projection; on anything that is not
a literal they fall back to the formers. -/

/-- A literal drift vector from a component function. -/
def Tw.vecOfFn {k : ℕ} {Θ : List Shape} :
    {n : ℕ} → (Fin n → Tw B k Θ .scalar) → Tw B k Θ (.vec n)
  | 0, _ => .vecnil
  | _ + 1, f => .veccons (f 0) (Tw.vecOfFn fun i => f i.succ)

/-- A literal drift matrix from a row function. -/
def Tw.matOfFn {k : ℕ} {Θ : List Shape} {n : ℕ} :
    {m : ℕ} → (Fin m → Tw B k Θ (.vec n)) → Tw B k Θ (.mat n m)
  | 0, _ => .matnil
  | _ + 1, g => .matcons (g 0) (Tw.matOfFn fun j => g j.succ)

/-- Projection that reduces on vector literals. -/
def Tw.projE {k : ℕ} {Θ : List Shape} :
    {n : ℕ} → Tw B k Θ (.vec n) → Fin n → Tw B k Θ .scalar
  | _, .veccons a v, i => Fin.cases a (fun i' => Tw.projE v i') i
  | _, t, i => .proj t i

/-- Row extraction that reduces on matrix literals. -/
def Tw.rowE {k : ℕ} {Θ : List Shape} {n : ℕ} :
    {m : ℕ} → Tw B k Θ (.mat n m) → Fin m → Tw B k Θ (.vec n)
  | _, .matcons r M, j => Fin.cases r (fun j' => Tw.rowE M j') j
  | _, t, j => .row t j

/-- The trivial ratio, as syntax, at every shape: the unit `1` at a scalar,
`1` in every component at a space, the constant trivial family at an arrow
and under a unit binder. This is the ratio the frees-at-one assignment gives
every context variable of a program: an input is a measurement, and a
measurement rescales ideally, so its ratio is `1`. Atoms are reserved for
`lam`-bound variables, whose future arguments may genuinely drift. -/
def Tw.one : {k : ℕ} → {Θ : List Shape} → (s : Shape) → Tw B k Θ s
  | _, _, .scalar => .unit 1
  | _, _, .arrow _ t => .lam (Tw.one t)
  | _, _, .vec _ => Tw.vecOfFn fun _ => .unit 1
  | _, _, .mat _ _ => Tw.matOfFn fun _ => Tw.vecOfFn fun _ => .unit 1
  | _, _, .bind s => .ulam (Tw.one s)

@[simp] theorem Tw.eval_vecOfFn {k : ℕ} (ψ : Scaling B k) {Θ : List Shape} :
    ∀ {n : ℕ} (f : Fin n → Tw B k Θ .scalar) (ρ : TwEnv Θ) (i : Fin n),
    Tw.eval ψ (Tw.vecOfFn f) ρ i = Tw.eval ψ (f i) ρ
  | 0, _, _, i => i.elim0
  | n + 1, f, ρ, i => by
      cases i using Fin.cases with
      | zero => simp [Tw.vecOfFn, Tw.eval]
      | succ i =>
        simp [Tw.vecOfFn, Tw.eval, Tw.eval_vecOfFn ψ (fun i => f i.succ) ρ i]

@[simp] theorem Tw.eval_matOfFn {k : ℕ} (ψ : Scaling B k) {Θ : List Shape} {n : ℕ} :
    ∀ {m : ℕ} (g : Fin m → Tw B k Θ (.vec n)) (ρ : TwEnv Θ) (a : Fin m),
    Tw.eval ψ (Tw.matOfFn g) ρ a = Tw.eval ψ (g a) ρ
  | 0, _, _, a => a.elim0
  | m + 1, g, ρ, a => by
      cases a using Fin.cases with
      | zero => simp [Tw.matOfFn, Tw.eval]
      | succ a =>
        simp [Tw.matOfFn, Tw.eval, Tw.eval_matOfFn ψ (fun j => g j.succ) ρ a]

@[simp] theorem Tw.eval_projE {k : ℕ} (ψ : Scaling B k) {Θ : List Shape} :
    ∀ {n : ℕ} (t : Tw B k Θ (.vec n)) (i : Fin n) (ρ : TwEnv Θ),
    Tw.eval ψ (Tw.projE t i) ρ = Tw.eval ψ t ρ i
  | _, .veccons a v, i, ρ => by
      cases i using Fin.cases with
      | zero => simp [Tw.projE, Tw.eval]
      | succ i => simp [Tw.projE, Tw.eval, Tw.eval_projE ψ v i ρ]
  | _, .var n h, i, ρ => by simp [Tw.projE, Tw.eval]
  | _, .app f a, i, ρ => by simp [Tw.projE, Tw.eval]
  | _, .uapp t μ, i, ρ => by simp [Tw.projE, Tw.eval]
  | _, .vecnil, i, ρ => i.elim0
  | _, .row M j, i, ρ => by simp [Tw.projE, Tw.eval]

@[simp] theorem Tw.eval_rowE {k : ℕ} (ψ : Scaling B k) {Θ : List Shape} {n : ℕ} :
    ∀ {m : ℕ} (t : Tw B k Θ (.mat n m)) (j : Fin m) (ρ : TwEnv Θ),
    Tw.eval ψ (Tw.rowE t j) ρ = Tw.eval ψ t ρ j
  | _, .matcons r M, j, ρ => by
      cases j using Fin.cases with
      | zero => simp [Tw.rowE, Tw.eval]
      | succ j => simp [Tw.rowE, Tw.eval, Tw.eval_rowE ψ M j ρ]
  | _, .var n h, j, ρ => by simp [Tw.rowE, Tw.eval]
  | _, .app f a, j, ρ => by simp [Tw.rowE, Tw.eval]
  | _, .uapp t μ, j, ρ => by simp [Tw.rowE, Tw.eval]
  | _, .matnil, j, ρ => j.elim0

/-! ### Renaming and substitution preserve evaluation -/

/-- Renaming preserves evaluation, at environments that agree along the
renaming. -/
theorem Tw.eval_rename : ∀ {k : ℕ} (ψ : Scaling B k) {Θ Θ' : List Shape}
    (f : ℕ → ℕ) (hf : ∀ (n : ℕ) (s : Shape), Θ[n]? = some s → Θ'[f n]? = some s)
    {s : Shape} (t : Tw B k Θ s) (ρ : TwEnv Θ) (ρ' : TwEnv Θ'),
    (∀ (n : ℕ) (sh : Shape) (h : Θ[n]? = some sh),
        TwEnv.lookup (f n) (hf n sh h) ρ' = TwEnv.lookup n h ρ) →
    Tw.eval ψ (t.rename f hf) ρ' = Tw.eval ψ t ρ
  | _, ψ, _, _, f, hf, _, .var n h, ρ, ρ', hρ => hρ n _ h
  | _, _, _, _, _, _, _, .unit u, _, _, _ => rfl
  | _, ψ, _, _, f, hf, _, .mul a b, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf a ρ ρ' hρ,
        Tw.eval_rename ψ f hf b ρ ρ' hρ]
  | _, ψ, _, _, f, hf, _, .div a b, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf a ρ ρ' hρ,
        Tw.eval_rename ψ f hf b ρ ρ' hρ]
  | _, ψ, _, _, f, hf, _, .qpow t q, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf t ρ ρ' hρ]
  | _, ψ, _, _, f, hf, _, .lam t, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval]
      exact funext fun r => Tw.eval_rename ψ (Tw.liftR f) (Tw.liftR_ok f hf) t
        (r, ρ) (r, ρ') fun n sh h => by
          cases n with
          | zero => rfl
          | succ n => exact hρ n sh (by simpa using h)
  | _, ψ, _, _, f, hf, _, .app g a, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf g ρ ρ' hρ,
        Tw.eval_rename ψ f hf a ρ ρ' hρ]
  | _, _, _, _, _, _, _, .vecnil, _, _, _ => rfl
  | _, ψ, _, _, f, hf, _, .veccons a v, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf a ρ ρ' hρ,
        Tw.eval_rename ψ f hf v ρ ρ' hρ]
  | _, ψ, _, _, f, hf, _, .proj v i, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf v ρ ρ' hρ]
  | _, _, _, _, _, _, _, .matnil, _, _, _ => rfl
  | _, ψ, _, _, f, hf, _, .matcons r M, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf r ρ ρ' hρ,
        Tw.eval_rename ψ f hf M ρ ρ' hρ]
  | _, ψ, _, _, f, hf, _, .row M j, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf M ρ ρ' hρ]
  | _, ψ, _, _, f, hf, _, .ulam t, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval]
      exact funext fun r => Tw.eval_rename (ψ.cons r) f hf t ρ ρ' hρ
  | _, ψ, _, _, f, hf, _, .uapp t μ, ρ, ρ', hρ => by
      simp only [Tw.rename, Tw.eval, Tw.eval_rename ψ f hf t ρ ρ' hρ]

/-- Weakening by a fresh ratio variable is invisible to evaluation. -/
theorem Tw.eval_weakenR {k : ℕ} (ψ : Scaling B k) {Θ : List Shape}
    {s₀ s : Shape} (t : Tw B k Θ s) (r : SemTw s₀) (ρ : TwEnv Θ) :
    Tw.eval ψ (t.weakenR (s₀ := s₀)) (r, ρ) = Tw.eval ψ t ρ := by
  rw [Tw.weakenR]
  refine Tw.eval_rename (Θ' := s₀ :: Θ) ψ (· + 1) _ t ρ (r, ρ) fun _ _ _ => ?_
  rfl

/-- The unit-scope pullback is the syntactic face of `Scaling.pull`. -/
theorem Tw.eval_pullU : ∀ {k k' : ℕ} (ψ : Scaling B k') (η : Fin k → UExp B k')
    {Θ : List Shape} {s : Shape} (t : Tw B k Θ s) (ρ : TwEnv Θ),
    Tw.eval ψ (t.pullU η) ρ = Tw.eval (ψ.pull η) t ρ
  | _, _, _, _, _, _, .var n h, _ => rfl
  | _, _, ψ, η, _, _, .unit u, _ => by
      simp only [Tw.pullU, Tw.eval]
      exact Subtype.ext (Scaling.scale_pull ψ η u).symm
  | _, _, ψ, η, _, _, .mul a b, ρ => by
      simp only [Tw.pullU, Tw.eval, Tw.eval_pullU ψ η a ρ, Tw.eval_pullU ψ η b ρ]
  | _, _, ψ, η, _, _, .div a b, ρ => by
      simp only [Tw.pullU, Tw.eval, Tw.eval_pullU ψ η a ρ, Tw.eval_pullU ψ η b ρ]
  | _, _, ψ, η, _, _, .qpow t q, ρ => by
      simp only [Tw.pullU, Tw.eval, Tw.eval_pullU ψ η t ρ]
  | _, _, ψ, η, _, _, .lam t, ρ => by
      simp only [Tw.pullU, Tw.eval]
      exact funext fun r => Tw.eval_pullU (Θ := _ :: _) ψ η t (r, ρ)
  | _, _, ψ, η, _, _, .app g a, ρ => by
      simp only [Tw.pullU, Tw.eval, Tw.eval_pullU ψ η g ρ, Tw.eval_pullU ψ η a ρ]
  | _, _, _, _, _, _, .vecnil, _ => rfl
  | _, _, ψ, η, _, _, .veccons a v, ρ => by
      simp only [Tw.pullU, Tw.eval, Tw.eval_pullU ψ η a ρ, Tw.eval_pullU ψ η v ρ]
  | _, _, ψ, η, _, _, .proj v i, ρ => by
      simp only [Tw.pullU, Tw.eval, Tw.eval_pullU ψ η v ρ]
  | _, _, _, _, _, _, .matnil, _ => rfl
  | _, _, ψ, η, _, _, .matcons r M, ρ => by
      simp only [Tw.pullU, Tw.eval, Tw.eval_pullU ψ η r ρ, Tw.eval_pullU ψ η M ρ]
  | _, _, ψ, η, _, _, .row M j, ρ => by
      simp only [Tw.pullU, Tw.eval, Tw.eval_pullU ψ η M ρ]
  | _, _, ψ, η, _, _, .ulam t, ρ => by
      simp only [Tw.pullU, Tw.eval]
      exact funext fun r => by
        rw [Tw.eval_pullU (ψ.cons r) (liftU η) t ρ, Scaling.pull_liftU]
  | _, _, ψ, η, _, _, .uapp t μ, ρ => by
      simp only [Tw.pullU, Tw.eval]
      rw [Tw.eval_pullU ψ η t ρ, Scaling.logScale_pull]

/-- Weakening the unit scope is invisible to evaluation. -/
theorem Tw.eval_uweaken {k : ℕ} (ψ : Scaling B k) (r : ℝ) {Θ : List Shape}
    {s : Shape} (t : Tw B k Θ s) (ρ : TwEnv Θ) :
    Tw.eval (ψ.cons r) t.uweaken ρ = Tw.eval ψ t ρ := by
  rw [Tw.uweaken, Tw.eval_pullU, Scaling.pull_weaken]

/-- Substitution preserves evaluation, at environments where each substituend
evaluates to the value it replaces. -/
theorem Tw.eval_subst : ∀ {k : ℕ} (ψ : Scaling B k) {Θ Θ' : List Shape}
    (σ : ∀ (n : ℕ) (s : Shape), Θ[n]? = some s → Tw B k Θ' s) {s : Shape}
    (t : Tw B k Θ s) (ρ : TwEnv Θ) (ρ' : TwEnv Θ'),
    (∀ (n : ℕ) (sh : Shape) (h : Θ[n]? = some sh),
        Tw.eval ψ (σ n sh h) ρ' = TwEnv.lookup n h ρ) →
    Tw.eval ψ (t.subst σ) ρ' = Tw.eval ψ t ρ
  | _, ψ, _, _, σ, _, .var n h, ρ, ρ', hσ => hσ n _ h
  | _, _, _, _, _, _, .unit u, _, _, _ => rfl
  | _, ψ, _, _, σ, _, .mul a b, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ a ρ ρ' hσ,
        Tw.eval_subst ψ σ b ρ ρ' hσ]
  | _, ψ, _, _, σ, _, .div a b, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ a ρ ρ' hσ,
        Tw.eval_subst ψ σ b ρ ρ' hσ]
  | _, ψ, _, _, σ, _, .qpow t q, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ t ρ ρ' hσ]
  | _, ψ, _, _, σ, _, .lam t, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval]
      exact funext fun r => Tw.eval_subst ψ (Tw.liftS σ) t (r, ρ) (r, ρ')
        fun n sh h => by
          cases n with
          | zero => rfl
          | succ n =>
              simpa [Tw.liftS, Tw.eval_weakenR, TwEnv.lookup]
                using hσ n sh (by simpa using h)
  | _, ψ, _, _, σ, _, .app g a, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ g ρ ρ' hσ,
        Tw.eval_subst ψ σ a ρ ρ' hσ]
  | _, _, _, _, _, _, .vecnil, _, _, _ => rfl
  | _, ψ, _, _, σ, _, .veccons a v, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ a ρ ρ' hσ,
        Tw.eval_subst ψ σ v ρ ρ' hσ]
  | _, ψ, _, _, σ, _, .proj v i, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ v ρ ρ' hσ]
  | _, _, _, _, _, _, .matnil, _, _, _ => rfl
  | _, ψ, _, _, σ, _, .matcons r M, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ r ρ ρ' hσ,
        Tw.eval_subst ψ σ M ρ ρ' hσ]
  | _, ψ, _, _, σ, _, .row M j, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ M ρ ρ' hσ]
  | _, ψ, _, _, σ, _, .ulam t, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval]
      exact funext fun r => Tw.eval_subst (ψ.cons r) _ t ρ ρ' fun n sh h => by
        rw [Tw.eval_uweaken]
        exact hσ n sh h
  | _, ψ, _, _, σ, _, .uapp t μ, ρ, ρ', hσ => by
      simp only [Tw.subst, Tw.eval, Tw.eval_subst ψ σ t ρ ρ' hσ]

/-- β: substituting for the most recent ratio variable evaluates the body at
the substituend's value. -/
theorem Tw.eval_subst0 {k : ℕ} (ψ : Scaling B k) {Θ : List Shape} {s₀ s : Shape}
    (t : Tw B k (s₀ :: Θ) s) (a : Tw B k Θ s₀) (ρ : TwEnv Θ) :
    Tw.eval ψ (t.subst0 a) ρ = Tw.eval ψ t (Tw.eval ψ a ρ, ρ) := by
  refine Tw.eval_subst ψ _ t (Tw.eval ψ a ρ, ρ) ρ fun n sh h => ?_
  cases n with
  | zero =>
      obtain rfl : s₀ = sh := Option.some.inj h
      rfl
  | succ n => rfl

/-- The reducing application evaluates as `app` does. -/
@[simp] theorem Tw.eval_appE {k : ℕ} (ψ : Scaling B k) : ∀ {Θ : List Shape}
    {s t : Shape} (f : Tw B k Θ (.arrow s t)) (a : Tw B k Θ s) (ρ : TwEnv Θ),
    Tw.eval ψ (Tw.appE f a) ρ = Tw.eval ψ f ρ (Tw.eval ψ a ρ)
  | _, _, _, .lam b, a, ρ => by
      simp only [Tw.appE, Tw.eval, Tw.eval_subst0]
  | _, _, _, .var n h, a, ρ => by simp [Tw.appE, Tw.eval]
  | _, _, _, .app g b, a, ρ => by simp [Tw.appE, Tw.eval]
  | _, _, _, .uapp t μ, a, ρ => by simp [Tw.appE, Tw.eval]

/-- The reducing unit instantiation evaluates as `uapp` does: performing the
recorded substitution syntactically agrees with reading the family at the
instantiating unit's magnitude, which is `Scaling.pull_subst`. -/
@[simp] theorem Tw.eval_uappE {k : ℕ} (ψ : Scaling B k) : ∀ {Θ : List Shape}
    {s : Shape} (t : Tw B k Θ (.bind s)) (μ : UExp B k) (ρ : TwEnv Θ),
    Tw.eval ψ (Tw.uappE t μ) ρ = Tw.eval ψ t ρ (ψ.logScale μ)
  | _, _, .ulam t, μ, ρ => by
      simp only [Tw.uappE, Tw.eval, Tw.eval_pullU, Scaling.pull_subst]
  | _, _, .var n h, μ, ρ => by simp [Tw.uappE, Tw.eval]
  | _, _, .app g a, μ, ρ => by simp [Tw.uappE, Tw.eval]
  | _, _, .uapp t ν, μ, ρ => by simp [Tw.uappE, Tw.eval]

/-- The trivial semantic ratio at each shape: `1` at a quantity, `1` in every
component at a space, and "maps trivial to trivial" at a function. -/
def oneSem : (s : Shape) → SemTw s
  | .scalar => 1
  | .arrow _ t => fun _ => oneSem t
  | .vec _ => fun _ => 1
  | .mat _ _ => fun _ _ => 1
  | .bind s => fun _ => oneSem s

/-- The trivial syntactic ratio evaluates to the trivial semantic one, in
every scaling and every environment. -/
theorem Tw.eval_one : ∀ {k : ℕ} (ψ : Scaling B k) {Θ : List Shape} (s : Shape)
    (θρ : TwEnv Θ), Tw.eval ψ (Tw.one s) θρ = oneSem s
  | _, ψ, _, .scalar, _ => Subtype.ext (by simp [Tw.one, Tw.eval, oneSem])
  | _, ψ, _, .arrow _ t, θρ => by
      simp only [Tw.one, Tw.eval, oneSem]
      exact funext fun r => Tw.eval_one (Θ := _ :: _) ψ t (r, θρ)
  | _, ψ, _, .vec _, θρ =>
      funext fun i => Subtype.ext (by simp [Tw.one, Tw.eval, oneSem])
  | _, ψ, _, .mat _ _, θρ =>
      funext fun a => funext fun i => Subtype.ext (by simp [Tw.one, Tw.eval, oneSem])
  | _, ψ, _, .bind s, θρ => by
      simp only [Tw.one, Tw.eval, oneSem]
      exact funext fun r => Tw.eval_one (ψ.cons r) s θρ

/-! ## The twisted logical relation

`Rel` says a term is scale-invariant. `TwRel` says it is invariant *up to* a
ratio, and the square is what a conversion costs: both readings carry the
factor, so it appears twice. At ratio `1` this is `Rel`.

At a unit binder the ratio is a family indexed by the bound unit's *scaling*,
while the denotation is a family indexed by its *magnitude*. Those are different
things, which is why both indices appear. -/

variable [UnitSys B D]

/-- **The logical relation, twisted by a ratio.** -/
def TwRel : {j k : ℕ} → (τ : Ty B D j k) → SemTw (Ty.shape τ) → Scaling B k →
    Ty.den τ → Ty.den τ → Prop
  | _, _, .Q u, s, ψ, x, y => y = ψ.scale u * ((s : ℝ) * (s : ℝ)) * x
  | _, _, .arrow a b, φ, ψ, f, g =>
      ∀ (r : SemTw (Ty.shape a)) x y, TwRel a r ψ x y → TwRel b (φ r) ψ (f x) (g y)
  | _, _, .vec V, r, ψ, v, w =>
      ∀ i, w i = ψ.scale (V.get i) * ((r i : ℝ) * (r i)) * v i
  | _, _, .lin V W, t, ψ, A, C =>
      ∀ a i, C a i = (ψ.scale (W.get a) / ψ.scale (V.get i))
        * ((t a i : ℝ) * (t a i)) * A a i
  | _, _, .all _ τ, F, ψ, X, Y =>
      ∀ r s : ℝ, TwRel τ (F s) (ψ.cons s) (X r) (Y (r + s))
  | _, _, .allDim τ, F, ψ, X, Y => TwRel τ F ψ X Y

/-- **Having a trivial ratio**, at every shape: `1` at a quantity, and at a
function "maps trivial to trivial". The arrow clause is what a convert-free
function satisfies (`λx. x·x` sends ratio `1` to `1` even though it squares
others), and it is a *predicate* rather than a value for exactly that reason. -/
def IsOneSem : (s : Shape) → SemTw s → Prop
  | .scalar, r => r = 1
  | .arrow s t, φ => ∀ r, IsOneSem s r → IsOneSem t (φ r)
  | .vec _, v => ∀ i, v i = 1
  | .mat _ _, A => ∀ a i, A a i = 1
  | .bind s, F => ∀ r, IsOneSem s (F r)

/-- The canonical trivial ratio is trivial. -/
theorem isOneSem_oneSem : ∀ s : Shape, IsOneSem s (oneSem s)
  | .scalar => rfl
  | .arrow _ t => fun _ _ => isOneSem_oneSem t
  | .vec _ => fun _ => rfl
  | .mat _ _ => fun _ _ => rfl
  | .bind s => fun _ => isOneSem_oneSem s

omit [UnitSys B D] in
/-- **At the trivial ratio and at scalar type, `TwRel` is `Rel`.** So Kennedy's
theorem is the `s = 1` case of the twisted one rather than a separate result.

Stated at scalar type, and that is not a limitation to apologize for: at arrow
type `TwRel` quantifies over *every* argument ratio, so it is strictly stronger
than `Rel` there rather than equivalent to it. The scalar case is where the
characterization is used, and where the two genuinely coincide. -/
@[simp] theorem trel_Q_one {k : ℕ} {u : UExp B k} (ψ : Scaling B k) (x y : ℝ) :
    TwRel (D := D) (j := 0) (.Q u) 1 ψ x y ↔ Rel (D := D) (j := 0) (.Q u) ψ x y := by
  simp [TwRel, Rel]

/-! Ratios were once proved positive by a logical relation over shapes
(`PosSem`); the positivity now lives in the carrier itself, `SemScalar`, where
the rational-power former needs it. A scalar ratio's value is positive by
type, which is what lets the characterization divide by it, and it is the
semantic face of the group having no zero. -/

/-! ## Transporting the twisted relation

The same shape as `rel_ground` and `relCo_ground`, now carrying the ratio as
well. The ratio's transport is along an equality of *shapes*, which is why it
costs nothing: `Ty.shape_ground` says grounding leaves the shape alone. -/

omit [UnitSys B D] in
/-- **`TwRel` transports along grounding.** -/
theorem twRel_ground : ∀ {j k : ℕ} (τ : Ty B D j k) {j₀ k₀ : ℕ}
    (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀) (ψ : Scaling B k₀)
    {w : SemTw (Ty.shape τ)} {w' : SemTw (Ty.shape (Ty.ground η δ τ))}
    {x y : Ty.den τ} {x' y' : Ty.den (Ty.ground η δ τ)},
    HEq w w' → HEq x x' → HEq y y' →
    (TwRel (Ty.ground η δ τ) w' ψ x' y' ↔ TwRel τ w (ψ.pull η) x y) := by
  intro j k τ
  induction τ with
  | Q u =>
    intro _ _ η δ ψ w w' x y x' y' hw hx hy
    obtain rfl := eq_of_heq hw
    obtain rfl := eq_of_heq hx
    obtain rfl := eq_of_heq hy
    simp [Ty.ground, TwRel, Scaling.scale_pull]
  | vec V =>
    intro _ _ η δ ψ w w' x y x' y' hw hx hy
    have hlen : V.length = (V.map (substU η)).length := by simp
    have hw : HEq (show Fin V.length → SemScalar from w)
        (show Fin (V.map (substU η)).length → SemScalar from w') := hw
    have hx : HEq (show Fin V.length → ℝ from x)
        (show Fin (V.map (substU η)).length → ℝ from x') := hx
    have hy : HEq (show Fin V.length → ℝ from y)
        (show Fin (V.map (substU η)).length → ℝ from y') := hy
    rw [Fin.heq_fun_iff hlen] at hw hx hy
    show (∀ i, y' i
        = ψ.scale ((V.map (substU η)).get i) * ((w' i : ℝ) * (w' i : ℝ)) * x' i)
      ↔ ∀ i, y i = (ψ.pull η).scale (V.get i) * ((w i : ℝ) * (w i : ℝ)) * x i
    constructor
    · intro h i
      have := h ⟨(i : ℕ), hlen ▸ i.2⟩
      rw [← hw i, ← hx i, ← hy i] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
    · intro h i
      have := h ⟨(i : ℕ), hlen.symm ▸ i.2⟩
      rw [hw ⟨(i : ℕ), hlen.symm ▸ i.2⟩, hx ⟨(i : ℕ), hlen.symm ▸ i.2⟩,
          hy ⟨(i : ℕ), hlen.symm ▸ i.2⟩] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
  | lin V W =>
    intro _ _ η δ ψ w w' x y x' y' hw hx hy
    have hV : V.length = (V.map (substU η)).length := by simp
    have hW : W.length = (W.map (substU η)).length := by simp
    have hw : HEq (show Fin W.length → Fin V.length → SemScalar from w)
        (show Fin (W.map (substU η)).length → Fin (V.map (substU η)).length → SemScalar from w') := hw
    have hx : HEq (show Fin W.length → Fin V.length → ℝ from x)
        (show Fin (W.map (substU η)).length → Fin (V.map (substU η)).length → ℝ from x') := hx
    have hy : HEq (show Fin W.length → Fin V.length → ℝ from y)
        (show Fin (W.map (substU η)).length → Fin (V.map (substU η)).length → ℝ from y') := hy
    rw [Fin.heq_fun₂_iff hW hV] at hw hx hy
    show (∀ a i, y' a i
            = (ψ.scale ((W.map (substU η)).get a) / ψ.scale ((V.map (substU η)).get i))
              * ((w' a i : ℝ) * (w' a i : ℝ)) * x' a i)
      ↔ ∀ a i, y a i
            = ((ψ.pull η).scale (W.get a) / (ψ.pull η).scale (V.get i))
              * ((w a i : ℝ) * (w a i : ℝ)) * x a i
    constructor
    · intro h a i
      have := h ⟨(a : ℕ), hW ▸ a.2⟩ ⟨(i : ℕ), hV ▸ i.2⟩
      rw [← hw a i, ← hx a i, ← hy a i] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
    · intro h a i
      have := h ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩
      rw [hw ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩,
          hx ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩,
          hy ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
  | arrow a b iha ihb =>
    intro _ _ η δ ψ w w' x y x' y' hw hx hy
    have ha := Ty.den_ground a η δ
    have hb := Ty.den_ground b η δ
    have hsa : SemTw (Ty.shape a) = SemTw (Ty.shape (Ty.ground η δ a)) := by
      rw [Ty.shape_ground]
    have hsb : SemTw (Ty.shape b) = SemTw (Ty.shape (Ty.ground η δ b)) := by
      rw [Ty.shape_ground]
    constructor
    · intro h r p q hpq
      exact (ihb η δ ψ (heq_app hsa hsb hw (cast_heq hsa r).symm)
          (heq_app ha.symm hb.symm hx (cast_heq ha.symm p).symm)
          (heq_app ha.symm hb.symm hy (cast_heq ha.symm q).symm)).mp
        (h _ _ _ ((iha η δ ψ (cast_heq hsa r).symm (cast_heq ha.symm p).symm
          (cast_heq ha.symm q).symm).mpr hpq))
    · intro h r p q hpq
      exact (ihb η δ ψ (heq_app hsa hsb hw (cast_heq hsa.symm r))
          (heq_app ha.symm hb.symm hx (cast_heq ha p))
          (heq_app ha.symm hb.symm hy (cast_heq ha q))).mpr
        (h _ _ _ ((iha η δ ψ (cast_heq hsa.symm r) (cast_heq ha p)
          (cast_heq ha q)).mp hpq))
  | all d τ ih =>
    intro _ _ η δ ψ w w' x y x' y' hw hx hy
    have hτ := Ty.den_ground τ (liftU η) δ
    have hsτ : SemTw (Ty.shape τ) = SemTw (Ty.shape (Ty.ground (liftU η) δ τ)) := by
      rw [Ty.shape_ground]
    show (∀ r s : ℝ, TwRel (Ty.ground (liftU η) δ τ) (w' s) (ψ.cons s) (x' r) (y' (r + s)))
      ↔ ∀ r s : ℝ, TwRel τ (w s) ((ψ.pull η).cons s) (x r) (y (r + s))
    constructor
    · intro h r s
      have := (ih (liftU η) δ (ψ.cons s)
        (heq_app rfl hsτ hw (HEq.refl s))
        (heq_app rfl hτ.symm hx (HEq.refl r))
        (heq_app rfl hτ.symm hy (HEq.refl (r + s)))).mp (h r s)
      rwa [Scaling.pull_liftU] at this
    · intro h r s
      refine (ih (liftU η) δ (ψ.cons s)
        (heq_app rfl hsτ hw (HEq.refl s))
        (heq_app rfl hτ.symm hx (HEq.refl r))
        (heq_app rfl hτ.symm hy (HEq.refl (r + s)))).mpr ?_
      rw [Scaling.pull_liftU]
      exact h r s
  | allDim τ ih =>
    intro _ _ η δ ψ w w' x y x' y' hw hx hy
    exact ih η (liftU δ) ψ hw hx hy

omit [UnitSys B D] in
omit [UnitSys B D] in
/-- Instantiating a unit variable, for `TwRel`. -/
theorem twRel_subst {j k : ℕ} (τ : Ty B D j (k + 1)) (σ : UExp B k) (ψ : Scaling B k)
    {w : SemTw (Ty.shape τ)} {w' : SemTw (Ty.shape (τ.subst σ))}
    {x y : Ty.den τ} {x' y' : Ty.den (τ.subst σ)}
    (hw : HEq w w') (hx : HEq x x') (hy : HEq y y') :
    TwRel (τ.subst σ) w' ψ x' y' ↔ TwRel τ w (ψ.cons (ψ.logScale σ)) x y := by
  have h := twRel_ground τ (Fin.cons σ (idU B k)) (idU D j) ψ hw hx hy
  rwa [Scaling.pull_subst] at h

omit [UnitSys B D] in
omit [UnitSys B D] in
/-- Instantiating a dimension variable, for `TwRel`. -/
theorem twRel_substDim {j k : ℕ} (τ : Ty B D (j + 1) k) (d : DExp D j) (ψ : Scaling B k)
    {w : SemTw (Ty.shape τ)} {w' : SemTw (Ty.shape (τ.substDim d))}
    {x y : Ty.den τ} {x' y' : Ty.den (τ.substDim d)}
    (hw : HEq w w') (hx : HEq x x') (hy : HEq y y') :
    TwRel (τ.substDim d) w' ψ x' y' ↔ TwRel τ w ψ x y := by
  have h := twRel_ground τ (idU B k) (Fin.cons d (idU D j)) ψ hw hx hy
  rwa [Scaling.pull_id] at h

omit [UnitSys B D] in
omit [UnitSys B D] in
/-- Weakening under a unit binder, for `TwRel`. -/
theorem twRel_weaken {j k : ℕ} (τ : Ty B D j k) (ψ : Scaling B k) (s : ℝ)
    {w : SemTw (Ty.shape τ)} {w' : SemTw (Ty.shape (Ty.weaken τ))}
    {x y : Ty.den τ} {x' y' : Ty.den (Ty.weaken τ)}
    (hw : HEq w w') (hx : HEq x x') (hy : HEq y y') :
    TwRel (Ty.weaken τ) w' (ψ.cons s) x' y' ↔ TwRel τ w ψ x y := by
  have h := twRel_ground τ (fun i => Term.ofVar i.succ) (idU D j) (ψ.cons s) hw hx hy
  rwa [Scaling.pull_weaken] at h

/-- Every argument enters with trivial ratio: a `TwEnv` of ones. -/
def oneTwEnv : (Θ : List Shape) → TwEnv Θ
  | [] => PUnit.unit
  | s :: Θ => (oneSem s, oneTwEnv Θ)

/-- Looking up the all-ones environment gives the trivial ratio. -/
theorem TwEnv.lookup_oneTwEnv : ∀ {Θ : List Shape} {s : Shape} (n : ℕ)
    (h : Θ[n]? = some s), TwEnv.lookup n h (oneTwEnv Θ) = oneSem s
  | [], _, _, h => absurd h (by simp)
  | _ :: _, _, 0, h => by obtain rfl := Option.some.inj h; rfl
  | _ :: _, _, n + 1, h => TwEnv.lookup_oneTwEnv n (by simpa using h)

/-- **The pinned region of a ratio environment.** A ratio environment is
trivial from position `p` on: positions below `p` are the genuine atoms,
introduced by `lam` binders, and positions at `p` and beyond are the
program's own context variables, whose ratio the frees-at-one assignment
fixes at `1`. -/
def TwEnv.OnesFrom (p : ℕ) {Θ : List Shape} (θρ : TwEnv Θ) : Prop :=
  ∀ (n : ℕ) (s : Shape) (h : Θ[n]? = some s), p ≤ n →
    TwEnv.lookup n h θρ = oneSem s

/-- Extending the environment at a fresh atom moves the pinned region one
position out: the `lam` case of the scaling law. -/
theorem TwEnv.OnesFrom.cons {p : ℕ} {Θ : List Shape} {θρ : TwEnv Θ}
    {s : Shape} (r : SemTw s) (hθ : TwEnv.OnesFrom p θρ) :
    TwEnv.OnesFrom (p + 1) (Θ := s :: Θ) (r, θρ) := by
  intro n s' h hp
  cases n with
  | zero => exact absurd hp (by omega)
  | succ n => exact hθ n s' (by simpa using h) (by omega)

/-- The all-ones environment is trivial from every position on. -/
theorem TwEnv.onesFrom_oneTwEnv (p : ℕ) {Θ : List Shape} :
    TwEnv.OnesFrom p (oneTwEnv Θ) :=
  fun n _ h _ => TwEnv.lookup_oneTwEnv n h

/-! ## The symbolic normalizer

A ratio's value under `ψ` at the trivial environment is `ψ.scale` of a single
unit expression, and that expression is computable. This is what makes the
triviality of a ratio *decidable*, which is the point of ratios being syntax.

The normalizer is environment-passing in the unit scope: rather than moving
values between scopes (which would force a Kripke model, since the function
space at arrow shape cannot be weakened), every value lives at one global scope
`k₀`, and a term's own unit variables are interpreted through `υ`. Crossing a
`ulam` extends `υ`; nothing is ever weakened. `bind` is interpreted as a
function from *unit expressions*, not from reals: the semantic family is read
only at magnitudes of expressible units (`uapp` records a `UExp`), so agreement
there is agreement everywhere it is consulted. -/

/-- The symbolic model, at a fixed global unit scope. -/
@[reducible] def SynTw (B : Type) (k₀ : ℕ) : Shape → Type
  | .scalar => UExp B k₀
  | .arrow s t => SynTw B k₀ s → SynTw B k₀ t
  | .vec n => Fin n → UExp B k₀
  | .mat n m => Fin m → Fin n → UExp B k₀
  | .bind s => UExp B k₀ → SynTw B k₀ s

/-- Trivial values, at every shape. -/
def SynTw.one : {k₀ : ℕ} → (s : Shape) → SynTw B k₀ s
  | _, .scalar => 1
  | _, .arrow _ t => fun _ => SynTw.one t
  | _, .vec _ => fun _ => 1
  | _, .mat _ _ => fun _ _ => 1
  | _, .bind s => fun _ => SynTw.one s

/-- Symbolic environments. -/
@[reducible] def SynEnv (B : Type) (k₀ : ℕ) : List Shape → Type
  | [] => PUnit
  | s :: Θ => SynTw B k₀ s × SynEnv B k₀ Θ

/-- Looking a symbolic value up. -/
def SynEnv.lookup {k₀ : ℕ} : {Θ : List Shape} → {s : Shape} → (n : ℕ) →
    Θ[n]? = some s → SynEnv B k₀ Θ → SynTw B k₀ s
  | [], _, _, h, _ => absurd h (by simp)
  | _ :: _, _, 0, h, ρ => Option.some.inj h ▸ ρ.1
  | _ :: _, _, n + 1, h, ρ => SynEnv.lookup n (by simpa using h) ρ.2

/-- The all-ones symbolic environment. -/
def SynEnv.ones {k₀ : ℕ} : (Θ : List Shape) → SynEnv B k₀ Θ
  | [] => PUnit.unit
  | s :: Θ => (SynTw.one s, SynEnv.ones Θ)

/-- **The normalizer.** Computes the symbolic value of a ratio. -/
def Tw.nf {k₀ : ℕ} : {k : ℕ} → (υ : Fin k → UExp B k₀) → {Θ : List Shape} →
    {s : Shape} → Tw B k Θ s → SynEnv B k₀ Θ → SynTw B k₀ s
  | _, _, _, _, .var n h, ρ => SynEnv.lookup n h ρ
  | _, υ, _, _, .unit u, _ => substU υ u
  | _, υ, _, _, .mul a b, ρ => Term.mul (Tw.nf υ a ρ) (Tw.nf υ b ρ)
  | _, υ, _, _, .div a b, ρ => Term.div (Tw.nf υ a ρ) (Tw.nf υ b ρ)
  | _, υ, _, _, .qpow t q, ρ => Term.rpow (Tw.nf υ t ρ) q
  | _, υ, _, _, .lam t, ρ => fun x => Tw.nf υ t (x, ρ)
  | _, υ, _, _, .app f a, ρ => (Tw.nf υ f ρ) (Tw.nf υ a ρ)
  | _, _, _, _, .vecnil, _ => fun i => i.elim0
  | _, υ, _, _, .veccons a v, ρ => Fin.cons (Tw.nf υ a ρ) (Tw.nf υ v ρ)
  | _, υ, _, _, .proj v i, ρ => (Tw.nf υ v ρ) i
  | _, _, _, _, .matnil, _ => fun j => j.elim0
  | _, υ, _, _, .matcons r M, ρ => Fin.cons (Tw.nf υ r ρ) (Tw.nf υ M ρ)
  | _, υ, _, _, .row M j, ρ => (Tw.nf υ M ρ) j
  | _, υ, _, _, .ulam t, ρ => fun μ => Tw.nf (Fin.cons μ υ) t ρ
  | _, υ, _, _, .uapp t μ, ρ => (Tw.nf υ t ρ) (substU υ μ)

/-! ### Correctness -/

/-- The relation between symbolic and semantic values. At `bind` the two
families need only agree at magnitudes of expressible units: those are the only
points `uapp` ever reads. -/
def SRel {k₀ : ℕ} (ψ : Scaling B k₀) : (s : Shape) → SynTw B k₀ s → SemTw s → Prop
  | .scalar, m, v => (v : ℝ) = ψ.scale m
  | .arrow s t, F, G => ∀ m v, SRel ψ s m v → SRel ψ t (F m) (G v)
  | .vec _, mV, vV => ∀ i, (vV i : ℝ) = ψ.scale (mV i)
  | .mat _ _, mA, vA => ∀ a i, (vA a i : ℝ) = ψ.scale (mA a i)
  | .bind s, F, G => ∀ μ : UExp B k₀, SRel ψ s (F μ) (G (ψ.logScale μ))

/-- Environments related pointwise. -/
def SRelEnv {k₀ : ℕ} (ψ : Scaling B k₀) :
    (Θ : List Shape) → SynEnv B k₀ Θ → TwEnv Θ → Prop
  | [], _, _ => True
  | s :: Θ, mρ, θρ => SRel ψ s mρ.1 θρ.1 ∧ SRelEnv ψ Θ mρ.2 θρ.2

theorem SRelEnv.lookup {k₀ : ℕ} {ψ : Scaling B k₀} : ∀ {Θ : List Shape} {s : Shape}
    (n : ℕ) (h : Θ[n]? = some s) {mρ : SynEnv B k₀ Θ} {θρ : TwEnv Θ},
    SRelEnv ψ Θ mρ θρ → SRel ψ s (SynEnv.lookup n h mρ) (TwEnv.lookup n h θρ)
  | [], _, _, h, _, _, _ => absurd h (by simp)
  | _ :: _, _, 0, h, _, _, hp => by
      obtain rfl := Option.some.inj h
      exact hp.1
  | _ :: _, _, n + 1, h, _, _, hp => SRelEnv.lookup n (by simpa using h) hp.2

/-- The trivial symbolic value relates to the trivial semantic one. -/
theorem srel_one {k₀ : ℕ} (ψ : Scaling B k₀) :
    ∀ s : Shape, SRel ψ s (SynTw.one s) (oneSem s)
  | .scalar => by simp [SRel, SynTw.one, oneSem]
  | .arrow s t => fun _ _ _ => srel_one ψ t
  | .vec _ => fun _ => by simp [SynTw.one, oneSem]
  | .mat _ _ => fun _ _ => by simp [SynTw.one, oneSem]
  | .bind s => fun _ => srel_one ψ s

/-- The all-ones environments are related. -/
theorem srelEnv_ones {k₀ : ℕ} (ψ : Scaling B k₀) : ∀ Θ : List Shape,
    SRelEnv ψ Θ (SynEnv.ones Θ) (oneTwEnv Θ)
  | [] => trivial
  | s :: Θ => ⟨srel_one ψ s, srelEnv_ones ψ Θ⟩

/-- **The normalizer is correct.** Its output, under `SRel`, matches the
ratio's value (the ratio's unit scope read through `υ`, its scaling therefore
the pullback). The `ulam` case is `pull_cons` and the `uapp` case is
`logScale_pull`: the environment-passing design paying off, with no weakening,
no Kripke structure, and no transport. -/
theorem Tw.nf_correct {k₀ : ℕ} (ψ : Scaling B k₀) : ∀ {k : ℕ}
    (υ : Fin k → UExp B k₀) {Θ : List Shape} {s : Shape} (t : Tw B k Θ s)
    (mρ : SynEnv B k₀ Θ) (θρ : TwEnv Θ), SRelEnv ψ Θ mρ θρ →
    SRel ψ s (Tw.nf υ t mρ) (Tw.eval (ψ.pull υ) t θρ)
  | _, υ, _, _, .var n h, mρ, θρ, hρ => SRelEnv.lookup n h hρ
  | _, υ, _, _, .unit u, _, _, _ =>
      show (ψ.pull υ).scale u = ψ.scale (substU υ u) from Scaling.scale_pull ψ υ u
  | _, υ, _, _, .mul a b, mρ, θρ, hρ => by
      show (Tw.eval (ψ.pull υ) a θρ : ℝ) * (Tw.eval (ψ.pull υ) b θρ : ℝ)
        = ψ.scale (Term.mul (Tw.nf υ a mρ) (Tw.nf υ b mρ))
      rw [Scaling.scale_mul,
        show (Tw.eval (ψ.pull υ) a θρ : ℝ) = ψ.scale (Tw.nf υ a mρ) from
          Tw.nf_correct ψ υ a mρ θρ hρ,
        show (Tw.eval (ψ.pull υ) b θρ : ℝ) = ψ.scale (Tw.nf υ b mρ) from
          Tw.nf_correct ψ υ b mρ θρ hρ]
  | _, υ, _, _, .div a b, mρ, θρ, hρ => by
      show (Tw.eval (ψ.pull υ) a θρ : ℝ) / (Tw.eval (ψ.pull υ) b θρ : ℝ)
        = ψ.scale (Term.div (Tw.nf υ a mρ) (Tw.nf υ b mρ))
      rw [Scaling.scale_div,
        show (Tw.eval (ψ.pull υ) a θρ : ℝ) = ψ.scale (Tw.nf υ a mρ) from
          Tw.nf_correct ψ υ a mρ θρ hρ,
        show (Tw.eval (ψ.pull υ) b θρ : ℝ) = ψ.scale (Tw.nf υ b mρ) from
          Tw.nf_correct ψ υ b mρ θρ hρ]
  | _, υ, _, _, .qpow t q, mρ, θρ, hρ => by
      show (Tw.eval (ψ.pull υ) t θρ : ℝ) ^ (q : ℝ)
        = ψ.scale (Term.rpow (Tw.nf υ t mρ) q)
      rw [Scaling.scale_rpow,
        show (Tw.eval (ψ.pull υ) t θρ : ℝ) = ψ.scale (Tw.nf υ t mρ) from
          Tw.nf_correct ψ υ t mρ θρ hρ]
  | _, υ, _, _, .lam t, mρ, θρ, hρ => fun m v hmv =>
      Tw.nf_correct ψ υ t (m, mρ) (v, θρ) ⟨hmv, hρ⟩
  | _, υ, _, _, .app f a, mρ, θρ, hρ =>
      (Tw.nf_correct ψ υ f mρ θρ hρ) _ _ (Tw.nf_correct ψ υ a mρ θρ hρ)
  | _, _, _, _, .vecnil, _, _, _ => fun i => i.elim0
  | _, υ, _, _, .veccons a v, mρ, θρ, hρ => by
      intro i
      cases i using Fin.cases with
      | zero => simpa [SRel, Tw.eval, Tw.nf] using Tw.nf_correct ψ υ a mρ θρ hρ
      | succ i => simpa [SRel, Tw.eval, Tw.nf] using (Tw.nf_correct ψ υ v mρ θρ hρ) i
  | _, υ, _, _, .proj v i, mρ, θρ, hρ => (Tw.nf_correct ψ υ v mρ θρ hρ) i
  | _, _, _, _, .matnil, _, _, _ => fun a => a.elim0
  | _, υ, _, _, .matcons r M, mρ, θρ, hρ => by
      intro a i
      cases a using Fin.cases with
      | zero => simpa [SRel, Tw.eval, Tw.nf] using (Tw.nf_correct ψ υ r mρ θρ hρ) i
      | succ a => simpa [SRel, Tw.eval, Tw.nf] using (Tw.nf_correct ψ υ M mρ θρ hρ) a i
  | _, υ, _, _, .row M j, mρ, θρ, hρ => (Tw.nf_correct ψ υ M mρ θρ hρ) j
  | _, υ, _, _, .ulam t, mρ, θρ, hρ => fun μ => by
      have h := Tw.nf_correct ψ (Fin.cons μ υ) t mρ θρ hρ
      rwa [Scaling.pull_cons] at h
  | _, υ, _, _, .uapp t μ, mρ, θρ, hρ => by
      have h := (Tw.nf_correct ψ υ t mρ θρ hρ) (substU υ μ)
      show SRel ψ _ ((Tw.nf υ t mρ) (substU υ μ))
        ((Tw.eval (ψ.pull υ) t θρ) ((ψ.pull υ).logScale μ))
      rw [Scaling.logScale_pull]
      exact h

end LambdaS

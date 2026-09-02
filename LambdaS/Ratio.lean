import LambdaS.Fundamental

/-!
# Conversion ratios as syntax

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
(`arrow`), where there is nothing to track (`triv`, for spaces and linear maps),
and where a unit binder was crossed (`bind`).
-/

namespace LambdaS

/-- The skeleton of a type, as far as conversion ratios can see. -/
inductive Shape where
  /-- A quantity: the ratio is a unit expression. -/
  | scalar : Shape
  /-- A function: the ratio maps ratios to ratios. -/
  | arrow : Shape → Shape → Shape
  /-- A space or a linear map: no ratio to track, since `convert` is scalar. -/
  | triv : Shape
  /-- Under a unit binder: the ratio lives one unit scope out. -/
  | bind : Shape → Shape
  deriving DecidableEq, Repr

variable {B D : Type}

/-- The shape of a type. Units are ignored; only the structure survives.

`@[reducible]` for the same reason `Ty.den` is: instance synthesis runs at
reducible transparency, and `SemTw (Ty.shape (.Q u))` has to resolve to `ℝ`. -/
@[reducible] def Ty.shape : {j k : ℕ} → Ty B D j k → Shape
  | _, _, .Q _ => .scalar
  | _, _, .arrow a b => .arrow (Ty.shape a) (Ty.shape b)
  | _, _, .vec _ => .triv
  | _, _, .lin _ _ => .triv
  | _, _, .all _ τ => .bind (Ty.shape τ)
  | _, _, .allDim τ => Ty.shape τ

/-- The shapes of a context, one ratio variable per term variable. -/
def Ctx.shapes {j k : ℕ} (Γ : Ctx B D j k) : List Shape := Γ.map Ty.shape

@[simp] theorem Ctx.shapes_nil {j k : ℕ} :
    Ctx.shapes ([] : Ctx B D j k) = [] := rfl

@[simp] theorem Ctx.shapes_cons {j k : ℕ} (τ : Ty B D j k) (Γ : Ctx B D j k) :
    Ctx.shapes (τ :: Γ) = Ty.shape τ :: Ctx.shapes Γ := rfl

/-- **Shape is blind to units.** Grounding a type through unit and dimension
environments leaves its shape alone, which is why ratios need no transport: the
`Tw` indexed by a type is equally an index for every instantiation of it. -/
@[simp] theorem Ty.shape_ground : ∀ {j k : ℕ} (τ : Ty B D j k) {j₀ k₀ : ℕ}
    (η : Fin k → UExp B k₀) (δ : Fin j → DExp D j₀),
    Ty.shape (Ty.ground η δ τ) = Ty.shape τ := by
  intro j k τ
  induction τ with
  | Q u => intro _ _ _ _; rfl
  | arrow a b iha ihb => intro _ _ η δ; simp only [Ty.ground, Ty.shape, iha, ihb]
  | vec V => intro _ _ _ _; rfl
  | lin V W => intro _ _ _ _; rfl
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
  /-- Abstraction binds a ratio variable. This is the first-order replacement
  for the function space, and the whole point of the file. -/
  | lam {k Θ s t} : Tw B k (s :: Θ) t → Tw B k Θ (.arrow s t)
  /-- Application. -/
  | app {k Θ s t} : Tw B k Θ (.arrow s t) → Tw B k Θ s → Tw B k Θ t
  /-- Nothing to track. -/
  | triv {k Θ} : Tw B k Θ .triv
  /-- Under a unit binder the ratio lives at the larger unit scope. -/
  | ulam {k Θ s} : Tw B (k + 1) Θ s → Tw B k Θ (.bind s)
  /-- Unit instantiation is **recorded**, not performed. -/
  | uapp {k Θ s} : Tw B k Θ (.bind s) → UExp B k → Tw B k Θ s

/-- Retyping a ratio along an equality of shapes. Needed only at `uapp` and
`dapp`, where the result type is `τ.subst σ` and `Ty.shape_subst` is a theorem
rather than a definitional equality. -/
def Tw.castShape {k : ℕ} {Θ : List Shape} {s s' : Shape} (h : s = s') :
    Tw B k Θ s → Tw B k Θ s' := fun t => h ▸ t

@[simp] theorem Tw.castShape_rfl {k : ℕ} {Θ : List Shape} {s : Shape}
    (t : Tw B k Θ s) : Tw.castShape rfl t = t := rfl

/-! ## What a ratio means -/

/-- The semantic ratio at each shape: a scale factor at a quantity, a map at a
function, a family at a unit binder. -/
@[reducible] def SemTw : Shape → Type
  | .scalar => ℝ
  | .arrow s t => SemTw s → SemTw t
  | .triv => PUnit
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
  | _, ψ, _, _, .unit u, _ => ψ.scale u
  | _, ψ, _, _, .mul a b, ρ => Tw.eval ψ a ρ * Tw.eval ψ b ρ
  | _, ψ, _, _, .div a b, ρ => Tw.eval ψ a ρ / Tw.eval ψ b ρ
  | _, ψ, _, _, .lam t, ρ => fun r => Tw.eval ψ t (r, ρ)
  | _, ψ, _, _, .app f a, ρ => (Tw.eval ψ f ρ) (Tw.eval ψ a ρ)
  | _, _, _, _, .triv, _ => PUnit.unit
  | _, ψ, _, _, .ulam t, ρ => fun r => Tw.eval (ψ.cons r) t ρ
  | _, ψ, _, _, .uapp t μ, ρ => (Tw.eval ψ t ρ) (ψ.logScale μ)

/-- Evaluation commutes with retyping. -/
@[simp] theorem Tw.eval_castShape {k : ℕ} (ψ : Scaling B k) {Θ : List Shape}
    {s s' : Shape} (h : s = s') (t : Tw B k Θ s) (ρ : TwEnv Θ) :
    Tw.eval ψ (Tw.castShape h t) ρ = h ▸ Tw.eval ψ t ρ := by
  subst h; rfl

/-- The trivial semantic ratio at each shape: `1` at a quantity, and "maps
trivial to trivial" at a function. -/
def oneSem : (s : Shape) → SemTw s
  | .scalar => 1
  | .arrow _ t => fun _ => oneSem t
  | .triv => PUnit.unit
  | .bind s => fun _ => oneSem s

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
  | _, _, .vec V, _, ψ, v, w => ∀ i, w i = ψ.scale (V.get i) * v i
  | _, _, .lin V W, _, ψ, A, C =>
      ∀ a i, C a i = (ψ.scale (W.get a) / ψ.scale (V.get i)) * A a i
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
  | .triv, _ => True
  | .bind s, F => ∀ r, IsOneSem s (F r)

/-- The canonical trivial ratio is trivial. -/
theorem isOneSem_oneSem : ∀ s : Shape, IsOneSem s (oneSem s)
  | .scalar => rfl
  | .arrow _ t => fun _ _ => isOneSem_oneSem t
  | .triv => trivial
  | .bind s => fun _ => isOneSem_oneSem s

/-- **At the trivial ratio and at scalar type, `TwRel` is `Rel`.** So Kennedy's
theorem is the `s = 1` case of the twisted one rather than a separate result.

Stated at scalar type, and that is not a limitation to apologize for: at arrow
type `TwRel` quantifies over *every* argument ratio, so it is strictly stronger
than `Rel` there rather than equivalent to it. The scalar case is where the
characterization is used, and where the two genuinely coincide. -/
@[simp] theorem trel_Q_one {k : ℕ} {u : UExp B k} (ψ : Scaling B k) (x y : ℝ) :
    TwRel (D := D) (j := 0) (.Q u) 1 ψ x y ↔ Rel (D := D) (j := 0) (.Q u) ψ x y := by
  simp [TwRel, Rel]

/-! ## Ratios are positive

A ratio's value is built from scale factors, which are positive, by operations
that preserve positivity. Stated as a logical relation over shapes, because a
ratio at arrow shape is positive in the mapping sense. This is what lets the
characterization divide by a ratio's value, and it is the semantic face of the
group having no zero. -/

/-- Positivity at each shape. -/
def PosSem : (s : Shape) → SemTw s → Prop
  | .scalar, r => 0 < r
  | .arrow s t, φ => ∀ r, PosSem s r → PosSem t (φ r)
  | .triv, _ => True
  | .bind s, F => ∀ r, PosSem s (F r)

/-- Positive ratio environments. -/
def PosEnv : (Θ : List Shape) → TwEnv Θ → Prop
  | [], _ => True
  | s :: Θ, θρ => PosSem s θρ.1 ∧ PosEnv Θ θρ.2

theorem PosEnv.lookup : ∀ {Θ : List Shape} {s : Shape} (n : ℕ) (h : Θ[n]? = some s)
    {θρ : TwEnv Θ}, PosEnv Θ θρ → PosSem s (TwEnv.lookup n h θρ)
  | [], _, _, h, _, _ => absurd h (by simp)
  | _ :: _, _, 0, h, _, hp => by
      obtain rfl := Option.some.inj h
      exact hp.1
  | _ :: _, _, n + 1, h, _, hp => PosEnv.lookup n (by simpa using h) hp.2

/-- The trivial ratio is positive. -/
theorem posSem_oneSem : ∀ s : Shape, PosSem s (oneSem s)
  | .scalar => one_pos
  | .arrow _ t => fun _ _ => posSem_oneSem t
  | .triv => trivial
  | .bind s => fun _ => posSem_oneSem s

/-- **Every ratio is positive**, in every positive environment, under every
scaling. -/
theorem Tw.eval_pos : ∀ {k : ℕ} (ψ : Scaling B k) {Θ : List Shape} {s : Shape}
    (t : Tw B k Θ s) (θρ : TwEnv Θ), PosEnv Θ θρ → PosSem s (Tw.eval ψ t θρ)
  | _, ψ, _, _, .var n h, θρ, hp => PosEnv.lookup n h hp
  | _, ψ, _, _, .unit u, _, _ => ψ.scale_pos u
  | _, ψ, _, _, .mul a b, θρ, hp =>
      mul_pos (Tw.eval_pos ψ a θρ hp) (Tw.eval_pos ψ b θρ hp)
  | _, ψ, _, _, .div a b, θρ, hp =>
      div_pos (Tw.eval_pos ψ a θρ hp) (Tw.eval_pos ψ b θρ hp)
  | _, ψ, _, _, .lam t, θρ, hp => fun r hr => Tw.eval_pos ψ t (r, θρ) ⟨hr, hp⟩
  | _, ψ, _, _, .app f a, θρ, hp =>
      (Tw.eval_pos ψ f θρ hp) _ (Tw.eval_pos ψ a θρ hp)
  | _, _, _, _, .triv, _, _ => trivial
  | _, ψ, _, _, .ulam t, θρ, hp => fun r => Tw.eval_pos (ψ.cons r) t θρ hp
  | _, ψ, _, _, .uapp t μ, θρ, hp => (Tw.eval_pos ψ t θρ hp) (ψ.logScale μ)

/-! ## Transporting the twisted relation

The same shape as `rel_ground` and `relCo_ground`, now carrying the ratio as
well. The ratio's transport is along an equality of *shapes*, which is why it
costs nothing: `Ty.shape_ground` says grounding leaves the shape alone. -/

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
    intro _ _ η δ ψ w w' x y x' y' _ hx hy
    have hlen : V.length = (V.map (substU η)).length := by simp
    have hx : HEq (show Fin V.length → ℝ from x)
        (show Fin (V.map (substU η)).length → ℝ from x') := hx
    have hy : HEq (show Fin V.length → ℝ from y)
        (show Fin (V.map (substU η)).length → ℝ from y') := hy
    rw [Fin.heq_fun_iff hlen] at hx hy
    show (∀ i, y' i = ψ.scale ((V.map (substU η)).get i) * x' i)
      ↔ ∀ i, y i = (ψ.pull η).scale (V.get i) * x i
    constructor
    · intro h i
      have := h ⟨(i : ℕ), hlen ▸ i.2⟩
      rw [← hx i, ← hy i] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
    · intro h i
      have := h ⟨(i : ℕ), hlen.symm ▸ i.2⟩
      rw [hx ⟨(i : ℕ), hlen.symm ▸ i.2⟩, hy ⟨(i : ℕ), hlen.symm ▸ i.2⟩] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
  | lin V W =>
    intro _ _ η δ ψ w w' x y x' y' _ hx hy
    have hV : V.length = (V.map (substU η)).length := by simp
    have hW : W.length = (W.map (substU η)).length := by simp
    have hx : HEq (show Fin W.length → Fin V.length → ℝ from x)
        (show Fin (W.map (substU η)).length → Fin (V.map (substU η)).length → ℝ from x') := hx
    have hy : HEq (show Fin W.length → Fin V.length → ℝ from y)
        (show Fin (W.map (substU η)).length → Fin (V.map (substU η)).length → ℝ from y') := hy
    rw [Fin.heq_fun₂_iff hW hV] at hx hy
    show (∀ a i, y' a i
            = (ψ.scale ((W.map (substU η)).get a) / ψ.scale ((V.map (substU η)).get i)) * x' a i)
      ↔ ∀ a i, y a i
            = ((ψ.pull η).scale (W.get a) / (ψ.pull η).scale (V.get i)) * x a i
    constructor
    · intro h a i
      have := h ⟨(a : ℕ), hW ▸ a.2⟩ ⟨(i : ℕ), hV ▸ i.2⟩
      rw [← hx a i, ← hy a i] at this
      simpa [List.get_eq_getElem, Scaling.scale_pull] using this
    · intro h a i
      have := h ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩
      rw [hx ⟨(a : ℕ), hW.symm ▸ a.2⟩ ⟨(i : ℕ), hV.symm ▸ i.2⟩,
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

/-- Instantiating a unit variable, for `TwRel`. -/
theorem twRel_subst {j k : ℕ} (τ : Ty B D j (k + 1)) (σ : UExp B k) (ψ : Scaling B k)
    {w : SemTw (Ty.shape τ)} {w' : SemTw (Ty.shape (τ.subst σ))}
    {x y : Ty.den τ} {x' y' : Ty.den (τ.subst σ)}
    (hw : HEq w w') (hx : HEq x x') (hy : HEq y y') :
    TwRel (τ.subst σ) w' ψ x' y' ↔ TwRel τ w (ψ.cons (ψ.logScale σ)) x y := by
  have h := twRel_ground τ (Fin.cons σ (idU B k)) (idU D j) ψ hw hx hy
  rwa [Scaling.pull_subst] at h

/-- Instantiating a dimension variable, for `TwRel`. -/
theorem twRel_substDim {j k : ℕ} (τ : Ty B D (j + 1) k) (d : DExp D j) (ψ : Scaling B k)
    {w : SemTw (Ty.shape τ)} {w' : SemTw (Ty.shape (τ.substDim d))}
    {x y : Ty.den τ} {x' y' : Ty.den (τ.substDim d)}
    (hw : HEq w w') (hx : HEq x x') (hy : HEq y y') :
    TwRel (τ.substDim d) w' ψ x' y' ↔ TwRel τ w ψ x y := by
  have h := twRel_ground τ (idU B k) (Fin.cons d (idU D j)) ψ hw hx hy
  rwa [Scaling.pull_id] at h

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
  | .triv => PUnit
  | .bind s => UExp B k₀ → SynTw B k₀ s

/-- Trivial values, at every shape. -/
def SynTw.one : {k₀ : ℕ} → (s : Shape) → SynTw B k₀ s
  | _, .scalar => 1
  | _, .arrow _ t => fun _ => SynTw.one t
  | _, .triv => PUnit.unit
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
  | _, υ, _, _, .lam t, ρ => fun x => Tw.nf υ t (x, ρ)
  | _, υ, _, _, .app f a, ρ => (Tw.nf υ f ρ) (Tw.nf υ a ρ)
  | _, _, _, _, .triv, _ => PUnit.unit
  | _, υ, _, _, .ulam t, ρ => fun μ => Tw.nf (Fin.cons μ υ) t ρ
  | _, υ, _, _, .uapp t μ, ρ => (Tw.nf υ t ρ) (substU υ μ)

/-! ### Correctness -/

/-- The relation between symbolic and semantic values. At `bind` the two
families need only agree at magnitudes of expressible units: those are the only
points `uapp` ever reads. -/
def SRel {k₀ : ℕ} (ψ : Scaling B k₀) : (s : Shape) → SynTw B k₀ s → SemTw s → Prop
  | .scalar, m, v => v = ψ.scale m
  | .arrow s t, F, G => ∀ m v, SRel ψ s m v → SRel ψ t (F m) (G v)
  | .triv, _, _ => True
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
  | .triv => trivial
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
      show (Tw.eval (ψ.pull υ) a θρ) * (Tw.eval (ψ.pull υ) b θρ)
        = ψ.scale (Term.mul (Tw.nf υ a mρ) (Tw.nf υ b mρ))
      rw [Scaling.scale_mul,
        show Tw.eval (ψ.pull υ) a θρ = ψ.scale (Tw.nf υ a mρ) from
          Tw.nf_correct ψ υ a mρ θρ hρ,
        show Tw.eval (ψ.pull υ) b θρ = ψ.scale (Tw.nf υ b mρ) from
          Tw.nf_correct ψ υ b mρ θρ hρ]
  | _, υ, _, _, .div a b, mρ, θρ, hρ => by
      show (Tw.eval (ψ.pull υ) a θρ) / (Tw.eval (ψ.pull υ) b θρ)
        = ψ.scale (Term.div (Tw.nf υ a mρ) (Tw.nf υ b mρ))
      rw [Scaling.scale_div,
        show Tw.eval (ψ.pull υ) a θρ = ψ.scale (Tw.nf υ a mρ) from
          Tw.nf_correct ψ υ a mρ θρ hρ,
        show Tw.eval (ψ.pull υ) b θρ = ψ.scale (Tw.nf υ b mρ) from
          Tw.nf_correct ψ υ b mρ θρ hρ]
  | _, υ, _, _, .lam t, mρ, θρ, hρ => fun m v hmv =>
      Tw.nf_correct ψ υ t (m, mρ) (v, θρ) ⟨hmv, hρ⟩
  | _, υ, _, _, .app f a, mρ, θρ, hρ =>
      (Tw.nf_correct ψ υ f mρ θρ hρ) _ _ (Tw.nf_correct ψ υ a mρ θρ hρ)
  | _, _, _, _, .triv, _, _, _ => trivial
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

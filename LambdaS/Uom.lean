import Mathlib.Tactic

/-!
# Units of measure

A unit of measure over a set `B` of base units is a **ℚ-valued exponent vector**:
a function `B → ℚ` recording the power of each base unit.

Units are written *multiplicatively* (`m * s⁻¹`, `m ^ (-1/2 : ℚ)`), so the
carrier is `Multiplicative ℚ` pointwise. Unit multiplication is then exponent
addition, and `Pi.commGroup` supplies the whole abelian group structure.

## Why ℚ and not ℤ

Two independent reasons, recorded because the choice looks like an
extravagance and is not:

* It is **forced by the domain.** A normalized three-dimensional wavefunction
  carries `m ^ (-3/2)`; volatility carries `Time ^ (-1/2)`. Neither is
  expressible with integer exponents, which is why no existing static units
  system can type either one.
* It makes the solver **simpler**, not harder. Over `ℤ` the unit group is a
  lattice and unification needs Hermite or Smith normal form; over `ℚ` it is a
  vector space and unification is Gaussian elimination.
-/

namespace LambdaS

/-- A unit of measure over base units `B`: a ℚ-valued exponent vector,
written multiplicatively. -/
abbrev Uom (B : Type*) := B → Multiplicative ℚ

namespace Uom

variable {B : Type*}

/-- The exponent of base unit `b` in `u`. -/
def exp (u : Uom B) (b : B) : ℚ := Multiplicative.toAdd (u b)

/-- Build a unit from an exponent vector. -/
def ofExp (f : B → ℚ) : Uom B := fun b => Multiplicative.ofAdd (f b)

@[simp] theorem exp_ofExp (f : B → ℚ) (b : B) : exp (ofExp f) b = f b := rfl

@[simp] theorem exp_one (b : B) : exp (1 : Uom B) b = 0 := rfl

@[simp] theorem exp_mul (u v : Uom B) (b : B) : exp (u * v) b = exp u b + exp v b := rfl

@[simp] theorem exp_inv (u : Uom B) (b : B) : exp u⁻¹ b = -exp u b := rfl

@[simp] theorem exp_div (u v : Uom B) (b : B) : exp (u / v) b = exp u b - exp v b := rfl

/-- Two units are equal exactly when all their exponents agree. This is the
only extensionality principle the development needs. -/
@[ext] theorem ext {u v : Uom B} (h : ∀ b, exp u b = exp v b) : u = v := funext h

theorem ext_iff' {u v : Uom B} : u = v ↔ ∀ b, exp u b = exp v b :=
  ⟨fun h _ => by rw [h], ext⟩

/-- Raising a unit to a rational power. This is the operation integer-exponent
systems cannot provide, and it is *total*: every unit has an `n`-th root. -/
def rpow (u : Uom B) (q : ℚ) : Uom B := ofExp fun b => q * exp u b

/-- Rational powers are written `u ^ q`, exactly as on paper. -/
instance : HPow (Uom B) ℚ (Uom B) := ⟨rpow⟩

@[simp] theorem exp_rpow (u : Uom B) (q : ℚ) (b : B) :
    exp (u ^ q) b = q * exp u b := rfl

@[simp] theorem rpow_one (u : Uom B) : u ^ (1 : ℚ) = u := by ext b; simp

@[simp] theorem rpow_zero (u : Uom B) : u ^ (0 : ℚ) = 1 := by ext b; simp

theorem rpow_add (u : Uom B) (p q : ℚ) : u ^ (p + q) = u ^ p * u ^ q := by
  ext b; simp; ring

theorem rpow_mul (u : Uom B) (p q : ℚ) : u ^ (p * q) = (u ^ q) ^ p := by
  ext b; simp; ring

/-- Every unit has an `n`-th root for `n ≠ 0`. Over `ℤ` this fails, which is
precisely why the square root of a dimensioned quantity is inexpressible there. -/
theorem rpow_nth_root (u : Uom B) {n : ℚ} (hn : n ≠ 0) : (u ^ (1 / n)) ^ n = u := by
  ext b; simp; field_simp

/-- ℚ is torsion-free, so the unit group is too: a unit equal to its own
inverse is trivial.

This single fact is what forces the Cholesky factor into the dimensionless
space in `LambdaS.Map`, and it is where the choice of ℚ (rather than, say,
ℤ/2ℤ-graded exponents) does load-bearing work. -/
theorem eq_inv_iff_one {u : Uom B} : u = u⁻¹ ↔ u = 1 := by
  constructor
  · intro h
    ext b
    have hb : exp u b = -exp u b := by rw [← exp_inv, ← h]
    simp only [exp_one]
    linarith
  · rintro rfl
    ext b
    simp

end Uom

end LambdaS

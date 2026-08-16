import Lean4Axiomatic.Rational.Order

/-! # Rational numbers: floor and ceiling functions -/

namespace Lean4Axiomatic.Rational

/-! ## Axioms -/

/-- Floor and ceiling functions on rational numbers. -/
class FloorCeil.Ops (ℤ : outParam Type) (ℚ : Type) where
  /-- The greatest integer less than or equivalent to the given value. -/
  floor : ℚ → ℤ

  /-- The least integer greater than or equivalent to the given value. -/
  ceil : ℚ → ℤ

export FloorCeil.Ops (ceil floor)

/-- Defining properties of floor and ceiling functions on rational numbers. -/
class FloorCeil.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Sign ℚ] [Subtraction ℚ] [Order ℚ] [Ops ℤ ℚ]
    where
  /-- A rational is no smaller than its floor. -/
  floor_ub {p : ℚ} : floor p ≤ p

  /--
  A rational's floor is the greatest integer not greater than the rational
  itself.
  -/
  floor_lb {p : ℚ} {a : ℤ} : a ≤ p → a ≤ floor p

  /-- A rational is no larger than its ceiling. -/
  ceil_lb {p : ℚ} : p ≤ ceil p

  /--
  A rational's ceiling is the least integer not less than the rational itself.
  -/
  ceil_ub {p : ℚ} {a : ℤ} : p ≤ a → ceil p ≤ a

export FloorCeil.Props (ceil_lb ceil_ub floor_lb floor_ub)

/-- All floor and ceiling axioms for rational numbers. -/
class FloorCeil
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : outParam Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ][Negation ℚ] [Sign ℚ]
      [Subtraction ℚ] [Order ℚ]
    where
  toOps : FloorCeil.Ops (ℤ := ℤ) ℚ
  toProps : FloorCeil.Props ℚ

attribute [implicit_reducible, instance] FloorCeil.toOps
attribute [instance] FloorCeil.toProps

/-! ## Derived properties -/

variable
  {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
  [Sign ℚ] [Subtraction ℚ] [Order ℚ] [FloorCeil ℚ]

/--
A rational is less than an integer if its floor is.

This is equivalent to the contrapositive of `floor_lb`.
-/
theorem floor_lb_mt {p : ℚ} {a : ℤ} : floor p < a → p < a := by
  intro (_ : floor p < a)
  show p < a
  have : ¬(floor p ≥ a) := Integer.not_ge_iff_lt.mpr ‹floor p < a›
  have : ¬(a ≤ floor p) := ‹¬(floor p ≥ a)›
  -- ↓ begin key steps ↓
  have : ¬(a ≤ p) := mt floor_lb ‹¬(a ≤ floor p)›
  -- ↑  end key steps  ↑
  have : ¬(p ≥ a) := ‹¬(a ≤ p)›
  have : p < a := not_ge_iff_lt.mp ‹¬(p ≥ a)›
  exact this

/--
Every rational number is located between consecutive integers, with the smaller
being that number's unique floor.
-/
theorem floor_bounds {p : ℚ} : floor p ≤ p ∧ p < floor p + 1 := by
  have : floor p ≤ p := floor_ub
  have : floor p < floor p + 1 := Integer.lt_inc
  have : p < floor p + 1 := calc
    _ = p                 := rfl
    _ < (floor p + 1 : ℤ) := floor_lb_mt ‹floor p < floor p + 1›
    _ ≃ floor p + 1       := add_compat_from_integer
  exact And.intro ‹floor p ≤ p› ‹p < floor p + 1›

end Lean4Axiomatic.Rational

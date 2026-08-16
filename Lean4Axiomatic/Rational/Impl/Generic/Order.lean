import Lean4Axiomatic.Rational.Order

/-! # Generic implementation of rational order and properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Signed (sgn)

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Sign ℚ] [Subtraction ℚ]

/-- Definition of _less than or equivalent to_ that matches the axioms. -/
def le (p q : ℚ) : Prop := sgn (p - q) ≄ 1

/-- Definition of _less than_ that matches the axioms. -/
def lt (p q : ℚ) : Prop := sgn (p - q) ≃ -1

local instance order_ops : Order.Ops ℚ := {
  le := le
  lt := lt
}

@[implicit_reducible]
def order_props : Order.Props ℚ := {
  le_sgn := Iff.intro id id
  lt_sgn := Iff.intro id id
}

@[implicit_reducible]
def order : Order ℚ := {
  toOps := order_ops
  toProps := order_props
}

end Lean4Axiomatic.Rational.Impl.Generic

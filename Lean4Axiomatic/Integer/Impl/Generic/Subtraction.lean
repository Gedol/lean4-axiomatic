import Lean4Axiomatic.Integer.Subtraction

/-! # Generic implementation of integer subtraction and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition ℤ] [Negation (ℕ := ℕ) ℤ]

/-- Define subtraction of a value from another as adding its negation. -/
def sub (a b : ℤ) : ℤ := a + (-b)

/--
The `sub` function has the signature required for integer subtraction.

Declared as an instance to enable the `· - ·` notation. It's local to prevent
it from being used in other files where it could conflict with other instances.
Most code will be written to use the `Integer` class generically, and the
instance of `Subtraction.Ops` would be obtained from that.
-/
local instance sub_ops : Subtraction.Ops ℤ := {
  sub := sub
}

/-- The `sub` function satisfies the definition of subtraction. -/
theorem sub_defn {a b : ℤ} : a - b ≃ a + (-b) := Rel.refl

/-- The `sub` function meets all the criteria needed for subtraction. -/
@[implicit_reducible]
def sub_props : Subtraction.Props ℤ := {
  sub_defn := sub_defn
}

/--
Any type `ℤ` which satifies the integer addition and negation axioms, also
satisfies the integer subtraction axioms.

Declared as an instance so that it can be easily used by other components of
this integer implementation. It's scoped to avoid conflicts with other integer
subtraction instances; when needed, it can be brought into scope via the
`open scoped` statement.
-/
scoped instance subtraction : Subtraction ℤ := {
  toOps := sub_ops
  toProps := sub_props
}

end Lean4Axiomatic.Integer.Impl.Generic

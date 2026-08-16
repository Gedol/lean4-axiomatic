import Lean4Axiomatic.Integer.Order

/-! # Generic implementations of integer order and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

open Coe (coe)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition (ℕ := ℕ) ℤ]

/-- Definition of _less than or equal_ that matches the axioms. -/
def le (a b : ℤ) : Prop := ∃ k : ℕ, b ≃ a + coe k

local instance leOp : LE ℤ := { le := le }

/-- Definition of _less than_ that matches the axioms. -/
def lt (a b : ℤ) : Prop := a ≤ b ∧ a ≄ b

@[implicit_reducible]
def order : Order ℤ := {
  leOp := leOp
  le_iff_add_nat := Iff.intro id id
  ltOp := { lt := lt }
  lt_iff_le_neqv := Iff.intro id id
}

end Lean4Axiomatic.Integer.Impl.Generic

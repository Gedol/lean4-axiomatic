import Lean4Axiomatic.Natural.Addition

/-! # Generic implementation of natural number order relations -/

namespace Lean4Axiomatic.Natural.Impl.Generic

variable {ℕ : Type} [Core ℕ] [Addition ℕ]

def le (n m : ℕ) : Prop := ∃ k : ℕ, n + k ≃ m
local instance le_ex_add : LE ℕ := LE.mk le

def lt (n m : ℕ) : Prop := n ≤ m ∧ n ≄ m

@[implicit_reducible]
def lt_le_neqv : LT ℕ := LT.mk lt

end Lean4Axiomatic.Natural.Impl.Generic

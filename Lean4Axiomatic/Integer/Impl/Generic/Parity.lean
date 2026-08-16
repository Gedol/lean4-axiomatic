import Lean4Axiomatic.Integer.Parity

/-! # Generic implementation of integer parity functions and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Order ℤ]
    [Sign ℤ] [Metric ℤ] [Division ℤ]

local instance parity_ops : Parity.Ops ℤ := {
  Even a := (div_floored a 2).remainder ≃ 0
  Odd a := (div_floored a 2).remainder ≃ 1
  half_floored a := (div_floored a 2).quotient
}

@[implicit_reducible]
def parity_props : Parity.Props ℤ := {
  even_rem := Iff.rfl
  odd_rem := Iff.rfl
  half_floored_eqv := Rel.refl
}

@[implicit_reducible]
def parity : Parity ℤ := {
  toOps := parity_ops
  toProps := parity_props
}

end Lean4Axiomatic.Integer.Impl.Generic


import Lean4Axiomatic.Natural.Exponentiation

/-!
# Generic implementation of natural number exponentiation and properties
-/

namespace Lean4Axiomatic.Natural.Impl.Generic

open Relation.Equivalence (EqvOp)
open Lean4Axiomatic.CA.Monoid (identL identR)

variable
  {ℕ : Type} [Core ℕ] [Induction.{1} ℕ]
  {α : Type} [EqvOp α]
  {binop : α → α → α} {ident : α}
  [m : CA.Monoid.Monoid α binop ident]

/-- Enables the use of `· * ·` syntax. -/
local instance mul_inst {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} [CA.Monoid.Monoid α binop ident] : Mul α := {
  mul := binop
}

local instance ofNatIdent {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} [CA.Monoid.Monoid α binop ident] : OfNat α 1 := {
  ofNat := ident
}

/--
Raise a value to a natural number power.

**Definition intuition**: Performs the correct number of multiplications using
recursion.
-/
def _pow (x : α) (n : ℕ) : α := rec_on n ident (· * x)

local instance exponentiation_ops : Exponentiation.Ops α ℕ := {
  _pow := _pow (binop := binop) (ident := ident)
}

/--
Anything to the zero power is one.

**Property and proof intuition**: This corresponds to the base case in the
recursive definition of `_pow`.
-/
theorem pow_zero {x : α} : x ^ (0:ℕ) ≃ 1 := calc
  _ ≃ x ^ (0:ℕ)         := Rel.refl
  _ = rec_on 0 1 (· * x) := rfl
  _ = 1                  := rec_on_zero

/--
Adding one to the exponent multiplies the result by the base.

**Property and proof intuition**: This corresponds to the recursive case in the
definition of `_pow`.
-/
theorem pow_step {x : α} {n : ℕ} : x ^ step n ≃ x ^ n * x := calc
  _ ≃ x ^ step n                := Rel.refl
  _ = rec_on (step n) 1 (· * x) := rfl
  _ = (rec_on n 1 (· * x)) * x  := rec_on_step
  _ = x ^ n * x                 := rfl

def exponentiation_props : Exponentiation.Props (α := α) binop ident := {
  pow_zero := pow_zero
  pow_step := pow_step
}

def exponentiation : Exponentiation ℕ α binop ident := {
  toOps := exponentiation_ops
  toProps := exponentiation_props
}

end Lean4Axiomatic.Natural.Impl.Generic

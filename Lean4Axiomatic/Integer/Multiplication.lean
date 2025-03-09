import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Addition

/-! # Integer multiplication -/

namespace Lean4Axiomatic.Integer

/-! ## Axioms -/

/--
Definition of multiplication, and properties that it must satisfy.

All other properties of multiplication can be derived from these.

**Named parameters**
- `ℕ`: The natural numbers.
- `ℤ`: The integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
- All other class parameters provide the subset of integer properties necessary
  to define the fields of this class.
-/
class Multiplication
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ]
    where
  /-- Definition of and syntax for multiplication. -/
  mulOp : Mul ℤ

  /--
  Multiplication preserves equality of integers; two equal integers are still
  equal after the same quantity is multiplied with both (on the left or right).
  -/
  mul_substitutive : AA.Substitutive₂ (α := ℤ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)

  /-- Exchanging the operands of multiplication does not change the result. -/
  mul_commutative : AA.Commutative (α := ℤ) (· * ·)

  /-- The grouping of the terms in a product doesn't matter. -/
  mul_associative : AA.Associative (α := ℤ) (· * ·)

  /-- Multiplying an integer by one produces the same integer. -/
  mul_identity : AA.Identity (α := ℤ) ↑(1 : ℕ) (· * ·)

  /--
  Multiplication of a sum by a value is equivalent to summing the
  multiplication of each term by that value.
  -/
  mul_distributive : AA.Distributive (α := ℤ) (· * ·) (· + ·)

  /--
  Multiplying two natural numbers and then converting to an integer gives the
  same result as converting each number to an integer and then multiplying.
  -/
  mul_compatible_from_natural
    : AA.Compatible₂ (α := ℕ) (β := ℤ) (↑·) (· * ·) (· * ·)

attribute [instance] Multiplication.mulOp
attribute [instance] Multiplication.mul_associative
attribute [instance] Multiplication.mul_commutative
attribute [instance] Multiplication.mul_compatible_from_natural
attribute [instance] Multiplication.mul_distributive
attribute [instance] Multiplication.mul_identity
attribute [instance] Multiplication.mul_substitutive

export Multiplication (mulOp)

/-! ## Derived properties -/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ]


def mul_monoid_props : CA.Monoid.Props (α := ℤ) (· * ·) 1 := {
  substL  := AA.substL
  substR  := AA.substR
  assoc   := AA.assoc
  identL  := AA.identL
  identR  := AA.identR
}

/--
Integers with multiplication form a monoid.  This allow us to avoid
reproving basic facts about integers that are true of all monoids.
-/
instance mul_monoid : CA.Monoid.Monoid (α := ℤ) (· * ·) 1 := {
  toProps := mul_monoid_props
}

end Lean4Axiomatic.Integer

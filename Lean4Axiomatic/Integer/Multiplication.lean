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

/--
Non-typeclass version of `mul_substitutive.substitutiveL`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
@[gcongr]
theorem mul_substL {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ * b ≃ a₂ * b := AA.substL

/--
Non-typeclass version of `mul_substitutive.substitutiveR`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
@[gcongr]
theorem mul_substR {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b * a₁ ≃ b * a₂ := AA.substR

/--
Non-typeclass version of `mul_associative.assoc`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem mul_assoc {a b c : ℤ} : (a * b) * c ≃ a * (b * c) := AA.assoc

/--
Non-typeclass version of `mul_commutative.comm`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem mul_comm {a b : ℤ} : a * b ≃ b * a := AA.comm

/--
Non-typeclass version of `mul_identity.identityL`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem mul_identL {a : ℤ} : 1 * a ≃ a := AA.identL

/--
Non-typeclass version of `mul_identity.identityR`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem mul_identR {a : ℤ} : a * 1 ≃ a := AA.identR

/--
Non-typeclass version of `mul_distributive.distribL`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem mul_distribL {a b c : ℤ} : a * (b + c) ≃ a * b + a * c := AA.distribL

/--
Non-typeclass version of `mul_distributive.distribR`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem mul_distribR {a b c : ℤ} : (b + c) * a ≃ b * a + c * a := AA.distribR

end Lean4Axiomatic.Integer

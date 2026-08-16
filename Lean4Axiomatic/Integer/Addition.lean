import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Core

/-! # Integer addition -/

namespace Lean4Axiomatic.Integer

/-! ## Axioms -/

/--
Definition of addition, and properties that it must satisfy.

All other properties of addition can be derived from these.

**Named parameters**
- `ℤ`: The type of integers.

**Class parameters**
- `Core ℤ`: Required to express most properties of addition.
-/
class Addition
    {ℕ : outParam Type} [Natural ℕ] (ℤ : Type) [Core (ℕ := ℕ) ℤ]
    where
  /-- Definition of and syntax for addition. -/
  addOp : Add ℤ

  /--
  Addition preserves equivalence of integers; two equivalent integers are still
  equivalent after the same quantity is added to both (on the left or right).
  -/
  add_substitutive : AA.Substitutive₂ (α := ℤ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)

  /-- Exchanging the operands of an addition does not change the result. -/
  add_commutative : AA.Commutative (α := ℤ) (· + ·)

  /-- The grouping of the terms in a sum doesn't matter. -/
  add_associative : AA.Associative (α := ℤ) (· + ·)

  /-- Adding zero to an integer produces the same integer. -/
  add_identity : AA.Identity (α := ℤ) 0 (· + ·)

  /--
  Adding two natural numbers and then converting to an integer gives the same
  result as converting each number to an integer and then adding.
  -/
  add_compatible_from_natural
    : AA.Compatible₂ (α := ℕ) (β := ℤ) (↑·) (· + ·) (· + ·)

attribute [implicit_reducible, instance] Addition.addOp
attribute [instance] Addition.add_associative
attribute [instance] Addition.add_commutative
attribute [instance] Addition.add_compatible_from_natural
attribute [instance] Addition.add_identity
attribute [instance] Addition.add_substitutive

export Addition (addOp)

/-! ## Derived properties -/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition (ℕ := ℕ) ℤ]

/--
Non-typeclass version of `add_substitutive.substitutiveL`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
@[gcongr]
theorem add_substL {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ + b ≃ a₂ + b := AA.substL

/--
Non-typeclass version of `add_substitutive.substitutiveR`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
@[gcongr]
theorem add_substR {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b + a₁ ≃ b + a₂ := AA.substR

/--
Non-typeclass version of `add_associative`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem add_assoc {a b c : ℤ} : (a + b) + c ≃ a + (b + c) := AA.assoc

/--
Non-typeclass version of `add_commutative`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem add_comm {a b : ℤ} : a + b ≃ b + a := AA.comm

/--
Non-typeclass version of `add_identity.identL`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem add_identL {a : ℤ} : 0 + a ≃ a := AA.identL

/--
Non-typeclass version of `add_identity.identR`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem add_identR {a : ℤ} : a + 0 ≃ a := AA.identR

/--
Non-typeclass version of `add_compatible_from_natural.compat₂`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem add_compat_nat {n m : ℕ} : ((n + m : ℕ):ℤ) ≃ (n:ℤ) + (m:ℤ) := AA.compat₂

/--
In the integers, one plus one is two.

**Proof intuition**: Delegate to natural numbers.
-/
theorem add_one_one : (1:ℤ) + 1 ≃ 2 := calc
  _ ≃ (1:ℤ) + 1             := Rel.refl
  _ ≃ ((1:ℕ):ℤ) + ((1:ℕ):ℤ) := Rel.refl
  _ ≃ ((1 + 1 : ℕ):ℤ)       := Rel.symm AA.compat₂
  _ ≃ ((2:ℕ):ℤ)             := by srw [Natural.add_one_one]
  _ ≃ 2                     := Rel.refl

end Lean4Axiomatic.Integer

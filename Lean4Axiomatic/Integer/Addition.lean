import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Core

namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer addition
-/

/--
Definition of addition, and properties that it must satisfy.

All other properties of addition can be derived from these.

**Named parameters**
- `ℤ`: The type of integers.

**Class parameters**
- `Equality ℤ`: Required to express most properties of addition.
-/
class Addition.Base
    (ℕ : Type) [Natural ℕ] (ℤ : Type) [Equality ℤ] [Conversion ℕ ℤ]
    :=
  /-- Definition of and syntax for addition. -/
  addOp : Add ℤ

  /--
  Addition preserves equality of integers; two equal integers are still equal
  after the same quantity is added to both (on the left or right).
  -/
  add_substitutive : AA.Substitutive₂ (α := ℤ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)

  /-- Exchanging the operands of an addition does not change the result. -/
  add_commutative : AA.Commutative (α := ℤ) (· + ·)

  /-- The grouping of the terms in a sum doesn't matter. -/
  add_associative : AA.Associative (α := ℤ) (· + ·)

  /-- Adding zero to an integer produces the same integer. -/
  add_identity : AA.Identity (α := ℤ) ↑(0 : ℕ) (· + ·)

attribute [instance] Addition.Base.addOp
attribute [instance] Addition.Base.add_identity

namespace Addition
export Addition.Base (addOp)
end Addition

end Lean4Axiomatic.Integer

import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Addition
import Lean4Axiomatic.Integer.Core

namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer negation
-/

/--
Definition of negation, and properties that it must satisfy.

All other properties of negation can be derived from these.

**Named parameters**
- `ℤ`: The type of integers.

**Class parameters**
- `Equality ℤ`: Required to express most properties of negation.
-/
class Negation.Base
    (ℕ : Type) [Natural ℕ]
    (ℤ : Type) [Equality ℤ] [Conversion ℕ ℤ] [Addition.Base ℕ ℤ]
    :=
  /-- Definition of and syntax for negation. -/
  negOp : Neg ℤ

  /--
  Negation preserves equality of integers; two equal integers are still equal
  after both are negated.
  -/
  neg_substitutive : AA.Substitutive₁ (α := ℤ) (-·) (· ≃ ·) (· ≃ ·)

  /-- Every integer is either positive, negative, or zero. -/
  trichotomy {a : ℤ}
    : AA.ExactlyOneOfThree
      (a ≃ ↑(0 : ℕ))
      (∃ (n : ℕ), Natural.Positive n ∧ a ≃ n)
      (∃ (n : ℕ), Natural.Positive n ∧ a ≃ -n)

  /-- An integer added to its negation is always zero. -/
  neg_inverse : AA.Inverse (α := ℤ) (-·) (· + ·)

attribute [instance] Negation.Base.negOp
attribute [instance] Negation.Base.neg_substitutive

namespace Negation
export Negation.Base (negOp)
end Negation

end Lean4Axiomatic.Integer
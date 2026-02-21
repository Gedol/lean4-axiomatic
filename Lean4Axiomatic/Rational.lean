import Lean4Axiomatic.Rational.Exponentiation
import Lean4Axiomatic.Rational.Induction
import Lean4Axiomatic.Rational.Metric

/-! # Rational numbers -/

namespace Lean4Axiomatic

/-! ## Axioms -/

/--
The class of [rational numbers](https://en.wikipedia.org/wiki/Rational_number).

Provides fundamental operations and properties that any type implementing the
rational numbers must have. They are broken out into subclasses to keep them
better organized.
-/
class Rational
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] (ℚ : Type)
    where
  toCore : Rational.Core (ℤ := ℤ) ℚ
  toAddition : Rational.Addition ℚ
  toMultiplication : Rational.Multiplication ℚ
  toNaturalExponentiation :
    Natural.Exponentiation ℕ (α := ℚ) (mul := (· * ·)) (ident := (1 : ℚ))
  toNegation : Rational.Negation ℚ
  toSubtraction : Rational.Subtraction ℚ
  toReciprocation : Rational.Reciprocation ℚ
  toDivision : Rational.Division ℚ
  toInduction : Rational.Induction ℚ
  toSign : Rational.Sign ℚ
  toIntegerExponentiation : Rational.Exponentiation ℚ
  toOrder : Rational.Order ℚ
  toMinMax : Rational.MinMax ℚ
  toMetric : Rational.Metric ℚ

attribute [instance] Rational.toAddition
attribute [instance] Rational.toCore
attribute [instance] Rational.toDivision
attribute [instance] Rational.toInduction
attribute [instance] Rational.toIntegerExponentiation
attribute [instance] Rational.toMetric
attribute [instance] Rational.toMinMax
attribute [instance] Rational.toMultiplication
attribute [instance] Rational.toNaturalExponentiation
attribute [instance] Rational.toNegation
attribute [instance] Rational.toOrder
attribute [instance] Rational.toReciprocation
attribute [instance] Rational.toSign
attribute [instance] Rational.toSubtraction

end Lean4Axiomatic

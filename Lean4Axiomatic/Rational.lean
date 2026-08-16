import Lean4Axiomatic.Rational.Exponentiation
import Lean4Axiomatic.Rational.FloorCeil
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
  toInduction₀ : Rational.Induction.{0} ℚ
  toInduction₁ : Rational.Induction.{1} ℚ
  toSign : Rational.Sign ℚ
  toIntegerExponentiation : Rational.Exponentiation ℚ
  toOrder : Rational.Order ℚ
  toMinMax : Rational.MinMax ℚ
  toMetric : Rational.Metric ℚ
  toFloorCeil : Rational.FloorCeil ℚ

attribute [implicit_reducible, instance] Rational.toAddition
attribute [implicit_reducible, instance] Rational.toCore
attribute [implicit_reducible, instance] Rational.toDivision
attribute [implicit_reducible, instance] Rational.toFloorCeil
attribute [implicit_reducible, instance] Rational.toInduction₀
attribute [implicit_reducible, instance] Rational.toInduction₁
attribute [implicit_reducible, instance] Rational.toIntegerExponentiation
attribute [implicit_reducible, instance] Rational.toMetric
attribute [implicit_reducible, instance] Rational.toMinMax
attribute [implicit_reducible, instance] Rational.toMultiplication
attribute [implicit_reducible, instance] Rational.toNaturalExponentiation
attribute [implicit_reducible, instance] Rational.toNegation
attribute [implicit_reducible, instance] Rational.toOrder
attribute [implicit_reducible, instance] Rational.toReciprocation
attribute [implicit_reducible, instance] Rational.toSign
attribute [implicit_reducible, instance] Rational.toSubtraction

end Lean4Axiomatic

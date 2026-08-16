import Lean4Axiomatic.Natural.Division
import Lean4Axiomatic.Natural.Exponentiation

namespace Lean4Axiomatic

open Natural

/--
The class of [natural numbers](https://en.wikipedia.org/wiki/Natural_number).

The fields of this class express many natural number properties. Any type `α`
for which an instance of `Natural α` exists must obey all of them. However,
most of the properties can be derived from a few essential ones (e.g. the
[Peano axioms](https://en.wikipedia.org/wiki/Peano_axioms)), reducing the work
required to construct an instance.

**Named parameters**
- `ℕ`: a type that obeys all of the properties provided by this class.
-/
class Natural (ℕ : semiOutParam Type) where
  toCore : Core ℕ
  toInduction₀ : Induction.{0} ℕ
  toInduction₁ : Induction.{1} ℕ
  toAddition : Addition ℕ
  toSign : Sign ℕ
  toOrder : Order ℕ
  toCompare : Compare ℕ
  toMultiplication : Multiplication ℕ
  toExponentiation : Exponentiation ℕ ℕ (· * ·) 1 (minst := nat_mul_monoid)
  toDivision : Division ℕ

attribute [implicit_reducible, instance] Natural.toAddition
attribute [implicit_reducible, instance] Natural.toCompare
attribute [implicit_reducible, instance] Natural.toCore
attribute [implicit_reducible, instance] Natural.toDivision
attribute [implicit_reducible, instance] Natural.toExponentiation
attribute [implicit_reducible, instance] Natural.toInduction₀
attribute [implicit_reducible, instance] Natural.toInduction₁
attribute [implicit_reducible, instance] Natural.toMultiplication
attribute [implicit_reducible, instance] Natural.toOrder
attribute [implicit_reducible, instance] Natural.toSign

end Lean4Axiomatic

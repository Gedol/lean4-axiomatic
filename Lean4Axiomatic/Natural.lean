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
  toInduction : Induction.{0} ℕ
  toAddition : Addition ℕ
  toSign : Sign ℕ
  toOrder : Order ℕ
  toCompare : Compare ℕ
  toMultiplication : Multiplication ℕ
  toExponentiation : Exponentiation ℕ ℕ (mul := (· * ·)) (ident := 1) (minst := mul_monoid)
  toDivision : Division ℕ

attribute [instance] Natural.toAddition
attribute [instance] Natural.toCompare
attribute [instance] Natural.toCore
attribute [instance] Natural.toDivision
attribute [instance] Natural.toExponentiation
attribute [instance] Natural.toInduction
attribute [instance] Natural.toMultiplication
attribute [instance] Natural.toOrder
attribute [instance] Natural.toSign

end Lean4Axiomatic

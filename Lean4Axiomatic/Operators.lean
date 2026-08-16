/-!
# Operator syntax

Defines classes and syntax for mathematical operators. The goal is to make the
operators general enough to be useful but specific enough to be understandable.
-/

namespace Operators

/--
Provides the `· ≃ ·` operator.

Intended to be used for equality or equivalence relations.
-/
class TildeDash (α : Sort u) where
  /-- The `· ≃ ·` operator. -/
  tildeDash : α → α → Prop

export TildeDash (tildeDash)

infix:50 " ≃ " => tildeDash

/-- The `· ≄ ·` operator, the negation of `TildeDash.tildeDash`. -/
abbrev tildeDashNot {α : Sort u} [TildeDash α] (x y : α) : Prop := ¬ (x ≃ y)

infix:50 " ≄ " => tildeDashNot

/--
Provides the `· ≃? ·` operator.

Explicitly defined to be a decision prodcedure, for a relation intended to be
equality or equivalence.
-/
class TildeDashQuestion {α : Sort u} (β : α → α → Prop) where
  /-- The `· ≃? ·` operator, a decision procedure for `β`. -/
  tildeDashQuestion : DecidableRel β

export TildeDashQuestion (tildeDashQuestion)

attribute [implicit_reducible, instance] tildeDashQuestion

infix:50 " ≃? " => tildeDashQuestion

/-- The `· ≮ ·` operator, the negation of `LT.lt`. -/
def ltNot {α : Type u} [LT α] (x y : α) : Prop := ¬ (x < y)

infix:50 " ≮ " => ltNot

/-- The `· ≯ ·` operator, the negation of `· > ·`. -/
def gtNot {α : Type u} [LT α] (x y : α) : Prop := ¬ (x > y)

infix:50 " ≯ " => gtNot

/--
Provides the `· ÷ ·` operator.

The result type is dependent on the input values for increased generality.
-/
class DivisionSign {α : Type} (Result : outParam (α → α → Type)) where
  /-- Implementation of a division operation. -/
  divisionSign (x y : α) : Result x y

export DivisionSign (divisionSign)

infix:50 " ÷ " => divisionSign

end Operators

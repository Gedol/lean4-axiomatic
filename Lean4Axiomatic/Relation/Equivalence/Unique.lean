import Lean4Axiomatic.Relation.Equivalence.Core

namespace Lean4Axiomatic.Relation.Equivalence

/--
Demonstrates that a unique value (up to equivalence) satisfies a predicate.
-/
structure Unique {α : Sort u} [EqvOp α] (P : α → Prop) : Sort (u+1) where
  /-- The unique value. -/
  val : α

  /-- The unique value satisfies the predicate. -/
  atLeastOne : P val

  /-- All values satisfying the predicate are equivalent. -/
  atMostOne : {x₁ x₂ : α} → P x₁ → P x₂ → x₁ ≃ x₂

end Lean4Axiomatic.Relation.Equivalence

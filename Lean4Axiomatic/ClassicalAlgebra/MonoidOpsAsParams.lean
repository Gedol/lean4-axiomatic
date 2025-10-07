import Lean4Axiomatic.AbstractAlgebra

namespace Lean4Axiomatic.CA.Monoid

open Relation.Equivalence (EqvOp)

/-!
An attempt at formalizing traditional algebraic structures
such as groups and rings.

Here we introduce a Monoid using a multiplicative notation.

Note that we only require a binary operation that is associative and
has identities.  For example, the natural numbers with the addition
operator is a monoid.
-/

/-! ### Definitions -/

/-- Properties of Monoid. -/
class Props (α : Type) [EqvOp α]
    (binop : semiOutParam (α → α → α)) (ident : outParam α) where
  substL {x y z : α} : x ≃ y → binop x z ≃ binop  y z
  substR {x y z : α} : x ≃ y → binop z x ≃ binop z y
  assoc {x y z : α} : binop (binop x y) z ≃ binop x (binop y z)
  identL {x : α} : binop ident x ≃ x
  identR {x : α} : binop x ident ≃ x
export Props (substL substR assoc identL identR)

set_option linter.dupNamespace false in
/-- All axioms for generic types to form a Monoid. -/
class Monoid (α : Type) [EqvOp α] (binop : semiOutParam (α → α → α)) (ident : outParam α) where
  toProps : Monoid.Props α binop ident


class testOfMonoid
  (α : semiOutParam Type) [EqvOp α] (mul : semiOutParam (α → α → α)) (ident : outParam α) [Monoid α mul ident] where
  tempField : α

attribute [instance] Monoid.toProps


/-- Enables the use of the `· * ·` operator for binop. -/
local instance monoid_mul_op_inst {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} [Monoid α binop ident] : Mul α := {
  mul := binop
}

/-! ### Properties -/

variable {α : Type} [EqvOp α] {binop : α → α → α} {ident : outParam α} [m : Monoid α binop ident]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
scoped instance monoid_subst_inst
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => m.toProps.substL }
  substitutiveR := { subst₂ := λ (_ : True) => m.toProps.substR }
}

/-- Enables the use of AA.assoc. -/
scoped instance monoid_assoc_inst : AA.Associative (α := α) (· * ·) := {
    assoc := assoc
}

/--
  There is only one element, namely the identity ident, such that
  ident * y ≃ ident for all elements y.
-/
theorem identity_unique
    {x : α} (x_is_left_ident : ((y : α) → (x * y) ≃ y)) : x ≃ ident := calc
  _ ≃  x        := Rel.refl
  _ ≃ x * ident := Rel.symm identR
  _ ≃ ident     := x_is_left_ident ident

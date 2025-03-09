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

/--
Operations for Monoid, namely the binary operation and identity element.
-/
class Ops (α : Type) where
  binop : α → α → α
  ident : α
export Ops (ident binop)

/-- Enables the use of the `· * ·` operator for binop. -/
local instance monoid_mul_op_inst {α : Type} [Monoid.Ops α] : Mul α := {
  mul := Ops.binop
}

/-- Properties of Monoid. -/
class Props (α : Type) [EqvOp α] [Ops α] where
  substL {x y z : α} : x ≃ y → x * z ≃ y * z
  substR {x y z : α} : x ≃ y → z * x ≃ z * y
  assoc {x y z : α} : (x * y) * z ≃ x * (y * z)
  identL {x : α} : ident * x ≃ x
  identR {x : α} : x * ident ≃ x
export Props (substL substR assoc identL identR)

attribute [gcongr] substL substR

set_option linter.dupNamespace false in
/-- All axioms for generic types to form a Monoid. -/
class oldMonoid (α : Type) [EqvOp α] where
  toOps : Monoid.Ops α
  toProps : Monoid.Props α

attribute [instance] oldMonoid.toOps
attribute [instance] oldMonoid.toProps


/-! ### Properties -/

variable {α : Type} [EqvOp α] [m : oldMonoid α]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
scoped instance monoid_subst_inst
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => substL }
  substitutiveR := { subst₂ := λ (_ : True) => substR }
}

/-- Enables the use of AA.assoc. -/
scoped instance monoid_assoc_inst : AA.Associative (α := α) (· * ·) := {
    assoc := assoc
}

/--
  There is only one element, namely the identity ident, such that
  ident * y ≃ ident for all elements y.
-/
theorem mul_identity_unique
    {x : α} (x_is_left_ident : ((y : α) → (x * y) ≃ y)) : x ≃ ident := calc
  _ ≃  x        := Rel.refl
  _ ≃ x * ident := Rel.symm identR
  _ ≃ ident     := x_is_left_ident ident

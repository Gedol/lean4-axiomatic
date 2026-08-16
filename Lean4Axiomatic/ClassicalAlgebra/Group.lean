import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid

namespace Lean4Axiomatic.CA.Group

open Relation.Equivalence (EqvOp)


/-!
A formalization of Group using multiplicative notation.

The binary operation, identity, and inverse function are passed as parameters.
-/

/-! ### Definitions -/

/-- Properties of Group. -/
class Props (α : Type) [EqvOp α]
    (binop : semiOutParam (α → α → α)) (ident : outParam α)
    (inverse : semiOutParam (α → α)) where
  substL {x y z : α} : x ≃ y → binop x z ≃ binop y z
  substR {x y z : α} : x ≃ y → binop z x ≃ binop z y
  assoc {x y z : α} : binop (binop x y) z ≃ binop x (binop y z)
  identL {x : α} : binop ident x ≃ x
  identR {x : α} : binop x ident ≃ x
  inverseL (x : α) : binop (inverse x) x ≃ ident
  inverseR (x : α) : binop x (inverse x) ≃ ident

export Props (
  substL substR assoc identL identR inverseL inverseR
)

set_option linter.dupNamespace false in
/-- All axioms for generic types to form a Group. -/
class Group (α : Type) [EqvOp α]
    (binop : semiOutParam (α → α → α)) (ident : outParam α)
    (inverse : semiOutParam (α → α)) where
  toProps : Group.Props α binop ident inverse

attribute [implicit_reducible, instance] Group.toProps

/-- Enables the use of the `· * ·` operator for binop. -/
local instance group_mul_op_inst
    {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} {inverse : α → α}
    [Group α binop ident inverse]
    : Mul α := {
  mul := binop
}

/-- Enables the use of the `·⁻¹` operator for the inverse. -/
local instance group_inv_op_inst
    {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} {inverse : α → α}
    [Group α binop ident inverse]
    : Inv α := {
  inv := inverse
}

/-! ### Properties -/

variable {α : Type} [EqvOp α]
    {binop : α → α → α} {ident : α} {inverse : α → α}
    [g : Group α binop ident inverse]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
local instance group_subst_inst
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => g.toProps.substL }
  substitutiveR := { subst₂ := λ (_ : True) => g.toProps.substR }
}

/--
You May perform cancellation of an element x, and conclude from
x * y ≃ x * z that y ≃ z.
-/
theorem group_cancelL
    {x y z : α} : x * y ≃ x * z → y ≃ z := by
  intro (_ : x * y ≃ x * z)
  show y ≃ z
  calc
    _ ≃ y               := Rel.refl
    _ ≃ ident * y       := Rel.symm g.toProps.identL
    _ ≃ ((x⁻¹) * x) * y := g.toProps.substL (Rel.symm (g.toProps.inverseL x))
    _ ≃ (x⁻¹) * (x * y) := g.toProps.assoc
    _ ≃ (x⁻¹) * (x * z) := g.toProps.substR ‹x * y ≃ x * z›
    _ ≃ (x⁻¹ * x) * z   := Rel.symm g.toProps.assoc
    _ ≃ ident * z       := g.toProps.substL (g.toProps.inverseL x)
    _ ≃ z               := g.toProps.identL


/--
Demonstrates that any group is also a monoid.
-/
instance monoid_from_group : CA.Monoid.Monoid α binop ident := {
  toProps := {
    substL    := g.toProps.substL
    substR    := g.toProps.substR
    assoc     := g.toProps.assoc
    identL    := g.toProps.identL
    identR    := g.toProps.identR
  }
}

/--
  Demonstration of using results of monoids for groups.  Since a group is a
  monoid, everything true about a monoid is true for a group.
-/
example {x : α} (x_is_left_ident : ((y : α) → (x * y) ≃ y)) : x ≃ ident :=
  Lean4Axiomatic.CA.Monoid.identity_unique (binop := binop) x_is_left_ident

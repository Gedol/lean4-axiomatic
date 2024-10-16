import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid

namespace Lean4Axiomatic.CA.Group

open Relation.Equivalence (EqvOp)


/-!
A formalization of Group using multiplicative notation.
-/

/-! ### Definitions -/

/--
Operations for Group, namely the binary operation, identity element, and
existence of inverses.
-/
class Ops (α : Type) :=
  binop : α → α → α
  ident : α
  inverse : (x : α) → α

export Ops (ident)

/-- Enables the use of the `· * ·` operator for binop. -/
local instance {α : Type} [Ops α] : Mul α := {
  mul := Group.Ops.binop
}

/-- Enables the use of the `·⁻¹` operator for taking the inverse. -/
postfix:120 "⁻¹" => Group.Ops.inverse


/-- Properties of Group. -/
class Props (α : Type) [EqvOp α] [Ops α] :=
  substL {x y z : α} : x ≃ y → x * z ≃ y * z
  substR {x y z : α} : x ≃ y → z * x ≃ z * y
  assoc {x y z : α} : (x * y) * z ≃ x * (y * z)
  identL {x : α} : ident * x ≃ x
  identR {x : α} : x * ident ≃ x
  inverseL (x : α) : (x⁻¹) * x ≃ ident
  inverseR (x : α) : x * (x⁻¹) ≃ ident

export Props (
  substL substR assoc identL identR inverseL inverseR
)

/-- All axioms for generic types to form a Group. -/
class Group (α : Type) [EqvOp α] :=
  toOps : Group.Ops α
  toProps : Group.Props α

attribute [instance] Group.toOps
attribute [instance] Group.toProps

/-! ### Properties -/

variable {α : Type} [EqvOp α] [g : Group α]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
local instance group_subst_inst
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => substL }
  substitutiveR := { subst₂ := λ (_ : True) => substR }
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
    _ ≃ ident * y       := Rel.symm identL
    _ ≃ ((x⁻¹) * x) * y := substL (Rel.symm (inverseL x))
    _ ≃ (x⁻¹) * (x * y) := assoc
    _ ≃ (x⁻¹) * (x * z) := substR ‹x * y ≃ x * z›
    _ ≃ (x⁻¹ * x) * z   := Rel.symm assoc
    _ ≃ ident * z       := substL (inverseL x)
    _ ≃ z               := identL


local instance monoid_from_group_ops :  CA.Monoid.Ops α := {
  binop := (· * ·)
  ident := ident
}

/--
Demonstrates that any group is also a monoid.
-/
instance monoid_from_group : CA.Monoid.Monoid (α := α) := {
  toOps := monoid_from_group_ops
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
  Lean4Axiomatic.CA.Monoid.mul_identity_unique x_is_left_ident

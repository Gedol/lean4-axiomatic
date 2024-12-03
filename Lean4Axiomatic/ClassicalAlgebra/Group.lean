import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid

namespace Lean4Axiomatic.CA.Group

open Relation.Equivalence (EqvOp)


/-!
A formalization of Group using multiplicative notation.
-/

/-! ### Definitions -/
/--
Operations for Group, namely the inverse function that enforces existence
of inverses.

Note that the binary operation and identity element functions will be passed
into the structure Props explicity.  This allows callers to more naturally
create instances of different groups on the same underlying type with different
operations (e.g. Rationals with addtion vs Rationals with mulitplication).
-/
class Ops (α : Type) :=
  inverse : (x : α) → α

export Ops (inverse)

/-- Enables the use of the `·⁻¹` operator for taking the inverse. -/
postfix:120 "⁻¹" => Group.Ops.inverse

/-- Properties of Group.
  binop is the binary operator of the group.  It is a semiOutParam because we
  require all callers of Group to supply it, but there may be multiple Groups
  on the same type with different values of binop.
  ident is an outParam as callers it's required and must be unique.
-/
class Props
    (α : Type) [EqvOp α]
    (binop : semiOutParam (α → α → α)) (ident : outParam α) [Ops α]
    :=
  substL {x y z : α} : x ≃ y → binop x z ≃ binop y z
  substR {x y z : α} : x ≃ y → binop z x ≃ binop z y
  assoc {x y z : α} : binop (binop x y) z ≃ binop x (binop y z)
  identL {x : α} : binop ident x ≃ x
  identR {x : α} : binop x ident ≃ x
  inverseL (x : α) : binop (inverse x) x ≃ ident
  inverseR (x : α) : binop x (inverse x) ≃ ident

export Props (
  inverseL inverseR assoc identL identR substL substR
)

/-- All axioms for generic types to form a Group. -/
class Group
    (α : Type) [eqv : EqvOp α]
    (binop : semiOutParam (α → α → α)) (ident : outParam α)
    :=
  toOps : Group.Ops α
  toProps : Group.Props α binop ident

attribute [instance] Group.toOps
attribute [instance] Group.toProps

/-- Enables the use of the `· * ·` operator for binop. -/
local instance group_mul_op_inst
    {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} [Group α binop ident]
    : Mul α := {
  mul := binop
}

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
local instance group_subst_inst
    {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} [Group α binop ident]
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => substL }
  substitutiveR := { subst₂ := λ (_ : True) => substR }
}

/-! ### Properties -/

variable {α : Type} [EqvOp α] {binop : α → α → α} {ident : α}
  [g : Group α binop ident]

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

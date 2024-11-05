import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid

namespace Lean4Axiomatic.CA.Group2

open Relation.Equivalence (EqvOp)


/-!
A formalization of Group using multiplicative notation.

Experimental approach 2: make binop, ident parameters
-/

/-! ### Definitions -/
/--
Operations for Group, namely the binary operation, identity element, and
existence of inverses.
-/
class Ops (α : Type) :=
  inverse : (x : α) → α

export Ops (inverse)

postfix:120 "⁻¹" => Group2.Ops.inverse

/-- Properties of Group.
For testing purposes just a subset of what we'd really have.
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
class Group2
    (α : Type) [eqv : EqvOp α]
    (binop : semiOutParam (α → α → α)) (ident : outParam α)
    :=
  toOps : Group2.Ops α
  toProps : Group2.Props α binop ident

attribute [instance] Group2.toOps
attribute [instance] Group2.toProps

local instance group_mul_op_inst
    {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} [Group2 α binop ident]
    : Mul α := {
  mul := binop
}

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
local instance group_subst_inst
    {α : Type} [EqvOp α] {binop : α → α → α} {ident : α} [Group2 α binop ident]
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => substL }
  substitutiveR := { subst₂ := λ (_ : True) => substR }
}

variable {α : Type} [EqvOp α] {binop : α → α → α} {ident : α}
  [g : Group2 α binop ident]


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

import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid

namespace Lean4Axiomatic.CA.Group2

open Relation.Equivalence (EqvOp)


/-!
A formalization of Group using multiplicative notation.

Experimental approach 2: make binop, ident parameters AND
explicitly have [Mul α] as a parameter so we can use the '*' notation
in this file.


Note : I could not get monoid_from_group below to compile below, so it's commented out.

Furthermore requiring the callers to pass in Mul and Add instances may cause problems.

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


/-- Properties of Group. -/
class Props (α : Type) [EqvOp α] [Ops α] [Mul α] (ident : α) :=
  substL {x y z : α} : x ≃ y → x * z ≃ y * z
  substR {x y z : α} : x ≃ y → z * x ≃ z * y
  assoc {x y z : α} : (x * y) * z ≃ x * (y * z)
  identL {x : α} : ident * x ≃ x
  identR {x : α} : x * ident ≃ x
  inverseL (x : α) : (x ⁻¹) * x ≃ ident
  inverseR (x : α) : x * (x ⁻¹) ≃ ident

export Props (
  substL substR assoc identL identR inverseL inverseR
)

/-- All axioms for generic types to form a Group. -/
class Group2 (α : Type) [eqv : EqvOp α] [ma : Mul α] (ident : outParam α) :=
  toOps : Group2.Ops α
  toProps : Group2.Props α ident


attribute [instance] Group2.toOps
attribute [instance] Group2.toProps

/-! ### Properties -/

variable {α : Type} [EqvOp α] [Mul α] (ident : α) [g : Group2 α ident]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
local instance group_subst_inst
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => substL ident}
  substitutiveR := { subst₂ := λ (_ : True) => substR ident}
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
    _ ≃ ((x⁻¹) * x) * y := (substL ident) (Rel.symm (inverseL x))
    _ ≃ (x⁻¹) * (x * y) := (assoc ident)
    _ ≃ (x⁻¹) * (x * z) := (substR ident) ‹x * y ≃ x * z›
    _ ≃ (x⁻¹ * x) * z   := Rel.symm (assoc ident)
    _ ≃ ident * z       := (substL ident) (inverseL x)
    _ ≃ z               := identL


local instance monoid_from_group_ops : CA.Monoid.Ops α := {
  binop := (· * ·)
  ident := ident
}

/-
Demonstrates that any group is also a monoid.
-/
/- instance monoid_from_group : CA.Monoid.Monoid (α := α) := {
  toOps := monoid_from_group_ops ident
  toProps := {   -- ←← Error here, failed to synthesize Monoid.Ops α
    substL    := g.toProps.substL
    substR    := g.toProps.substR
    assoc     := g.toProps.assoc
    identL    := g.toProps.identL
    identR    := g.toProps.identR
  }
} -/

/-
  Demonstration of using results of monoids for groups.  Since a group is a
  monoid, everything true about a monoid is true for a group.
-/
/- example {x : α} (x_is_left_ident : ((y : α) → (x * y) ≃ y)) : x ≃ ident :=
  Lean4Axiomatic.CA.Monoid.mul_identity_unique x_is_left_ident -/

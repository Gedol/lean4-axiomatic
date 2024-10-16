import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid

namespace Lean4Axiomatic.CA.Group2

open Relation.Equivalence (EqvOp)


/-!
A formalization of Group using multiplicative notation.

Experimental approach 2: make binop, ident parameters

Problem compiling line below:
attribute [instance] Group2.toOps

maybe that's ok.

Also I do not know how to define a Mul instance so that instead of writing
binop a b
we write
a * b

when binop is always passed in a param.

}

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
class Props (α : Type) [EqvOp α] [Ops α]
  (binop : α → α → α) (ident : α) :=
  substL {x y z : α} : x ≃ y → binop x z ≃ binop y z
  inverseL (x : α) : binop (x ⁻¹) x ≃ ident

export Props (
  substL inverseL
)

/-- All axioms for generic types to form a Group. -/
class Group2 (α : Type) [eqv : EqvOp α]
    (binop : outParam α → α → α)  (ident : outParam α) :=
  toOps : Group2.Ops α
  toProps : Group2.Props α binop ident


/-
cannot find synthesization order for instance @Group2.toOps with type
  {α : Type} →
    [eqv : EqvOp α] → (binop : outParam α → α → α) → {ident : outParam α} → [self : Group2 α binop ident] → Ops α
all remaining arguments have metavariables:
  @Group2 α eqv ?binop ?ident
-/
/-
attribute [instance] Group2.toOps  -- ← Error here "cannot find synthesization
attribute [instance] Group2.toProps
-/


variable {α : Type} [EqvOp α] (binop : α → α → α) (ident : outParam α)
  [g : Group2 α binop ident]


local instance group_mul_op_inst [Ops α] : Mul α := {
  mul := binop
}

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

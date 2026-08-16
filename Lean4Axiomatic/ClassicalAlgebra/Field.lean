import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Ring
import Lean4Axiomatic.Logic

namespace Lean4Axiomatic.CA.Field

open Logic (AP)
open Relation.Equivalence (EqvOp)

/-!
A formalization of Fields.

A field is a commutative ring in which every element apart from the additive
identity has a multiplicative inverse. As in Ring.lean, the binary operations
are passed in as parameters rather than being fields in the structure Ops.
-/

/-! ### Definitions -/

variable (α : Type) [EqvOp α]

/--
Operations for Field beyond those of Ring, i.e. the multiplicative inverse.

The inverse is only defined for values apart from the additive identity.
-/
class Ops (add_ident : outParam α) where
  mult_inverse : (x : α) → [AP (x ≄ add_ident)] → α
export Ops (mult_inverse)

/-- Enables the use of the `·⁻¹` operator for taking the multiplicative inverse. -/
postfix:120 "⁻¹" => Ops.mult_inverse

/-- Properties of Field, beyond those of Ring. -/
class Props (α : Type) [EqvOp α]
  (binop_add : semiOutParam (α → α → α)) (add_ident : outParam α)
  (binop_mult : semiOutParam (α → α → α)) (mult_ident : outParam α)
  [Ops α add_ident] where
  -- Multiplication is commutative
  m_comm {x y : α} : binop_mult x y ≃ binop_mult y x
  -- α - {0} with * is a group
  m_inverseL (x : α) [AP (x ≄ add_ident)] : binop_mult (x⁻¹) x ≃ mult_ident
  m_inverseR (x : α) [AP (x ≄ add_ident)] : binop_mult x (x⁻¹) ≃ mult_ident
  -- The identities are distinct, i.e. a field has at least two elements
  ident_split : mult_ident ≄ add_ident

export Props (m_comm m_inverseL m_inverseR ident_split)

set_option linter.dupNamespace false in
/-- All axioms for generic types to form a Field. -/
class Field (α : Type) [EqvOp α]
  (binop_add : semiOutParam (α → α → α)) (add_ident : outParam α)
  (binop_mult : semiOutParam (α → α → α)) (mult_ident : outParam α)
  where
  toRing : Ring.Ring α binop_add add_ident binop_mult mult_ident
  toOps : Field.Ops α add_ident
  toProps : Field.Props α binop_add add_ident binop_mult mult_ident

attribute [implicit_reducible, instance] Field.toRing
attribute [implicit_reducible, instance] Field.toOps
attribute [instance] Field.toProps

/-- Enables the use of the `· * ·` operator for binop_mult -/
local instance field_mul_op_inst
  {α : Type} [EqvOp α] {binop_add : α → α → α} {add_ident : α}
  {binop_mult : α → α → α} {mult_ident : α}
  [Field α binop_add add_ident binop_mult mult_ident]
  : Mul α := {
  mul := binop_mult
}

/-- Enables the use of the `· + ·` operator for binop_add -/
local instance field_add_op_inst
  {α : Type} [EqvOp α] {binop_add : α → α → α} {add_ident : α}
  {binop_mult : α → α → α} {mult_ident : α}
  [Field α binop_add add_ident binop_mult mult_ident]
  : Add α := {
  add := binop_add
}

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
local instance field_subst_inst_mult
  {α : Type} [EqvOp α] {binop_add : α → α → α} {add_ident : α}
  {binop_mult : α → α → α} {mult_ident : α}
  [Field α binop_add add_ident binop_mult mult_ident]
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => Ring.m_substL (binop_add := binop_add) (binop_mult := binop_mult) }
  substitutiveR := { subst₂ := λ (_ : True) => Ring.m_substR (binop_add := binop_add) (binop_mult := binop_mult) }
}

/-! ### Properties -/

variable {α : Type} [EqvOp α]
 {binop_add : α → α → α} {add_ident : α}
 {binop_mult : α → α → α} {mult_ident : α}
 [field_inst : Field α binop_add add_ident binop_mult mult_ident]

/- The `OfNat` instances from Ring.lean apply, via `Field.toRing`. -/
example : (0 : α) ≃ add_ident := Rel.refl
example : (1 : α) ≃ mult_ident := Rel.refl

/--
Multiplication is cancellative on the left for nonzero elements, i.e. if
x * y ≃ x * z and x is nonzero, then y ≃ z.
-/
theorem field_m_cancelL
    {x y z : α} [AP (x ≄ add_ident)] : x * y ≃ x * z → y ≃ z := by
  intro (_ : x * y ≃ x * z)
  show y ≃ z
  calc
    _ ≃ y               := Rel.refl
    _ ≃ mult_ident * y  := Rel.symm field_inst.toRing.toProps.m_identL
    _ ≃ ((x⁻¹) * x) * y := AA.substL (Rel.symm (field_inst.toProps.m_inverseL x))
    _ ≃ (x⁻¹) * (x * y) := field_inst.toRing.toProps.m_assoc
    _ ≃ (x⁻¹) * (x * z) := AA.substR ‹x * y ≃ x * z›
    _ ≃ ((x⁻¹) * x) * z := Rel.symm field_inst.toRing.toProps.m_assoc
    _ ≃ mult_ident * z  := AA.substL (field_inst.toProps.m_inverseL x)
    _ ≃ z               := field_inst.toRing.toProps.m_identL

/--
Multiplication is cancellative on the right for nonzero elements, i.e. if
y * x ≃ z * x and x is nonzero, then y ≃ z.

Follows from left cancellation because multiplication is commutative.
-/
theorem field_m_cancelR
    {x y z : α} [AP (x ≄ add_ident)] : y * x ≃ z * x → y ≃ z := by
  intro (_ : y * x ≃ z * x)
  show y ≃ z
  have : x * y ≃ x * z := calc
    _ ≃ x * y := Rel.refl
    _ ≃ y * x := field_inst.toProps.m_comm
    _ ≃ z * x := ‹y * x ≃ z * x›
    _ ≃ x * z := field_inst.toProps.m_comm
  exact field_m_cancelL ‹x * y ≃ x * z›

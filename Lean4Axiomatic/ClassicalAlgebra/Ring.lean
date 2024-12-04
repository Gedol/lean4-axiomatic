import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Group
import Lean4Axiomatic.Logic

namespace Lean4Axiomatic.CA.Ring

open Relation.Equivalence (EqvOp)
open Logic (AP)

/-!
A formalization of Rings.

First approach, have all operations as fields in the structure Ops, rather than
passing them in as parameters.
-/

/-! ### Definitions -/

variable (α : Type) [EqvOp α]

/--
Operations for Ring, namely the binary operation, identity element, and
existence of inverses.
-/
class Ops :=
  binop_add : α → α → α
  binop_mult : α → α → α
  add_ident : α
  add_inverse : (x : α) → α
  mult_ident : α
  mult_inverse : (x : α) → [AP (x ≄ add_ident)] → α
export Ops (binop_add add_ident add_inverse mult_ident mult_inverse)

/-- Enables the use of the `· * ·` operator for binop. -/
local instance group_mul_op_inst [Ops α] : Mul α := {
  mul := Ring.Ops.binop_mult
}
local instance group_add_op_inst [Ops α] : Add α := {
  add := Ring.Ops.binop_add
}

/-- Enables the use of the `·⁻¹` operator for taking the inverse. -/
postfix:120 "⁻¹" => Ops.mult_inverse

prefix:100 "-" => Ops.add_inverse

/-- Properties of Ring. -/
class Props (α : Type) [EqvOp α] [Ops α] :=
  -- α with + is a group:
  substL {x y z : α} : x ≃ y → x + z ≃ y + z
  substR {x y z : α} : x ≃ y → z + x ≃ z + y
  assoc {x y z : α} : (x + y) + z ≃ x + (y + z)
  identL {x : α} : add_ident + x ≃ x
  identR {x : α} : x + add_ident ≃ x
  inverseL (x : α) : (add_inverse x) + x ≃ add_ident
  inverseR (x : α) : x + (add_inverse x) ≃ ident
  comm {x y : α} : x + y ≃ y + x
  -- α - {0} with * is a group
  m_substL {x y z : α} : x ≃ y → x * z ≃ y * z
  m_substR {x y z : α} : x ≃ y → z * x ≃ z * y
  m_assoc {x y z : α} : (x * y) * z ≃ x * (y * z)
  m_identL {x : α} : mult_ident * x ≃ x
  m_identR {x : α} : x * mult_ ≃ x
  m_inverseL (x : α) [AP (x ≄ add_ident)] : (x⁻¹) * x ≃ mult_ident
  m_inverseR (x : α) [AP (x ≄ add_ident)] : x * (x⁻¹) ≃ mult_ident
  /- ring assoc -/
  assoc1 {x y z : α} : (x + y) * z ≃ (x * z) + (y * z)
  assoc2 {x y z : α} : z * (x + y) ≃ (z * x) + (z * y)

export Props (
  substL substR assoc identL identR inverseL inverseR comm
  m_substL m_substR m_assoc m_identL m_identR m_inverseL m_inverseR
)

/-- All axioms for generic types to form a Group. -/
class Ring (α : Type) [EqvOp α] :=
  toOps : Ring.Ops α
  toProps : Ring.Props α

attribute [instance] Ring.toOps
attribute [instance] Ring.toProps

/-! ### Properties -/

variable {α : Type} [EqvOp α] [r : Ring α]

instance ofNatIdent0 : OfNat α 0 := {
  ofNat := r.toOps.add_ident
}

instance ofNatIdent1 : OfNat α 1 := {
  ofNat := r.toOps.mult_ident
}

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
local instance Ring_subst_inst_add
    : AA.Substitutive₂ (α := α) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => substL }
  substitutiveR := { subst₂ := λ (_ : True) => substR }
}

local instance Ring_subst_inst_mult
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => m_substL }
  substitutiveR := { subst₂ := λ (_ : True) => m_substR }
}

theorem Ring_a_cancelL
    {x y z : α} : x + y ≃ x + z → y ≃ z := by
  intro (_ : x + y ≃ x + z)
  show y ≃ z
  calc
    _ ≃ y               := Rel.refl
    _ ≃ 0 + y       := Rel.symm identL
    _ ≃ ((-x) + x) + y := substL (Rel.symm (inverseL x))
    _ ≃ (-x) + (x + y) := assoc
    _ ≃ (-x) + (x + z) := substR ‹x + y ≃ x + z›
    _ ≃ (-x + x) + z   := Rel.symm assoc
    _ ≃ 0 + z       := substL (inverseL x)
    _ ≃ z               := identL


local instance add_monoid_ops : CA.Monoid.Ops α := {
  binop := (· + ·)
  ident := 0
}

def add_monoid_props : CA.Monoid.Props (α := α) :=
{
  substL  := r.toProps.substL
  substR  := r.toProps.substR
  assoc   := r.toProps.assoc
  identL  := r.toProps.identL
  identR  := r.toProps.identR
}

local instance group_from_monoid_a_ops :  CA.Group.Ops α := {
  binop := (· + ·)
  ident := 0
  inverse := r.toOps.add_inverse
}

instance group_from_monoid_a : CA.Group.Group (α := α) := {
  toOps := group_from_monoid_a_ops
  toProps := {
    substL    := r.toProps.substL
    substR    := r.toProps.substR
    assoc     := r.toProps.assoc
    identL    := r.toProps.identL
    identR    := r.toProps.identR
    inverseL  := r.toProps.inverseL
    inverseR  := r.toProps.inverseR
  }
}
theorem Ring_a_cancelL_2
    {x y z : α} : x + y ≃ x + z → y ≃ z :=
  CA.Group.group_cancelL

theorem Ring_m_cancelL
    {x y z : α}  [AP (x ≄ add_ident)] : x * y ≃ x * z → y ≃ z := by
  intro (_ : x * y ≃ x * z)
  show y ≃ z
  calc
    _ ≃ y               := Rel.refl
    _ ≃ 1 * y       := Rel.symm m_identL
    _ ≃ ((mult_inverse x) * x) * y := AA.substL (Rel.symm (m_inverseL x))
    _ ≃ (mult_inverse x) * (x * y) := m_assoc
    _ ≃ (mult_inverse x) * (x * z) := AA.substR ‹x * y ≃ x * z›
    _ ≃ ((mult_inverse x) * x) * z   := Rel.symm m_assoc
    _ ≃ 1 * z       := AA.substL (m_inverseL x)
    _ ≃ z               := m_identL

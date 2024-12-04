import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid
import Lean4Axiomatic.ClassicalAlgebra.GroupOpsAsParams
import Lean4Axiomatic.Logic

namespace Lean4Axiomatic.CA.Ring

open Relation.Equivalence (EqvOp)
open Logic (AP)

/-!
A formalization of Rings.

An alternative approach to that of Ring.lean, here we pass in the binary operations as
parameters rather than making them fields in the structure Ops.
-/

/-! ### Definitions -/

variable (α : Type) [EqvOp α]

/--
Operations for Ring, namely
-/
class Ops (add_ident : outParam α) :=
  add_inverse : (x : α) → α
  mult_inverse : (x : α) → [AP (x ≄ add_ident)] → α
export Ops (add_inverse mult_inverse)


/-- Enables the use of the `·⁻¹` operator for taking the inverse. -/
postfix:120 "⁻¹" => Ops.mult_inverse

prefix:100 "-" => Ops.add_inverse

/-- Properties of Ring. -/
class Props (α : Type) [EqvOp α]
  (binop_add : semiOutParam (α → α → α)) (add_ident : outParam α)
  (binop_mult : semiOutParam (α → α → α)) (mult_ident : outParam α)
  [Ops α add_ident] :=
  -- α with + is a group:
  substL {x y z : α} : x ≃ y → binop_add x z ≃ binop_add y z
  substR {x y z : α} : x ≃ y → binop_add z x ≃ binop_add z y
  assoc {x y z : α} : binop_add (binop_add x y) z ≃ binop_add x (binop_add y z)
  identL {x : α} : binop_add add_ident x ≃ x
  identR {x : α} : binop_add x add_ident ≃ x
  inverseL (x : α) : binop_add (add_inverse x) x ≃ add_ident
  inverseR (x : α) : binop_add x (add_inverse x) ≃ ident
  comm {x y : α} : binop_add x y ≃ binop_add y x
  -- α - {0} with * is a group
  m_substL {x y z : α} : x ≃ y → binop_mult x z ≃ binop_mult y z
  m_substR {x y z : α} : x ≃ y → binop_mult z x ≃ binop_mult z y
  m_assoc {x y z : α} :binop_mult (binop_mult x y) z ≃ binop_mult x (binop_mult y z)
  m_identL {x : α} : binop_mult mult_ident x ≃ x
  m_identR {x : α} : binop_mult x mult_ ≃ x
  m_inverseL (x : α) [AP (x ≄ add_ident)] : binop_mult (x⁻¹) x ≃ mult_ident
  m_inverseR (x : α) [AP (x ≄ add_ident)] : binop_mult x (x⁻¹) ≃ mult_ident
  /- ring assoc -/
  assoc1 {x y z : α} : binop_mult (binop_add x y) z ≃ binop_add (binop_mult x z) (binop_mult y z)
  assoc2 {x y z : α} : binop_mult z (binop_add x y) ≃ binop_add (binop_mult z x) (binop_mult z y)

export Props (
  substL substR assoc identL identR inverseL inverseR comm
  m_substL m_substR m_assoc m_identL m_identR m_inverseL m_inverseR
)

/-- All axioms for generic types to form a Group. -/
class Ring (α : Type) [EqvOp α]
  (binop_add : semiOutParam (α → α → α)) (add_ident : outParam α)
  (binop_mult : semiOutParam (α → α → α)) (mult_ident : outParam α)
:=
  toOps : Ring.Ops α add_ident
  toProps : Ring.Props α binop_add add_ident binop_mult mult_ident

attribute [instance] Ring.toOps
attribute [instance] Ring.toProps

/-- Enables the use of the `· * ·` operator for binop. -/
local instance group_mul_op_inst
  {α : Type} [EqvOp α] {binop_add : α → α → α} {add_ident : α}
  {binop_mult : α → α → α} {mult_ident : α} [Ring α binop_add add_ident binop_mult mult_ident]
  : Mul α := {
  mul := binop_mult
}

local instance group_add_op_inst
  {α : Type} [EqvOp α] {binop_add : α → α → α} {add_ident : α}
  {binop_mult : α → α → α} {mult_ident : α} [Ring α binop_add add_ident binop_mult mult_ident]
  : Add α := {
  add := binop_add
}

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
local instance Ring_subst_inst_add
  {α : Type} [EqvOp α] {binop_add : α → α → α} {add_ident : α}
  {binop_mult : α → α → α} {mult_ident : α} [Ring α binop_add add_ident binop_mult mult_ident]
  : AA.Substitutive₂ (α := α) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  substitutiveL := { subst₂ := λ (_ : True) => substL (binop_add := binop_add) (binop_mult := binop_mult) }
  substitutiveR := { subst₂ := λ (_ : True) => substR (binop_add := binop_add) (binop_mult := binop_mult) }
}

local instance Ring_subst_inst_mult
  {α : Type} [EqvOp α] {binop_add : α → α → α} {add_ident : α}
  {binop_mult : α → α → α} {mult_ident : α} [Ring α binop_add add_ident binop_mult mult_ident]
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => m_substL (binop_add := binop_add) (binop_mult := binop_mult)}
  substitutiveR := { subst₂ := λ (_ : True) => m_substR (binop_add := binop_add) (binop_mult := binop_mult) }
}

/-! ### Properties -/

variable {α : Type} [EqvOp α]
 {binop_add : α → α → α} {add_ident : α}
 {binop_mult : α → α → α} {mult_ident : α} [ring_inst : Ring α binop_add add_ident binop_mult mult_ident]


/-- these OfNat instances don't appear to actually work, see comments above Ring_a_cancelL below. -/
instance ofNatIdent0 : OfNat α 0 := {
  ofNat := add_ident
}

instance ofNatIdent1 : OfNat α 1 := {
  ofNat := mult_ident
}

/--
Note, a couple of issues in below:

1) Despite the above OfNatIndent0, I cannot seem to use the literal 0 (or 1) below. For
 0, I get an error "
failed to synthesize
  OfNat α 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  α
due to the absence of the instance above

2) when calling Ring properties it's tedious to directly refer to them, e.g.
in proof that add_ident + y ≃ y, we'd intuitively like to justify it with identL,
however that fails to load and to make it work you need to pass in the ops like
identL (binop_add := binop_add) (binop_mult := binop_mult)
alternatively below we use the named Ring instance to avoid this:
ringinst.toProps.identL
"
-/
theorem Ring_a_cancelL
    {x y z : α} : x + y ≃ x + z → y ≃ z := by
  intro (_ : x + y ≃ x + z)
  show y ≃ z
  calc
    _ ≃ y              := Rel.refl
    _ ≃ add_ident + y  := Rel.symm (ring_inst.toProps.identL)
    _ ≃ ((-x) + x) + y := AA.substL (Rel.symm (ring_inst.toProps.inverseL x) )
    _ ≃ (-x) + (x + y) := ring_inst.toProps.assoc
    _ ≃ (-x) + (x + z) := AA.substR ‹x + y ≃ x + z›
    _ ≃ (-x + x) + z   := Rel.symm (ring_inst.toProps.assoc)
    _ ≃ add_ident + z  := AA.substL (ring_inst.toProps.inverseL x)
    _ ≃ z              := ring_inst.toProps.identL


local instance add_monoid_ops : CA.Monoid.Ops α := {
  binop := (· + ·)
  ident := add_ident
}

def add_monoid_props : CA.Monoid.Props (α := α) :=
{
  substL  := ring_inst.toProps.substL
  substR  := ring_inst.toProps.substR
  assoc   := ring_inst.toProps.assoc
  identL  := ring_inst.toProps.identL
  identR  := ring_inst.toProps.identR
}

local instance group_from_monoid_a_ops : CA.Group.Ops α := {
  inverse := ring_inst.toOps.add_inverse
}

instance group_from_monoid_a : CA.Group.Group α binop_add add_ident := {
  toOps := group_from_monoid_a_ops
  toProps := {
    substL    := ring_inst.toProps.substL
    substR    := ring_inst.toProps.substR
    assoc     := ring_inst.toProps.assoc
    identL    := ring_inst.toProps.identL
    identR    := ring_inst.toProps.identR
    inverseL  := ring_inst.toProps.inverseL
    inverseR  := ring_inst.toProps.inverseR
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
    _ ≃ y                          := Rel.refl
    _ ≃ mult_ident * y             := Rel.symm ring_inst.toProps.m_identL
    _ ≃ ((mult_inverse x) * x) * y := AA.substL (Rel.symm (ring_inst.toProps.m_inverseL x))
    _ ≃ (mult_inverse x) * (x * y) := ring_inst.toProps.m_assoc
    _ ≃ (mult_inverse x) * (x * z) := AA.substR ‹x * y ≃ x * z›
    _ ≃ ((mult_inverse x) * x) * z := Rel.symm ring_inst.toProps.m_assoc
    _ ≃ mult_ident * z             := AA.substL (ring_inst.toProps.m_inverseL x)
    _ ≃ z                          := ring_inst.toProps.m_identL

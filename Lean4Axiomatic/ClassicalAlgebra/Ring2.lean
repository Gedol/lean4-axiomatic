import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Group2_Mul
import Lean4Axiomatic.Logic

namespace Lean4Axiomatic.CA.Ring2

open Relation.Equivalence (EqvOp)
open Logic (AP)

/-!
A formalization of Rings

Approach 2.  Try to reuse Group axioms, uses Group2.
-/

/-! ### Definitions -/

def helper [Add α] : Mul α := {
  mul := (· + ·)
}

class Props [EqvOp α] [mul : Mul α] [Add α] (add_ident : α) (mult_ident : α) :=
  multiplication_is_group : Group2.Group2 α mult_ident
  substLA {x y z : α} : x ≃ y → x + z ≃ y + z
  addition_is_group : Group2.Group2 α add_ident -- problem here, we want to pass in addition as type Mul


class Ring2 [EqvOp α] [mul : Mul α] [Add α] (add_ident : α) (mult_ident : α) :=
  toProps : Ring2.Props add_ident mult_ident

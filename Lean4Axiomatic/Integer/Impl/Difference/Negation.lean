import Lean4Axiomatic.Integer.Impl.Difference.Addition

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Negation of formal differences -/

variable {ℕ : Type} [Natural ℕ]

open Signed (Positive)

/--
Negation of differences.

**Definition intuition**: It's easiest to use the "directed gap" interpretation
of differences to see this. If `a——b` represents the process of traveling from
`a` to `b`, then its negation should represent the opposite process: traveling
from `b` to `a`.
-/
def neg : Difference ℕ → Difference ℕ
| a——b => b——a

instance negOp : Neg (Difference ℕ) := {
  neg := neg
}

/--
Negating two equivalent differences preserves their equivalence.

**Property intuition**: For negation to make sense as an operation (i.e., have
a consistent definition as a function) on integers, this property must be true.

**Proof intuition**: Nothing too insightful here, it's just expanding the
definitions of negation and equality and performing some algebra.
-/
@[gcongr]
theorem neg_subst {a₁ a₂ : Difference ℕ} : a₁ ≃ a₂ → -a₁ ≃ -a₂ := by
  revert a₁; intro (n——m); let a₁ := n——m
  revert a₂; intro (k——j); let a₂ := k——j
  intro (_ : a₁ ≃ a₂)
  show -a₁ ≃ -a₂

  have : n——m ≃ k——j := ‹a₁ ≃ a₂›
  have : n + j ≃ k + m := ‹n——m ≃ k——j›
  have : m + k ≃ j + n := calc
    _ = m + k := rfl
    _ ≃ k + m := Natural.add_comm
    _ ≃ n + j := Rel.symm ‹n + j ≃ k + m›
    _ ≃ j + n := Natural.add_comm
  have : m——n ≃ j——k := ‹m + k ≃ j + n›

  calc
    _ = -a₁     := rfl
    _ = -(n——m) := rfl
    _ = m——n    := rfl
    _ ≃ j——k    := ‹m——n ≃ j——k›
    _ = -(k——j) := rfl
    _ = -a₂     := rfl

@[implicit_reducible]
def neg_substitutive
    : AA.Substitutive₁ (α := Difference ℕ) (-·) (· ≃ ·) (· ≃ ·)
    := {
  subst₁ := neg_subst
}

/--
The negation of a natural number difference is that difference's left additive
inverse.

**Property intuition**: This property is pretty much why the integers are a
useful concept in the first place.

**Proof intuition**: Negation swaps the elements of a difference, so adding a
difference to its negation will result in a difference with equal elements. All
differences with equal elements represent zero.
-/
theorem neg_invL {a : Difference ℕ} : (-a) + a ≃ 0 := by
  revert a; intro (n——m); let a := n——m

  have : m + n ≃ n + m := Natural.add_comm
  have : (m + n) + 0 ≃ 0 + (n + m) := Natural.add_swapped_zeros_eqv.mpr this
  have diff_eqv : (m + n)——(n + m) ≃ 0——0 := this

  calc
    _ = (-a) + a         := rfl
    _ = -(n——m) + n——m   := rfl
    _ = m——n + n——m      := rfl
    _ = (m + n)——(n + m) := rfl
    _ ≃ 0——0             := diff_eqv
    _ = 0                := rfl

/--
The negation of a natural number difference is that difference's right additive
inverse.
-/
theorem neg_invR {a : Difference ℕ} : a + (-a) ≃ 0 := calc
  _ = a + (-a) := rfl
  _ ≃ (-a) + a := add_comm
  _ ≃ 0        := neg_invL

@[implicit_reducible]
def neg_inverse : AA.Inverse (α := Difference ℕ) (-·) (· + ·) := {
  inverseL := { inverse := neg_invL }
  inverseR := { inverse := neg_invR }
}

instance negation : Negation (ℕ := ℕ) (Difference ℕ) := {
  negOp := negOp
  neg_substitutive := neg_substitutive
  neg_inverse := neg_inverse
}

end Lean4Axiomatic.Integer.Impl.Difference

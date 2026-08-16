import Lean4Axiomatic.Rational.Core

/-! # Rational numbers: addition -/

namespace Lean4Axiomatic.Rational

/-! ## Axioms -/

/-- Operations pertaining to rational number addition. -/
class Addition.Ops (ℚ : Type) where
  /-- Addition of rational numbers. -/
  add : ℚ → ℚ → ℚ

export Addition.Ops (add)

/-- Enables the use of the `· + ·` operator for addition. -/
instance add_op_inst {ℚ : Type} [Addition.Ops ℚ] : Add ℚ := {
  add := add
}

/-- Properties of rational number addition. -/
class Addition.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Ops ℚ]
    where
  /-- Addition respects equivalence over its left operand. -/
  add_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ + q ≃ p₂ + q

  /-- Addition respects equivalence over its right operand. -/
  add_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q + p₁ ≃ q + p₂

  /-- Addition is consistent with its integer equivalent. -/
  add_compat_from_integer {a b : ℤ} : ((a + b : ℤ) : ℚ) ≃ (a : ℚ) + (b : ℚ)

  /-- Addition is commutative. -/
  add_comm {p q : ℚ} : p + q ≃ q + p

  /-- Addition is associative. -/
  add_assoc {p q r : ℚ} : (p + q) + r ≃ p + (q + r)

  /-- Zero is a left additive identity. -/
  add_identL {p : ℚ} : 0 + p ≃ p

  /-- Zero is a right additive identity. -/
  add_identR {p : ℚ} : p + 0 ≃ p

export Addition.Props (
  add_assoc add_comm add_compat_from_integer add_identL add_identR add_substL
  add_substR
)

attribute [gcongr] add_substL add_substR

/-- All axioms of addition for rational numbers. -/
class Addition
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ]
    where
  toOps : Addition.Ops ℚ
  toProps : Addition.Props ℚ

attribute [implicit_reducible, instance] Addition.toOps
attribute [instance] Addition.toProps

/-! ## Derived properties -/

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Core (ℤ := ℤ) ℚ] [Addition ℚ]

instance add_assoc_inst : AA.Associative (α := ℚ) (· + ·) := {
  assoc := add_assoc
}

instance add_comm_inst : AA.Commutative (α := ℚ) (· + ·) := {
  comm := add_comm
}

instance add_subst_inst
    : AA.Substitutive₂ (α := ℚ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => add_substL }
  substitutiveR := { subst₂ := λ (_ : True) => add_substR }
}

/--
In the rationals, one plus one is two.

**Proof intuition**: Delegates to the equivalent integer property.
-/
theorem add_one_one : (1:ℚ) + 1 ≃ 2 := calc
  _ ≃ (1:ℚ) + 1             := eqv_refl
  _ ≃ ((1:ℤ):ℚ) + ((1:ℤ):ℚ) := eqv_refl
  _ ≃ ((1 + 1 : ℤ):ℚ)       := eqv_symm add_compat_from_integer
  _ ≃ ((2:ℤ):ℚ)             := by srw [Integer.add_one_one]
  _ ≃ 2                     := eqv_refl

end Lean4Axiomatic.Rational

import Lean4Axiomatic.Rational.Multiplication

/-! # Rational numbers: negation and subtraction -/

namespace Lean4Axiomatic.Rational

open Logic (AP)

/-! ## Axioms -/

/-- Operations pertaining to rational number negation. -/
class Negation.Ops (ℚ : Type) where
  /-- Negation of rational numbers. -/
  neg : ℚ → ℚ

export Negation.Ops (neg)

/-- Enables the use of the `-·` operator for negation. -/
instance neg_op_inst {ℚ : Type} [Negation.Ops ℚ] : Neg ℚ := {
  neg := neg
}

/-- Properties of rational number negation. -/
class Negation.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Ops ℚ]
    where
  /-- Negation respects equivalence over its operand. -/
  neg_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → -p₁ ≃ -p₂

  /-- Negation is consistent with its integer equivalent. -/
  neg_compat_from_integer {a : ℤ} : ((-a : ℤ) : ℚ) ≃ -(a : ℚ)

  /-- The negation of a value is its left additive inverse. -/
  add_inverseL {p : ℚ} : -p + p ≃ 0

  /-- The negation of a value is its right additive inverse. -/
  add_inverseR {p : ℚ} : p + -p ≃ 0

export Negation.Props (
  add_inverseL add_inverseR neg_compat_from_integer neg_subst
)

attribute [gcongr] neg_subst

/-- All rational number negation axioms. -/
class Negation
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ]
    where
  toOps : Negation.Ops ℚ
  toProps : Negation.Props ℚ

attribute [implicit_reducible, instance] Negation.toOps
attribute [instance] Negation.toProps

/-- Operations pertaining to rational number subtraction. -/
class Subtraction.Ops (ℚ : Type) where
  /-- Subtraction of rational numbers. -/
  sub : ℚ → ℚ → ℚ

export Subtraction.Ops (sub)

/-- Enables the use of the `· - ·` operator for subtraction. -/
instance sub_op_inst {ℚ : Type} [Subtraction.Ops ℚ] : Sub ℚ := {
  sub := sub
}

/-- Properties of rational number subtraction. -/
class Subtraction.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Negation ℚ] [Ops ℚ]
    where
  /-- Subtraction is equivalent to addition of a negated second argument. -/
  sub_add_neg {p q : ℚ} : p - q ≃ p + (-q)

export Subtraction.Props (sub_add_neg)

/-- All rational number subtraction axioms. -/
class Subtraction
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Negation ℚ]
    where
  toOps : Subtraction.Ops ℚ
  toProps : Subtraction.Props ℚ

attribute [implicit_reducible, instance] Subtraction.toOps
attribute [instance] Subtraction.toProps

/-! ## Derived properties -/

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type} [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Negation ℚ]

/--
Adding or removing a negation from zero leaves it unchanged.

**Property intuition**: Zero doesn't have a sign (alternatively, it has a sign
of zero), so it can't be negated.

**Proof intuition**: Introduce the additive inverse of the variable on the left
by adding zero and turning it into the variable from the hypothesis.
-/
theorem neg_preserves_zero {p : ℚ} : -p ≃ 0 ↔ p ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : -p ≃ 0)
    show p ≃ 0
    calc
      p      ≃ _ := eqv_symm add_identR
      p + 0  ≃ _ := by srw [←‹-p ≃ 0›]
      p + -p ≃ _ := add_inverseR
      0      ≃ _ := eqv_refl
  case mpr =>
    intro (_ : p ≃ 0)
    show -p ≃ 0
    calc
      -p     ≃ _ := eqv_symm add_identL
      0 + -p ≃ _ := by srw [←‹p ≃ 0›]
      p + -p ≃ _ := add_inverseR
      0      ≃ _ := eqv_refl

/--
The negation of a nonzero rational is also nonzero.

**Property intuition**: Negation produces the "mirror image" of a rational
number, reflected across zero. Any nonzero number will be some finite distance
away from zero, and so will its negation.

**Proof intuition**: Show that `-p ≃ 0` implies `p ≃ 0`, and take the
contrapositive.
-/
theorem neg_preserves_nonzero {p : ℚ} : p ≄ 0 → -p ≄ 0 :=
  mt neg_preserves_zero.mp

/-- Useful for having negated expressions under the division sign. -/
instance neg_preserves_nonzero_inst {p : ℚ} [AP (p ≄ 0)] : AP (-p ≄ 0) :=
  AP.mk (neg_preserves_nonzero ‹AP (p ≄ 0)›.ev)

/--
Negating twice is the same as not negating at all.

The proof is identical to `Integer.neg_involutive`; see its comment for
intuition.
-/
theorem neg_involutive {p : ℚ} : -(-p) ≃ p := calc
  -(-p)            ≃ _ := eqv_symm add_identL
  0 + -(-p)        ≃ _ := by srw [←add_inverseR]
  (p + -p) + -(-p) ≃ _ := add_assoc
  p + (-p + -(-p)) ≃ _ := by srw [add_inverseR]
  p + 0            ≃ _ := add_identR
  p                ≃ _ := eqv_refl

section mul_only
variable [Multiplication ℚ]

/--
Zero is a left absorbing element for multiplication.

The proof is identical to `Integer.mul_absorbL`; see its comment for intuition.
-/
theorem mul_absorbL {p : ℚ} : 0 * p ≃ 0 := calc
  0 * p                      ≃ _ := eqv_symm add_identR
  0 * p + 0                  ≃ _ := by srw [←add_inverseR]
  0 * p + (0 * p + -(0 * p)) ≃ _ := eqv_symm add_assoc
  (0 * p + 0 * p) + -(0 * p) ≃ _ := by srw [←mul_distribR]
  (0 + 0) * p + -(0 * p)     ≃ _ := by srw [add_identL]
  0 * p + -(0 * p)           ≃ _ := add_inverseR
  0                          ≃ _ := eqv_refl

/--
Zero is a right absorbing element for multiplication.

This follows from left absorption because multiplication is commutative.
-/
theorem mul_absorbR {p : ℚ} : p * 0 ≃ 0 := calc
  p * 0 ≃ _ := mul_comm
  0 * p ≃ _ := mul_absorbL
  0     ≃ _ := eqv_refl

/--
Instance for the absorption property of zero in the rationals.

This enables the use of abstract algebraic theorems depending on this property,
in proofs involving rational numbers.
-/
instance mul_absorbing_inst : AA.Absorbing (0:ℚ) (· * ·) := {
  absorbingL := { absorb := mul_absorbL }
  absorbingR := { absorb := mul_absorbR }
}

/--
Negation is left-semicompatible with multiplication.

The proof is identical to `Integer.neg_scompatL_mul`; see its comment for
intuition.
-/
theorem neg_scompatL_mul {p q : ℚ} : -(p * q) ≃ -p * q := calc
  -(p * q)                      ≃ _ := eqv_symm add_identL
  0 + -(p * q)                  ≃ _ := by srw [←mul_absorbL]
  0 * q + -(p * q)              ≃ _ := by srw [←add_inverseL]
  (-p + p) * q + -(p * q)       ≃ _ := by srw [mul_distribR]
  (-p * q + p * q) + -(p * q)   ≃ _ := add_assoc
  (-p) * q + (p * q + -(p * q)) ≃ _ := by srw [add_inverseR]
  (-p) * q + 0                  ≃ _ := add_identR
  (-p) * q                      ≃ _ := eqv_refl

/--
Negation is right-semicompatible with multiplication.

This follows from left-semicompatibility because multiplication is commutative.
-/
theorem neg_scompatR_mul {p q : ℚ} : -(p * q) ≃ p * -q := calc
  (-(p * q)) ≃ _ := by srw [mul_comm]
  (-(q * p)) ≃ _ := neg_scompatL_mul
  (-q) * p   ≃ _ := mul_comm
  p * -q     ≃ _ := eqv_refl

/--
Multiplication by negative one is the same as negation.

The proof is identical to `Integer.mul_neg_one`; see its comment for intuition.
-/
theorem mul_neg_one {p : ℚ} : -1 * p ≃ -p := calc
  -1 * p     ≃ _ := eqv_symm neg_scompatL_mul
  (-(1 * p)) ≃ _ := by srw [mul_identL]
  (-p)       ≃ _ := eqv_refl

/--
Negation is compatible with addition; i.e., it distributes over addition.

**Property intuition**: Visualizing rational numbers as vectors, the theorem
says that adding vectors and then reflecting the result across zero is the same
as reflecting the vectors before adding them.

**Proof intuition**: Negation is the same as multiplication by `-1`. The result
follows from the distributive property.
-/
theorem neg_compat_add {p q : ℚ} : -(p + q) ≃ -p + -q := calc
  _ ≃ -(p + q)        := eqv_refl
  _ ≃ -1 * (p + q)    := eqv_symm mul_neg_one
  _ ≃ -1 * p + -1 * q := mul_distribL
  _ ≃ -p + -q         := by srw [mul_neg_one, mul_neg_one]

/--
Square roots of unity are nonzero.

**Property and proof intuition**: Trivial because `p * p ≃ 1` can only hold if
`p ≄ 0`, otherwise the absorption property of zero would make the product zero.
-/
theorem sqrt1_nonzero {p : ℚ} : Sqrt1 p → p ≄ 0 := by
  intro (_ : Sqrt1 p) (_ : p ≃ 0)
  show False
  have : (1 : ℚ) ≃ 0 := calc
    (1 : ℚ) ≃ _ := eqv_symm ‹Sqrt1 p›.elim
    p * p   ≃ _ := by srw [‹p ≃ 0›]
    0 * p   ≃ _ := mul_absorbL
    0       ≃ _ := eqv_refl
  have : (1 : ℚ) ≄ 0 := nonzero_one
  exact absurd ‹(1 : ℚ) ≃ 0› ‹(1 : ℚ) ≄ 0›

/--
Instance version of `sqrt1_nonzero`, to enable clean syntax for square roots of
unity in contexts where they need to be nonzero, such as taking reciprocals.
-/
instance sqrt1_nonzero_inst {p : ℚ} [Sqrt1 p] : AP (p ≄ 0) :=
  AP.mk (sqrt1_nonzero ‹Sqrt1 p›)

end mul_only
section sub_only
variable [Subtraction ℚ]

/--
Replacing the left operand of subtraction with an equivalent value gives an
equivalent result.

**Property intuition**: This must be true for subtraction to be a function on
rational numbers.

**Proof intuition**: Expand subtraction into addition; addition is left
substitutive.
-/
@[gcongr]
theorem sub_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ - q ≃ p₂ - q := by
  intro (_ : p₁ ≃ p₂)
  show p₁ - q ≃ p₂ - q
  calc
    p₁ - q  ≃ _ := sub_add_neg
    p₁ + -q ≃ _ := by srw [‹p₁ ≃ p₂›]
    p₂ + -q ≃ _ := eqv_symm sub_add_neg
    p₂ - q  ≃ _ := eqv_refl

/--
Replacing the right operand of subtraction with an equivalent value gives an
equivalent result.

**Property intuition**: This must be true for subtraction to be a function on
rational numbers.

**Proof intuition**: Expand subtraction into addition of the negation; addition
and negation obey substitution.
-/
@[gcongr]
theorem sub_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q - p₁ ≃ q - p₂ := by
  intro (_ : p₁ ≃ p₂)
  show q - p₁ ≃ q - p₂
  calc
    q - p₁  ≃ _ := sub_add_neg
    q + -p₁ ≃ _ := by srw [‹p₁ ≃ p₂›]
    q + -p₂ ≃ _ := eqv_symm sub_add_neg
    q - p₂  ≃ _ := eqv_refl

/--
Two rational numbers are equal if and only if their difference is zero.

See `Integer.zero_diff_iff_eqv` for intuition.
-/
theorem sub_eqv_zero_iff_eqv {p q : ℚ} : p - q ≃ 0 ↔ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (_ : p - q ≃ 0)
    show p ≃ q
    calc
      p            ≃ _ := eqv_symm add_identR
      p + 0        ≃ _ := by srw [←add_inverseL]
      p + (-q + q) ≃ _ := eqv_symm add_assoc
      (p + -q) + q ≃ _ := by srw [←sub_add_neg]
      (p - q) + q  ≃ _ := by srw [‹p - q ≃ 0›]
      0 + q        ≃ _ := add_identL
      q            ≃ _ := eqv_refl
  case mpr =>
    intro (_ : p ≃ q)
    show p - q ≃ 0
    calc
      p - q  ≃ _ := sub_add_neg
      p + -q ≃ _ := by srw [‹p ≃ q›]
      q + -q ≃ _ := add_inverseR
      0      ≃ _ := eqv_refl

/--
Subtracting zero from any rational number leaves it unchanged.

**Property and proof intuition**: It's the reverse situation of adding zero.
-/
theorem sub_zero {p : ℚ} : p - 0 ≃ p := calc
  p - 0  ≃ _ := sub_add_neg
  p + -0 ≃ _ := by srw [neg_preserves_zero.mpr eqv_refl]
  p + 0  ≃ _ := add_identR
  p      ≃ _ := eqv_refl

/--
Subtraction of rational numbers is consistent with its integer equivalent.

**Property intuition**: The integers are embedded in the rationals, so
subtraction had better continue to work.

**Proof intuition**: Expand subtraction into addition and negation, and use
the `from_integer` compatibility properties for those operations.
-/
theorem sub_compat_from_integer
    {a b : ℤ} : ((a - b : ℤ) : ℚ) ≃ (a : ℚ) - (b : ℚ)
    := calc
  ((a - b : ℤ) : ℚ)        ≃ _ := by srw [Integer.sub_defn]
  ((a + -b : ℤ) : ℚ)       ≃ _ := add_compat_from_integer
  (a : ℚ) + ((-b : ℤ) : ℚ) ≃ _ := by srw [neg_compat_from_integer]
  (a : ℚ) + -(b : ℚ)       ≃ _ := eqv_symm sub_add_neg
  (a : ℚ) - (b : ℚ)        ≃ _ := eqv_refl

/--
The simplest example of a "telescoping" sum: adding two differences with a
common middle value results in the difference of the endpoints.

**Property and proof intuition**: The middle value is positive in one of the
sum's arguments, and negative in the other. Those are additive inverses so they
sum to zero and disappear from the result.
-/
theorem add_sub_telescope {p q r : ℚ} : (p - q) + (q - r) ≃ p - r := calc
  (p - q) + (q - r)   ≃ _ := by srw [sub_add_neg, sub_add_neg]
  (p + -q) + (q + -r) ≃ _ := AA.expr_xxfxxff_lr_swap_rr
  (p + -r) + (q + -q) ≃ _ := by srw [add_inverseR]
  (p + -r) + 0        ≃ _ := add_identR
  p + -r              ≃ _ := eqv_symm sub_add_neg
  p - r               ≃ _ := eqv_refl

end sub_only
variable [Multiplication ℚ] [Subtraction ℚ]

/--
The rational number `-1` is a square root of unity.

**Property and proof intuition**: This is a (nearly) trivial corollary of the
proof that integer square roots of unity are also rational square roots of
unity. There's a single, technical, complication in that the most natural
syntax for representing `-1` as a rational number is `(-1 : ℚ)`, but this is
interpreted as `(-(1 : ℤ) : ℚ)` by Lean, instead of the more convenient
`((-1 : ℤ) : ℚ)`.
-/
instance sqrt1_neg_one : Sqrt1 (-1:ℚ) := by
  have : Integer.Sqrt1 (-1:ℤ) := Integer.sqrt1_neg_one
  have : Sqrt1 ((-1:ℤ):ℚ)     := from_integer_preserves_sqrt1.mpr this
  have : Sqrt1 (-((1:ℤ):ℚ))   := by prw [neg_compat_from_integer] this
  have : Sqrt1 (-1:ℚ)         := this
  exact this

/--
Negating a subtraction operation swaps its operands.

For intuition, see the identical proof for integers, `Integer.sub_neg_flip`.
-/
theorem neg_sub {p q : ℚ} : -(p - q) ≃ q - p := calc
  -(p - q)             ≃ _ := eqv_symm mul_neg_one
  (-1) * (p - q)       ≃ _ := by srw [sub_add_neg]
  (-1) * (p + -q)      ≃ _ := mul_distribL
  (-1) * p + (-1) * -q ≃ _ := by srw [mul_neg_one, mul_neg_one]
  (-p) + -(-q)         ≃ _ := by srw [neg_involutive]
  (-p) + q             ≃ _ := add_comm
  q + -p               ≃ _ := eqv_symm sub_add_neg
  q - p                ≃ _ := eqv_refl

/--
A common left operand can be removed from a subtraction of two sums.

**Property intuition**: Changing two values by the same amount doesn't change
their difference.

**Proof intuition**: Expand subtraction into addition and rearrange so that the
common term and its additive inverse sum to zero.
-/
theorem sub_cancelL_add {p q r : ℚ} : (r + p) - (r + q) ≃ p - q := calc
  _ ≃ (r + p) - (r + q)   := eqv_refl
  _ ≃ (r + p) + -(r + q)  := sub_add_neg
  _ ≃ (r + p) + (-r + -q) := by srw [neg_compat_add]
  _ ≃ (r + -r) + (p + -q) := AA.expr_xxfxxff_lr_swap_rl
  _ ≃ 0 + (p + -q)        := by srw [add_inverseR]
  _ ≃ p + -q              := add_identL
  _ ≃ p - q               := eqv_symm sub_add_neg

/--
A common right operand can be removed from a subtraction of two sums.

**Property intuition**: Changing two values by the same amount doesn't change
their difference.

**Proof intuition**: Follows from left cancellation because addition is
commutative.
-/
theorem sub_cancelR_add {p q r : ℚ} : (p + r) - (q + r) ≃ p - q := calc
  _ ≃ (p + r) - (q + r) := eqv_refl
  _ ≃ (r + p) - (r + q) := by srw [add_comm, add_comm]
  _ ≃ p - q             := sub_cancelL_add

/--
Multiplication on the left distributes over subtraction.

**Property and proof intuition**: Subtraction is just addition; multiplication
distributes over addition.
-/
theorem mul_distribL_sub {p q r : ℚ} : r * (p - q) ≃ r * p - r * q := calc
   r * (p - q)      ≃ _ := by srw [sub_add_neg]
   r * (p + -q)     ≃ _ := mul_distribL
   r * p + r * -q   ≃ _ := by srw [←neg_scompatR_mul]
   r * p + -(r * q) ≃ _ := eqv_symm sub_add_neg
   r * p - r * q    ≃ _ := eqv_refl

/--
Multiplication on the right distributes over subtraction.

**Property and proof intuition**: Subtraction is just addition; multiplication
distributes over addition.
-/
theorem mul_distribR_sub {p q r : ℚ} : (p - q) * r ≃ p * r - q * r := calc
   (p - q) * r   ≃ _ := mul_comm
   r * (p - q)   ≃ _ := mul_distribL_sub
   r * p - r * q ≃ _ := by srw [mul_comm, mul_comm]
   p * r - q * r ≃ _ := eqv_refl

end Lean4Axiomatic.Rational

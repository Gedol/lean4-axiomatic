import Lean4Axiomatic.Rational.Induction

/-! # Rational numbers: sign -/

namespace Lean4Axiomatic.Rational

open Logic (AP iff_subst_covar or_identR or_mapL or_mapR)
open Metric (abs)
open Signed (Negative Positive sgn)

/--
Operations pertaining to rational number signedness.

The operation names are prefixed with underscores so that they don't conflict
with the standard names. This allows the standard names to be used unqualified,
without a namespace prefix.
-/
class Sign.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] (ℚ : Type)
    where
  /--
  The [_signum function_](https://en.wikipedia.org/wiki/Sign_function).

  Extracts the sign of a rational number.
  -/
  _sgn : ℚ → ℤ

  /-- Holds only for positive rational numbers. -/
  _Positive : ℚ → Prop

  /-- Holds only for negative rational numbers. -/
  _Negative : ℚ → Prop

/-- Enables the use of the standard name `sgn` for signum. -/
instance sgn_ops
    {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Sign.Ops (ℤ := ℤ) ℚ]
    : Signed.Sgn.Ops (ℤ := ℤ) ℚ
    := {
  sgn := Sign.Ops._sgn
}

/-- Enables the use of the standard names `Positive` and `Negative`. -/
instance signed_ops
    {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    [Core (ℤ := ℤ) ℚ] [Sign.Ops (ℤ := ℤ) ℚ]
    : Signed.Ops ℚ := {
  Positive := Sign.Ops._Positive
  Negative := Sign.Ops._Negative
  Nonzero := (· ≄ 0)
}

/-- Properties of rational number signedness. -/
class Sign.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
      [Ops (ℤ := ℤ) ℚ]
    where
  /-- `sgn` respects rational number equivalence. -/
  sgn_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → sgn p₁ ≃ sgn p₂

  /-- Zero is the only rational number whose `sgn` is zero. -/
  sgn_zero_only_for_zero {p : ℚ} : sgn p ≃ 0 → p ≃ 0

  /-- Converting integers to rational numbers preserves their sign. -/
  sgn_from_integer {a : ℤ} : sgn (a : ℚ) ≃ sgn a

  /-- The `sgn` function is compatible with multiplication. -/
  sgn_compat_mul {p q : ℚ} : sgn (p * q) ≃ sgn p * sgn q

  /-- There are only three possible values of the `sgn` function. -/
  sgn_trichotomy (p : ℚ) : AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1)

  /-- A rational number is positive iff its sign is `1`. -/
  sgn_positive {p : ℚ} : Positive p ↔ sgn p ≃ 1

  /-- A rational number is negative iff its sign is `-1`. -/
  sgn_negative {p : ℚ} : Negative p ↔ sgn p ≃ -1

export Sign.Props (
  sgn_compat_mul sgn_from_integer sgn_negative sgn_positive sgn_subst
  sgn_trichotomy
)

attribute [gcongr] sgn_subst

/-- All rational number sign axioms. -/
class Sign
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    where
  toOps : Sign.Ops (ℤ := ℤ) ℚ
  toProps : Sign.Props ℚ

attribute [implicit_reducible, instance] Sign.toOps
attribute [instance] Sign.toProps

/-! ## Derived properties -/

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ] [Sign ℚ]

/--
Zero's sign is zero, and it's the only rational number with that sign value.

**Property intuition**: Zero is neither positive nor negative.

**Proof intuition**: Directly follows from the `sgn_from_integer` and
`sgn_zero_only_for_zero` axioms.
-/
theorem sgn_zero {p : ℚ} : p ≃ 0 ↔ sgn p ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : p ≃ 0)
    show sgn p ≃ 0
    calc
      _ = sgn p         := rfl
      _ ≃ sgn (0:ℚ)     := by srw [‹p ≃ 0›]
      _ = sgn ((0:ℤ):ℚ) := rfl
      _ ≃ sgn (0:ℤ)     := sgn_from_integer
      _ ≃ 0             := Integer.sgn_zero.mpr Rel.refl
  case mpr =>
    exact Sign.Props.sgn_zero_only_for_zero

/--
Allows the syntax `sgn p` to be used in places that require a nonzero value,
such as under a division operator, as long as the underlying value `p` is also
nonzero.
-/
instance sgn_preserves_nonzero_inst
    {p : ℚ} [AP (p ≄ 0)] : AP (sgn p ≄ 0)
    :=
  ‹AP (p ≄ 0)›.map (mt sgn_zero.mpr)

/--
The sign of (the rational number) one, is one.

**Property and proof intuition**: It's the same in the integers, and signs of
integers are consistent with their equivalent rational numbers.
-/
theorem sgn_one : sgn (1 : ℚ) ≃ 1 := calc
  _ ≃ sgn (1 : ℚ) := Rel.refl
  _ ≃ sgn (1 : ℤ) := sgn_from_integer
  _ ≃ 1           := Integer.sgn_positive.mp Integer.one_positive

/--
The sign of (the rational number) negative one, is negative one.

**Property and proof intuition**: It's the same in the integers, and signs of
integers are consistent with their equivalent rational numbers.
-/
theorem sgn_neg_one : sgn (-1:ℚ) ≃ -1 := calc
  _ = sgn (-1:ℚ)       := rfl
  _ = sgn (-(1:ℚ))     := rfl
  _ = sgn (-((1:ℤ):ℚ)) := rfl
  _ ≃ sgn ((-1:ℤ):ℚ)   := by srw [←neg_compat_from_integer]
  _ ≃ sgn (-1:ℤ)       := sgn_from_integer
  _ ≃ -1               := Integer.sgn_negative.mp Integer.neg_one_negative

/--
The rational number two is positive.

**Proof intuition**: Delegates to the equivalent property for integers.
-/
theorem sgn_two : sgn (2:ℚ) ≃ 1 := calc
  _ ≃ sgn (2:ℚ) := Rel.refl
  _ ≃ sgn (2:ℤ) := sgn_from_integer
  _ ≃ 1         := Integer.sgn_two_eqv_one

/--
Taking both the `sgn` and negation of a rational number can be done in either
order.

**Property intuition**: The two functions do independent things to their input
numbers. The `sgn` function normalizes any rational into a sign value; the
negation function inverts the sign.

**Proof intuition**: Convert negation into multiplication by negative one, then
use compatibility of multiplication and `sgn`.
-/
theorem sgn_compat_neg {p : ℚ} : sgn (-p) ≃ -(sgn p) := calc
  _ ≃ sgn (-p)           := Rel.refl
  _ ≃ sgn (-1 * p)       := by srw [←mul_neg_one]
  _ ≃ sgn (-1:ℚ) * sgn p := sgn_compat_mul
  _ ≃ -1 * sgn p         := by srw [sgn_neg_one]
  _ ≃ -(sgn p)           := Integer.mul_neg_one

/--
The sign of a nonzero rational number is a square root of unity.

**Property and proof intuition**: The allowed sign values are `1`, `0`, and
`-1`; nonzero rationals have nonzero signs; `1` and `-1` are square roots of
unity.
-/
theorem sqrt1_sgn_nonzero {p : ℚ} : p ≄ 0 → Integer.Sqrt1 (sgn p) := by
  intro (_ : p ≄ 0)
  show Integer.Sqrt1 (sgn p)

  have : AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1) := sgn_trichotomy p
  have : sgn p ≃ 1 ∨ sgn p ≃ -1 :=
    match this with
    | AA.OneOfThree.first (_ : sgn p ≃ 0) =>
      have : sgn p ≄ 0 := mt sgn_zero.mpr ‹p ≄ 0›
      absurd ‹sgn p ≃ 0› ‹sgn p ≄ 0›
    | AA.OneOfThree.second (_ : sgn p ≃ 1) =>
      Or.inl ‹sgn p ≃ 1›
    | AA.OneOfThree.third (_ : sgn p ≃ -1) =>
      Or.inr ‹sgn p ≃ -1›
  have : Integer.Sqrt1 (sgn p) := Integer.sqrt1_cases.mpr this
  exact this

/--
For a product of rational numbers to be zero, at least one of its factors must
be zero.

**Property intuition**: This holds for integers, and since rational numbers
are just scaled integers it should hold for them as well.

**Proof intuition**: The `sgn` of a rational number is an integer, so we can
use the integer version of this property to show that the sign value of one of
the factors must be zero. But only zero has a zero sign value, so one of the
rational numbers must itself be zero.
-/
theorem mul_split_zero {p q : ℚ} : p * q ≃ 0 ↔ p ≃ 0 ∨ q ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : p * q ≃ 0)
    show p ≃ 0 ∨ q ≃ 0
    have : sgn p * sgn q ≃ 0 := calc
      -- TODO: We shouldn't need to use `sgn_compat_mul` to prove this; use
      -- rational induction instead
      sgn p * sgn q ≃ _ := Rel.symm sgn_compat_mul
      sgn (p * q)   ≃ _ := sgn_zero.mp ‹p * q ≃ 0›
      0             ≃ _ := Rel.refl
    have : sgn p ≃ 0 ∨ sgn q ≃ 0 := Integer.mul_split_zero.mp this
    have : p ≃ 0 ∨ q ≃ 0 := match this with
    | Or.inl (_ : sgn p ≃ 0) =>
      have : p ≃ 0 := sgn_zero.mpr ‹sgn p ≃ 0›
      Or.inl this
    | Or.inr (_ : sgn q ≃ 0) =>
      have : q ≃ 0 := sgn_zero.mpr ‹sgn q ≃ 0›
      Or.inr this
    exact this
  case mpr =>
    intro (_ : p ≃ 0 ∨ q ≃ 0)
    show p * q ≃ 0
    match ‹p ≃ 0 ∨ q ≃ 0› with
    | Or.inl (_ : p ≃ 0) => calc
      p * q ≃ _ := by srw [‹p ≃ 0›]
      0 * q ≃ _ := mul_absorbL
      0     ≃ _ := eqv_refl
    | Or.inr (_ : q ≃ 0) => calc
      p * q ≃ _ := by srw [‹q ≃ 0›]
      p * 0 ≃ _ := mul_absorbR
      0     ≃ _ := eqv_refl

/--
Instance for the zero-product property in the rationals.

This enables the use of abstract algebraic theorems depending on this property,
in proofs involving rational numbers.
-/
instance zero_product_inst : AA.ZeroProduct (α := ℚ) (· * ·) := {
  zero_prod := mul_split_zero.mp
}

/--
For a product of rational numbers to be nonzero, both of its factors must be
nonzero.

**Property and proof intuition**: The contrapositive of `mul_split_zero`.
-/
theorem mul_split_nonzero {p q : ℚ} : p * q ≄ 0 ↔ p ≄ 0 ∧ q ≄ 0 := calc
  _ ↔ p * q ≄ 0           := Iff.rfl
  _ ↔ ¬(p * q ≃ 0)        := Iff.rfl
  _ ↔ ¬(p ≃ 0 ∨ q ≃ 0)    := Logic.iff_subst_contra mt mul_split_zero
  _ ↔ ¬(p ≃ 0) ∧ ¬(q ≃ 0) := Logic.not_or_iff_and_not
  _ ↔ p ≄ 0 ∧ q ≄ 0       := Iff.rfl

/--
Enables clean syntax when taking reciprocals of, or dividing by, products.
-/
instance mul_split_nonzero_mpr_inst
    {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] : AP (p * q ≄ 0)
    :=
  AP.mk (mul_split_nonzero.mpr (And.intro ‹AP (p ≄ 0)›.ev ‹AP (q ≄ 0)›.ev))

/-- Helper to get the left factor out of the `mul_split_nonzero` result. -/
theorem mul_split_nonzero_left {p q : ℚ} : p * q ≄ 0 → p ≄ 0 := by
  intro (_ : p * q ≄ 0)
  show p ≄ 0
  have (And.intro (_ : p ≄ 0) _) := mul_split_nonzero.mp ‹p * q ≄ 0›
  exact ‹p ≄ 0›

/-- Helper to get the right factor out of the `mul_split_nonzero` result. -/
theorem mul_split_nonzero_right {p q : ℚ} : p * q ≄ 0 → q ≄ 0 := by
  intro (_ : p * q ≄ 0)
  show q ≄ 0
  have (And.intro _ (_ : q ≄ 0)) := mul_split_nonzero.mp ‹p * q ≄ 0›
  exact ‹q ≄ 0›

/--
The largest sign value is one.

**Property and proof intuition**: The three possible sign values are `-1`, `0`,
and `1`. Show that each of these is less than or equal to `1`.
-/
theorem sgn_max {p : ℚ} : sgn p ≤ 1 := by
  have : AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1) := sgn_trichotomy p
  match this with
  | AA.OneOfThree.first (_ : sgn p ≃ 0) =>
    have : (0 : ℤ) < 1 := Integer.zero_lt_one
    have : (0 : ℤ) ≤ 1 := Integer.le_split.mpr (Or.inl this)
    have : sgn p ≤ 1 := by prw [←‹sgn p ≃ 0›] this
    exact this
  | AA.OneOfThree.second (_ : sgn p ≃ 1) =>
    have : (1 : ℤ) ≤ 1 := Integer.le_refl
    have : sgn p ≤ 1 := by prw [←‹sgn p ≃ 1›] this
    exact this
  | AA.OneOfThree.third (_ : sgn p ≃ -1) =>
    have : (-1 : ℤ) < 0 := Integer.neg_one_lt_zero
    have : (0 : ℤ) < 1 := Integer.zero_lt_one
    have : (-1 : ℤ) < 1 := Integer.trans_lt_lt_lt ‹(-1 : ℤ) < 0› ‹(0 : ℤ) < 1›
    have : (-1 : ℤ) ≤ 1 := Integer.le_split.mpr (Or.inl this)
    have : sgn p ≤ 1 := by prw [←‹sgn p ≃ -1›] this
    exact this

/--
The smallest sign value is negative one.

**Proof intuition**: Use `sgn_max` on the negation of the input number, then
transform algebraically to show the result.
-/
theorem sgn_min {p : ℚ} : sgn p ≥ -1 := by
  have : sgn (-p) ≤ 1 := sgn_max
  have : -1 ≤ sgn p := calc
    _ = -1          := rfl
    _ ≤ -(sgn (-p)) := Integer.le_neg_flip.mp ‹sgn (-p) ≤ 1›
    _ ≃ -(-(sgn p)) := by srw [sgn_compat_neg]
    _ ≃ sgn p       := by srw [Integer.neg_involutive]

  have : sgn p ≥ -1 := ‹-1 ≤ sgn p›
  exact this

section sub_only
variable [Subtraction ℚ]

/--
Multiplication by a rational number can be added or removed from both sides of
an equivalence of rational numbers.
-/
theorem eqv_mulR {p q  r : ℚ} : p ≃ q ∨ r ≃ 0 ↔ p * r ≃ q * r := calc
  _ ↔ p ≃ q ∨ r ≃ 0     := Iff.rfl
  -- ↓ begin key lines ↓
  _ ↔ p - q ≃ 0 ∨ r ≃ 0 := iff_subst_covar or_mapL sub_eqv_zero_iff_eqv.symm
  _ ↔ (p - q) * r ≃ 0   := mul_split_zero.symm
  -- ↑  end key lines  ↑
  _ ↔ p * r - q * r ≃ 0 := AA.eqv_substL_iff mul_distribR_sub
  _ ↔ p * r ≃ q * r     := sub_eqv_zero_iff_eqv

/--
Removing a common positive left factor from a difference of two rational
numbers will leave the difference's sign value unchanged.

This is a useful lemma for proving properties of ordering relations, which are
defined using signs of differences.

**Property intuition**: The positive factor doesn't change the signs of the
difference's operands, and it can only scale their magnitudes, not change their
relative ordering.

**Proof intuition**: Pull out the sign of the common factor using
distributivity and `sgn`'s compatibility with multiplication; it disappears
from the result because it has value `1`.
-/
theorem sgn_sub_cancelL_mul_pos
    {p q r : ℚ} : sgn r ≃ 1 → sgn (r * p - r * q) ≃ sgn (p - q)
    := by
  intro (_ : sgn r ≃ 1)
  show sgn (r * p - r * q) ≃ sgn (p - q)
  calc
    _ ≃ sgn (r * p - r * q) := Rel.refl
    _ ≃ sgn (r * (p - q))   := by srw [←mul_distribL_sub]
    _ ≃ sgn r * sgn (p - q) := sgn_compat_mul
    _ ≃ 1 * sgn (p - q)     := by srw [‹sgn r ≃ 1›]
    _ ≃ sgn (p - q)         := AA.identL

/--
Removing a common positive right factor from a difference of two rational
numbers will leave the difference's sign value unchanged.

This is a useful lemma for proving properties of ordering relations, which are
defined using signs of differences.

**Property intuition**: The positive factor doesn't change the signs of the
difference's operands, and it can only scale their magnitudes, not change their
relative ordering.

**Proof intuition**: Follows from the left-factor version of the property, due
to multiplication's commutativity.
-/
theorem sgn_sub_cancelR_mul_pos
    {p q r : ℚ} : sgn r ≃ 1 → sgn (p * r - q * r) ≃ sgn (p - q)
    := by
  intro (_ : sgn r ≃ 1)
  show sgn (p * r - q * r) ≃ sgn (p - q)
  calc
    _ ≃ sgn (p * r - q * r) := Rel.refl
    _ ≃ sgn (r * p - r * q) := by srw [mul_comm, mul_comm]
    _ ≃ sgn (p - q)         := sgn_sub_cancelL_mul_pos ‹sgn r ≃ 1›

/--
Removing a common negative left factor from a difference of two rational
numbers will leave the difference's sign value unchanged only if its remaining
operands are swapped.

This is a useful lemma for proving properties of ordering relations, which are
defined using signs of differences.

**Property intuition**: The negative factor reflects the two numbers across
zero, reversing their relative ordering. (Their magnitudes may also be scaled,
but that doesn't affect order.) That inverts the sign of their difference; swap
the operands to compensate.

**Proof intuition**: Pull out the sign of the common factor using
distributivity and `sgn`'s compatibility with multiplication. Convert it into
negation, and send it back under the `sgn` to reverse the remaining difference.
-/
theorem sgn_sub_cancelL_mul_neg
    {p q r : ℚ} : sgn r ≃ -1 → sgn (r * p - r * q) ≃ sgn (q - p)
    := by
  intro (_ : sgn r ≃ -1)
  show sgn (r * p - r * q) ≃ sgn (q - p)
  calc
    _ ≃ sgn (r * p - r * q) := Rel.refl
    _ ≃ sgn (r * (p - q))   := by srw [←mul_distribL_sub]
    _ ≃ sgn r * sgn (p - q) := sgn_compat_mul
    _ ≃ -1 * sgn (p - q)    := by srw [‹sgn r ≃ -1›]
    _ ≃ -sgn (p - q)        := Integer.mul_neg_one
    _ ≃ sgn (-(p - q))      := Rel.symm sgn_compat_neg
    _ ≃ sgn (q - p)         := by srw [neg_sub]

/--
Removing a common negative right factor from a difference of two rational
numbers will leave the difference's sign value unchanged only if its remaining
operands are swapped.

This is a useful lemma for proving properties of ordering relations, which are
defined using signs of differences.

**Property intuition**: The negative factor reflects the two numbers across
zero, reversing their relative ordering. (Their magnitudes may also be scaled,
but that doesn't affect order.) That inverts the sign of their difference; swap
the operands to compensate.

**Proof intuition**: Follows from the left-factor version of the property, due
to multiplication's commutativity.
-/
theorem sgn_sub_cancelR_mul_neg
    {p q r : ℚ} : sgn r ≃ -1 → sgn (p * r - q * r) ≃ sgn (q - p)
    := by
  intro (_ : sgn r ≃ -1)
  show sgn (p * r - q * r) ≃ sgn (q - p)
  calc
    _ ≃ sgn (p * r - q * r) := Rel.refl
    _ ≃ sgn (r * p - r * q) := by srw [mul_comm, mul_comm]
    _ ≃ sgn (q - p)         := sgn_sub_cancelL_mul_neg ‹sgn r ≃ -1›

/--
Two rational numbers are equivalent exactly when the sign of their difference
is zero.

This lemma is mainly useful to support the proof of `order_trichotomy`.

**Property and proof intuition**: We already know that rational numbers are
equivalent when their difference is zero (`sub_eqv_zero_iff_eqv`); combine that
with the proof that the `sgn` of zero is zero.
-/
theorem eqv_sgn {p q : ℚ} : p ≃ q ↔ sgn (p - q) ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : p ≃ q)
    show sgn (p - q) ≃ 0
    have : p - q ≃ 0 := sub_eqv_zero_iff_eqv.mpr ‹p ≃ q›
    have : sgn (p - q) ≃ 0 := sgn_zero.mp this
    exact this
  case mpr =>
    intro (_ : sgn (p - q) ≃ 0)
    show p ≃ q
    have : p - q ≃ 0 := sgn_zero.mpr ‹sgn (p - q) ≃ 0›
    have : p ≃ q := sub_eqv_zero_iff_eqv.mp this
    exact this

end sub_only

variable [Reciprocation ℚ]

/--
Taking the reciprocal of a rational number preserves its sign.

**Property intuition**: Flipping a fraction over doesn't change the sign of the
numerator or denominator.

**Proof intuition**: This can only be shown for nonzero rational numbers, since
they have reciprocals. Use the property that the sign values of nonzero
rationals are square roots of unity, along with the algebraic interactions of
`sgn` with multiplication and reciprocation.
-/
theorem sgn_recip {p : ℚ} [AP (p ≄ 0)] : sgn (p⁻¹) ≃ sgn p := by
  have : Integer.Sqrt1 (sgn p) := sqrt1_sgn_nonzero ‹AP (p ≄ 0)›.ev
  calc
    sgn (p⁻¹)                   ≃ _ := Rel.symm AA.identR
    sgn (p⁻¹) * 1               ≃ _ := by srw [←‹Integer.Sqrt1 (sgn p)›.elim]
    sgn (p⁻¹) * (sgn p * sgn p) ≃ _ := by srw [←sgn_compat_mul]
    sgn (p⁻¹) * sgn (p * p)     ≃ _ := Rel.symm sgn_compat_mul
    sgn (p⁻¹ * (p * p))         ≃ _ := by srw [←mul_assoc]
    sgn ((p⁻¹ * p) * p)         ≃ _ := by srw [mul_inverseL, mul_identL]
    sgn p                       ≃ _ := Rel.refl

/--
Extracting the sign of a rational number, and taking its reciprocal, can be
performed in either order and achieve the same result.

**Property intuition**: The reciprocal of a rational number has the same sign.
Likewise, the nonzero sign values `1` and `-1` are identical to their
reciprocals.
-/
theorem sgn_swap_recip
    {p : ℚ} [AP (p ≄ 0)] : (sgn (p⁻¹):ℚ) ≃ (sgn p:ℚ)⁻¹
    := by
  -- Proof intuition: both sides reduce to `(sgn p:ℚ)`.
  have : Integer.Sqrt1 (sgn p) := sqrt1_sgn_nonzero ‹AP (p ≄ 0)›.ev
  have : Sqrt1 (sgn p:ℚ) := from_integer_preserves_sqrt1.mpr this
  calc
    _ = (sgn (p⁻¹):ℚ) := rfl
    _ ≃ (sgn p:ℚ)     := by srw [sgn_recip]
    _ ≃ (sgn p:ℚ)⁻¹   := eqv_symm recip_sqrt1

/--
Taking the reciprocal of a product of rational numbers is equivalent to the
product of each of their reciprocals.

**Property intuition**: Reciprocals and products have independent effects on
fractions, so it makes sense that they can be done in any order.

**Proof intuition**: Follows from algebraic operations, mostly associativity
and the multiplicative identity and inverse properties.
-/
theorem recip_compat_mul
    {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] : (p * q)⁻¹ ≃ p⁻¹ * q⁻¹
    := by
  have swap_middle {w x y z : ℚ} : (w * x) * (y * z) ≃ (w * y) * (x * z) :=
    AA.expr_xxfxxff_lr_swap_rl
  calc
    (p * q)⁻¹                           ≃ _ := eqv_symm mul_identR
    (p * q)⁻¹ * 1                       ≃ _ := by srw [←mul_identR]
    (p * q)⁻¹ * (1 * 1)                 ≃ _ := by srw [←mul_inverseR]
    (p * q)⁻¹ * ((p * p⁻¹) * 1)         ≃ _ := by srw [←mul_inverseR]
    (p * q)⁻¹ * ((p * p⁻¹) * (q * q⁻¹)) ≃ _ := by srw [swap_middle]
    (p * q)⁻¹ * ((p * q) * (p⁻¹ * q⁻¹)) ≃ _ := eqv_symm mul_assoc
    ((p * q)⁻¹ * (p * q)) * (p⁻¹ * q⁻¹) ≃ _ := by srw [mul_inverseL]
    1 * (p⁻¹ * q⁻¹)                     ≃ _ := mul_identL
    p⁻¹ * q⁻¹                           ≃ _ := eqv_refl

/--
Taking the reciprocal of a negated rational number is equivalent to negating
its reciprocal.

**Property intuition**: Reciprocals and negation have independent effects on
fractions, so it makes sense that they can be done in any order.

**Proof intuition**: Convert negation to multiplication by `-1`, then use the
result that reciprocals are compatible with multiplication.
-/
theorem recip_compat_neg {p : ℚ} [AP (p ≄ 0)] : (-p)⁻¹ ≃ -p⁻¹ := calc
  (-p)⁻¹         ≃ _ := by srw [←mul_neg_one]
  (-1 * p)⁻¹     ≃ _ := recip_compat_mul
  (-1:ℚ)⁻¹ * p⁻¹ ≃ _ := by srw [recip_sqrt1]
  (-1) * p⁻¹     ≃ _ := mul_neg_one
  (-p⁻¹)         ≃ _ := eqv_refl

variable [Division ℚ]

/--
The ordering of sign and division operations on rational numbers doesn't
matter.

**Property intuition**: Division is form of scaling a value, and scaling can't
cause a sign to change. Similarly, division of nonzero sign values just gives
nonzero sign values as results.
-/
theorem sgn_compat_div
    {p q : ℚ} [AP (q ≄ 0)] : (sgn (p / q):ℚ) ≃ sgn p / sgn q
    := calc
  _ = (sgn (p / q):ℚ)           := rfl
  _ ≃ (sgn (p * q⁻¹):ℚ)         := by srw [div_mul_recip]
  _ ≃ ((sgn p * sgn (q⁻¹):ℤ):ℚ) := by srw [sgn_compat_mul]
  _ ≃ (sgn p:ℚ) * (sgn (q⁻¹):ℚ) := mul_compat_from_integer
  -- This is the key proof step
  _ ≃ (sgn p:ℚ) * (sgn q:ℚ)⁻¹   := by srw [sgn_swap_recip]
  _ ≃ (sgn p:ℚ) / (sgn q:ℚ)     := eqv_symm div_mul_recip

/--
The sign of a division is the product of the signs of its operands.

**Property intuition**: Signs can be viewed as multiplicative factors on their
underlying number. The factors from the numerator and the denominator can be
pulled out into factors of the division's result.

**Proof intuition**: Expand the division into multiplication by a reciprocal,
then apply `sgn_compat_mul` and `sgn_recip`.
-/
theorem sgn_div {p q : ℚ} [AP (q ≄ 0)] : sgn (p / q) ≃ sgn p * sgn q := calc
  _ = sgn (p / q)       := rfl
  _ ≃ sgn (p * q⁻¹)     := by srw [div_mul_recip]
  _ ≃ sgn p * sgn (q⁻¹) := sgn_compat_mul
  _ ≃ sgn p * sgn q     := by srw [sgn_recip]

/--
The sign of a fraction formed from integers is the product of the integers'
signs.

**Property and proof intuition**: By `sgn_div` and `sgn_from_integer`.
-/
theorem sgn_div_integers
    {a b : ℤ} [Integer.Nonzero b] : sgn ((a:ℚ) / (b:ℚ)) ≃ sgn a * sgn b
    := calc
  _ = sgn ((a:ℚ) / (b:ℚ))   := rfl
  _ ≃ sgn (a:ℚ) * sgn (b:ℚ) := sgn_div
  _ ≃ sgn a * sgn b         := by srw [sgn_from_integer, sgn_from_integer]

/--
Negation can be moved between the "outside" of a division operation and the
"inside", specifically its right operand.

**Property and proof intuition**: Division is the multiplication of the left
operand with the reciprocal of the right operand. Negation can be moved from
the "outside" to the "inside" of both reciprocation and multiplication.
-/
theorem neg_scompatR_div {p q : ℚ} [AP (q ≄ 0)] : -(p / q) ≃ p / (-q) := calc
  (-(p / q))   ≃ _ := by srw [div_mul_recip]
  (-(p * q⁻¹)) ≃ _ := neg_scompatR_mul
  p * -(q⁻¹)   ≃ _ := by srw [←recip_compat_neg]
  p * (-q)⁻¹   ≃ _ := eqv_symm div_mul_recip
  p / (-q)     ≃ _ := eqv_refl

/--
A division operation where both operands are negated is equivalent to one where
neither operand is.

**Property intuition**: This is one of the basic properties of fractions from
school: negation on the top and bottom of a fraction can be canceled.

**Proof intuition**: Using semicompatibility of negation, move both negations
to the "outside" of the division, where they can be removed by the
double-negation property.
-/
theorem div_neg_cancel {p q : ℚ} [AP (q ≄ 0)] : (-p)/(-q) ≃ p / q := calc
  (-p)/(-q)     ≃ _ := eqv_symm neg_scompatL_div
  (-(p / -q))   ≃ _ := by srw [←neg_scompatR_div]
  (-(-(p / q))) ≃ _ := neg_involutive
  p / q         ≃ _ := eqv_refl

/--
The sum of two fractions (division operations on converted integers) can be
written as a single fraction.

**Property intuition**: Since rational numbers are equivalent to fractions, we
know this must be the case.

**Proof intuition**: Expand division into multiplication by the reciprocal (we
do this only because we haven't proven many algebraic identities for division).
Introduce multiplicative inverse terms to generate a common reciprocal value
(i.e., denominator) and factor it out. Move the integer-to-rational conversions
to the outermost layer, then switch back into a fraction for the result.
-/
theorem add_div_integers
    {a b c d : ℤ} [Integer.Nonzero b] [Integer.Nonzero d]
    : (a:ℚ)/b + (c:ℚ)/d ≃ ((a * d + b * c : ℤ):ℚ)/((b * d : ℤ):ℚ)
    := by
  let aQ := (a:ℚ); let bQ := (b:ℚ); let cQ := (c:ℚ); let dQ := (d:ℚ)
  have swap_middle {w x y z : ℚ} : (w * x) * (y * z) ≃ (w * y) * (x * z) :=
    AA.expr_xxfxxff_lr_swap_rl
  have swap_endsR {w x y z : ℚ} : (w * x) * (y * z) ≃ (w * z) * (y * x) :=
    AA.expr_xxfxxff_lr_swap_rr
  have add_compat_ℤ {x y : ℤ} : ((x + y : ℤ):ℚ) ≃ (x:ℚ) + (y:ℚ) :=
    add_compat_from_integer
  have mul_compat_ℤ {x y : ℤ} : ((x * y : ℤ):ℚ) ≃ (x:ℚ) * (y:ℚ) :=
    mul_compat_from_integer
  calc
    _ = (a:ℚ)/b + (c:ℚ)/d                       := rfl
    _ = aQ/bQ + cQ/dQ                           := rfl
    _ ≃ aQ*bQ⁻¹ + cQ/dQ                         := by srw [div_mul_recip]
    _ ≃ aQ*bQ⁻¹ + cQ*dQ⁻¹                       := by srw [div_mul_recip]
    _ ≃ aQ*bQ⁻¹ * 1 + cQ*dQ⁻¹                   := by srw [←mul_identR]
    _ ≃ aQ*bQ⁻¹ * (dQ*dQ⁻¹) + cQ*dQ⁻¹           := by srw [←mul_inverseR]
    _ ≃ aQ*dQ * (bQ⁻¹*dQ⁻¹) + cQ*dQ⁻¹           := by srw [swap_middle]
    _ ≃ aQ*dQ * (bQ*dQ)⁻¹ + cQ*dQ⁻¹             := by srw [←recip_compat_mul]
    _ ≃ aQ*dQ * (bQ*dQ)⁻¹ + cQ*dQ⁻¹ * 1         := by srw [←mul_identR]
    _ ≃ aQ*dQ * (bQ*dQ)⁻¹ + cQ*dQ⁻¹ * (bQ⁻¹*bQ) := by srw [←mul_inverseL]
    _ ≃ aQ*dQ * (bQ*dQ)⁻¹ + cQ*bQ * (bQ⁻¹*dQ⁻¹) := by srw [swap_endsR]
    _ ≃ aQ*dQ * (bQ*dQ)⁻¹ + bQ*cQ * (bQ⁻¹*dQ⁻¹) := by srw [mul_comm]
    _ ≃ aQ*dQ * (bQ*dQ)⁻¹ + bQ*cQ * (bQ*dQ)⁻¹   := by srw [←recip_compat_mul]
    _ ≃ (aQ*dQ + bQ*cQ) * (bQ*dQ)⁻¹             := eqv_symm mul_distribR
    _ ≃ ((a * d : ℤ) + bQ*cQ) * (bQ*dQ)⁻¹       := by srw [←mul_compat_ℤ]
    _ ≃ ((a * d : ℤ) + (b * c : ℤ)) * (bQ*dQ)⁻¹ := by srw [←mul_compat_ℤ]
    _ ≃ (a * d + b * c : ℤ) * (bQ*dQ)⁻¹         := by srw [←add_compat_ℤ]
    _ ≃ (a * d + b * c : ℤ) * ((b * d : ℤ):ℚ)⁻¹ := by srw [←mul_compat_ℤ]
    _ ≃ ((a * d + b * c : ℤ):ℚ)/((b * d : ℤ):ℚ) := eqv_symm div_mul_recip

/--
The product of two fractions is a fraction of the product of the numerators
and the product of the denominators.

**Property intuition**: Multiplication and division associate with each other,
so the multiplication of the numerators and denominators can happen before the
division, or after.

**Proof intuition**: Expand division into multiplication by reciprocal. Group
the reciprocals together; they become a single reciprocal due to compatibility
with multiplication. This is equivalent to division of the products.
-/
theorem div_mul_swap
    {p q r s : ℚ} [AP (q ≄ 0)] [AP (s ≄ 0)] : (p/q) * (r/s) ≃ (p * r)/(q * s)
    := calc
  _ ≃ (p/q) * (r/s)         := eqv_refl
  _ ≃ (p * q⁻¹) * (r * s⁻¹) := by srw [div_mul_recip, div_mul_recip]
  _ ≃ (p * r) * (q⁻¹ * s⁻¹) := AA.expr_xxfxxff_lr_swap_rl
  _ ≃ (p * r) * (q * s)⁻¹   := by srw [←recip_compat_mul]
  _ ≃ (p * r)/(q * s)       := eqv_symm div_mul_recip

/--
A common factor on the right can be dropped from the division of two rational
numbers.
-/
theorem div_cancelR_mul
    {p q r : ℚ} [AP (q * r ≄ 0)]
    : have : AP (q ≄ 0) := ‹AP (q * r ≄ 0)›.map mul_split_nonzero_left
      (p * r)/(q * r) ≃ p/q
    := by
  intro (_ : AP (q ≄ 0))
  show (p * r)/(q * r) ≃ p/q
  have : AP (r ≄ 0) := ‹AP (q * r ≄ 0)›.map mul_split_nonzero_right
  calc
    _ = (p * r)/(q * r) := rfl
    _ ≃ (p/q) * (r/r)   := eqv_symm div_mul_swap
    _ ≃ (p/q) * 1       := by srw [div_same]
    _ ≃ p/q             := mul_identR

/--
A rational number can be multiplied (on the left) and divided by another
rational without changing its value.

Useful when a specific denominator is needed.

**Property intuition**: This is equivalent to multiplying by one.

**Proof intuition**: Use algebraic properties to factor out the common value
from the numerator and denominator as a separate fraction. This cancels to one,
leaving only the original number.
-/
theorem mulL_div_same {p q : ℚ} [AP (p ≄ 0)] : (p * q)/p ≃ q := calc
  _ = (p * q)/p       := rfl
  _ ≃ (p * q)/(p * 1) := by srw [←mul_identR]
  _ ≃ (p/p) * (q/1)   := eqv_symm div_mul_swap
  _ ≃ 1 * q           := by srw [div_same, div_identR]
  _ ≃ q               := mul_identL

/--
A rational number can be multiplied (on the right) and divided by another
rational without changing its value.

Useful when a specific denominator is needed.

**Property intuition**: This is equivalent to multiplying by one.

**Proof intuition**: Follows from the left-multiplication version and
commutativity.
-/
theorem mulR_div_same {p q : ℚ} [AP (q ≄ 0)] : (p * q)/q ≃ p := calc
  _ = (p * q)/q := rfl
  _ ≃ (q * p)/q := by srw [mul_comm]
  _ ≃ p         := mulL_div_same

/--
The quotient of two rational numbers is zero if and only if its numerator is
zero.

**Property and proof intuition**: Division is multiplication, and
multiplication can only be zero if at least one factor is. The denominator
can't be zero, so it must be the numerator.
-/
theorem div_eqv_0 {p q : ℚ} [AP (q ≄ 0)] : p/q ≃ 0 ↔ p ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : p/q ≃ 0)
    show p ≃ 0
    have : p * q⁻¹ ≃ 0 := eqv_trans (eqv_symm div_mul_recip) ‹p/q ≃ 0›
    have : p ≃ 0 ∨ q⁻¹ ≃ 0 := mul_split_zero.mp this
    match this with
    | Or.inl (_ : p ≃ 0) =>
      exact ‹p ≃ 0›
    | Or.inr (_ : q⁻¹ ≃ 0) =>
      have : q⁻¹ ≄ 0 := recip_nonzero
      exact absurd ‹q⁻¹ ≃ 0› ‹q⁻¹ ≄ 0›
  case mpr =>
    intro (_ : p ≃ 0)
    show p/q ≃ 0
    calc
      _ ≃ p/q     := eqv_refl
      _ ≃ p * q⁻¹ := div_mul_recip
      _ ≃ 0 * q⁻¹ := by srw [‹p ≃ 0›]
      _ ≃ 0       := mul_absorbL

/--
A quotient is nonzero when its numerator is.

**Property and proof intuition**: If the quotient was zero, that contradicts
the numerator being nonzero.
-/
theorem div_preserves_nonzero {p q : ℚ} [AP (q ≄ 0)] : p ≄ 0 → p/q ≄ 0 := by
  intro (_ : p ≄ 0) (_ : p/q ≃ 0)
  show False
  have : p ≃ 0 := div_eqv_0.mp ‹p/q ≃ 0›
  exact absurd ‹p ≃ 0› ‹p ≄ 0›

/--
Instance equivalent of `div_preserves_nonzero`.

Enables easy syntax of quotients under reciprocation, or as denominators.
-/
instance div_preserves_nonzero_inst
    {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] : AP (p/q ≄ 0)
    :=
  ‹AP (p ≄ 0)›.map div_preserves_nonzero

/--
Taking the reciprocal of a quotient "flips" it.

**Property intuition**: For `(p/q)⁻¹` to be the multiplicative inverse of
`p/q`, it must be equivalent to `q/p` for both numerator and denominator to
cancel out.

**Proof intuition**: Expand definitions, push reciprocation into
subexpressions, and simplify.
-/
theorem recip_flip_div
    {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] : (p/q)⁻¹ ≃ q/p
    := calc
  _ ≃ (p/q)⁻¹       := eqv_refl
  _ ≃ (p * q⁻¹)⁻¹   := by srw [div_mul_recip]
  _ ≃ p⁻¹ * (q⁻¹)⁻¹ := recip_compat_mul
  _ ≃ p⁻¹ * q       := by srw [recip_idemp]
  _ ≃ q * p⁻¹       := mul_comm
  _ ≃ q/p           := eqv_symm div_mul_recip

/--
Reduce a quotient of quotients into a single quotient.

**Property and proof intuition**: Division is multipliction by the reciprocal,
so flip the second quotient and multiply numerators and denominators.
-/
theorem div_div_div
    {p q r s : ℚ} [AP (q ≄ 0)] [AP (r ≄ 0)] [AP (s ≄ 0)] :
    (p/q) / (r/s) ≃ (p * s)/(q * r)
    := calc
  _ ≃ (p/q) / (r/s)   := eqv_refl
  _ ≃ (p/q) * (r/s)⁻¹ := div_mul_recip
  _ ≃ (p/q) * (s/r)   := by srw [recip_flip_div]
  _ ≃ (p * s)/(q * r) := div_mul_swap

/--
The result of adding two ratios of rational numbers can be written as a single
ratio.

**Property and proof intuition**: Multiply both terms by ratios of factors that
cancel to `1`, so that a common denominator value can be reached. Then directly
add the numerators via `div_distribR`.
-/
theorem add_fractions
    {p q r s : ℚ} [AP (q ≄ 0)] [AP (s ≄ 0)]
    : p/q + r/s ≃ (p * s + q * r)/(q * s)
    := calc
  _ = p/q + r/s                 := rfl
  _ ≃ (p/q) * 1 + r/s           := by srw [←mul_identR]
  _ ≃ (p/q)*(s/s) + r/s         := by srw [←div_same]
  _ ≃ (p*s)/(q*s) + r/s         := by srw [div_mul_swap]
  _ ≃ (p*s)/(q*s) + 1 * (r/s)   := by srw [←mul_identL]
  _ ≃ (p*s)/(q*s) + (q/q)*(r/s) := by srw [←div_same]
  _ ≃ (p*s)/(q*s) + (q*r)/(q*s) := by srw [div_mul_swap]
  _ ≃ (p*s + q*r)/(q*s)         := eqv_symm div_distribR

section
variable [Subtraction ℚ]

/--
Division by a rational number can be added or removed from both sides of an
equivalence of rational numbers.
-/
theorem eqv_divR {p q r : ℚ} [AP (r ≄ 0)] : p ≃ q ↔ p/r ≃ q/r := by
  have : False ↔ r⁻¹ ≃ 0 := Iff.intro False.elim recip_nonzero
  calc
    _ ↔ p ≃ q             := Iff.rfl
    _ ↔ p ≃ q ∨ False     := or_identR.symm
    -- ↓ begin key lines ↓
    _ ↔ p ≃ q ∨ r⁻¹ ≃ 0   := iff_subst_covar or_mapR ‹False ↔ r⁻¹ ≃ 0›
    _ ↔ p * r⁻¹ ≃ q * r⁻¹ := eqv_mulR
    -- ↑  end key lines  ↑
    _ ↔ p/r ≃ q * r⁻¹     := AA.eqv_substL_iff (eqv_symm div_mul_recip)
    _ ↔ p/r ≃ q/r         := AA.eqv_substR_iff (eqv_symm div_mul_recip)

/--
Necessary and sufficient condition for two rational ratios to be equivalent.
-/
theorem div_eqv_div
    {p₁ p₂ q₁ q₂ : ℚ} [AP (q₁ ≄ 0)] [AP (q₂ ≄ 0)]
    : p₁/q₁ ≃ p₂/q₂ ↔ p₁ * q₂ ≃ p₂ * q₁
    := by
  -- Lemmas with short names that can fit on the lines of the main `calc` expr
  have div_mulR
      {x y z : ℚ} [AP (y ≄ 0)] [AP (z ≄ 0)] : x/y ≃ (x * z)/(y * z)
      := calc
    _ = x/y             := rfl
    _ ≃ x/y * 1         := eqv_symm mul_identR
    _ ≃ (x/y) * (z/z)   := mul_substR (eqv_symm div_same)
    _ ≃ (x * z)/(y * z) := div_mul_swap
  have eqvR_divR_subst
      {x y z₁ z₂ : ℚ} [AP (z₁ ≄ 0)] [AP (z₂ ≄ 0)]
      : z₁ ≃ z₂ → (x ≃ y/z₁ ↔ x ≃ y/z₂)
      :=
    AA.eqv_substR_iff ∘ div_substR

  calc
    _ ↔ p₁/q₁ ≃ p₂/q₂                             := Iff.rfl
    _ ↔ (p₁ * q₂)/(q₁ * q₂) ≃ p₂/q₂               := AA.eqv_substL_iff div_mulR
    _ ↔ (p₁ * q₂)/(q₁ * q₂) ≃ (p₂ * q₁)/(q₂ * q₁) := AA.eqv_substR_iff div_mulR
    -- ↓ begin key lines ↓
    _ ↔ (p₁ * q₂)/(q₁ * q₂) ≃ (p₂ * q₁)/(q₁ * q₂) := eqvR_divR_subst mul_comm
    _ ↔ p₁ * q₂ ≃ p₂ * q₁                         := eqv_divR.symm
    -- ↑  end key lines  ↑

/--
Necessary and sufficient condition for two integer ratios to be equivalent.
-/
theorem div_int_eqv_div_int
    {a₁ a₂ b₁ b₂ : ℤ} [AP (b₁ ≄ 0)] [AP (b₂ ≄ 0)]
    : (a₁:ℚ)/b₁ ≃ a₂/b₂ ↔ a₁ * b₂ ≃ a₂ * b₁
    := by
  have mul_compat {a b : ℤ} : (a:ℚ) * b ≃ (a * b : ℤ) :=
    eqv_symm mul_compat_from_integer
  have from_integer_eqv {a b : ℤ} : (a:ℚ) ≃ b ↔ a ≃ b :=
    Iff.intro from_integer_inject from_integer_subst

  calc
    -- ↓ begin key lines ↓
    _ ↔ (a₁:ℚ)/b₁ ≃ a₂/b₂                 := Iff.rfl
    _ ↔ (a₁:ℚ) * b₂ ≃ a₂ * b₁             := div_eqv_div
    -- ↑  end key lines  ↑
    _ ↔ ((a₁ * b₂ : ℤ):ℚ) ≃ a₂ * b₁       := AA.eqv_substL_iff mul_compat
    _ ↔ ((a₁ * b₂ : ℤ):ℚ) ≃ (a₂ * b₁ : ℤ) := AA.eqv_substR_iff mul_compat
    _ ↔ a₁ * b₂ ≃ a₂ * b₁                 := from_integer_eqv

/--
The result of subtracting two ratios of rational numbers can be written as a
single ratio.

**Property and proof intuition**: Convert subtraction into addition of a
negated value. Move the negation to the numerator of the ratio, then add the
ratios via `add_fractions`. Move the negation in the result to cover an entire
additive term, then convert back to subtraction.
-/
theorem sub_fractions
    {p q r s : ℚ} [AP (q ≄ 0)] [AP (s ≄ 0)]
    : p/q - r/s ≃ (p * s - q * r)/(q * s)
    := calc
  _ = p/q - r/s                  := rfl
  _ ≃ p/q + -(r/s)               := sub_add_neg
  _ ≃ p/q + (-r/s)               := by srw [neg_scompatL_div]
  _ ≃ (p * s + q * (-r))/(q * s) := add_fractions
  _ ≃ (p * s + -(q * r))/(q * s) := by srw [←neg_scompatR_mul]
  _ ≃ (p * s - q * r)/(q * s)    := by srw [←sub_add_neg]

end

variable [Induction.{1} ℚ]

/--
Evidence that a rational number can be written as a ratio of an integer
numerator over a positive integer denominator.
-/
structure AsHalfPosRatio (p : ℚ) where
  numerator : ℤ
  denominator : ℤ
  denominator_gt_zero : denominator > 0
  eqv
    : have : denominator ≄ 0 := Integer.neqv_zero_from_gt_zero ‹denominator > 0›
      have : AP (denominator ≄ 0) := AP.mk ‹denominator ≄ 0›
      p ≃ numerator / denominator

/--
Any rational can be written as an integer ratio with positive denominator.
-/
def as_half_pos_ratio (p : ℚ) : AsHalfPosRatio p :=
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) p_eqv) := as_ratio p
  have : p ≃ a/b := p_eqv

  -- Make a positive denominator
  -- ↓ begin key lines ↓
  let a' := a * sgn b
  let b' := b * sgn b
  have : b' ≥ 0 := calc
    _ = b'        := rfl
    _ = b * sgn b := rfl
    _ ≃ abs b     := Rel.symm Integer.abs_sgn
    _ ≥ 0         := Integer.abs_nonneg
  have : b ≄ 0 := ‹AP (b ≄ 0)›.ev
  have : b ≄ 0 ∧ sgn b ≄ 0 := And.intro ‹b ≄ 0› (mt Integer.sgn_zero.mp ‹b ≄ 0›)
  have : b * sgn b ≄ 0 := Integer.mul_split_neqv_zero.mpr ‹b ≄ 0 ∧ sgn b ≄ 0›
  have : b' ≄ 0 := ‹b * sgn b ≄ 0›
  have : b' > 0 := Integer.gt_from_ge_neqv ‹b' ≥ 0› ‹b' ≄ 0›
  -- ↑  end key lines  ↑

  -- Show the new ratio is equivalent to the input value
  have : AP (b' ≄ 0) := AP.mk (Integer.neqv_zero_from_gt_zero ‹b' > 0›)
  have : AP (sgn b ≄ 0) := ‹AP (b ≄ 0)›.map (mt Integer.sgn_zero.mp)
  have mul_compat {a b : ℤ} : (a:ℚ) * (b:ℚ) ≃ (a * b : ℤ) :=
    eqv_symm mul_compat_from_integer
  have : p ≃ a'/b' := calc
    _ = p                               := rfl
    _ ≃ a/b                             := ‹p ≃ a/b›
    _ ≃ ((a:ℚ)/b) * 1                   := eqv_symm mul_identR
    _ ≃ ((a:ℚ)/b) * ((sgn b : ℚ)/sgn b) := mul_substR (eqv_symm div_same)
    _ ≃ (a * sgn b)/(b * sgn b)         := div_mul_swap
    _ ≃ (a * sgn b : ℤ)/(b * sgn b)     := div_substL mul_compat
    _ ≃ (a * sgn b : ℤ)/(b * sgn b : ℤ) := div_substR mul_compat
    _ = (a':ℚ)/b'                       := rfl

  AsHalfPosRatio.mk a' b' ‹b' > 0› ‹p ≃ a'/b'›

/--
If two rational numbers have the same sign value, their sum will as well.

**Property intuition**: If we visualize rational numbers as arrows on a number
line, an arrow's length is its magnitude and its direction is its sign. Two
positive or two negative numbers will have their arrows pointing in the same
direction; adding them produces a longer arrow, again pointing in the same
direction.

**Proof intuition**: Convert both rational numbers to their fraction
representations. Their sum can be written as a single fraction, and its sign is
just the product of the signs of its numerator and denominator. This can be
rearranged algebraically into the sign of an integer sum, the operands of which
happen to share a sign. By the corresponding theorem for integers, the sum must
have that sign as well.
-/
theorem add_preserves_sign
    {s : ℤ} {p q : ℚ} : sgn p ≃ s → sgn q ≃ s → sgn (p + q) ≃ s
    := by
  intro (_ : sgn p ≃ s) (_ : sgn q ≃ s)
  show sgn (p + q) ≃ s
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) p_eqv) := as_ratio p
  have (AsRatio.mk (c : ℤ) (d : ℤ) (_ : AP (d ≄ 0)) q_eqv) := as_ratio q
  have : Integer.Nonzero b := Integer.nonzero_iff_neqv_zero.mpr ‹AP (b ≄ 0)›.ev
  have : Integer.Nonzero d := Integer.nonzero_iff_neqv_zero.mpr ‹AP (d ≄ 0)›.ev
  have : p ≃ a/b := p_eqv
  have : q ≃ c/d := q_eqv
  have : Integer.Sqrt1 (sgn b) := Integer.sgn_nonzero.mp ‹Integer.Nonzero b›
  have : Integer.Sqrt1 (sgn d) := Integer.sgn_nonzero.mp ‹Integer.Nonzero d›

  have : sgn (a * b * (d * d)) ≃ s := calc
    _ = sgn (a * b * (d * d))         := rfl
    _ ≃ sgn (a * b) * sgn (d * d)     := Integer.sgn_compat_mul
    _ ≃ sgn (a * b) * (sgn d * sgn d) := by srw [Integer.sgn_compat_mul]
    _ ≃ sgn (a * b) * 1               := by srw [‹Integer.Sqrt1 (sgn d)›.elim]
    _ ≃ sgn (a * b)                   := Integer.mul_identR
    _ ≃ sgn a * sgn b                 := Integer.sgn_compat_mul
    _ ≃ sgn ((a:ℚ)/b)                 := Rel.symm sgn_div_integers
    _ ≃ sgn p                         := by srw [←‹p ≃ a/b›]
    _ ≃ s                             := ‹sgn p ≃ s›
  have : sgn (b * b * (c * d)) ≃ s := calc
    _ = sgn (b * b * (c * d))       := rfl
    _ ≃ sgn (b * b) * sgn (c * d)   := Integer.sgn_compat_mul
    _ ≃ sgn b * sgn b * sgn (c * d) := by srw [Integer.sgn_compat_mul]
    _ ≃ 1 * sgn (c * d)             := by srw [‹Integer.Sqrt1 (sgn b)›.elim]
    _ ≃ sgn (c * d)                 := Integer.mul_identL
    _ ≃ (sgn c * sgn d)             := Integer.sgn_compat_mul
    _ ≃ sgn ((c:ℚ)/d)               := Rel.symm sgn_div_integers
    _ ≃ sgn q                       := by srw [←‹q ≃ c/d›]
    _ ≃ s                           := ‹sgn q ≃ s›
  have : sgn (a*b * (d*d) + b*b * (c*d)) ≃ s :=
    Integer.add_preserves_sign ‹sgn (a*b * (d*d)) ≃ s› ‹sgn (b*b * (c*d)) ≃ s›

  calc
    _ = sgn (p + q)                       := rfl
    _ ≃ sgn ((a:ℚ)/b + q)                 := by srw [‹p ≃ a/b›]
    _ ≃ sgn ((a:ℚ)/b + (c:ℚ)/d)           := by srw [‹q ≃ c/d›]
    _ ≃ sgn (((a*d+b*c:ℤ):ℚ)/((b*d:ℤ):ℚ)) := by srw [add_div_integers]
    _ ≃ sgn (a*d + b*c) * sgn (b*d)       := sgn_div_integers
    _ ≃ sgn ((a* d + b * c) * (b * d))    := Rel.symm Integer.sgn_compat_mul
    _ ≃ sgn (a*d * (b*d) + b*c * (b*d))   := by srw [Integer.mul_distribR]
    _ ≃ sgn (a*b * (d*d) + b*c * (b*d))   := by srw [AA.expr_xxfxxff_lr_swap_rl]
    _ ≃ sgn (a*b * (d*d) + b*b * (c*d))   := by srw [AA.expr_xxfxxff_lr_swap_rl]
    _ ≃ s                                 := ‹sgn (a*b*(d*d) + b*b*(c*d)) ≃ s›

/--
The _signum_ function is idempotent: applying it twice is the same as applying
it once.

**Property intuition**: The `sgn` function has only three possible results, and
each of them is a fixed point.

**Proof intuition**: Instead of using trichotomy to do tedious case analysis,
convert the rational into its fraction form and reduce it to an expression with
integer `sgn`, which we already know is idempotent.
-/
theorem sgn_idemp {p : ℚ} : sgn (sgn p) ≃ sgn p := by
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) eqv) := as_ratio p
  have : Integer.Nonzero b := Integer.nonzero_iff_neqv_zero.mpr ‹AP (b ≄ 0)›.ev
  have : p ≃ a/b := eqv
  calc
    sgn (sgn p)               ≃ _ := by srw [‹p ≃ a/b›]
    sgn (sgn ((a : ℚ)/b))     ≃ _ := by srw [sgn_div_integers]
    sgn (sgn a * sgn b)       ≃ _ := Integer.sgn_compat_mul
    sgn (sgn a) * sgn (sgn b) ≃ _ := by srw [Integer.sgn_idemp]
    sgn a * sgn (sgn b)       ≃ _ := by srw [Integer.sgn_idemp]
    sgn a * sgn b             ≃ _ := Rel.symm sgn_div_integers
    sgn ((a : ℚ)/b)           ≃ _ := by srw [←‹p ≃ a/b›]
    sgn p                     ≃ _ := Rel.refl

/--
Only the nonzero rational numbers have signs that are square roots of unity.

**Property intuition**: The nonzero sign values are `1` and `-1`, which are the
square roots of unity.

**Proof intuition**: Signs that are square roots of unity are nonzero, which
implies their originating numbers are also nonzero.
-/
theorem sgn_sqrt1_iff_nonzero {p : ℚ} : Integer.Sqrt1 (sgn p) ↔ p ≄ 0 := by
  have : Integer.Sqrt1 (sgn (sgn p)) ↔ Integer.Sqrt1 (sgn p) :=
    Rel.iff_subst_eqv Integer.sqrt1_subst sgn_idemp
  calc
    _ ↔ Integer.Sqrt1 (sgn p)       := Rel.refl
    _ ↔ Integer.Sqrt1 (sgn (sgn p)) := this.symm
    _ ↔ Integer.Nonzero (sgn p)     := Integer.sgn_nonzero.symm
    _ ↔ sgn p ≄ 0                   := Integer.nonzero_iff_neqv_zero
    _ ↔ p ≄ 0                       := Logic.iff_subst_contra mt sgn_zero.symm

/--
A positive rational is nonzero.

**Proof intuition**: Rationals with square roots of unity as their signs are
nonzero; positive rationals have a sign of one.
-/
theorem nonzero_if_pos {p : ℚ} : sgn p ≃ 1 → p ≄ 0 := by
  intro (_ : sgn p ≃ 1)
  show p ≄ 0
  have : Integer.Sqrt1 (sgn p) := Integer.sqrt1_cases.mpr (Or.inl ‹sgn p ≃ 1›)
  have : p ≄ 0 := sgn_sqrt1_iff_nonzero.mp ‹Integer.Sqrt1 (sgn p)›
  exact this

/--
A negative rational is nonzero.

**Proof intuition**: Rationals with square roots of unity as their signs are
nonzero; negative rationals have a sign of negative one.
-/
theorem nonzero_if_neg {p : ℚ} : sgn p ≃ -1 → p ≄ 0 := by
  intro (_ : sgn p ≃ -1)
  have : Integer.Sqrt1 (sgn p) := Integer.sqrt1_cases.mpr (Or.inr ‹sgn p ≃ -1›)
  have : p ≄ 0 := sgn_sqrt1_iff_nonzero.mp this
  exact this

/--
The square of a rational number is nonnegative.

**Property intuition**: The product of two negative numbers is positive, and
zero times anything is zero.

**Proof intuition**: An equivalent expression for the sign of the squared
rational is `sgn (sgn p * sgn p)`, because `sgn` is idempotent. That new
expression is nonnegative, by `Integer.nonneg_square`, and thus the original
expression is too.
-/
theorem nonneg_square {p : ℚ} : sgn (p * p) ≄ -1 := by
  have : sgn (sgn p * sgn p) ≃ sgn (p * p) := calc
    _ = sgn (sgn p * sgn p) := rfl
    _ ≃ sgn (sgn (p * p))   := by srw [←sgn_compat_mul]
    _ ≃ sgn (p * p)         := sgn_idemp
  have : sgn (sgn p * sgn p) ≄ -1 := Integer.nonneg_square
  have : sgn (p * p) ≄ -1 := by prw [‹sgn (sgn p * sgn p) ≃ sgn (p * p)›] this
  exact this

/--
The only sign value greater than zero, is one.

**Property intuition**: The only sign values are `1`, `0`, and `-1`.

**Proof intuition**: The sign of any number greater than zero is one; taking
the sign of a sign leaves it unchanged.
-/
theorem sgn_gt_zero_iff_pos {p : ℚ} : sgn p > 0 ↔ sgn p ≃ 1 := calc
  _ ↔ sgn p > 0       := Iff.rfl
  _ ↔ sgn (sgn p) ≃ 1 := Integer.gt_zero_sgn
  _ ↔ sgn p ≃ 1       := by srw [sgn_idemp]

variable [Subtraction ℚ]

/--
Removing a common positive denominator from a difference of two fractions will
leave the difference's sign value unchanged.

This is a useful lemma for proving properties of ordering relations, which are
defined using signs of differences.

**Property intuition**: The positive divisor doesn't change the signs of the
difference's operands, and it can only scale their magnitudes, not change their
relative ordering.

**Proof intuition**: Convert the divisions to multiplication by reciprocals.
The reciprocals of positive numbers are positive. Delegate to the
multiplicative version of this property.
-/
theorem sgn_sub_cancelR_div_pos
    {p q r : ℚ} (r_pos : sgn r ≃ 1)
    : have : AP (r ≄ 0) := AP.mk (nonzero_if_pos ‹sgn r ≃ 1›)
      sgn (p/r - q/r) ≃ sgn (p - q)
    := by
  intro (_ : AP (r ≄ 0))
  show sgn (p/r - q/r) ≃ sgn (p - q)

  have : sgn (r⁻¹) ≃ 1 := Rel.trans sgn_recip ‹sgn r ≃ 1›
  calc
    _ ≃ sgn (p/r - q/r)         := Rel.refl
    _ ≃ sgn (p * r⁻¹ - q * r⁻¹) := by srw [div_mul_recip, div_mul_recip]
    _ ≃ sgn (p - q)             := sgn_sub_cancelR_mul_pos this

/--
Removing a common negative right factor from a difference of two rational
numbers will leave the difference's sign value unchanged only if its remaining
operands are swapped.

This is a useful lemma for proving properties of ordering relations, which are
defined using signs of differences.

**Property intuition**: The negative divisor reflects the two numbers across
zero, reversing their relative ordering. (Their magnitudes may also be scaled,
but that doesn't affect order.) That inverts the sign of their difference; swap
the operands to compensate.

**Proof intuition**: Convert the divisions to multiplication by reciprocals.
The reciprocals of negative numbers are negative. Delegate to the
multiplicative version of this property.
-/
theorem sgn_sub_cancelR_div_neg
    {p q r : ℚ} (r_neg : sgn r ≃ -1)
    : have : AP (r ≄ 0) := AP.mk (nonzero_if_neg ‹sgn r ≃ -1›)
      sgn (p/r - q/r) ≃ sgn (q - p)
    := by
  intro (_ : AP (r ≄ 0))
  have : sgn (r⁻¹) ≃ -1 := Rel.trans sgn_recip ‹sgn r ≃ -1›
  calc
    _ ≃ sgn (p/r - q/r)         := Rel.refl
    _ ≃ sgn (p * r⁻¹ - q * r⁻¹) := by srw [div_mul_recip, div_mul_recip]
    _ ≃ sgn (q - p)             := sgn_sub_cancelR_mul_neg this

end Lean4Axiomatic.Rational

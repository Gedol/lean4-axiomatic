import Lean4Axiomatic.Rational.Reciprocation

/-! # Rational numbers: sign -/

namespace Lean4Axiomatic.Rational

open Logic (AP)
open Signed (Negative Positive sgn)

/--
Operations pertaining to rational number signedness.

The operation names are prefixed with underscores so that they don't conflict
with the standard names. This allows the standard names to be used unqualified,
without a namespace prefix.
-/
class Sign.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] (ℚ : Type)
    :=
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
    :=
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

/-- All rational number sign axioms. -/
class Sign
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    :=
  toOps : Sign.Ops (ℤ := ℤ) ℚ
  toProps : Sign.Props ℚ

attribute [instance] Sign.toOps
attribute [instance] Sign.toProps

/-! ## Derived properties -/

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Reciprocation ℚ] [Division ℚ] [Sign ℚ]

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
      sgn p             ≃ _ := sgn_subst ‹p ≃ 0›
      sgn ((0 : ℤ) : ℚ) ≃ _ := sgn_from_integer
      sgn (0 : ℤ)       ≃ _ := Integer.sgn_zero.mp Rel.refl
      0                 ≃ _ := Rel.refl
  case mpr =>
    exact Sign.Props.sgn_zero_only_for_zero

/--
Taking both the `sgn` and negation of a rational number can be done in either
order.

See `Integer.sgn_compat_neg` for intuition.
-/
theorem sgn_compat_neg {p : ℚ} : sgn (-p) ≃ -(sgn p) := by
  have : sgn (-1 : ℤ) ≃ -1 := Integer.sgn_negative.mp Integer.neg_one_negative
  have neg_coe : (-1 : ℚ) ≃ ((-1 : ℤ) : ℚ) := eqv_symm neg_compat_from_integer
  calc
    sgn (-p)                   ≃ _ := sgn_subst (eqv_symm mul_neg_one)
    sgn (-1 * p)               ≃ _ := sgn_compat_mul
    sgn (-1 : ℚ) * sgn p       ≃ _ := AA.substL (sgn_subst neg_coe)
    sgn ((-1 : ℤ) : ℚ) * sgn p ≃ _ := AA.substL sgn_from_integer
    sgn (-1 : ℤ) * sgn p       ≃ _ := AA.substL ‹sgn (-1 : ℤ) ≃ -1›
    (-1) * sgn p               ≃ _ := Integer.mul_neg_one
    (-(sgn p))                 ≃ _ := Rel.refl

/--
The sign of a nonzero rational number is a square root of unity.

**Property and proof intuition**: The allowed sign values are `1`, `0`, and
`-1`; nonzero rationals have nonzero signs; `1` and `-1` are square roots of
unity.
-/
theorem sqrt1_sgn_nonzero {p : ℚ} [AP (p ≄ 0)] : Integer.Sqrt1 (sgn p) := by
  have : AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1) := sgn_trichotomy p
  have : sgn p ≃ 1 ∨ sgn p ≃ -1 :=
    match this with
    | AA.OneOfThree.first (_ : sgn p ≃ 0) =>
      have : p ≄ 0 := ‹AP (p ≄ 0)›.ev
      have : sgn p ≄ 0 := mt sgn_zero.mpr this
      absurd ‹sgn p ≃ 0› ‹sgn p ≄ 0›
    | AA.OneOfThree.second (_ : sgn p ≃ 1) =>
      Or.inl ‹sgn p ≃ 1›
    | AA.OneOfThree.third (_ : sgn p ≃ -1) =>
      Or.inr ‹sgn p ≃ -1›
  have : Integer.Sqrt1 (sgn p) := Integer.sqrt1_cases.mpr this
  exact this

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
  have : 1 ≃ sgn p * sgn p := Rel.symm sqrt1_sgn_nonzero.elim
  calc
    sgn (p⁻¹)                   ≃ _ := Rel.symm AA.identR
    sgn (p⁻¹) * 1               ≃ _ := AA.substR ‹1 ≃ sgn p * sgn p›
    sgn (p⁻¹) * (sgn p * sgn p) ≃ _ := AA.substR (Rel.symm sgn_compat_mul)
    sgn (p⁻¹) * sgn (p * p)     ≃ _ := Rel.symm sgn_compat_mul
    sgn (p⁻¹ * (p * p))         ≃ _ := sgn_subst (eqv_symm mul_assoc)
    sgn ((p⁻¹ * p) * p)         ≃ _ := sgn_subst (mul_substL mul_inverseL)
    sgn (1 * p)                 ≃ _ := sgn_subst mul_identL
    sgn p                       ≃ _ := Rel.refl

/--
The sign of a fraction formed from integers is the product of the integers'
signs.

**Property and proof intuition**: Division is multiplication by a reciprocal,
and since reciprocal preserves signs, it can be ignored.
-/
theorem sgn_div_integers
    {a b : ℤ} [Integer.Nonzero b] : sgn ((a : ℚ) / (b : ℚ)) ≃ sgn a * sgn b
    := calc
  sgn ((a : ℚ) / (b : ℚ))       ≃ _ := sgn_subst div_mul_recip
  sgn ((a : ℚ) * (b : ℚ)⁻¹)     ≃ _ := sgn_compat_mul
  sgn (a : ℚ) * sgn ((b : ℚ)⁻¹) ≃ _ := AA.substR sgn_recip
  sgn (a : ℚ) * sgn (b : ℚ)     ≃ _ := AA.substL sgn_from_integer
  sgn a * sgn (b : ℚ)           ≃ _ := AA.substR sgn_from_integer
  sgn a * sgn b                 ≃ _ := Rel.refl

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
  have (AsRatio.intro (a : ℤ) (b : ℤ) (_ : Integer.Nonzero b) eqv) :=
    as_ratio p
  have : p ≃ a/b := eqv
  calc
    sgn (sgn p)               ≃ _ := Integer.sgn_subst (sgn_subst ‹p ≃ a/b›)
    sgn (sgn ((a : ℚ)/b))     ≃ _ := Integer.sgn_subst sgn_div_integers
    sgn (sgn a * sgn b)       ≃ _ := Integer.sgn_compat_mul
    sgn (sgn a) * sgn (sgn b) ≃ _ := AA.substL Integer.sgn_idemp
    sgn a * sgn (sgn b)       ≃ _ := AA.substR Integer.sgn_idemp
    sgn a * sgn b             ≃ _ := Rel.symm sgn_div_integers
    sgn ((a : ℚ)/b)           ≃ _ := sgn_subst (eqv_symm ‹p ≃ a/b›)
    sgn p                     ≃ _ := Rel.refl

/--
The square of a rational number is nonnegative.

**Property intuition**: The product of two negative numbers is positive, and
zero times anything is zero, so this must be true.

**Proof intuition**: Assume that the square is negative and reach a
contradiction. The sign of the number being squared must be nonzero, otherwise
its square would have a sign of zero. We also know that the square of the sign
is `-1`. If two nonzero signs have a negative product, then they must be
distinct -- but in this case that means the sign is distinct from itself.
Contradiction.
-/
theorem nonneg_square {p : ℚ} : sgn (p * p) ≄ -1 := by
  intro (_ : sgn (p * p) ≃ -1)
  show False
  have : sgn p * sgn p ≃ -1 :=
    Rel.trans (Rel.symm sgn_compat_mul) ‹sgn (p * p) ≃ -1›
  have : Integer.Nonzero (-1 : ℤ) := Integer.nonzero_sqrt1
  have : Integer.Nonzero (sgn p * sgn p) :=
    Integer.nonzero_subst (Rel.symm ‹sgn p * sgn p ≃ -1›) this
  have (And.intro (_ : Integer.Nonzero (sgn p)) _) :=
    Integer.nonzero_factors_if_nonzero_product this
  have : Integer.Sqrt1 (sgn (sgn p)) :=
    Integer.sgn_nonzero.mp ‹Integer.Nonzero (sgn p)›
  have : Integer.Sqrt1 (sgn p) := Integer.sqrt1_subst sgn_idemp this
  have : sgn p ≄ sgn p := Integer.mul_sqrt1_neqv.mp ‹sgn p * sgn p ≃ -1›
  exact absurd Rel.refl this

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
      p * q ≃ _ := mul_substL ‹p ≃ 0›
      0 * q ≃ _ := mul_absorbL
      0     ≃ _ := eqv_refl
    | Or.inr (_ : q ≃ 0) => calc
      p * q ≃ _ := mul_substR ‹q ≃ 0›
      p * 0 ≃ _ := mul_absorbR
      0     ≃ _ := eqv_refl

/--
The product of nonzero rational numbers is nonzero.

**Property and proof intuition**: This is essentially the contrapositive of
`mul_split_zero`.
-/
theorem mul_preserves_nonzero {p q : ℚ} : p ≄ 0 → q ≄ 0 → p * q ≄ 0 := by
  intro (_ : p ≄ 0) (_ : q ≄ 0)
  show p * q ≄ 0
  have : p ≄ 0 ∧ q ≄ 0 := And.intro ‹p ≄ 0› ‹q ≄ 0›
  have : ¬(p ≃ 0 ∨ q ≃ 0) := Logic.not_or_iff_and_not.mpr this
  have : p * q ≄ 0 := mt mul_split_zero.mp this
  exact this

/--
Enables clean syntax when taking reciprocals of, or dividing by, products.
-/
instance mul_preserves_nonzero_inst
    {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] : AP (p * q ≄ 0)
    :=
  AP.mk (mul_preserves_nonzero ‹AP (p ≄ 0)›.ev ‹AP (q ≄ 0)›.ev)

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
  have inv_p : 1 ≃ p * p⁻¹ := eqv_symm mul_inverseR
  have inv_q : 1 ≃ q * q⁻¹ := eqv_symm mul_inverseR
  have swap_middle : (p * p⁻¹) * (q * q⁻¹) ≃ (p * q) * (p⁻¹ * q⁻¹) :=
    AA.expr_xxfxxff_lr_swap_rl
  calc
    (p * q)⁻¹                           ≃ _ := eqv_symm mul_identR
    (p * q)⁻¹ * 1                       ≃ _ := mul_substR (eqv_symm mul_identR)
    (p * q)⁻¹ * (1 * 1)                 ≃ _ := mul_substR (mul_substL inv_p)
    (p * q)⁻¹ * ((p * p⁻¹) * 1)         ≃ _ := mul_substR (mul_substR inv_q)
    (p * q)⁻¹ * ((p * p⁻¹) * (q * q⁻¹)) ≃ _ := mul_substR swap_middle
    (p * q)⁻¹ * ((p * q) * (p⁻¹ * q⁻¹)) ≃ _ := eqv_symm mul_assoc
    ((p * q)⁻¹ * (p * q)) * (p⁻¹ * q⁻¹) ≃ _ := mul_substL mul_inverseL
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
  (-p)⁻¹       ≃ _ := recip_subst (eqv_symm mul_neg_one)
  (-1 * p)⁻¹   ≃ _ := recip_compat_mul
  (-1)⁻¹ * p⁻¹ ≃ _ := mul_substL recip_sqrt1
  (-1) * p⁻¹   ≃ _ := mul_neg_one
  (-p⁻¹)       ≃ _ := eqv_refl

/--
Negation can be moved between the "outside" of a division operation and the
"inside", specifically its left operand.

**Property and proof intuition**: The same property holds for multiplication,
and division is a form of multiplication.
-/
theorem neg_scompatL_div {p q : ℚ} [AP (q ≄ 0)] : -(p / q) ≃ (-p) / q := calc
  (-(p / q))   ≃ _ := neg_subst div_mul_recip
  (-(p * q⁻¹)) ≃ _ := neg_scompatL_mul
  (-p) * q⁻¹   ≃ _ := eqv_symm div_mul_recip
  (-p) / q     ≃ _ := eqv_refl

/--
Negation can be moved between the "outside" of a division operation and the
"inside", specifically its right operand.

**Property and proof intuition**: Division is the multiplication of the left
operand with the reciprocal of the right operand. Negation can be moved from
the "outside" to the "inside" of both reciprocation and multiplication.
-/
theorem neg_scompatR_div {p q : ℚ} [AP (q ≄ 0)] : -(p / q) ≃ p / (-q) := calc
  (-(p / q))   ≃ _ := neg_subst div_mul_recip
  (-(p * q⁻¹)) ≃ _ := neg_scompatR_mul
  p * -(q⁻¹)   ≃ _ := mul_substR (eqv_symm recip_compat_neg)
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
  (-(p / -q))   ≃ _ := neg_subst (eqv_symm neg_scompatR_div)
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
    : (a : ℚ)/b + (c : ℚ)/d ≃ ((a * d + b * c : ℤ) : ℚ)/((b * d : ℤ) : ℚ)
    := by
  let aQ := (a : ℚ); let bQ := (b : ℚ); let cQ := (c : ℚ); let dQ := (d : ℚ)
  calc
    aQ/bQ + cQ/dQ
      ≃ _ := add_substL div_mul_recip
    aQ * bQ⁻¹ + cQ/dQ
      ≃ _ := add_substR div_mul_recip
    aQ * bQ⁻¹ + cQ * dQ⁻¹
      ≃ _ := add_substL (eqv_symm mul_identR)
    aQ * bQ⁻¹ * 1 + cQ * dQ⁻¹
      ≃ _ := add_substL (mul_substR (eqv_symm mul_inverseR))
    aQ * bQ⁻¹ * (dQ * dQ⁻¹) + cQ * dQ⁻¹
      ≃ _ := add_substL AA.expr_xxfxxff_lr_swap_rl
    aQ * dQ * (bQ⁻¹ * dQ⁻¹) + cQ * dQ⁻¹
      ≃ _ := add_substL (mul_substR (eqv_symm recip_compat_mul))
    aQ * dQ * (bQ * dQ)⁻¹ + cQ * dQ⁻¹
      ≃ _ := add_substR (eqv_symm mul_identR)
    aQ * dQ * (bQ * dQ)⁻¹ + cQ * dQ⁻¹ * 1
      ≃ _ := add_substR (mul_substR (eqv_symm mul_inverseL))
    aQ * dQ * (bQ * dQ)⁻¹ + cQ * dQ⁻¹ * (bQ⁻¹ * bQ)
      ≃ _ := add_substR AA.expr_xxfxxff_lr_swap_rr
    aQ * dQ * (bQ * dQ)⁻¹ + cQ * bQ * (bQ⁻¹ * dQ⁻¹)
      ≃ _ := add_substR (mul_substL mul_comm)
    aQ * dQ * (bQ * dQ)⁻¹ + bQ * cQ * (bQ⁻¹ * dQ⁻¹)
      ≃ _ := add_substR (mul_substR (eqv_symm recip_compat_mul))
    aQ * dQ * (bQ * dQ)⁻¹ + bQ * cQ * (bQ * dQ)⁻¹
      ≃ _ := eqv_symm mul_distribR
    (aQ * dQ + bQ * cQ) * (bQ * dQ)⁻¹
      ≃ _ := mul_substL (add_substL (eqv_symm mul_compat_from_integer))
    ((a * d : ℤ) + bQ * cQ) * (bQ * dQ)⁻¹
      ≃ _ := mul_substL (add_substR (eqv_symm mul_compat_from_integer))
    ((a * d : ℤ) + (b * c : ℤ)) * (bQ * dQ)⁻¹
      ≃ _ := mul_substL (eqv_symm add_compat_from_integer)
    (a * d + b * c : ℤ) * (bQ * dQ)⁻¹
      ≃ _ := mul_substR (recip_subst (eqv_symm mul_compat_from_integer))
    (a * d + b * c : ℤ) * ((b * d : ℤ) : ℚ)⁻¹
      ≃ _ := eqv_symm div_mul_recip
    ((a * d + b * c : ℤ) : ℚ)/((b * d : ℤ) : ℚ)
      ≃ _ := eqv_refl

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
  have (AsRatio.intro (a : ℤ) (b : ℤ) (_ : Integer.Nonzero b) p_eqv) :=
    as_ratio p
  have (AsRatio.intro (c : ℤ) (d : ℤ) (_ : Integer.Nonzero d) q_eqv) :=
    as_ratio q
  have : p ≃ a/b := p_eqv
  have : q ≃ c/d := q_eqv
  have : Integer.Sqrt1 (sgn b) := Integer.sgn_nonzero.mp ‹Integer.Nonzero b›
  have : Integer.Sqrt1 (sgn d) := Integer.sgn_nonzero.mp ‹Integer.Nonzero d›
  have : sgn (a * b) ≃ s := calc
    sgn (a * b)     ≃ _ := Integer.sgn_compat_mul
    sgn a * sgn b   ≃ _ := Rel.symm sgn_div_integers
    sgn ((a : ℚ)/b) ≃ _ := sgn_subst (eqv_symm ‹p ≃ a/b›)
    sgn p           ≃ _ := ‹sgn p ≃ s›
    s               ≃ _ := Rel.refl
  have : sgn (c * d) ≃ s := calc
    sgn (c * d)     ≃ _ := Integer.sgn_compat_mul
    sgn c * sgn d   ≃ _ := Rel.symm sgn_div_integers
    sgn ((c : ℚ)/d) ≃ _ := sgn_subst (eqv_symm ‹q ≃ c/d›)
    sgn q           ≃ _ := ‹sgn q ≃ s›
    s               ≃ _ := Rel.refl
  have sgn_abdd : sgn (a * b * (d * d)) ≃ s := calc
    sgn (a * b * (d * d))     ≃ _ := Integer.sgn_compat_mul
    sgn (a * b) * sgn (d * d) ≃ _ := AA.substL ‹sgn (a * b) ≃ s›
    s * sgn (d * d)           ≃ _ := AA.substR Integer.sgn_compat_mul
    s * (sgn d * sgn d)       ≃ _ := AA.substR ‹Integer.Sqrt1 (sgn d)›.elim
    s * 1                     ≃ _ := AA.identR
    s                         ≃ _ := Rel.refl
  have sgn_bbcd : sgn (b * b * (c * d)) ≃ s := calc
    sgn (b * b * (c * d))     ≃ _ := Integer.sgn_compat_mul
    sgn (b * b) * sgn (c * d) ≃ _ := AA.substR ‹sgn (c * d) ≃ s›
    sgn (b * b) * s           ≃ _ := AA.substL Integer.sgn_compat_mul
    sgn b * sgn b * s         ≃ _ := AA.substL ‹Integer.Sqrt1 (sgn b)›.elim
    1 * s                     ≃ _ := AA.identL
    s                         ≃ _ := Rel.refl
  have : sgn (p + q) ≃ s := calc
    sgn (p + q)
      ≃ _ := sgn_subst (add_substL ‹p ≃ a/b›)
    sgn ((a : ℚ)/b + q)
      ≃ _ := sgn_subst (add_substR ‹q ≃ c/d›)
    sgn ((a : ℚ)/b + (c : ℚ)/d)
      ≃ _ := sgn_subst add_div_integers
    sgn (((a * d + b * c : ℤ) : ℚ)/((b * d : ℤ) : ℚ))
      ≃ _ := sgn_div_integers
    sgn (a * d + b * c) * sgn (b * d)
      ≃ _ := Rel.symm Integer.sgn_compat_mul
    sgn ((a * d + b * c) * (b * d))
      ≃ _ := Integer.sgn_subst AA.distribR
    sgn (a * d * (b * d) + b * c * (b * d))
      ≃ _ := Integer.sgn_subst (AA.substL AA.expr_xxfxxff_lr_swap_rl)
    sgn (a * b * (d * d) + b * c * (b * d))
      ≃ _ := Integer.sgn_subst (AA.substR AA.expr_xxfxxff_lr_swap_rl)
    sgn (a * b * (d * d) + b * b * (c * d))
      ≃ _ := Integer.add_preserves_sign sgn_abdd sgn_bbcd
    s
      ≃ _ := Rel.refl
  exact this

end Lean4Axiomatic.Rational

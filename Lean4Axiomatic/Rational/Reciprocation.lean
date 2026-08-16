import Lean4Axiomatic.Rational.Negation

/-! # Rational numbers: reciprocation and division -/

namespace Lean4Axiomatic.Rational

open Logic (AP)

/-- Operations pertaining to rational number reciprocation. -/
class Reciprocation.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ]
    where
  /-- Reciprocation of rational numbers. -/
  reciprocal (p : ℚ) [AP (p ≄ 0)] : ℚ

export Reciprocation.Ops (reciprocal)

/-- Enables the use of the `·⁻¹` operator for reciprocation. -/
postfix:120 "⁻¹" => reciprocal

/--
Implementation of floating-point notation for rational numbers.

The input parameters are specified by Lean's `OfScientific.ofScientific` class
and field.

**Intuition**: Let's define a value `expSign := if exponentIsNegative then -1
else 1`. Then this function computes
`mantissa * 10 ^ (expSign * decimalExponent)`. Exponentiation isn't defined for
rational numbers at this point, so we compute `10 ^ decimalExponent` in the
naturals and take its reciprocal if `exponentIsNegative`. This requires a proof
that `10 ^ decimalExponent` is never zero.
-/
def of_scientific
    {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation.Ops ℚ]
    (mantissa : Nat) (exponentIsNegative : Bool) (decimalExponent : Nat) : ℚ
    :=
  let naturalMantissa : ℕ := OfNat.ofNat mantissa
  let naturalDecimalExponent : ℕ := OfNat.ofNat decimalExponent
  let powTen := (10:ℕ) ^ naturalDecimalExponent

  have : (1:ℕ) ≄ 0 := Natural.one_neqv_zero
  have : AP ((1:ℕ) ≄ 0) := AP.mk this

  have : Natural.step 9 ≄ 0 := Natural.step_neqv_zero
  have : (10:ℕ) ≄ 0 := by prw [←Natural.literal_step] this
  have : AP (powTen ≄ 0) := AP.mk (Natural.pow_preserves_nonzero_base this)
  let rationalPowTen : ℚ := if exponentIsNegative then powTen⁻¹ else powTen

  naturalMantissa * rationalPowTen

/--
Enables the use of scientific-notation literals for rational numbers.

It's given a higher default instance priority than the built-in `Float` type.
-/
@[default_instance mid+2]
instance of_scientific_inst
    {ℕ ℤ ℚ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation.Ops ℚ]
    : OfScientific ℚ
    := {
  ofScientific := of_scientific
}

/-- Properties of rational number reciprocation. -/
class Reciprocation.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Ops ℚ]
    where
  /-- Reciprocation respects equivalence over its operand. -/
  recip_subst {p₁ p₂ : ℚ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁⁻¹ ≃ p₂⁻¹

  /-- The reciprocal of a value is its left multiplicative inverse. -/
  mul_inverseL {p : ℚ} [AP (p ≄ 0)] : p⁻¹ * p ≃ 1

  /-- The reciprocal of a value is its right multiplicative inverse. -/
  mul_inverseR {p : ℚ} [AP (p ≄ 0)] : p * p⁻¹ ≃ 1

export Reciprocation.Props (mul_inverseL mul_inverseR recip_subst)

attribute [gcongr] recip_subst

/-- All rational number reciprocation axioms. -/
class Reciprocation
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    where
  toOps : Reciprocation.Ops ℚ
  toProps : Reciprocation.Props ℚ

attribute [implicit_reducible, instance] Reciprocation.toOps
attribute [instance] Reciprocation.toProps

/-- Operations pertaining to rational number division. -/
class Division.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ]
    where
  /-- Division of rational numbers. -/
  div (p q : ℚ) [AP (q ≄ 0)] : ℚ

export Division.Ops (div)

/--
Enables the use of the `· / ·` operator for division.

We define the operator syntax directly here, instead of using the `Div` class
from the standard library. This is because our `div` operation has an extra
argument, an instance expressing that the divisor must be nonzero. The `Div`
class only provides a simple binary operation for its `div`.

Defined with high priority to avoid conflicts with `Div`'s syntax.
-/
infixl:70 (priority := high) " / " => div

/-- Properties of rational number division. -/
class Division.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation ℚ]
      [Ops ℚ]
    where
  /--
  Division is equivalent to multiplication by the reciprocal of the second
  argument.
  -/
  div_mul_recip {p q : ℚ} [AP (q ≄ 0)] : p / q ≃ p * q⁻¹

export Division.Props (div_mul_recip)

/-- All rational number division axioms. -/
class Division
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation ℚ]
    where
  toOps : Division.Ops ℚ
  toProps : Division.Props ℚ

attribute [implicit_reducible, instance] Division.toOps
attribute [instance] Division.toProps

/-! ## Derived properties -/

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type}
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation ℚ]

section neg_only
variable [Negation ℚ]

/--
Square roots of unity are their own reciprocals.

**Property intuition**: Taking the reciprocal of a number doesn't change its
sign, and the only fraction that would be unchanged when flipping it is `1/1`,
i.e. the rational number `1`. Thus `1` and `-1` should be the only numbers to
satisfy this property.

**Proof intuition**: The defining proprty of square roots of unity,
`s * s ≃ 1`, is cruical for this proof because it introduces two factors of
`s`. One of them gets canceled by the reciprocal, leaving the other as the
result.
-/
theorem recip_sqrt1 {s : ℚ} [Sqrt1 s] : s⁻¹ ≃ s := calc
  s⁻¹           ≃ _ := eqv_symm mul_identL
  1 * s⁻¹       ≃ _ := by srw [←‹Sqrt1 s›.elim]
  (s * s) * s⁻¹ ≃ _ := mul_assoc
  s * (s * s⁻¹) ≃ _ := by srw [mul_inverseR]
  s * 1         ≃ _ := mul_identR
  s             ≃ _ := eqv_refl

/--
The reciprocal of a nonzero rational is itself nonzero.

**Property and proof intuition**: For `p * p⁻¹ ≃ 1` to hold, neither factor can
be zero.
-/
theorem recip_nonzero {p : ℚ} [AP (p ≄ 0)] : p⁻¹ ≄ 0 := by
  intro (_ : p⁻¹ ≃ 0)
  show False
  have : p ≃ 0 := calc
    _ ≃ p             := eqv_refl
    _ ≃ p * 1         := eqv_symm mul_identR
    _ ≃ p * (p * p⁻¹) := by srw [←mul_inverseR]
    _ ≃ 0             := by srw [‹p⁻¹ ≃ 0›, mul_absorbR, mul_absorbR]
  exact absurd ‹p ≃ 0› ‹AP (p ≄ 0)›.ev

/--
Instance equivalent of `recip_nonzero`.

Enables easy syntax for nested reciprocals, or reciprocals in denominators.
-/
instance recip_nonzero_inst {p : ℚ} [AP (p ≄ 0)] : AP (p⁻¹ ≄ 0) :=
  AP.mk recip_nonzero

/--
Double reciprocation is idempotent.

**Property intuition**: "Flipping over" a fraction twice brings back the
original fraction.

**Proof intuition**: Uses multiplicative inverse twice: first to introduce `p`
and `p⁻¹`, then to cancel `p⁻¹` and `(p⁻¹)⁻¹`, leaving `p` behind.
-/
theorem recip_idemp {p : ℚ} [AP (p ≄ 0)] : (p⁻¹)⁻¹ ≃ p := calc
  _ ≃ (p⁻¹)⁻¹             := eqv_refl
  _ ≃ 1 * (p⁻¹)⁻¹         := eqv_symm mul_identL
  _ ≃ (p * p⁻¹) * (p⁻¹)⁻¹ := by srw [←mul_inverseR]
  _ ≃ p * (p⁻¹ * (p⁻¹)⁻¹) := mul_assoc
  _ ≃ p * 1               := by srw [mul_inverseR]
  _ ≃ p                   := mul_identR

end neg_only
section div_only
variable [Division ℚ]

/--
Division respects equivalence over its left operand.

**Property intuition**: Necessary for division to be a valid function on
rational numbers.

**Proof intuition**: The left operand of division is also the left operand of
the underlying multiplication, which is already known to obey the substitution
property.
-/
@[gcongr]
theorem div_substL {p₁ p₂ q : ℚ} [AP (q ≄ 0)] : p₁ ≃ p₂ → p₁ / q ≃ p₂ / q := by
  intro (_ : p₁ ≃ p₂)
  show p₁ / q ≃ p₂ / q
  calc
    p₁ / q   ≃ _ := div_mul_recip
    p₁ * q⁻¹ ≃ _ := by srw [‹p₁ ≃ p₂›]
    p₂ * q⁻¹ ≃ _ := eqv_symm div_mul_recip
    p₂ / q   ≃ _ := eqv_refl

/--
Division respects equivalence over its right operand.

**Property intuition**: Necessary for division to be a valid function on
rational numbers.

**Proof intuition**: Division's right operand's reciprocal is the underlying
multiplication's right operand. Multiplication and reciprocation are already
known to obey the substitution property.
-/
@[gcongr]
theorem div_substR
    {p₁ p₂ q : ℚ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → q / p₁ ≃ q / p₂
    := by
  intro (_ : p₁ ≃ p₂)
  show q / p₁ ≃ q / p₂
  calc
    q / p₁   ≃ _ := div_mul_recip
    q * p₁⁻¹ ≃ _ := by srw [‹p₁ ≃ p₂›]
    q * p₂⁻¹ ≃ _ := eqv_symm div_mul_recip
    q / p₂   ≃ _ := eqv_refl

/--
Dividing one by a rational number gives that number's reciprocal.

**Property intuition**: Multiplying `p` by `1/p` gives `1`, exactly the same as
multiplying by `p⁻¹`.

**Proof intuition**: Expand division into multiplication by reciprocal. The
factor of one disappears, leaving the result.
-/
theorem div_identL {p : ℚ} [AP (p ≄ 0)] : 1/p ≃ p⁻¹ := calc
  _ ≃ 1/p     := eqv_refl
  _ ≃ 1 * p⁻¹ := div_mul_recip
  _ ≃ p⁻¹     := mul_identL

/--
Dividing a rational number by itself gives one.

**Property and proof intuition**: Self-division is equivalent to multiplication
by the reciprocal, which always gives one.
-/
theorem div_same {p : ℚ} [AP (p ≄ 0)] : p/p ≃ 1 := calc
  _ ≃ p/p     := eqv_refl
  _ ≃ p * p⁻¹ := div_mul_recip
  _ ≃ 1       := mul_inverseR

/--
Two rational numbers are equivalent if and only if their quotient is one.

**Property intuition**: A fraction with a numerator less than its denominator
is less than one; with a numerator greater than its denominator, greater than
one.

**Proof intuition**: The reverse direction trivially follows from `div_same`.
The forward direction uses the hypothesis `p/q ≃ 1` and the property
`q⁻¹ * q ≃ 1` to cancel out `p`, leaving `q` behind.
-/
theorem div_eqv_1 {p q : ℚ} [AP (q ≄ 0)] : p/q ≃ 1 ↔ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (_ : p/q ≃ 1)
    show p ≃ q
    calc
      _ ≃ p             := eqv_refl
      _ ≃ p * 1         := eqv_symm mul_identR
      _ ≃ p * (q⁻¹ * q) := by srw [←mul_inverseL]
      _ ≃ (p * q⁻¹) * q := eqv_symm mul_assoc
      _ ≃ (p/q) * q     := by srw [←div_mul_recip]
      _ ≃ 1 * q         := by srw [‹p/q ≃ 1›]
      _ ≃ q             := mul_identL
  case mpr =>
    intro (_ : p ≃ q)
    show p/q ≃ 1
    calc
      _ ≃ p/q := eqv_refl
      _ ≃ q/q := by srw [‹p ≃ q›]
      _ ≃ 1   := div_same

/--
Division by a rational number distributes over addition of rational numbers.

**Property intuition**: The result of the division is the same, whether the
numbers are added before dividing them or after.

**Proof intuition**: Expand division into multiplication by a reciprocal. The
reciprocal factor distributes over addition. Then convert the two terms back to
division.
-/
theorem div_distribR {p q r : ℚ} [AP (r ≄ 0)] : (p + q)/r ≃ p/r + q/r := calc
  _ = (p + q)/r         := rfl
  _ ≃ (p + q) * r⁻¹     := div_mul_recip
  _ ≃ p * r⁻¹ + q * r⁻¹ := mul_distribR
  _ ≃ p/r + q/r         := by srw [←div_mul_recip, ←div_mul_recip]

end div_only
variable [Negation ℚ] [Division ℚ]

/--
Dividing a rational number by one gives that number back.

**Property intuition**: Dividing a quantity into a single piece has no effect.

**Proof intuition**: Expand division into multiplication by reciprocal. The
reciprocal of one is one, which disappears, leaving the original number.
-/
theorem div_identR {p : ℚ} : p/1 ≃ p := calc
  _ ≃ p/1         := eqv_refl
  _ ≃ p * (1:ℚ)⁻¹ := div_mul_recip
  _ ≃ p * 1       := by srw [recip_sqrt1]
  _ ≃ p           := mul_identR

/--
Negation can be moved between the "outside" of a division operation and the
"inside", specifically its left operand.

**Property and proof intuition**: The same property holds for multiplication,
and division is a form of multiplication.
-/
theorem neg_scompatL_div {p q : ℚ} [AP (q ≄ 0)] : -(p / q) ≃ (-p) / q := calc
  (-(p / q))   ≃ _ := by srw [div_mul_recip]
  (-(p * q⁻¹)) ≃ _ := neg_scompatL_mul
  (-p) * q⁻¹   ≃ _ := eqv_symm div_mul_recip
  (-p) / q     ≃ _ := eqv_refl

end Lean4Axiomatic.Rational

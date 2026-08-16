import Lean4Axiomatic.Rational.Impl.Fraction.Negation
import Lean4Axiomatic.Rational.Sign

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Logic (AP)
open Signed (Negative Positive sgn)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/-! ## Fraction signedness -/

/--
Implementation of signum for integer fractions.

The `Fraction` data structure was designed specifically to make this definition
simple. The denominator is positive, so the numerator is what determines the
sign of the fraction. This emphasizes that fractions are an integer (the
numerator) that has been scaled down in size by a factor (the denominator).
-/
def _sgn (p : Fraction ℤ) : ℤ := sgn p.numerator

/--
Implementation of a predicate for positive integer fractions.

The easiest definition is to delegate to the signum function.
-/
def _Positive (p : Fraction ℤ) : Prop := _sgn p ≃ 1

/--
Implementation of a predicate for negative integer fractions.

The easiest definition is to delegate to the signum function.
-/
def _Negative (p : Fraction ℤ) : Prop := _sgn p ≃ -1

instance sign_ops : Sign.Ops (ℤ := ℤ) (Fraction ℤ) := {
  _sgn := _sgn
  _Positive := _Positive
  _Negative := _Negative
}

/--
The signum function respects integer fraction equivalence.

**Property intuition**: This is necessary for `sgn` to be a function on integer
fractions.

**Proof intuition**: Expand the fraction definitions and `sgn` on fractions to
obtain integer expressions. Then use integer `sgn` properties and algebra.
-/
@[gcongr]
theorem sgn_subst {p₁ p₂ : Fraction ℤ} : p₁ ≃ p₂ → sgn p₁ ≃ sgn p₂ := by
  revert p₁; intro (a//b); let p₁ := a//b
  revert p₂; intro (c//d); let p₂ := c//d
  intro (_ : p₁ ≃ p₂)
  show sgn p₁ ≃ sgn p₂

  have : a//b ≃ c//d := ‹p₁ ≃ p₂›
  have : a * d ≃ c * b := ‹a//b ≃ c//d›
  have : Positive b := ‹AP (Positive b)›.ev
  have : sgn b ≃ 1 := Integer.sgn_positive.mp this
  have : Positive d := ‹AP (Positive d)›.ev
  have : sgn d ≃ 1 := Integer.sgn_positive.mp this
  calc
    _ = sgn p₁        := rfl
    _ = sgn (a//b)    := rfl
    _ = sgn a         := rfl
    _ ≃ sgn a * 1     := Rel.symm AA.identR
    _ ≃ sgn a * sgn d := by srw [←‹sgn d ≃ 1›]
    _ ≃ sgn (a * d)   := Rel.symm Integer.sgn_compat_mul
    _ ≃ sgn (c * b)   := by srw [‹a * d ≃ c * b›]
    _ ≃ sgn c * sgn b := Integer.sgn_compat_mul
    _ ≃ sgn c * 1     := by srw [‹sgn b ≃ 1›]
    _ ≃ sgn c         := AA.identR
    _ = sgn (c//d)    := rfl
    _ = sgn p₂        := rfl

/--
Fractions that are equivalent to zero are the only ones with sign zero.

**Property and proof intuition**: The sign of a fraction is the sign of its
numerator; this property also holds for integers; fractions with zero-valued
numerators are equivalent to zero.
-/
theorem sgn_zero_only_for_zero {p : Fraction ℤ} : sgn p ≃ 0 → p ≃ 0 := by
  intro (_ : sgn p ≃ 0)
  show p ≃ 0
  have : sgn p.numerator ≃ 0 := ‹sgn p ≃ 0›
  have : p.numerator ≃ 0 := Integer.sgn_zero.mp this
  have : p ≃ 0 := eqv_zero_iff_numerator_eqv_zero.mpr this
  exact this

/--
The fraction equivalent of an integer has the same sign.

**Property intuition**: This must be true for the fraction to be a faithful
representation of the integer.

**Proof intuition**: True by definition of `sgn` for integer fractions.
-/
theorem sgn_from_integer {a : ℤ} : sgn (a : Fraction ℤ) ≃ sgn a := calc
  sgn (a : Fraction ℤ) ≃ _ := Rel.refl
  sgn (a//1)           ≃ _ := Rel.refl
  sgn a                ≃ _ := Rel.refl

/--
The `sgn` function is compatible with multiplication.

**Property intuition**: This holds for integers, so it should also hold for
fractions (which are just rescaled integers).

**Proof intuition**: Expand definitions to obtain the integer version of this
property.
-/
theorem sgn_compat_mul {p q : Fraction ℤ} : sgn (p * q) ≃ sgn p * sgn q := by
  revert p; intro (a//b); let p := a//b; revert q; intro (c//d); let q := c//d
  show sgn (p * q) ≃ sgn p * sgn q
  calc
    _ = sgn (p * q)             := rfl
    _ = sgn (a//b * c//d)       := rfl
    _ = sgn ((a * c)//(b * d))  := rfl
    _ = sgn (a * c)             := rfl
    _ ≃ sgn a * sgn c           := Integer.sgn_compat_mul
    _ = sgn (a//b) * sgn (c//d) := rfl
    _ = sgn p * sgn q           := rfl

/--
The sign of a fraction is `0`, `1`, or `-1`.

**Property intuition**: This is a fundamental fact about signs.

**Proof intuition**: Find the numerator's sign using the integer equivalent of
this property. The sign of the numerator is the sign of the entire fraction.
-/
theorem sgn_trichotomy
    (p : Fraction ℤ) : AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1)
    := by
  have
    : AA.OneOfThree
      (p.numerator ≃ 0)
      (Positive p.numerator)
      (Negative p.numerator)
    := (Integer.sign_trichotomy p.numerator).atLeastOne
  match this with
  | AA.OneOfThree.first (_ : p.numerator ≃ 0) =>
    have : sgn p ≃ 0 := calc
      sgn p           ≃ _ := Rel.refl
      sgn p.numerator ≃ _ := Integer.sgn_zero.mpr ‹p.numerator ≃ 0›
      0               ≃ _ := Rel.refl
    exact AA.OneOfThree.first this
  | AA.OneOfThree.second (_ : Positive p.numerator) =>
    have : sgn p ≃ 1 := calc
      sgn p           ≃ _ := Rel.refl
      sgn p.numerator ≃ _ := Integer.sgn_positive.mp ‹Positive p.numerator›
      1               ≃ _ := Rel.refl
    exact AA.OneOfThree.second this
  | AA.OneOfThree.third (_ : Negative p.numerator) =>
    have : sgn p ≃ -1 := calc
      sgn p           ≃ _ := Rel.refl
      sgn p.numerator ≃ _ := Integer.sgn_negative.mp ‹Negative p.numerator›
      (-1)            ≃ _ := Rel.refl
    exact AA.OneOfThree.third this

/--
Integer fractions are positive iff their sign is `1`.

**Property and proof intuition**: True by definition.
-/
theorem sgn_positive {p : Fraction ℤ} : Positive p ↔ sgn p ≃ 1 :=
  Iff.intro id id

/--
Integer fractions are negative iff their sign is `-1`.

**Property and proof intuition**: True by definition.
-/
theorem sgn_negative {p : Fraction ℤ} : Negative p ↔ sgn p ≃ -1 :=
  Iff.intro id id

instance sign_props : Sign.Props (Fraction ℤ) := {
  sgn_subst := sgn_subst
  sgn_zero_only_for_zero := sgn_zero_only_for_zero
  sgn_from_integer := sgn_from_integer
  sgn_compat_mul := sgn_compat_mul
  sgn_trichotomy := sgn_trichotomy
  sgn_positive := sgn_positive
  sgn_negative := sgn_negative
}

instance sign : Sign (Fraction ℤ) := {
  toOps := sign_ops
  toProps := sign_props
}

end Lean4Axiomatic.Rational.Impl.Fraction

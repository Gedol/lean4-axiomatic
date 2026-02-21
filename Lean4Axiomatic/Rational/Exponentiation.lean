import Lean4Axiomatic.Rational.Metric

/-!
# Rational numbers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Rational

open Lean4Axiomatic.Function (idx_fam_prop)
open Lean4Axiomatic.Logic (AP iff_subst_covar or_identR or_mapR)
open Lean4Axiomatic.Metric (abs)
open Lean4Axiomatic.Natural (pow_step pow_zero step)
open Lean4Axiomatic.Signed (Positive sgn)

/-! ## Derived properties for exponentiation to a natural number -/

section pow_nat

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (mul := (· * ·)) (ident := (1 : ℚ)) (minst := mul_monoid)]

/--
Casting an integer to a rational number is left-semicompatible with natural
number exponentiation.

In other words, starting from an integer value, the operations of (i) raising a
value to a natural number power, and (ii) converting an integer to a rational
number, can be done in either order and produce the same result.

**Property intuition**: Multiplication is compatible with integer-to-rational
conversion, so the base of exponentiation should also be compatible.

**Proof intuition**: By induction on the exponent. The zero case is trivial:
both sides reduce to `1` via `pow_zero`. The step case follows from `pow_step`
and `mul_compat_from_integer`.
-/
theorem pow_scompatL_from_integer {a : ℤ} {n : ℕ} : ((a^n:ℤ):ℚ) ≃ (a:ℚ)^n := by
  apply Natural.ind_on n
  case zero =>
    show ((a^0:ℤ):ℚ) ≃ (a:ℚ)^0
    calc
      _ = ((a^0:ℤ):ℚ) := rfl
      _ ≃ ((1:ℤ):ℚ)   := by srw [Natural.pow_zero]
      _ = 1           := rfl
      _ ≃ (a:ℚ)^0     := eqv_symm Natural.pow_zero
  case step =>
    intro (n' : ℕ) (ih : ((a^n':ℤ):ℚ) ≃ (a:ℚ)^n')
    show ((a^(step n'):ℤ):ℚ) ≃ (a:ℚ)^(step n')
    calc
      _ = ((a^(step n'):ℤ):ℚ)  := rfl
      _ ≃ ((a^n' * a : ℤ):ℚ)   := by srw [Natural.pow_step]
      _ ≃ ((a^n':ℤ):ℚ) * (a:ℚ) := mul_compat_from_integer
      _ ≃ (a:ℚ)^n' * (a:ℚ)     := by srw [ih]
      _ ≃ (a:ℚ)^(step n')      := eqv_symm Natural.pow_step

variable [Negation ℚ] [Sign ℚ]
section metric_only
variable [Subtraction ℚ] [Order ℚ] [Metric ℚ]

/--
Absolute value is semicompatible with the base argument of exponentiation.

**Property intuition**: Absolute value is compatible with multiplication, so
applying it to repeated multiplication means that it gets applied to every
factor in the expression.

**Proof intuition**: Induction and algebra.
-/
theorem pow_nat_scompatL_abs {p : ℚ} {n : ℕ} : abs (p^n) ≃ (abs p)^n := by
  apply Natural.ind_on n
  case zero =>
    show abs (p^0) ≃ (abs p)^0
    have : sgn (1:ℚ) ≃ 1 := sgn_one
    have : abs (1:ℚ) ≃ 1 := abs_positive this
    calc
      _ ≃ abs (p^0) := eqv_refl
      _ ≃ abs 1     := by srw [pow_zero]
      _ ≃ 1         := ‹abs (1:ℚ) ≃ 1›
      _ ≃ (abs p)^0 := eqv_symm pow_zero
  case step =>
    intro (n' : ℕ) (ih : abs (p^n') ≃ (abs p)^n')
    show abs (p^(step n')) ≃ (abs p)^(step n')
    calc
      _ ≃ abs (p^(step n'))  := eqv_refl
      _ ≃ abs (p^n' * p)     := by srw [pow_step]
      _ ≃ abs (p^n') * abs p := abs_compat_mul
      _ ≃ (abs p)^n' * abs p := by srw [ih]
      _ ≃ (abs p)^(step n')  := eqv_symm pow_step

end metric_only
variable [Reciprocation ℚ]

/--
Raising rationals to natural number powers is semicompatible with reciprocation
on the left operand.

**Property intuition**: Reciprocation and multiplication are compatible, so it
shouldn't matter if the multiplications for exponentiation happen first, or the
reciprocation.

**Proof intuition**: Use induction and the compatibility of multiplication and
reciprocation.
-/
theorem pow_scompatL_recip
    {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : (p^n)⁻¹ ≃ (p⁻¹)^n
    := by
  apply Natural.ind_on n
  case zero =>
    show (p^(0:ℕ))⁻¹ ≃ (p⁻¹)^(0:ℕ)
    calc
      _ = (p^(0:ℕ))⁻¹ := rfl
      _ ≃ 1⁻¹         := by srw [pow_zero]
      _ ≃ 1           := recip_sqrt1
      _ ≃ (p⁻¹)^(0:ℕ) := eqv_symm pow_zero
  case step =>
    intro (n' : ℕ) (ih : (p^n')⁻¹ ≃ (p⁻¹)^n')
    show (p^(step n'))⁻¹ ≃ (p⁻¹)^(step n')
    calc
      _ ≃ (p^(step n'))⁻¹ := eqv_refl
      _ ≃ (p^n' * p)⁻¹    := by srw [pow_step]
      _ ≃ (p^n')⁻¹ * p⁻¹  := recip_compat_mul
      _ ≃ (p⁻¹)^n' * p⁻¹  := by srw [ih]
      _ ≃ (p⁻¹)^(step n') := eqv_symm pow_step

variable [Division ℚ]

/--
A natural number exponent distributes over division.

**Property intuition**: The product of two fractions is the product of their
numerators over the product of their denominators. Exponentiation is repeated
multiplication, so we'd expect the same pattern to hold.

**Proof intuition**: Convert division to multiplication by the reciprocal. Then
distribute the exponent over multiplication, and commute it with reciprocation.
-/
theorem pow_distribR_div
    {p q : ℚ} [AP (q ≄ 0)] {n : ℕ} : (p / q)^n ≃ p^n / q^n
    := calc
  _ = (p / q)^n     := rfl
  _ ≃ (p * q⁻¹)^n   := by srw [div_mul_recip]
  _ ≃ p^n * (q⁻¹)^n := by
    letI : CA.Monoid.Monoid ℚ Mul.mul 1 := mul_monoid
    exact Natural.pow_distribR_mul
  _ ≃ p^n * (q^n)⁻¹ := by srw [←pow_scompatL_recip]
  _ ≃ p^n / q^n     := eqv_symm div_mul_recip

variable [Induction.{1} ℚ]

/--
Swap the order of two operations on a rational number: raising it to a natural
number power, and extracting its sign.
-/
theorem sgn_int_pow_nat {p : ℚ} {n : ℕ} : sgn (p^n) ≃ (sgn p)^n := by
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) p_eqv) := as_ratio p
  have : p ≃ a/b := p_eqv

  -- Helpers to keep the main proof short and avoid repetition
  have int_sgn_pow {x : ℤ} : sgn ((x:ℚ)^n) ≃ (sgn x)^n := calc
    _ = sgn ((x:ℚ)^n)   := rfl
    _ ≃ sgn ((x^n:ℤ):ℚ) := by srw [←pow_scompatL_from_integer]
    _ ≃ sgn (x^n)       := sgn_from_integer
    -- This is the key step of the whole proof
    _ ≃ (sgn x)^n       := Integer.sgn_pow
  have sgn_merge : sgn a * sgn b ≃ sgn p := Rel.symm $ calc
    _ = sgn p                 := rfl
    _ ≃ sgn ((a:ℚ)/b)         := by srw [‹p ≃ a/b›]
    _ ≃ sgn (a:ℚ) * sgn (b:ℚ) := sgn_div
    _ ≃ sgn a * sgn b         := by srw [sgn_from_integer, sgn_from_integer]

  calc
    _ = sgn (p^n)                     := rfl
    _ ≃ sgn (((a:ℚ)/b)^n)             := by srw [p_eqv]
    _ ≃ sgn ((a:ℚ)^n/b^n)             := by srw [pow_distribR_div]
    _ ≃ sgn ((a:ℚ)^n) * sgn ((b:ℚ)^n) := sgn_div
    -- The following step is the most important at this level
    _ ≃ (sgn a)^n * (sgn b)^n         := by srw [int_sgn_pow, int_sgn_pow]
    _ ≃ (sgn a * sgn b)^n             := Rel.symm Natural.pow_distribR_mul
    _ ≃ (sgn p)^n                     := by srw [sgn_merge]

/--
Swap the order of two operations on a rational number: raising it to a natural
number power, and extracting its (rational-valued) sign.
-/
theorem sgn_pow_nat {p : ℚ} {n : ℕ} : (sgn (p^n):ℚ) ≃ (sgn p:ℚ)^n := calc
  _ = (sgn (p^n):ℚ)     := rfl
  -- This is the key step
  _ ≃ (((sgn p)^n:ℤ):ℚ) := by srw [sgn_int_pow_nat]
  _ ≃ (sgn p:ℚ)^n       := pow_scompatL_from_integer

variable [Subtraction ℚ] [Order ℚ]

/--
A positive rational number raised to a natural number power is still positive.

**Property intuition**: Exponentiation preserves signs.

**Proof intuition**: Convert the ordering relation to its `sgn` representation.
The result follows from `sgn_pow`.
-/
theorem pow_preserves_pos {p : ℚ} {n : ℕ} : p > 0 → p^n > 0 := by
  intro (_ : p > 0)
  show p^n > 0
  have : sgn p ≃ 1 := gt_zero_sgn.mp ‹p > 0›
  have : sgn (p^n) ≃ 1 := calc
    _ = sgn (p^n) := rfl
    _ ≃ (sgn p)^n := sgn_int_pow_nat
    _ ≃ 1^n       := by srw [‹sgn p ≃ 1›]
    _ ≃ 1         := Natural.pow_absorbL
  have : p^n > 0 := gt_zero_sgn.mpr ‹sgn (p^n) ≃ 1›
  exact this

/--
A nonnegative rational number raised to a natural number power is still
nonnegative.

**Property intuition**: Multiplication cannot generate a negative value from
nonnegative factors.

**Proof intuition**: Split the nonnegativity assumption into positive and zero
cases. The positive case follows by `pow_preserves_pos`. In the zero case, if
the exponent is also zero, then the result is one; otherwise, it's zero. Both
results are nonnegative.
-/
theorem pow_preserves_nonneg {p : ℚ} {n : ℕ} : p ≥ 0 → p^n ≥ 0 := by
  intro (_ : p ≥ 0)
  show p^n ≥ 0

  have : p > 0 ∨ p ≃ 0 := ge_cases.mp ‹p ≥ 0›
  match this with
  | Or.inl (_ : p > 0) =>
    have : p^n > 0 := pow_preserves_pos ‹p > 0›
    have : p^n ≥ 0 := ge_cases.mpr (Or.inl ‹p^n > 0›)
    exact this
  | Or.inr (_ : p ≃ 0) =>
    have : (0:ℚ)^n ≃ 0 ∨ (0:ℚ)^n ≃ 1 := Natural.pow_of_zero
    match this with
    | Or.inl (_ : (0:ℚ)^n ≃ 0) =>
      calc
        _ = p^n := rfl
        _ ≃ 0^n := by srw [‹p ≃ 0›]
        _ ≃ 0   := ‹(0:ℚ)^n ≃ 0›
        _ ≥ 0   := le_refl
    | Or.inr (_ : (0:ℚ)^n ≃ 1) =>
      calc
        _ = p^n := rfl
        _ ≃ 0^n := by srw [‹p ≃ 0›]
        _ ≃ 1   := ‹(0:ℚ)^n ≃ 1›
        _ ≥ 0   := one_ge_zero

/--
Raising two nonnegative rational numbers to the same positive natural number
power preserves their ordering.

**Property intuition**: If the numbers are greater than one, they increase in
magnitude proportionally when raised to the same power. If they are less than
one, then they decrease in magnitude proportionally when raised to the same
power, approaching zero but not reaching it. And if one number is greater than
zero and the other is less than zero, then their relative ordering is still
preserved because they both move away from one.

**Proof intuition**: This proof has a large amount of helper code, but the core
can be found in the final `calc` block. The proof strategy is to convert the
rational numbers into integer fractions and back. The fractions simplify under
`sgn` into several integer values raised to the same natural number power. The
powers can be removed from the values via integer theorems. Finally, the simple
expressions that remain can be combined back into rational numbers, which turn
out to be exactly the ones we wanted.
-/
theorem sgn_diff_pow_pos
    {p q : ℚ} {n : ℕ} : p ≥ 0 → q ≥ 0 → n ≥ 1 → sgn (p^n - q^n) ≃ sgn (p - q)
    := by
  intro (_ : p ≥ 0) (_ : q ≥ 0) (_ : n ≥ 1)
  show sgn (p^n - q^n) ≃ sgn (p - q)
  have (NonnegRatio.intro
      (a : ℤ) (b : ℤ) (_ : a ≥ 0) (_ : b > 0) (_ : AP ((b:ℚ) ≄ 0)) p_eqv)
      :=
    as_nonneg_ratio ‹p ≥ 0›
  have : p ≃ a/b := p_eqv
  have (NonnegRatio.intro
      (c : ℤ) (d : ℤ) (_ : c ≥ 0) (_ : d > 0) (_ : AP ((d:ℚ) ≄ 0)) q_eqv)
      :=
    as_nonneg_ratio ‹q ≥ 0›
  have : q ≃ c/d := q_eqv

  have sgn_mul_absorbL {x y : ℤ} : x > 0 → sgn (x * y) ≃ sgn y := by
    intro (_ : x > 0)
    show sgn (x * y) ≃ sgn y
    calc
      _ = sgn (x * y)   := rfl
      _ ≃ sgn x * sgn y := Integer.sgn_compat_mul
      _ ≃ 1 * sgn y     := by srw [Integer.gt_zero_sgn.mp ‹x > 0›]
      _ ≃ sgn y         := AA.identL
  have : sgn (b * d) ≃ 1 := calc
    _ = sgn (b * d)   := rfl
    _ ≃ sgn d         := sgn_mul_absorbL ‹b > 0›
    _ ≃ 1             := Integer.gt_zero_sgn.mp ‹d > 0›
  have sqr_sgn_bd_idemp : (sgn (b * d))^2 ≃ sgn (b * d) :=
    Integer.sqr_idemp_reasons.mpr (Or.inr ‹sgn (b * d) ≃ 1›)
  have sgn_bd_pow {k : ℕ} : sgn ((b * d)^k) ≃ 1 := calc
    _ = sgn ((b * d)^k) := rfl
    _ ≃ (sgn (b * d))^k := Integer.sgn_pow
    _ ≃ 1^k             := by srw [‹sgn (b * d) ≃ 1›]
    _ ≃ 1               := Natural.pow_absorbL
  have : Integer.Sqrt1 (sgn (b * d)) :=
    Integer.sqrt1_cases.mpr (Or.inl ‹sgn (b * d) ≃ 1›)
  have : Integer.Nonzero (b * d) := Integer.sgn_nonzero.mpr this
  have sqrt1_sgn_bd_pow {k : ℕ} : Integer.Sqrt1 (sgn ((b * d)^k)) :=
    Integer.sqrt1_cases.mpr (Or.inl sgn_bd_pow)
  have nonzero_bd_pow {k : ℕ} : Integer.Nonzero ((b * d)^k) :=
    Integer.sgn_nonzero.mpr sqrt1_sgn_bd_pow
  have : sgn (b * c) ≥ 0 := calc
    _ = sgn (b * c)   := rfl
    _ ≃ sgn c         := sgn_mul_absorbL ‹b > 0›
    _ ≥ 0             := Integer.sgn_preserves_ge_zero.mp ‹c ≥ 0›
  have : b * c ≥ 0 := Integer.sgn_preserves_ge_zero.mpr this
  have : d ≥ 0 := Integer.ge_split.mpr (Or.inl ‹d > 0›)
  have : a * d ≥ 0 := Integer.mul_preserves_nonneg ‹a ≥ 0› ‹d ≥ 0›

  have sub_liftQ {x y : ℤ} : (x:ℚ) - y ≃ ((x - y : ℤ):ℚ) :=
    eqv_symm sub_compat_from_integer
  have mul_liftQ {x y : ℤ} : (x:ℚ) * y ≃ ((x * y : ℤ):ℚ) :=
    eqv_symm mul_compat_from_integer
  have mpℚ {x y : ℤ} {k : ℕ} : (x:ℚ)^k * (y:ℚ)^k ≃ (((x * y)^k : ℤ):ℚ) := calc
    _ = (x:ℚ)^k * (y:ℚ)^k   := rfl
    _ ≃ ((x:ℚ) * y)^k       := by
      letI : CA.Monoid.Monoid ℚ Mul.mul 1 := mul_monoid
      exact eqv_symm Natural.pow_distribR_mul
    _ ≃ ((x * y : ℤ):ℚ)^k   := by srw [mul_liftQ]
    _ ≃ (((x * y)^k : ℤ):ℚ) := eqv_symm pow_scompatL_from_integer
  have sub_mul_liftQ
      {k : ℕ}
      : (a:ℚ)^k * (d:ℚ)^k - (b:ℚ)^k * (c:ℚ)^k ≃ (((a * d)^k - (b * c)^k : ℤ):ℚ)
      := calc
    _ = (a:ℚ)^k * (d:ℚ)^k - (b:ℚ)^k * (c:ℚ)^k := rfl
    _ ≃ (((a*d)^k:ℤ):ℚ) - (((b*c)^k:ℤ):ℚ)     := by srw [mpℚ, mpℚ]
    _ ≃ (((a*d)^k - (b*c)^k : ℤ):ℚ)           := sub_liftQ
  have sub_pow_expand {k : ℕ} : p^k - q^k ≃ (a:ℚ)^k/b^k - (c:ℚ)^k/d^k := calc
    _ = p^k - q^k                 := rfl
    _ ≃ (a:ℚ)^k/b^k - q^k         := by srw [‹p ≃ a/b›, pow_distribR_div]
    _ ≃ (a:ℚ)^k/b^k - ((c:ℚ)/d)^k := by srw [‹q ≃ c/d›]
    _ ≃ (a:ℚ)^k/b^k - (c:ℚ)^k/d^k := by srw [pow_distribR_div]
  have sub_pow_frac
      {k : ℕ}
      : have : Integer.Nonzero ((b * d)^k) := nonzero_bd_pow
        p^k - q^k ≃ (((a * d)^k - (b * c)^k : ℤ):ℚ)/(((b * d)^k : ℤ):ℚ)
      := by
    have : Integer.Nonzero ((b * d)^k) := nonzero_bd_pow
    calc
    _ = p^k - q^k                                   := rfl
    _ ≃ (a:ℚ)^k/b^k - (c:ℚ)^k/d^k                   := sub_pow_expand
    _ ≃ ((a:ℚ)^k*(d:ℚ)^k - (b:ℚ)^k*(c:ℚ)^k)/((b:ℚ)^k*(d:ℚ)^k) := sub_fractions
    _ ≃ (((a*d)^k-(b*c)^k:ℤ):ℚ)/((b:ℚ)^k * (d:ℚ)^k) := by srw [sub_mul_liftQ]
    _ ≃ (((a*d)^k-(b*c)^k:ℤ):ℚ)/(((b*d)^k:ℤ):ℚ)     := by srw [mpℚ]

  let ad := a * d; let bc := b * c; let bd := b * d
  have sgn_sub_pow_factor
      : sgn (p^n - q^n) ≃ sgn (ad^n - bc^n) * sgn (bd^n)
      := calc
    _ = sgn (p^n - q^n)                      := rfl
    _ ≃ sgn (((ad^n-bc^n:ℤ):ℚ)/((bd^n:ℤ):ℚ)) := by srw [sub_pow_frac]
    _ ≃ sgn (ad^n-bc^n) * sgn (bd^n)         := sgn_div_integers
  have sgn_diff_int_pow : sgn (ad^n - bc^n) ≃ sgn (ad - bc) :=
    Integer.sgn_diff_pow_pos ‹ad ≥ 0› ‹bc ≥ 0› ‹n ≥ 1›
  have sgn_bd_drop_pow : sgn (bd^n) ≃ sgn bd := calc
    _ = sgn (bd^n) := rfl
    _ ≃ (sgn bd)^n := Integer.sgn_pow
    _ ≃ sgn bd     := Integer.pow_absorbL ‹n ≥ 1› sqr_sgn_bd_idemp

  have p1ℤ {x : ℤ} : x^1 ≃ x := Natural.pow_one
  have p1ℚ {x : ℚ} : x^1 ≃ x := Natural.pow_one
  have sub_frac : p - q ≃ ((a * d - b * c : ℤ):ℚ)/((b * d : ℤ):ℚ) := calc
    _ = p - q                              := rfl
    _ ≃ p^1 - q^1                          := eqv_symm (by srw [p1ℚ, p1ℚ])
    _ ≃ ((ad^1 - bc^1 : ℤ):ℚ)/((bd^1:ℤ):ℚ) := sub_pow_frac
    _ ≃ ((ad - bc : ℤ):ℚ)/((bd:ℤ):ℚ)       := by srw [p1ℤ, p1ℤ, p1ℤ]

  calc
    _ = sgn (p^n - q^n)                  := rfl
    _ ≃ sgn (ad^n-bc^n) * sgn (bd^n)     := sgn_sub_pow_factor
    _ ≃ sgn (ad - bc) * sgn (bd^n)       := by srw [sgn_diff_int_pow]
    _ ≃ sgn (ad - bc) * sgn bd           := by srw [sgn_bd_drop_pow]
    _ ≃ sgn (((ad - bc:ℤ):ℚ)/((bd:ℤ):ℚ)) := Rel.symm sgn_div_integers
    _ ≃ sgn (p - q)                      := by srw [←sub_frac]

/--
The greater-than relation between two nonnegative rational numbers is
maintained when they are both raised to the same positive natural number power.

**Property and proof intuition**: Follows directly from `sgn_diff_pow_pos`.
-/
theorem pow_pos_preserves_gt_nonneg
    {p q : ℚ} {n : ℕ} : p > q → q ≥ 0 → n ≥ 1 → p^n > q^n
    := by
  intro (_ : p > q) (_ : q ≥ 0) (_ : n ≥ 1)
  show p^n > q^n
  have : p ≥ q := ge_cases.mpr (Or.inl ‹p > q›)
  have : p ≥ 0 := ge_trans ‹p ≥ q› ‹q ≥ 0›
  have : sgn (p^n - q^n) ≃ 1 := calc
    _ = sgn (p^n - q^n) := rfl
    _ ≃ sgn (p - q)     := sgn_diff_pow_pos ‹p ≥ 0› ‹q ≥ 0› ‹n ≥ 1›
    _ ≃ 1               := gt_sgn.mp ‹p > q›
  have : p^n > q^n := gt_sgn.mpr ‹sgn (p^n - q^n) ≃ 1›
  exact this

/--
The greater-than-or-equivalent-to relation between two nonnegative rational
numbers is maintained when they are both raised to the same natural number
power.

**Property and proof intuition**: When the exponent is positive, follows
directly from `sgn_diff_pow_pos`. When the exponent is zero, both values reduce
to one, and thus they trivially satisfy the relation.
-/
theorem pow_preserves_ge_nonneg
    {p q : ℚ} {n : ℕ} : p ≥ q → q ≥ 0 → p^n ≥ q^n
    := by
  intro (_ : p ≥ q) (_ : q ≥ 0)
  show p^n ≥ q^n
  have : n ≥ 0 := Natural.ge_zero
  have : n > 0 ∨ n ≃ 0 := Natural.ge_split ‹n ≥ 0›
  match ‹n > 0 ∨ n ≃ 0› with
  | Or.inl (_ : n > 0) =>
    have : n ≥ 1 := Natural.gt_zero_iff_ge_one.mp ‹n > 0›
    have : p ≥ 0 := ge_trans ‹p ≥ q› ‹q ≥ 0›
    have : sgn (p^n - q^n) ≥ 0 := calc
      _ = sgn (p^n - q^n) := rfl
      _ ≃ sgn (p - q)     := sgn_diff_pow_pos ‹p ≥ 0› ‹q ≥ 0› ‹n ≥ 1›
      _ ≥ 0               := ge_iff_sub_sgn_nonneg.mp ‹p ≥ q›
    have : p^n ≥ q^n := ge_iff_sub_sgn_nonneg.mpr ‹sgn (p^n - q^n) ≥ 0›
    exact this
  | Or.inr (_ : n ≃ 0) =>
    have : p^n ≃ q^n := calc
      _ = p^n := rfl
      _ ≃ p^0 := by srw [‹n ≃ 0›]
      _ ≃ 1   := Natural.pow_zero
      _ ≃ q^0 := eqv_symm Natural.pow_zero
      _ ≃ q^n := by srw [←‹n ≃ 0›]
    have : p^n ≥ q^n := ge_cases.mpr (Or.inr ‹p^n ≃ q^n›)
    exact this

end pow_nat

/-! ## Axioms for exponentiation to an integer -/

/-- Operations for raising rational numbers to integer powers. -/
class Exponentiation.Ops
    {ℕ : outParam Type} (ℚ ℤ : Type)
    [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Core (ℤ := ℤ) ℚ]
    where
  /-- Exponentiation to an integer power. -/
  _pow (p : ℚ) [AP (p ≄ 0)] (a : ℤ) : ℚ

/-- Enables the use of the `· ^ ·` operator for exponentiation. -/
infixr:80 " ^ " => Exponentiation.Ops._pow

/-- Properties of exponentiation to an integer. -/
class Exponentiation.Props
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (mul := (· * ·)) (ident := (1 : ℚ)) (minst := mul_monoid)]
    [Negation ℚ] [Sign ℚ] [Ops ℚ ℤ]
    where
  /--
  An equivalence between raising a rational number to the power of a
  difference, and the quotient of that rational number raised individually to
  each of the difference's components.

  **Intuition**: If `n` counts multiples of `p` to include in the final result,
  and `m` counts multiples of `p` to take away, then `p^n / p^m` denotes how to
  calculate it; the multiples on top and bottom cancel out. If we tried to
  represent this result using a single exponent, then `(n:ℤ) - (m:ℤ)` would be
  how to do it, as it captures the behavior of the cancellation.
  -/
  pow_diff {p : ℚ} {n m : ℕ} [AP (p ≄ 0)] : p^((n:ℤ) - (m:ℤ)) ≃ p^n / p^m

  /--
  Rational number exponentiation to an integer respects equivalence of the
  exponents.

  **Intuition**: For exponentiation to make sense as a function on integers,
  this needs to be true.
  -/
  pow_substR {p : ℚ} [AP (p ≄ 0)] {a₁ a₂ : ℤ} : a₁ ≃ a₂ → p^a₁ ≃ p^a₂

export Exponentiation.Props (pow_diff pow_substR)

attribute [gcongr] pow_substR

/-- All integer exponentiation axioms. -/
class Exponentiation
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (mul := (· * ·)) (ident := (1 : ℚ)) (minst := mul_monoid)]
    [Negation ℚ] [Sign ℚ]
    where
  toOps : Exponentiation.Ops ℚ ℤ
  toProps : Exponentiation.Props ℚ

attribute [instance] Exponentiation.toOps
attribute [instance] Exponentiation.toProps

/-! ## Derived properties for exponentiation to an integer -/

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Reciprocation ℚ] [Division ℚ] [Sign ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (mul := (· * ·)) (ident := (1 : ℚ)) (minst := mul_monoid)]
    [Exponentiation ℚ]

/--
Rational number exponentiation to an integer respects equivalence of the base
values.

**Property intuition**: For integer exponentiation to make sense as a function
on rationals, this needs to be true.

**Proof intuition**: Write the integer exponent as a difference of natural
numbers, and use `pow_diff` to convert the integer power into a ratio of
natural number powers. Then delegate to `Natural.pow_substL`.
-/
@[gcongr]
theorem pow_substL
    {p₁ p₂ : ℚ} {a : ℤ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁^a ≃ p₂^a
    := by
  intro (_ : p₁ ≃ p₂)
  show p₁^a ≃ p₂^a

  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a
  calc
    _ = p₁^a           := rfl
    _ ≃ p₁^((n:ℤ) - m) := by srw [‹a ≃ n - m›]
    _ ≃ p₁^n / p₁^m    := pow_diff
    _ ≃ p₂^n / p₁^m    := by srw [‹p₁ ≃ p₂›]
    _ ≃ p₂^n / p₂^m    := by srw [‹p₁ ≃ p₂›]
    _ ≃ p₂^((n:ℤ) - m) := eqv_symm pow_diff
    _ ≃ p₂^a           := by srw [←‹a ≃ n - m›]

/--
Raising a nonzero rational number to any integer power gives a nonzero result.

**Property intuition**: As the product of two nonzero rational numbers is
nonzero, this is simply an extension of that fact to any number of
multiplications. "Negative" multiplications are accounted for because
reciprocals are always nonzero.

**Proof intuition**: Assume the contrary, and reach a contradiction. Write the
integer exponent as a difference of natural numbers, and use `pow_diff` to
convert the this into a quotient of natural number powers. Show that the
numerator must be zero (from the assumption) and nonzero (from the analogous
theorem for natural number powers), giving us the desired contradiction.
-/
theorem pow_preserves_nonzero {p : ℚ} {a : ℤ} [AP (p ≄ 0)] : p^a ≄ 0 := by
  intro (_ : p^a ≃ 0)
  show False

  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a
  have : p^n / p^m ≃ 0 := calc
    _ = p^n / p^m     := rfl
    _ ≃ p^((n:ℤ) - m) := eqv_symm pow_diff
    _ ≃ p^a           := by srw [←‹a ≃ n - m›]
    _ ≃ 0             := ‹p^a ≃ 0›
  have : p^n ≃ 0 := div_eqv_0.mp this
  have : p^n ≄ 0 := Natural.pow_preserves_nonzero_base ‹AP (p ≄ 0)›.ev
  exact absurd ‹p^n ≃ 0› ‹p^n ≄ 0›

/-- Instance version of `pow_preserves_nonzero`. -/
instance pow_preserves_nonzero_inst
    {p : ℚ} {a : ℤ} [AP (p ≄ 0)] : AP (p^a ≄ 0)
    :=
  AP.mk pow_preserves_nonzero

/--
Raising a nonzero rational number to a nonnegative integer power is equivalent
to raising it to the corresponding natural number.

**Property intuition**: Natural numbers and nonnegative integers are
equivalent, and exponentiation respects equivalence.

**Proof intuition**: Convert the integer power into a difference of natural
numbers and simplify.
-/
theorem pow_nonneg {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : p^(n:ℤ) ≃ p^n := calc
  _ ≃ p^(n:ℤ)       := eqv_refl
  _ ≃ p^((n:ℤ) - 0) := by srw [←Integer.sub_identR]
  _ ≃ p^n / p^(0:ℕ) := pow_diff
  _ ≃ p^n / 1       := by srw [Natural.pow_zero]
  _ ≃ p^n           := div_identR

/--
Raising a nonzero rational number to a non-positive integer power is equivalent
to raising it to the natural number with the same absolute value, then taking
the reciprocal.

**Property intuition**: For addition of exponents to make sense, we need
negative values to "cancel out" the corresponding positive values. This can be
done if the negative values are reciprocals of the positives.

**Proof intuition**: Convert the integer power into a difference of natural
numbers and simplify.
-/
theorem pow_neg {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : p^(-(n:ℤ)) ≃ 1 / p^n := calc
  _ = p^(-(n:ℤ))    := rfl
  _ ≃ p^(0 - (n:ℤ)) := by srw [←Integer.sub_identL]
  _ ≃ p^(0:ℕ) / p^n := pow_diff
  _ ≃ 1 / p^n       := by srw [Natural.pow_zero]

/--
Exponentiation of rationals to integer powers is consistent with reciprocation.

**Property intuition**: The notation for reciprocation strongly suggests this
should be the case!

**Proof intuition**: Follows directly from `pow_neg` and the fractional form of
the reciprocal.
-/
theorem pow_neg_one {p : ℚ} [AP (p ≄ 0)] : p^(-1:ℤ) ≃ p⁻¹ := calc
  _ = p^(-1:ℤ)    := rfl
  _ = p^(-(1:ℤ))  := rfl
  _ ≃ 1 / p^(1:ℕ) := pow_neg
  _ ≃ 1 / p       := by srw [Natural.pow_one]
  _ ≃ p⁻¹         := div_identL

/--
Integer exponents add when powers of the same rational number are multiplied.

**Property intuition**: Exponentiation to integers is repeated multiplication,
either by the base (for positive exponents) or by the base's reciprocal (for
negative exponents). The exponent gives the number of repetitions. Thus if two
powers of the same base are multiplied, that's equivalent to the second power's
multiplication count being combined with the first power's count.

**Proof intuition**: Write both integer exponents as differences of natural
numbers. Invoke `pow_diff` to convert powers of differences to ratios of
natural number powers. Rearrange using algebra and the natural number version
of this property.
-/
theorem pow_compatL_add
    {p : ℚ} [AP (p ≄ 0)] {a b : ℤ} : p^(a + b) ≃ p^a * p^b
    := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a
  have Exists.intro (k : ℕ) (Exists.intro (j : ℕ) (_ : b ≃ k - j)) :=
    Integer.as_diff b
  have : a + b ≃ (n + k : ℕ) - (m + j : ℕ) := calc
    _ = a + b                     := rfl
    _ ≃ (n - m) + (k - j)         := by srw [‹a ≃ n - m›, ‹b ≃ k - j›]
    _ ≃ (n + k) - (m + j)         := Integer.sub_xchg_add
    _ ≃ (n + k : ℕ) - (m + j)     := by srw [←AA.compat₂]
    _ ≃ (n + k : ℕ) - (m + j : ℕ) := by srw [←AA.compat₂]
  have : p^(a + b) ≃ p^(n + k) / p^(m + j) := calc
    _ = p^(a + b)                         := rfl
    _ ≃ p^(((n + k : ℕ):ℤ) - (m + j : ℕ)) := by srw [‹a+b ≃ (n+k:ℕ)-(m+j:ℕ)›]
    _ ≃ p^(n + k) / p^(m + j)             := pow_diff
  have : p^n / p^m ≃ p^a := calc
    _ = p^n / p^m     := rfl
    _ ≃ p^((n:ℤ) - m) := eqv_symm pow_diff
    _ ≃ p^a           := by srw [←‹a ≃ n - m›]
  have : p^k / p^j ≃ p^b := calc
    _ = p^k / p^j     := rfl
    _ ≃ p^((k:ℤ) - j) := eqv_symm pow_diff
    _ ≃ p^b           := by srw [←‹b ≃ k - j›]
  calc
    _ = p^(a + b)                 := rfl
    _ ≃ p^(n + k) / p^(m + j)     := by srw [‹p^(a+b) ≃ p^(n+k)/p^(m+j)›]
    _ ≃ (p^n * p^k) / p^(m + j)   := by srw [Natural.pow_compatL_add]
    _ ≃ (p^n * p^k) / (p^m * p^j) := by srw [Natural.pow_compatL_add]
    _ ≃ (p^n / p^m) * (p^k / p^j) := Rel.symm div_mul_swap
    _ ≃ p^a * p^b                 := by srw [‹p^n/p^m ≃ p^a›, ‹p^k/p^j ≃ p^b›]

/--
Powers of powers flatten into a single power whose exponent is the product of
the original exponents.

**Property intuition**: First, `p^a` is `a` repetitions of the base (either
directly or as a reciprocal, if `a` is negative). So `(p^a)^b` is `b`
repetitions _of_ an expression that's `a` repetitions of the base, giving
`a * b` repetitions total.

**Proof intuition**: Write both integer exponents as differences of natural
numbers. Use `pow_diff` to simplify the expression to one involving powers of
powers of _natural_ numbers. Use natural number exponent properties, and
`pow_diff` again, to factor out the base and combine exponents until the
expression has a single instance of the base raised to a single exponent.
Simplify that exponent to obtain the result.
-/
theorem pow_flatten {p : ℚ} [AP (p ≄ 0)] {a b : ℤ} : (p^a)^b ≃ p^(a * b) := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (a_eqv : a ≃ n - m)) :=
    Integer.as_diff a
  have Exists.intro (k : ℕ) (Exists.intro (j : ℕ) (b_eqv : b ≃ k - j)) :=
    Integer.as_diff b

  let pn := p^n; let pm := p^m
  have : p^a ≃ pn / pm := calc
    _ = p^a           := rfl
    _ ≃ p^((n:ℤ) - m) := by srw [‹a ≃ n - m›]
    _ ≃ pn / pm       := pow_diff
  have pow_expand : (p^a)^b ≃ (pn^k/pm^k) / (pn^j/pm^j) := calc
    _ = (p^a)^b                   := rfl
    _ ≃ (pn/pm)^b                 := by srw [‹p^a ≃ pn / pm›]
    _ ≃ (pn/pm)^((k:ℤ)-j)         := by srw [‹b ≃ k - j›]
    _ ≃ (pn/pm)^k / (pn/pm)^j     := pow_diff
    _ ≃ (pn^k/pm^k) / (pn^j/pm^j) := by srw [pow_distribR_div, pow_distribR_div]
  have pow_combine {w x y z : ℕ} : (p^w)^x*(p^y)^z ≃ p^(w*x + y*z) := calc
    _ = (p^w)^x*(p^y)^z := rfl
    _ ≃ p^(w*x)*p^(y*z) := by srw [Natural.pow_flatten, Natural.pow_flatten]
    _ ≃ p^(w*x + y*z)   := Rel.symm Natural.pow_compatL_add
  have multi_compat {w x y z : ℕ} : ((w*x + y*z : ℕ):ℤ) ≃ (w:ℤ)*x + y*z := calc
    _ = ((w*x + y*z : ℕ):ℤ)           := rfl
    _ ≃ ((w*x : ℕ):ℤ) + ((y*z : ℕ):ℤ) := AA.compat₂
    _ ≃ (w:ℤ)*x + ((y*z : ℕ):ℤ)       := by srw [AA.compat₂]
    _ ≃ (w:ℤ)*x + y*z                 := by srw [AA.compat₂]
  have pow_reduce₁
    : ((n*k+m*j:ℕ):ℤ) - ((m*k+n*j:ℕ):ℤ) ≃ ((n:ℤ)*k+m*j) - (m*k+n*j)
    := by srw [multi_compat, multi_compat]
  have diff_expand
      {w x y z : ℤ} : (w-x) * (y-z) ≃ (w*y + x*z) - (x*y + w*z)
      := by
    let wy := w*y; let wz := w*z; let xy := x*y; let xz := x*z
    have : -xy + -wz ≃ -(xy + wz) := Rel.symm Integer.neg_compat_add
    calc
      _ = (w-x) * (y-z)           := rfl
      _ ≃ w * (y-z) - x * (y-z)   := AA.distribR
      _ ≃ (wy - wz) - x * (y-z)   := by srw [Integer.mul_distribL_sub]
      _ ≃ (wy - wz) - (xy - xz)   := by srw [Integer.mul_distribL_sub]
      _ ≃ (wy - wz) + -(xy - xz)  := Integer.sub_defn
      _ ≃ (wy - wz) + (xz - xy)   := by srw [Integer.sub_neg_flip]
      _ ≃ (wy + -wz) + (xz + -xy) := by srw [Integer.sub_defn, Integer.sub_defn]
      _ ≃ (wy + xz) + (-wz + -xy) := AA.expr_xxfxxff_lr_swap_rl (f := (· + ·))
      _ ≃ (wy + xz) + (-xy + -wz) := by srw [Integer.add_comm]
      _ ≃ (wy + xz) + -(xy + wz)  := by srw [‹-xy + -wz ≃ -(xy + wz)›]
      _ ≃ (wy + xz) - (xy + wz)   := Rel.symm Integer.sub_defn
  have pow_reduce₂ : ((n:ℤ)*k + m*j) - (m*k + n*j) ≃ a * b := calc
    _ = ((n:ℤ)*k + m*j) - (m*k + n*j) := rfl
    _ ≃ ((n:ℤ) - m) * (k - j)         := Rel.symm diff_expand
    _ ≃ a * b                         := Rel.symm (by srw [a_eqv, b_eqv])
  have div_pow_reduce : p^(n*k + m*j) / p^(m*k + n*j) ≃ p^(a * b) := calc
    _ = p^(n*k + m*j) / p^(m*k + n*j)                 := rfl
    _ ≃ p^(((n*k + m*j : ℕ):ℤ) - ((m*k + n*j : ℕ):ℤ)) := eqv_symm pow_diff
    _ ≃ p^(((n:ℤ)*k + m*j) - (m*k + n*j))             := by srw [pow_reduce₁]
    _ ≃ p^(a * b)                                     := by srw [pow_reduce₂]
  calc
    _ = (p^a)^b                               := rfl
    _ ≃ ((p^n)^k/(p^m)^k) / ((p^n)^j/(p^m)^j) := pow_expand
    _ ≃ ((p^n)^k*(p^m)^j) / ((p^m)^k*(p^n)^j) := div_div_div
    _ ≃ p^(n*k + m*j) / ((p^m)^k*(p^n)^j)     := by srw [pow_combine]
    _ ≃ p^(n*k + m*j) / p^(m*k + n*j)         := by srw [pow_combine]
    _ ≃ p^(a * b)                             := div_pow_reduce

/--
Integer exponents distribute over multiplication.

**Property intuition**: Multiplication is commutative, so there should be no
difference between repeated multiplication of a product (or its reciprocal, for
negative exponents) and repeated multiplication of its first term, followed by
repeated multiplication of its second term.

**Proof intuition**: Write the integer exponent as a difference of natural
numbers. Convert the expression to a ratio of natural number powers via
`pow_diff`. Invoke the analogous property for natural number exponents, and
factor the result into a product of fractions. Run `pow_diff` in reverse and
convert back to integer exponents to obtain the goal.
-/
theorem pow_distribR_mul
    {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] {a : ℤ} : (p * q)^a ≃ p^a * q^a
    := by
  -- Bridge the eta mismatch locally: `mul_monoid` is for `(· * ·)` but
  -- `Natural.pow_distribR_mul` unifies `mul` to `Mul.mul` (eta-reduced).
  letI : CA.Monoid.Monoid ℚ Mul.mul 1 := mul_monoid
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (a_eqv : a ≃ n - m)) :=
    Integer.as_diff a

  calc
    _ = (p * q)^a                 := rfl
    _ ≃ (p * q)^((n:ℤ)-m)         := by srw [a_eqv]
    _ ≃ (p * q)^n / (p * q)^m     := pow_diff
    _ ≃ (p^n * q^n) / (p * q)^m   := by srw [Natural.pow_distribR_mul]
    _ ≃ (p^n * q^n) / (p^m * q^m) := by srw [Natural.pow_distribR_mul]
    _ ≃ (p^n / p^m) * (q^n / q^m) := eqv_symm div_mul_swap
    _ ≃ p^((n:ℤ)-m) * q^((n:ℤ)-m) := by srw [←pow_diff, ←pow_diff]
    _ ≃ p^a * q^((n:ℤ)-m)         := by srw [←a_eqv]
    _ ≃ p^a * q^a                 := by srw [←a_eqv]

/--
The rational number one, raised to any integer exponent, is one.

**Property intuition**: One to a positive exponent is always one; anything to a
zero exponent is one; one is its own reciprocal.

**Proof intuition**: Write the integer exponent as a difference of natural
numbers. Convert the expression to a ratio of natural number powers via
`pow_diff`. Each part of the ratio reduces to one via this property for natural
number exponents.
-/
theorem one_pow {a : ℤ} : (1:ℚ)^a ≃ 1 := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a
  calc
    _ = (1:ℚ)^a           := rfl
    _ ≃ (1:ℚ)^((n:ℤ) - m) := by srw [‹a ≃ n - m›]
    _ ≃ (1:ℚ)^n / (1:ℚ)^m := pow_diff
    _ ≃ (1:ℚ)^n / 1       := by srw [Natural.pow_absorbL]
    _ ≃ (1:ℚ)^n           := div_identR
    _ ≃ 1                 := Natural.pow_absorbL

section
variable [Subtraction ℚ] [Order ℚ] [Metric ℚ]

/--
Swap the order of two operations on a nonzero rational number: raising it to an
integer power, and computing its absolute value.
-/
theorem pow_int_scompatL_abs
    {p : ℚ} [AP (p ≄ 0)] {a : ℤ} : abs (p^a) ≃ (abs p)^a
    := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a

  calc
    _ = abs (p^a)             := rfl
    _ ≃ abs (p^((n:ℤ)-m))     := by srw [‹a ≃ n - m›]
    _ ≃ abs (p^n/p^m)         := by srw [pow_diff]
    -- ↓ begin key steps ↓
    _ ≃ abs (p^n) / abs (p^m) := abs_compat_div
    _ ≃ (abs p)^n / abs (p^m) := by srw [pow_nat_scompatL_abs]
    _ ≃ (abs p)^n / (abs p)^m := by srw [pow_nat_scompatL_abs]
    -- ↑  end key steps  ↑
    _ ≃ (abs p)^((n:ℤ)-m)     := eqv_symm pow_diff
    _ ≃ (abs p)^a             := by srw [←‹a ≃ n - m›]

end
variable [Induction.{1} ℚ]

/--
Swap the order of two operations on a nonzero rational number: raising it to an
integer power, and extracting its (rational-valued) sign.
-/
theorem sgn_pow_int
    {p : ℚ} [AP (p ≄ 0)] {a : ℤ} : (sgn (p^a):ℚ) ≃ (sgn p:ℚ)^a
    := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a
  calc
    _ = (sgn (p^a):ℚ)               := rfl
    _ ≃ (sgn (p^n/p^m):ℚ)           := by srw [‹a ≃ n - m›, pow_diff]
    _ ≃ (sgn (p^n):ℚ)/(sgn (p^m):ℚ) := sgn_compat_div
    -- ↓ begin key steps ↓
    _ ≃ (sgn p:ℚ)^n/(sgn p:ℚ)^m     := by srw [sgn_pow_nat, sgn_pow_nat]
    -- ↑  end key steps  ↑
    _ ≃ (sgn p:ℚ)^((n:ℤ) - m)       := eqv_symm pow_diff
    _ ≃ (sgn p:ℚ)^a                 := by srw [←‹a ≃ n - m›]

variable [Subtraction ℚ] [Order ℚ]

/-- A positive rational, raised to an integer power, is also positive. -/
theorem pow_preserves_pos_base
    {p : ℚ} {a : ℤ} (p_pos : p > 0)
    : have : AP (p ≄ 0) := AP.mk (pos_nonzero ‹p > 0›)
      p^a > 0
    := by
  intro (_ : AP (p ≄ 0))
  show p^a > 0

  have : sgn p ≃ 1 := gt_zero_sgn.mp ‹p > 0›
  have : (sgn (p^a):ℚ) ≃ 1 := calc
    _ = (sgn (p^a):ℚ) := rfl
    -- ↓ begin key steps ↓
    _ ≃ (sgn p:ℚ)^a   := sgn_pow_int
    _ ≃ ((1:ℤ):ℚ)^a   := by srw [‹sgn p ≃ 1›]
    -- ↑  end key steps  ↑
    _ ≃ 1             := one_pow
  have : sgn (p^a) ≃ 1 := from_integer_inject ‹(sgn (p^a):ℚ) ≃ 1›
  have : p^a > 0 := gt_zero_sgn.mpr ‹sgn (p^a) ≃ 1›
  exact this

/--
Generalizes a number of identities showing how the ordering of two rational
numbers relates to the ordering of their powers, when they are raised to the
same integer exponent.

Recall that `sgn (p - q)` evaluates to `1`, `0`, or `-1`, when `p` is greater
than, equal to, or less than `q`, respectively. Then this theorem shows how
the ordering of `p^a` and `q^a` can be calculated from the ordering of `p` and
`q` along with the sign of the exponent `a`.

For concrete examples of what this generalizes, see `pow_pos_preserves_ge_pos`
and `pow_neg_reverses_ge_pos` below.
-/
theorem sgn_diff_pow
    {p q : ℚ} {a : ℤ} (p_pos : p > 0) (q_pos : q > 0)
    : have : p ≄ 0 := pos_nonzero ‹p > 0›
      have : q ≄ 0 := pos_nonzero ‹q > 0›
      have : AP (p ≄ 0) := AP.mk ‹p ≄ 0›
      have : AP (q ≄ 0) := AP.mk ‹q ≄ 0›
      sgn (p^a - q^a) ≃ sgn (p - q) * sgn a
    := by
  intro (_ : p ≄ 0) (_ : q ≄ 0) (_ : AP (p ≄ 0)) (_ : AP (q ≄ 0))
  show sgn (p^a - q^a) ≃ sgn (p - q) * sgn a

  have : p ≥ 0 := ge_cases.mpr (Or.inl ‹p > 0›)
  have : q ≥ 0 := ge_cases.mpr (Or.inl ‹q > 0›)

  /-
  Split the proof into cases for a zero, positive, or negative exponent. This
  appears to be the only approach that works; converting the exponent into a
  difference of natural numbers and/or converting the rational numbers into
  ratios of integers and then rearranging via algebra gets stuck.
  -/
  have : a ≃ 0 ∨ Integer.Nonzero a := (Integer.zero? a).left
  match this with
  | Or.inl (_ : a ≃ 0) =>
    have pow_a_simp {x : ℚ} [AP (x ≄ 0)] : x^a ≃ 1 := calc
      _ = x^a     := rfl
      _ ≃ x^(0:ℤ) := by srw [‹a ≃ 0›]
      _ ≃ x^(0:ℕ) := pow_nonneg
      _ ≃ 1       := Natural.pow_zero
    have : sgn a ≃ 0 := Integer.sgn_zero.mp ‹a ≃ 0›
    calc
      -- ↓ begin key steps ↓
      _ = sgn (p^a - q^a)     := rfl
      _ ≃ sgn ((1:ℚ) - 1)     := by srw [pow_a_simp, pow_a_simp]
      _ ≃ sgn (0:ℚ)           := by srw [sub_eqv_zero_iff_eqv.mpr eqv_refl]
      -- ↑  end key steps ↑
      _ ≃ 0                   := sgn_zero.mp eqv_refl
      _ ≃ sgn (p - q) * 0     := Rel.symm AA.absorbR
      _ ≃ sgn (p - q) * sgn a := by srw [←‹sgn a ≃ 0›]
  | Or.inr (_ : Integer.Nonzero a) =>
    /-
    It's important to express `a` as a natural number with a sign, so that the
    proof can rely on properties of rational numbers with natural number
    exponents that have already been proven.
    -/
    have (Exists.intro (n:ℕ) (And.intro (_ : n ≥ 1) (_ : a ≃ n * sgn a))) :=
      Integer.as_size_with_sign ‹Integer.Nonzero a›
    have : Integer.Sqrt1 (sgn a) := Integer.sgn_nonzero.mp ‹Integer.Nonzero a›
    have : sgn a ≃ 1 ∨ sgn a ≃ -1 :=
      Integer.sqrt1_cases.mp ‹Integer.Sqrt1 (sgn a)›
    match ‹sgn a ≃ 1 ∨ sgn a ≃ -1› with
    | Or.inl (_ : sgn a ≃ 1) =>
      have pow_a_simp {x : ℚ} [AP (x ≄ 0)] : x^a ≃ x^n := calc
        _ = x^a               := rfl
        _ ≃ x^((n:ℤ) * sgn a) := by srw [‹a ≃ n * sgn a›]
        _ ≃ x^(n:ℤ)           := by srw [‹sgn a ≃ 1›, Integer.mul_identR]
        _ ≃ x^n               := pow_nonneg
      calc
        _ = sgn (p^a - q^a)     := rfl
        -- ↓ begin key steps ↓
        _ ≃ sgn (p^n - q^n)     := by srw [pow_a_simp, pow_a_simp]
        _ ≃ sgn (p - q)         := sgn_diff_pow_pos ‹p ≥ 0› ‹q ≥ 0› ‹n ≥ 1›
        -- ↑  end key steps  ↑
        _ ≃ sgn (p - q) * 1     := Rel.symm AA.identR
        _ ≃ sgn (p - q) * sgn a := by srw [←‹sgn a ≃ 1›]
    | Or.inr (_ : sgn a ≃ -1) =>
      have pow_a_simp {x : ℚ} [AP (x ≄ 0)] : x^a ≃ (x^n)⁻¹ := calc
        _ = x^a               := rfl
        _ ≃ x^((n:ℤ) * sgn a) := by srw [‹a ≃ n * sgn a›]
        _ ≃ x^((n:ℤ) * -1)    := by srw [‹sgn a ≃ -1›]
        _ ≃ (x^(n:ℤ))^(-1:ℤ)  := eqv_symm pow_flatten
        _ ≃ (x^(n:ℤ))⁻¹       := pow_neg_one
        _ ≃ (x^n)⁻¹           := by srw [pow_nonneg]
      have : p^n > 0 := pow_preserves_pos ‹p > 0›
      have : q^n > 0 := pow_preserves_pos ‹q > 0›
      have : p^n * q^n > 0 := mul_preserves_pos ‹p^n > 0› ‹q^n > 0›
      calc
        _ = sgn (p^a - q^a)         := rfl
        -- ↓ begin key steps ↓
        _ ≃ sgn ((p^n)⁻¹ - (q^n)⁻¹) := by srw [pow_a_simp, pow_a_simp]
        _ ≃ sgn (q^n - p^n)         := sgn_sub_recip ‹p^n * q^n > 0›
        _ ≃ sgn (q - p)             := sgn_diff_pow_pos ‹q ≥ 0› ‹p ≥ 0› ‹n ≥ 1›
        -- ↑  end key steps  ↑
        _ ≃ sgn (-(p - q))          := by srw [←neg_sub]
        _ ≃ -sgn (p - q)            := sgn_compat_neg
        _ ≃ -1 * sgn (p - q)        := Rel.symm Integer.mul_neg_one
        _ ≃ sgn (p - q) * -1        := AA.comm
        _ ≃ sgn (p - q) * sgn a     := by srw [←‹sgn a ≃ -1›]

/--
Raising two positive rational numbers (with one greater than or equivalent to
the other) to the same positive integer exponent leaves their ordering
unchanged.
-/
theorem pow_pos_preserves_ge_pos
    {p q : ℚ} {a : ℤ} (q_pos : q > 0) (a_pos : a > 0) (p_ge_q : p ≥ q)
    : have : p > 0 := trans ‹p ≥ q› ‹q > 0›
      have : AP (p ≄ 0) := AP.mk (pos_nonzero ‹p > 0›)
      have : AP (q ≄ 0) := AP.mk (pos_nonzero ‹q > 0›)
      p^a ≥ q^a
    := by
  intro (_ : p > 0) (_ : AP (p ≄ 0)) (_ : AP (q ≄ 0))
  show p^a ≥ q^a

  have : sgn (p^a - q^a) ≥ 0 := calc
    -- ↓ begin key steps ↓
    _ = sgn (p^a - q^a)     := rfl
    _ ≃ sgn (p - q) * sgn a := sgn_diff_pow ‹p > 0› ‹q > 0›
    -- ↑  end key steps  ↑
    _ ≃ sgn (p - q) * 1     := by srw [Integer.gt_zero_sgn.mp ‹a > 0›]
    _ ≃ sgn (p - q)         := AA.identR
    _ ≥ 0                   := ge_iff_sub_sgn_nonneg.mp ‹p ≥ q›
  have : p^a ≥ q^a := ge_iff_sub_sgn_nonneg.mpr ‹sgn (p^a - q^a) ≥ 0›
  exact this

/--
Raising two positive rational numbers (with one greater than or equivalent to
the other) to the same negative integer exponent reverses their ordering.
-/
theorem pow_neg_reverses_ge_pos
    {p q : ℚ} {a : ℤ} (q_pos : q > 0) (a_neg : a < 0) (p_ge_q : p ≥ q)
    : have : p > 0 := trans ‹p ≥ q› ‹q > 0›
      have : AP (p ≄ 0) := AP.mk (pos_nonzero ‹p > 0›)
      have : AP (q ≄ 0) := AP.mk (pos_nonzero ‹q > 0›)
      p^a ≤ q^a
    := by
  intro (_ : p > 0) (_ : AP (p ≄ 0)) (_ : AP (q ≄ 0))
  show p^a ≤ q^a

  have : sgn (q^a - p^a) ≥ 0 := calc
    -- ↓ begin key steps ↓
    _ = sgn (q^a - p^a)     := rfl
    _ ≃ sgn (q - p) * sgn a := sgn_diff_pow ‹q > 0› ‹p > 0›
    -- ↑  end key steps  ↑
    _ ≃ sgn (q - p) * -1    := by srw [Integer.lt_zero_sgn.mp ‹a < 0›]
    _ ≃ -1 * sgn (q - p)    := AA.comm
    _ ≃ -sgn (q - p)        := Integer.mul_neg_one
    _ ≃ sgn (-(q - p))      := Rel.symm sgn_compat_neg
    _ ≃ sgn (p - q)         := by srw [neg_sub]
    _ ≥ 0                   := ge_iff_sub_sgn_nonneg.mp ‹p ≥ q›
  have : p^a ≤ q^a := ge_iff_sub_sgn_nonneg.mpr ‹sgn (q^a - p^a) ≥ 0›
  exact this

/--
Exponentiation of positive rational numbers to a nonzero integer is bijective
in its left argument.

In other words, a common nonzero exponent can be dropped from an equivalence of
positive rational powers, or the reverse.
-/
theorem pow_bijectL
    {p q : ℚ} {a : ℤ} (p_pos : p > 0) (q_pos : q > 0)
    : have : AP (p ≄ 0) := AP.mk (pos_nonzero ‹p > 0›)
      have : AP (q ≄ 0) := AP.mk (pos_nonzero ‹q > 0›)
      a ≄ 0 → (p^a ≃ q^a ↔ p ≃ q)
    := by
  intro (_ : AP (p ≄ 0)) (_ : AP (q ≄ 0)) (_ : a ≄ 0)
  show p^a ≃ q^a ↔ p ≃ q

  -- Helpers to keep the lines within the margin for the main proof
  have factor : sgn (p^a - q^a) ≃ sgn (p - q) * sgn a :=
    sgn_diff_pow ‹p > 0› ‹q > 0›
  have a_neqv_0 : sgn a ≃ 0 ↔ False := calc
    _ ↔ sgn a ≃ 0 := Iff.rfl
    _ ↔ a ≃ 0     := Integer.sgn_zero.symm
    _ ↔ False     := Iff.intro ‹a ≄ 0› False.elim

  calc
    _ ↔ p^a ≃ q^a                   := Iff.rfl
    _ ↔ p^a - q^a ≃ 0               := sub_eqv_zero_iff_eqv.symm
    -- ↓ begin key steps ↓
    _ ↔ sgn (p^a - q^a) ≃ 0         := sgn_zero
    _ ↔ sgn (p - q) * sgn a ≃ 0     := by srw [factor]
    -- ↑  end key steps  ↑
    _ ↔ sgn (p - q) ≃ 0 ∨ sgn a ≃ 0 := Integer.mul_split_zero
    _ ↔ sgn (p - q) ≃ 0 ∨ False     := iff_subst_covar or_mapR a_neqv_0
    _ ↔ sgn (p - q) ≃ 0             := or_identR
    _ ↔ p - q ≃ 0                   := sgn_zero.symm
    _ ↔ p ≃ q                       := sub_eqv_zero_iff_eqv

/--
Sufficient conditions for an integer power of the rational number two being no
smaller than its exponent.

For a more general result with no restrictions on the value of the exponent,
see `pow_lower_bound`.
-/
theorem pow_two_lower_bound {a : ℤ} : a ≥ 1 → (2:ℚ)^a ≥ a := by
  /-
  By constraining the exponent to be strictly positive, even though the
  result would hold for any integer value, this proof becomes substantially
  simpler. And it's an exact match for the assumptions in scope where this
  result is used in the proof of `pow_lower_bound`. In short, this theorem is
  really a lemma that's precisely tuned for a single purpose.
  -/
  intro (_ : a ≥ 1)
  show (2:ℚ)^a ≥ a

  let motive := λ (x : ℤ) => (2:ℚ)^x ≥ x
  have motive_subst {c₁ c₂ : ℤ} : c₁ ≃ c₂ → motive c₁ → motive c₂ := by
    intro (_ : c₁ ≃ c₂) (_ : (2:ℚ)^c₁ ≥ c₁)
    show (2:ℚ)^c₂ ≥ c₂
    calc
      _ = (2:ℚ)^c₂ := rfl
      _ ≃ (2:ℚ)^c₁ := by srw [←‹c₁ ≃ c₂›]
      _ ≥ c₁       := ‹(2:ℚ)^c₁ ≥ c₁›
      _ ≃ c₂       := by srw [‹c₁ ≃ c₂›]

  apply Integer.ind_from motive_subst ‹a ≥ 1›
  case base =>
    show (2:ℚ)^(1:ℤ) ≥ 1
    calc
      _ = (2:ℚ)^(1:ℤ) := rfl
      _ ≃ (2:ℚ)^(1:ℕ) := pow_nonneg
      _ ≃ 2           := Natural.pow_one
      _ ≥ 1           := ge_cases.mpr (Or.inl two_gt_one)
  case next =>
    intro (c : ℤ) (_ : c ≥ 1) (_ : (2:ℚ)^c ≥ c)
    show (2:ℚ)^(c + 1) ≥ ((c + 1 : ℤ):ℚ)
    have : (c:ℚ) ≥ 1 := le_respects_from_integer.mp ‹c ≥ 1›
    calc
      _ = (2:ℚ)^(c + 1)             := rfl
      _ ≃ (2:ℚ)^c * (2:ℚ)^((1:ℕ):ℤ) := pow_compatL_add
      _ ≃ (2:ℚ)^c * (2:ℚ)^(1:ℕ)     := by srw [pow_nonneg]
      -- ↓ begin key steps ↓
      _ ≃ (2:ℚ)^c * 2               := by srw [Natural.pow_one]
      _ ≥ (c:ℚ) * 2                 := le_substL_mul_pos two_pos ‹(2:ℚ)^c ≥ c›
      _ ≃ (2:ℚ) * c                 := mul_comm
      _ ≃ (c:ℚ) + c                 := mul_two_add
      _ ≥ (c:ℚ) + 1                 := by srw [‹1 ≤ (c:ℚ)›]
      -- ↑  end key steps  ↑
      _ ≃ ((c + 1 : ℤ):ℚ)           := eqv_symm add_compat_from_integer

/--
Sufficient conditions for an integer power of a rational number being no
smaller than its exponent.
-/
theorem pow_lower_bound
    {p : ℚ} {a : ℤ} (p_ge : p ≥ 2)
    : have : (2:ℚ) > 0 := two_pos
      have : p > 0 := trans ‹p ≥ 2› ‹(2:ℚ) > 0›
      have : AP (p ≄ 0) := AP.mk (pos_nonzero ‹p > 0›)
      p^a ≥ a
    := by
  intro (_ : (2:ℚ) > 0) (_ : p > 0) (_ : AP (p ≄ 0))
  show p^a ≥ a
  have : a ≤ 0 ∨ a > 0 := Integer.le_or_gt
  match ‹a ≤ 0 ∨ a > 0› with
  | Or.inl (_ : a ≤ 0) =>
    -- ↓ begin key steps ↓
    have : p^a > 0 := pow_preserves_pos_base ‹p > 0›
    -- ↑  end key steps  ↑
    have : p^a ≥ 0 := ge_cases.mpr (Or.inl ‹p^a > 0›)
    have : (a:ℚ) ≤ 0 := le_respects_from_integer.mp ‹a ≤ 0›
    have : p^a ≥ a := Trans.trans ‹p^a ≥ 0› ‹(0:ℚ) ≥ a›
    exact this
  | Or.inr (_ : a > 0) =>
    have : a ≥ 1 := Integer.pos_gt_iff_ge.mp ‹a > 0›
    -- ↓ begin key steps ↓
    have : (2:ℚ)^a ≥ a := pow_two_lower_bound ‹a ≥ 1›
    have : p^a ≥ (2:ℚ)^a := pow_pos_preserves_ge_pos ‹(2:ℚ) > 0› ‹a > 0› ‹p ≥ 2›
    -- ↑  end key steps  ↑
    have : p^a ≥ a := Trans.trans ‹p^a ≥ (2:ℚ)^a› ‹(2:ℚ)^a ≥ a›
    exact this

end Lean4Axiomatic.Rational

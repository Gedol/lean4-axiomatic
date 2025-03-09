import Lean4Axiomatic.Integer.Order

/-!
# Integers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Integer

open Logic (AP iff_subst_covar or_mapL or_mapR)
open Natural (step)
open Signed (Positive)
open Multiplication (mulOp)

/-! ## Derived properties for exponentiation to a natural number -/

variable
  {ℕ ℤ : Type} [Natural ℕ] [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ]
  [Natural.Exponentiation ℕ (α := ℤ) (mul := (· * ·)) (ident := 1) (minst := mul_monoid)]

/--
Raising an integer to _any_ positive natural number power has no effect if
just squaring the integer has no effect.

**Property and proof intuition**: By induction, any power greater than two can
be reduced to the squaring case.
-/
theorem pow_absorbL {a : ℤ} {n : ℕ} : n ≥ 1 → a^2 ≃ a → a^n ≃ a := by
  intro (_ : n ≥ 1) (_ : a^2 ≃ a)
  show a^n ≃ a

  let motive := λ (x : ℕ) => a^x ≃ a
  have motive_subst {x₁ x₂ : ℕ} : x₁ ≃ x₂ → motive x₁ → motive x₂ := by
    intro (_ : x₁ ≃ x₂) (_ : a^x₁ ≃ a)
    show a^x₂ ≃ a
    calc
      _ = a^x₂ := rfl
      _ ≃ a^x₁ := by srw [←‹x₁ ≃ x₂›]
      _ ≃ a    := ‹a^x₁ ≃ a›

  apply Natural.ind_from motive_subst ‹n ≥ 1›
  case base =>
    show a^1 ≃ a
    exact Natural.pow_one
  case next =>
    intro (k : ℕ) (_ : k ≥ 1) (ih : a^k ≃ a)
    show a^(step k) ≃ a
    calc
      _ = a^(step k) := rfl
      _ ≃ a^k * a    := Natural.pow_step
      _ ≃ a * a      := by srw [ih]
      _ ≃ a^2        := Rel.symm Natural.pow_two
      _ ≃ a          := ‹a^2 ≃ a›

/--
The factors of `a^3` can be arranged as `a * a^2`.

This trivial lemma is useful for several integer exponentiation theorems.

**Property intuition**: `a^3 ≃ a * a * a ≃ a * (a * a) ≃ a * a^2`

**Proof intuition**: Convert `3` to `step 2` so that `pow_step` can be used to
separate a factor of `a`.
-/
theorem cube_splitL {a : ℤ} : a^3 ≃ a * a^2 := calc
  _ = a^3        := rfl
  _ ≃ a^(step 2) := by srw [Natural.literal_step]
  _ ≃ a^2 * a    := Natural.pow_step
  _ ≃ a * a^2    := AA.comm

variable [Negation ℤ]

section sub_only
variable [Subtraction ℤ]

/--
The difference of two integer squares can be rewritten as the product of two
factors linear in the original integers.

**Property intuition**: Using plane geometry where `a^2` and `b^2` are areas of
actual squares. Without loss of generality, let `a` be the side length of the
larger square and let `b` be the side length of the smaller. Then `a^2 - b^2`
is the area of the larger square that is not covered by the smaller square
(imagine the smaller square is fully inside the larger, sharing one corner).
The area of this region can be found by adding the areas of the rectangles that
share a side with `b^2`, and the small square in the opposite corner. Thus it's
equal to `(a - b) * b + (a - b) * b + (a - b)^2`. Factor out `(a - b)` and
simplify to obtain `(a - b) * (a + b)`.

**Proof intuition**: It's easier to prove the equivalence by multiplying out
the factors, so reverse the direction of the `calc` block. Then use algebra to
distribute terms and simplify.
-/
theorem factor_diff_sqr {a b : ℤ} : a^2 - b^2 ≃ (a - b) * (a + b) := by
  apply Rel.symm
  calc
    _ = (a - b) * (a + b)             := rfl
    _ ≃ a * (a + b) - b * (a + b)     := AA.distribR
    _ ≃ a^2 + a * b - b * (a + b)     := by srw [mul_distribL, ←Natural.pow_two]
    _ ≃ a^2 + a * b - (a + b) * b     := by srw [AA.comm]
    _ ≃ a^2 + a * b - (a * b + b^2)   := by srw [mul_distribR, ←Natural.pow_two]
    _ ≃ a^2 + (a * b - (a * b + b^2)) := sub_assoc_addL
    _ ≃ a^2 + ((a * b - a * b) - b^2) := by srw [←sub_assoc_subR]
    _ ≃ a^2 + (-b^2)                  := by srw [sub_same, sub_identL]
    _ ≃ a^2 - b^2                     := Rel.symm sub_defn

/--
A binary operation that sums its operands, then subtracts an "error term".

An auxiliary definition that's useful in the proof of `sgn_diff_pow_pos` and
related lemmas. The "error term" only really lives up to its name when the
operands are sign values, i.e. are `0`, `1`, or `-1`. See `sgn_sum`.
-/
def sum_sub_err (a b : ℤ) : ℤ := a + b - a * b^2

/--
The function `sum_sub_err` respects equivalence of its left operand.

**Property intuition**: For `sum_sub_err` to be a function on integers, it must
obey this property.

**Proof intuition**: Substitute the left operand in the expression defining
`sum_sub_err`; this is possible because it uses substitutive operations.
-/
@[gcongr]
theorem sse_substL
    {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → sum_sub_err a₁ b ≃ sum_sub_err a₂ b
    := by
  intro (_ : a₁ ≃ a₂)
  show sum_sub_err a₁ b ≃ sum_sub_err a₂ b
  calc
    _ = sum_sub_err a₁ b  := rfl
    _ = a₁ + b - a₁ * b^2 := rfl
    _ ≃ a₂ + b - a₁ * b^2 := by srw [‹a₁ ≃ a₂›]
    _ ≃ a₂ + b - a₂ * b^2 := by srw [‹a₁ ≃ a₂›]
    _ = sum_sub_err a₂ b  := rfl

/--
The function `sum_sub_err` respects equivalence of its right operand.

**Property intuition**: For `sum_sub_err` to be a function on integers, it must
obey this property.

**Proof intuition**: Substitute the right operand in the expression defining
`sum_sub_err`; this is possible because it uses substitutive operations.
-/
@[gcongr]
theorem sse_substR
    {a b₁ b₂ : ℤ} : b₁ ≃ b₂ → sum_sub_err a b₁ ≃ sum_sub_err a b₂
    := by
  intro (_ : b₁ ≃ b₂)
  show sum_sub_err a b₁ ≃ sum_sub_err a b₂
  calc
    _ = sum_sub_err a b₁  := rfl
    _ = a + b₁ - a * b₁^2 := rfl
    _ ≃ a + b₂ - a * b₁^2 := by srw [‹b₁ ≃ b₂›]
    _ ≃ a + b₂ - a * b₂^2 := by srw [‹b₁ ≃ b₂›]
    _ = sum_sub_err a b₂  := rfl

/--
When invoked on the same value for both operands, where the value must be a
result of `sgn` (satisfying `a^3 ≃ a`), then `sum_sub_err` evaluates to that
value as well.

**Property and proof intuition**: Due to the sign value constraint `a^3 ≃ a`,
the "error term" reduces to `a`. Subtracting it from the `a + a` sum value
gives the result.
-/
theorem sse_same {a : ℤ} : a^3 ≃ a → sum_sub_err a a ≃ a := by
  intro (_ : a^3 ≃ a)
  show sum_sub_err a a ≃ a
  calc
    _ = sum_sub_err a a := rfl
    _ = a + a - a * a^2 := rfl
    _ ≃ a + a - a^3     := by srw [←cube_splitL]
    _ ≃ a + a - a       := by srw [‹a^3 ≃ a›]
    _ ≃ a + (a - a)     := sub_assoc_addL
    _ ≃ a + 0           := by srw [sub_same]
    _ ≃ a               := AA.identR

/--
A factor can be moved between the arguments of `sum_sub_err` and its result, if
that factor is equivalent to its own cube.

**Proof intuition**: Direct simplification using algebra. The assumption
`a^3 ≃ a` is only used once.
-/
theorem sse_compat_mul
    {a b c : ℤ}
    : a^3 ≃ a → sum_sub_err (a * b) (a * c) ≃ a * sum_sub_err b c
    := by
  intro (_ : a^3 ≃ a)
  show sum_sub_err (a * b) (a * c) ≃ a * sum_sub_err b c
  have pull_out_a : (a * b) * (a * c)^2 ≃ a * (b * c^2) := calc
    _ = (a * b) * (a * c)^2   := rfl
    _ ≃ (a * b) * (a^2 * c^2) := by srw [Natural.pow_distribR_mul]
    _ ≃ (a * a^2) * (b * c^2) := AA.expr_xxfxxff_lr_swap_rl
    _ ≃ a^3 * (b * c^2)       := by srw [←cube_splitL]
    _ ≃ a * (b * c^2)         := by srw [‹a^3 ≃ a›]
  calc
    _ = sum_sub_err (a * b) (a * c)         := rfl
    _ = a * b + a * c - (a * b) * (a * c)^2 := rfl
    _ ≃ a * (b + c) - (a * b) * (a * c)^2   := by srw [←mul_distribL]
    _ ≃ a * (b + c) - a * (b * c^2)         := by srw [pull_out_a]
    _ ≃ a * (b + c - b * c^2)               := Rel.symm AA.distribL
    _ = a * sum_sub_err b c                 := rfl

end sub_only
section sign_only
variable [Sign ℤ]

/--
The operations of `sgn` and `·^n` (i.e. raising to a natural number power) give
the same result when applied to an integer in either order.

**Property and proof intuition**: Take the property that `sgn` is compatible
with multiplication (`sgn (a * b) ≃ sgn a * sgn b`) and repeatedly apply it to
the product formed by `a^n`.
-/
theorem sgn_pow {a : ℤ} {n : ℕ} : sgn (a^n) ≃ (sgn a)^n := by
  apply Natural.ind_on n
  case zero =>
    show sgn (a^0) ≃ (sgn a)^0
    calc
      _ = sgn (a^0) := rfl
      _ ≃ sgn (1:ℤ) := by srw [Natural.pow_zero]
      _ ≃ 1         := sgn_positive.mp one_positive
      _ ≃ (sgn a)^0 := Rel.symm Natural.pow_zero
  case step =>
    intro (n' : ℕ) (ih : sgn (a^n') ≃ (sgn a)^n')
    show sgn (a^(step n')) ≃ (sgn a)^(step n')
    calc
      _ = sgn (a^(step n'))  := rfl
      _ ≃ sgn (a^n' * a)     := by srw [Natural.pow_step]
      _ ≃ sgn (a^n') * sgn a := sgn_compat_mul
      _ ≃ (sgn a)^n' * sgn a := by srw [ih]
      _ ≃ (sgn a)^(step n')  := Rel.symm Natural.pow_step

end sign_only

variable [Subtraction ℤ] [Sign ℤ]

/--
Zero and one are the only integers that are identical to their squares.

**Property intuition**: Negative integers become positive when squared, and all
integers greater than one increase in magnitude.

**Proof intuition**: Corollary of `mul_identR_reasons`.
-/
theorem sqr_idemp_reasons {a : ℤ} : a^2 ≃ a ↔ a ≃ 0 ∨ a ≃ 1 := calc
  _ ↔ a^2 ≃ a       := Iff.rfl
  _ ↔ a * a ≃ a     := by srw [Natural.pow_two]
  _ ↔ a ≃ 0 ∨ a ≃ 1 := mul_identR_reasons

/--
Zero, one, and negative one are the only integers that are identical to their
cubes.

**Property intuition**: The cubes of integers less than negative one or greater
than one will have absolute value greater than one. Negative one squared is
one, so adding another factor of `-1` to cube it makes the result negative one
as well. Zero and one stay the same when raised to any positive power.

**Proof intuition**: Rearrange `a^3 ≃ a` as `a^3 - a ≃ 0`. Factor the left hand
side into `a * (a - 1) * (a + 1)` using algebra and `factor_diff_squares`. Then
apply `mul_split_zero` twice and rearrange to get the result.
-/
theorem cube_idemp_reasons {a : ℤ} : a^3 ≃ a ↔ a ≃ 0 ∨ a ≃ 1 ∨ a ≃ -1 := by
  have nonzero_values : (a - 1) * (a + 1) ≃ 0 ↔ a ≃ 1 ∨ a ≃ -1 := calc
    _ ↔ (a - 1) * (a + 1) ≃ 0 := Iff.rfl
    _ ↔ a - 1 ≃ 0 ∨ a + 1 ≃ 0 := mul_split_zero
    _ ↔ a ≃ 1 ∨ a + 1 ≃ 0     := iff_subst_covar or_mapL zero_diff_iff_eqv
    _ ↔ a ≃ 1 ∨ a ≃ 0 - 1     := iff_subst_covar or_mapR subR_moveL_addR.symm
    _ ↔ a ≃ 1 ∨ a ≃ -1        := iff_subst_covar or_mapR (by srw [sub_identL])

  calc
    _ ↔ a^3 ≃ a                       := Iff.rfl
    _ ↔ a^3 ≃ a * 1                   := by srw [←mul_identR]
    _ ↔ a^3 ≃ a * 1^2                 := by srw [←Natural.pow_absorbL]
    _ ↔ a^3 - a * 1^2 ≃ 0             := zero_diff_iff_eqv.symm
    _ ↔ a * a^2 - a * 1^2 ≃ 0         := by srw [cube_splitL]
    _ ↔ a * (a^2 - 1^2) ≃ 0           := by srw [←mul_distribL_sub]
    _ ↔ a * ((a - 1) * (a + 1)) ≃ 0   := by srw [factor_diff_sqr]
    _ ↔ a ≃ 0 ∨ (a - 1) * (a + 1) ≃ 0 := mul_split_zero
    _ ↔ a ≃ 0 ∨ a ≃ 1 ∨ a ≃ -1        := iff_subst_covar or_mapR nonzero_values

/--
Cubing the sign of an integer has no effect.

**Property and proof intuition**: An integer's sign can only be zero, one, or
negative one. All three of those numbers remain the same when cubed, by
`cube_idemp_reasons`.
-/
theorem sgn_cubed {a : ℤ} : (sgn a)^3 ≃ sgn a := by
  have : sgn a ≃ 0 ∨ sgn a ≃ 1 ∨ sgn a ≃ -1 := match sgn_trichotomy a with
  | AA.OneOfThree₁.first (_ : sgn a ≃ 0) =>
    Or.inl ‹sgn a ≃ 0›
  | AA.OneOfThree₁.second (_ : sgn a ≃ 1) =>
    Or.inr (Or.inl ‹sgn a ≃ 1›)
  | AA.OneOfThree₁.third (_ : sgn a ≃ -1) =>
    Or.inr (Or.inr ‹sgn a ≃ -1›)
  have : (sgn a)^3 ≃ sgn a := cube_idemp_reasons.mpr this
  exact this

/--
The only values that are identical to their cube are the outputs of `sgn`.

**Property and proof intuition**: From `sgn_cubed`, we know that the outputs of
`sgn` are identical to their cube. And from `cube_idemp_reasons`, we know that
the values identical to their cube are the outputs of `sgn`.
-/
theorem cube_idemp_iff_sgn {a : ℤ} : a^3 ≃ a ↔ ∃ (b : ℤ), a ≃ sgn b := by
  apply Iff.intro
  case mp =>
    intro (_ : a^3 ≃ a)
    show ∃ (b : ℤ), a ≃ sgn b
    have : a ≃ 0 ∨ a ≃ 1 ∨ a ≃ -1 := cube_idemp_reasons.mp ‹a^3 ≃ a›
    have : sgn a ≃ a := sgn_fixed_points.mpr ‹a ≃ 0 ∨ a ≃ 1 ∨ a ≃ -1›
    exact Exists.intro a (Rel.symm ‹sgn a ≃ a›)
  case mpr =>
    intro (Exists.intro (b : ℤ) (_ : a ≃ sgn b))
    show a^3 ≃ a
    calc
      _ = a^3       := rfl
      _ ≃ (sgn b)^3 := by srw [‹a ≃ sgn b›]
      _ ≃ sgn b     := sgn_cubed
      _ ≃ a         := Rel.symm ‹a ≃ sgn b›

variable [Order ℤ]

/--
All integer squares are nonnegative.

**Property intuition**: A negative times a negative is positive.

**Proof intuition**: Direct corollary of `nonneg_square`.
-/
theorem sqr_nonneg {a : ℤ} : a^2 ≥ 0 := by
  have : sgn (a * a) ≄ -1 := nonneg_square
  calc
    _ = a^2   := rfl
    _ ≃ a * a := Natural.pow_two
    _ ≥ 0     := ge_zero_sgn.mpr ‹sgn (a * a) ≄ -1›

/--
Squaring the sign of an integer leaves it the same iff the integer is
nonnegative.

**Property and proof intuition**: Only zero and one stay the same when squared,
and those are the two sign values of nonnegative integers.
-/
theorem sgn_sqr_nonneg {a : ℤ} : (sgn a)^2 ≃ sgn a ↔ a ≥ 0 := calc
  _ ↔ (sgn a)^2 ≃ sgn a     := Iff.rfl
  _ ↔ sgn a ≃ 0 ∨ sgn a ≃ 1 := sqr_idemp_reasons
  _ ↔ a ≃ 0 ∨ sgn a ≃ 1     := iff_subst_covar or_mapL sgn_zero.symm
  _ ↔ a ≃ 0 ∨ a > 0         := iff_subst_covar or_mapR gt_zero_sgn.symm
  _ ↔ a > 0 ∨ a ≃ 0         := Or.comm
  _ ↔ a ≥ 0                 := ge_split.symm

/--
Squaring preserves the relative ordering of nonnegative integers.

**Property intuition**: Multiplication by a constant already has this property;
squaring merely increases the distance between integers proportionally to their
value.

**Proof intuition**: Factor `a^2 - b^2` as `(a - b) * (a + b)`. We would obtain
the goal if we could drop `a + b` from the product. So, first demonstrate that
`sgn (a - b) ≃ 0 ∨ sgn (a + b) ≃ 1` —— the left side happens when `a ≃ b ≃ 0`,
and the right side happens in all other cases. Then use that to invoke
`mul_identR_reasons` and complete the proof.
-/
theorem sgn_diff_sqr
    {a b : ℤ} : a ≥ 0 → b ≥ 0 → sgn (a^2 - b^2) ≃ sgn (a - b)
    := by
  intro (_ : a ≥ 0) (_ : b ≥ 0)
  show sgn (a^2 - b^2) ≃ sgn (a - b)
  have : a + b ≥ 0 := calc
    _ = a + b := rfl
    _ ≥ 0 + b := ge_addR.mp ‹a ≥ 0›
    _ ≥ 0 + 0 := ge_addL.mp ‹b ≥ 0›
    _ ≃ 0     := AA.identL
  have : a + b > 0 ∨ a + b ≃ 0 := ge_split.mp ‹a + b ≥ 0›
  have diff_zero_sum_one : sgn (a - b) ≃ 0 ∨ sgn (a + b) ≃ 1 := match this with
  | Or.inl (_ : a + b > 0) =>
    have : sgn (a + b) ≃ 1 := gt_zero_sgn.mp ‹a + b > 0›
    Or.inr ‹sgn (a + b) ≃ 1›
  | Or.inr (_ : a + b ≃ 0) =>
    have (And.intro (_ : a ≃ 0) (_ : b ≃ 0)) :=
      (zero_sum_split ‹a ≥ 0› ‹b ≥ 0›).mp ‹a + b ≃ 0›
    have : a ≃ b := Rel.trans ‹a ≃ 0› (Rel.symm ‹b ≃ 0›)
    have : a - b ≃ 0 := zero_diff_iff_eqv.mpr ‹a ≃ b›
    have : sgn (a - b) ≃ 0 := sgn_zero.mp ‹a - b ≃ 0›
    Or.inl ‹sgn (a - b) ≃ 0›
  calc
    _ = sgn (a^2 - b^2)           := rfl
    _ ≃ sgn ((a - b) * (a + b))   := by srw [factor_diff_sqr]
    _ ≃ sgn (a - b) * sgn (a + b) := sgn_compat_mul
    _ ≃ sgn (a - b)               := mul_identR_reasons.mpr diff_zero_sum_one

/--
Express the sign of the sum of two integers in terms of their individual signs.

The integers must have a nonnegative product; i.e. their signs must be nonzero
and identical, or at least one of them must be zero.

**Proof intuition**: Split the assumption into two cases: positive product or
zero product. A positive product implies that `a` and `b` have the same sign,
which is also the sign of their sum by `add_preserves_sign`. The goal is found
with an application of `sse_same`. In the zero product case, one of the values
must be zero, so `sgn (a + b) ≃ sgn a + sgn b` holds, by `sgn_sum_zero_term`.
The result follows because the remaining term in `sum_sub_err (sgn a) (sgn b)`
is zero when either of the inputs is zero.
-/
theorem sgn_sum
    {a b : ℤ} : a * b ≥ 0 → sgn (a + b) ≃ sum_sub_err (sgn a) (sgn b)
    := by
  intro (_ : a * b ≥ 0)
  show sgn (a + b) ≃ sum_sub_err (sgn a) (sgn b)
  have : a * b > 0 ∨ a * b ≃ 0 := ge_split.mp ‹a * b ≥ 0›
  match this with
  | Or.inl (_ : a * b > 0) =>
    have (And.intro (_ : sgn a ≃ sgn b) _) :=
      mul_gt_zero_iff_sgn_same.mp ‹a * b > 0›
    have : sgn (a + b) ≃ sgn a :=
      add_preserves_sign Rel.refl (Rel.symm ‹sgn a ≃ sgn b›)
    calc
      _ = sgn (a + b)                 := rfl
      _ ≃ sgn a                       := ‹sgn (a + b) ≃ sgn a›
      _ ≃ sum_sub_err (sgn a) (sgn a) := Rel.symm (sse_same sgn_cubed)
      _ ≃ sum_sub_err (sgn a) (sgn b) := by srw [‹sgn a ≃ sgn b›]
  | Or.inr (_ : a * b ≃ 0) =>
    let sa := sgn a; let sb := sgn b
    have : a ≃ 0 ∨ b ≃ 0 := mul_split_zero.mp ‹a * b ≃ 0›
    have : sgn (a + b) ≃ sa + sb := sgn_sum_zero_term ‹a ≃ 0 ∨ b ≃ 0›

    exact Rel.symm $ calc
      _ = sum_sub_err (sgn a) (sgn b)  := rfl
      _ = sum_sub_err sa sb            := rfl
      _ = sa + sb - sa * sb^2          := rfl
      _ ≃ sa + sb - sa * (sb * sb)     := by srw [Natural.pow_two]
      _ ≃ sa + sb - (sa * sb) * sb     := by srw [←AA.assoc]
      _ ≃ sa + sb - (sgn (a * b)) * sb := by srw [←sgn_compat_mul]
      _ ≃ sa + sb - (sgn (0:ℤ)) * sb   := by srw [‹a * b ≃ 0›]
      _ ≃ sa + sb - 0 * sb             := by srw [sgn_zero.mp Rel.refl]
      _ ≃ sa + sb - 0                  := by srw [mul_absorbL]
      _ ≃ sa + sb                      := sub_identR
      _ ≃ sgn (a + b)                  := Rel.symm ‹sgn (a + b) ≃ sa + sb›

/--
Raising two nonnegative integers to the same positive natural number power
preserves their ordering.

**Property intuition**: Raising a nonnegative integer to a positive power
increases it or leaves it the same. And since the integers are being raised to
the _same_ power, they will be scaled proportionally, as occurs with
`sgn_diff_sqr`.

**Proof intuition**: By induction on `n ≥ 1`. The base case of `n ≃ 1` is
trivial. The inductive case, for `n > 1`, proceeds by first reducing
`a^(step n) - b^(step n)` to `a^2 - b^2` using algebra and properties of `sgn`
and ordering, in particular `sgn_sum` and `sse_compat_mul`. Then the conclusion
is reached via `sgn_diff_sqr`.
-/
theorem sgn_diff_pow_pos
    {a b : ℤ} {n : ℕ} : a ≥ 0 → b ≥ 0 → n ≥ 1 → sgn (a^n - b^n) ≃ sgn (a - b)
    := by
  intro (_ : a ≥ 0) (_ : b ≥ 0) (_ : n ≥ 1)
  show sgn (a^n - b^n) ≃ sgn (a - b)

  let motive := λ (x : ℕ) => sgn (a^x - b^x) ≃ sgn (a - b)
  have motive_subst {x₁ x₂ : ℕ} : x₁ ≃ x₂ → motive x₁ → motive x₂ := by
    intro (_ : x₁ ≃ x₂) (_ : sgn (a^x₁ - b^x₁) ≃ sgn (a - b))
    show sgn (a^x₂ - b^x₂) ≃ sgn (a - b)
    calc
      _ = sgn (a^x₂ - b^x₂) := rfl
      _ ≃ sgn (a^x₁ - b^x₂) := by srw [←‹x₁ ≃ x₂›]
      _ ≃ sgn (a^x₁ - b^x₁) := by srw [←‹x₁ ≃ x₂›]
      _ ≃ sgn (a - b)       := ‹sgn (a^x₁ - b^x₁) ≃ sgn (a - b)›

  apply Natural.ind_from motive_subst ‹n ≥ 1›
  case base =>
    show sgn (a^1 - b^1) ≃ sgn (a - b)
    srw [Natural.pow_one, Natural.pow_one]
  case next =>
    intro (m : ℕ) (_ : m ≥ 1) (ih : sgn (a^m - b^m) ≃ sgn (a - b))
    show sgn (a^(step m) - b^(step m)) ≃ sgn (a - b)

    have expand
        : a^(step m) - b^(step m) ≃ a^m * (a - b) + (a^m - b^m) * b
        := calc
      _ = a^(step m) - b^(step m)           := rfl
      _ ≃ a^m*a - b^(step m)                := by srw [Natural.pow_step]
      _ ≃ a^m*a - b^m*b                     := by srw [Natural.pow_step]
      _ ≃ (a^m*a - a^m*b) + (a^m*b - b^m*b) := Rel.symm add_sub_telescope
      _ ≃ a^m * (a - b) + (a^m*b - b^m*b)   := by srw [←mul_distribL_sub]
      _ ≃ a^m * (a - b) + (a^m - b^m) * b   := by srw [←mul_distribR_sub]

    have : a * b ≥ 0 := mul_preserves_nonneg ‹a ≥ 0› ‹b ≥ 0›
    have : (sgn a)^2 ≃ sgn a := sgn_sqr_nonneg.mpr ‹a ≥ 0›
    have : sgn (a^m) ≃ sgn a := calc
      _ = sgn (a^m) := rfl
      _ ≃ (sgn a)^m := sgn_pow
      _ ≃ sgn a     := pow_absorbL ‹m ≥ 1› ‹(sgn a)^2 ≃ sgn a›
    have reduce : sum_sub_err (sgn (a^m)) (sgn b) ≃ sgn (a + b) := calc
      _ = sum_sub_err (sgn (a^m)) (sgn b) := rfl
      _ ≃ sum_sub_err (sgn a) (sgn b)     := by srw [‹sgn (a^m) ≃ sgn a›]
      _ ≃ sgn (a + b)                     := Rel.symm (sgn_sum ‹a * b ≥ 0›)

    have factor_sumL : sgn (a^m * (a - b)) ≃ sgn (a - b) * sgn (a^m) := calc
      _ = sgn (a^m * (a - b))     := rfl
      _ ≃ sgn (a^m) * sgn (a - b) := sgn_compat_mul
      _ ≃ sgn (a - b) * sgn (a^m) := AA.comm
    have factor_sumR : sgn ((a^m - b^m) * b) ≃ sgn (a - b) * sgn b := calc
      _ = sgn ((a^m - b^m) * b)   := rfl
      _ ≃ sgn (a^m - b^m) * sgn b := sgn_compat_mul
      _ ≃ sgn (a - b) * sgn b     := AA.substL ih

    let sab := sgn (a - b)
    let sam := sgn (a^m)
    let amab := a^m * (a - b)
    let abmb := (a^m - b^m) * b
    have : sgn (a * b) ≥ 0 := sgn_preserves_ge_zero.mp ‹a * b ≥ 0›
    have : sab^2 * sgn (a * b) ≥ 0 := mul_preserves_nonneg sqr_nonneg this
    have : sgn (amab * abmb) ≥ 0 := calc
      _ = sgn (amab * abmb)           := rfl
      _ ≃ sgn amab * sgn abmb         := sgn_compat_mul
      _ ≃ (sab * sam) * sgn abmb      := by srw [factor_sumL]
      _ ≃ (sab * sam) * (sab * sgn b) := by srw [factor_sumR]
      _ ≃ (sab * sab) * (sam * sgn b) := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ sab^2 * (sam * sgn b)       := by srw [←Natural.pow_two]
      _ ≃ sab^2 * (sgn a * sgn b)     := by srw [‹sam ≃ sgn a›]
      _ ≃ sab^2 * sgn (a * b)         := by srw [←sgn_compat_mul]
      _ ≥ 0                           := ‹sab^2 * sgn (a * b) ≥ 0›
    have : amab * abmb ≥ 0 := sgn_preserves_ge_zero.mpr ‹sgn (amab * abmb) ≥ 0›

    calc
      _ = sgn (a^(step m) - b^(step m))         := rfl
      _ ≃ sgn (a^m * (a - b) + (a^m - b^m) * b) := by srw [expand]
      _ ≃ sum_sub_err (sgn amab) (sgn abmb)     := sgn_sum ‹amab * abmb ≥ 0›
      _ ≃ sum_sub_err (sab * sam) (sgn abmb)    := by srw [factor_sumL]
      _ ≃ sum_sub_err (sab * sam) (sab * sgn b) := by srw [factor_sumR]
      _ ≃ sab * sum_sub_err sam (sgn b)         := sse_compat_mul sgn_cubed
      _ = sgn (a - b) * sum_sub_err sam (sgn b) := rfl
      _ ≃ sgn (a - b) * sgn (a + b)             := by srw [reduce]
      _ ≃ sgn ((a - b) * (a + b))               := Rel.symm sgn_compat_mul
      _ ≃ sgn (a^2 - b^2)                       := by srw [←factor_diff_sqr]
      _ ≃ sgn (a - b)                           := sgn_diff_sqr ‹a ≥ 0› ‹b ≥ 0›

/--
The ordering of two nonnegative integers, each raised to the same natural
number power (`sgn (a^n - b^n)`), is exactly the product of the ordering of the
original integers with the sign of the power.

**Property and proof intuition**: The power is either zero or positive. If it's
zero, then both sides of the equivalence are zero. If it's positive, then by
`sgn_diff_pow_pos` the powers can be dropped, and `sgn (n:ℤ)` can be included
because it's equivalent to one.
-/
theorem sgn_diff_pow
    {a b : ℤ} {n : ℕ}
    : a ≥ 0 → b ≥ 0 → sgn (a^n - b^n) ≃ sgn (a - b) * sgn (n:ℤ)
    := by
  intro (_ : a ≥ 0) (_ : b ≥ 0)
  show sgn (a^n - b^n) ≃ sgn (a - b) * sgn (n:ℤ)
  have : n ≥ 0 := Natural.ge_zero
  have : n > 0 ∨ n ≃ 0 := Natural.ge_split ‹n ≥ 0›
  match this.symm with
  | Or.inl (_ : n ≃ 0) =>
    calc
      _ = sgn (a^n - b^n)             := rfl
      _ ≃ sgn (a^0 - b^n)             := by srw [‹n ≃ 0›]
      _ ≃ sgn (a^0 - b^0)             := by srw [‹n ≃ 0›]
      _ ≃ sgn (1 - b^0)               := by srw [Natural.pow_zero]
      _ ≃ sgn ((1:ℤ) - 1)             := by srw [Natural.pow_zero]
      _ ≃ sgn (0:ℤ)                   := by srw [sub_same]
      _ ≃ 0                           := sgn_zero.mp Rel.refl
      _ ≃ sgn (a - b) * 0             := Rel.symm AA.absorbR
      _ ≃ sgn (a - b) * sgn (0:ℤ)     := by srw [←sgn_zero.mp Rel.refl]
      _ = sgn (a - b) * sgn ((0:ℕ):ℤ) := rfl
      _ ≃ sgn (a - b) * sgn (n:ℤ)     := by srw [←‹n ≃ 0›]
  | Or.inr (_ : n > 0) =>
    have : Positive n := Natural.lt_zero_pos.mpr ‹n > 0›
    have : n ≥ 1 := Natural.positive_ge.mp ‹Positive n›
    have : Positive (n:ℤ) := positive_intro_nat ‹Positive n› Rel.refl
    have : sgn (n:ℤ) ≃ 1 := sgn_positive.mp ‹Positive (n:ℤ)›
    calc
      _ = sgn (a^n - b^n)         := rfl
      _ ≃ sgn (a - b)             := sgn_diff_pow_pos ‹a ≥ 0› ‹b ≥ 0› ‹n ≥ 1›
      _ ≃ sgn (a - b) * 1         := Rel.symm AA.identR
      _ ≃ sgn (a - b) * sgn (n:ℤ) := by srw [←‹sgn (n:ℤ) ≃ 1›]

end Lean4Axiomatic.Integer

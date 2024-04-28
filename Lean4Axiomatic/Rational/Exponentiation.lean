import Lean4Axiomatic.Rational.Metric

/-!
# Rational numbers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Rational

open Lean4Axiomatic.Function (idx_fam_prop)
open Lean4Axiomatic.Logic (AP)
open Lean4Axiomatic.Metric (abs)
open Lean4Axiomatic.Natural (pow_step pow_zero step)
open Lean4Axiomatic.Signed (sgn)

/-! ## Derived properties for exponentiation to a natural number -/

section pow_nat

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Negation ℚ] [Subtraction ℚ] [Reciprocation ℚ] [Division ℚ]
    [Sign ℚ] [Order ℚ] [Metric ℚ] [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]

/--
Raising two ordered, nonnegative values to the same natural number power
preserves their ordering and nonnegativity.

**Property intuition**: We already know that products of any nonnegative values
remain nonnegative, and that the greater the inputs, the greater the result. So
it's not surprising that this also holds for powers of nonnegative values.

**Proof intuition**: Induction and algebra. Substitutions on ordering relations
are the key steps.
-/
theorem pow_substL_ge_nonneg
    {p q : ℚ} {n : ℕ} : p ≥ q ∧ q ≥ 0 → p^n ≥ q^n ∧ q^n ≥ 0
    := by
  intro (And.intro (_ : p ≥ q) (_ : q ≥ 0))
  show p^n ≥ q^n ∧ q^n ≥ 0
  apply Natural.ind_on n
  case zero =>
    show p^0 ≥ q^0 ∧ q^0 ≥ 0
    have : p^(0:ℕ) ≥ q^(0:ℕ) := calc
      _ ≃ p^0 := eqv_refl
      _ ≃ 1   := pow_zero
      _ ≃ q^0 := eqv_symm pow_zero
      _ ≥ q^0 := le_refl
    have : q^(0:ℕ) ≥ 0 := calc
      _ ≃ q^0 := eqv_refl
      _ ≃ 1   := pow_zero
      _ ≥ 0   := one_ge_zero
    exact And.intro ‹p^(0:ℕ) ≥ q^(0:ℕ)› ‹q^(0:ℕ) ≥ 0›
  case step =>
    intro (n' : ℕ) (And.intro (_ : p^n' ≥ q^n') (_ : q^n' ≥ 0))
    show p^(step n') ≥ q^(step n') ∧ q^(step n') ≥ 0
    have : p ≥ 0 := ge_trans ‹p ≥ q› ‹q ≥ 0›
    have : p^(step n') ≥ q^(step n') := calc
      _ ≃ p^(step n') := eqv_refl
      _ ≃ p^n' * p    := pow_step
      _ ≥ q^n' * p    := le_substL_mul_nonneg ‹p ≥ 0› ‹p^n' ≥ q^n'›
      _ ≥ q^n' * q    := le_substR_mul_nonneg ‹q^n' ≥ 0› ‹p ≥ q›
      _ ≃ q^(step n') := eqv_symm pow_step
    have : q^(step n') ≥ 0 := calc
      _ ≃ q^(step n') := eqv_refl
      _ ≃ q^n' * q    := pow_step
      _ ≥ 0 * q       := le_substL_mul_nonneg ‹q ≥ 0› ‹q^n' ≥ 0›
      _ ≃ 0           := mul_absorbL
    exact And.intro ‹p^(step n') ≥ q^(step n')› ‹q^(step n') ≥ 0›

/--
Raising two strictly ordered, nonnegative values to the same positive natural
number power preserves their strict ordering and nonnegativity.

**Property intuition**: We already know that products of any nonnegative values
remain nonnegative, and that the greater the inputs, the greater the result. So
it's not surprising that this also holds for powers of nonnegative values.

**Proof intuition**: Induction and algebra. Substitutions on ordering relations
are the key steps. The base case is a contradiction because `n > 0` is an
assumption, so there's a case split inside the inductive step to handle the
"real" base case of `n ≃ 1`.
-/
theorem pow_pos_substL_gt_nonneg
    {p q : ℚ} {n : ℕ} : n > 0 → p > q ∧ q ≥ 0 → p^n > q^n ∧ q^n ≥ 0
    := by
  intro (_ : n > 0) (And.intro (_ : p > q) (_ : q ≥ 0))
  revert ‹n > 0›
  show n > 0 → p^n > q^n ∧ q^n ≥ 0
  apply Natural.ind_on n
  case zero =>
    intro (_ : (0:ℕ) > 0)
    show p^0 > q^0 ∧ q^0 ≥ 0
    have : (0:ℕ) ≯ 0 := Natural.lt_zero
    exact absurd ‹(0:ℕ) > 0› ‹(0:ℕ) ≯ 0›
  case step =>
    intro (n' : ℕ) (ih : n' > 0 → p^n' > q^n' ∧ q^n' ≥ 0) (_ : step n' > 0)
    show p^(step n') > q^(step n') ∧ q^(step n') ≥ 0
    have : n' ≃ 0 ∨ n' > 0 := Natural.gt_split ‹step n' > 0›
    match this with
    | Or.inl (_ : n' ≃ 0) =>
      have pow_step_zero {x : ℚ} : x^(step n') ≃ x := calc
        _ ≃ x^(step n') := eqv_refl
        _ ≃ x^n' * x    := pow_step
        _ ≃ x^0 * x     := mul_substL (Natural.pow_substR ‹n' ≃ 0›)
        _ ≃ 1 * x       := mul_substL pow_zero
        _ ≃ x           := mul_identL
      have : p^(step n') > q^(step n') := calc
        _ ≃ p^(step n') := eqv_refl
        _ ≃ p           := pow_step_zero
        _ > q           := ‹p > q›
        _ ≃ q^(step n') := eqv_symm pow_step_zero
      have : q^(step n') ≥ 0 := calc
        _ ≃ q^(step n') := eqv_refl
        _ ≃ q           := pow_step_zero
        _ ≥ 0           := ‹q ≥ 0›
      exact And.intro ‹p^(step n') > q^(step n')› ‹q^(step n') ≥ 0›
    | Or.inr (_ : n' > 0) =>
      have (And.intro (_ : p^n' > q^n') (_ : q^n' ≥ 0)) := ih ‹n' > 0›
      have : p ≥ q := ge_cases.mpr (Or.inl ‹p > q›)
      have : p > 0 := trans_gt_ge_gt ‹p > q› ‹q ≥ 0›
      have : p^(step n') > q^(step n') := calc
        _ ≃ p^(step n') := eqv_refl
        _ ≃ p^n' * p    := pow_step
        _ > q^n' * p    := lt_substL_mul_pos ‹p > 0› ‹p^n' > q^n'›
        _ ≥ q^n' * q    := le_substR_mul_nonneg ‹q^n' ≥ 0› ‹p ≥ q›
        _ ≃ q^(step n') := eqv_symm pow_step
      have : q^(step n') ≥ 0 := calc
        _ ≃ q^(step n') := eqv_refl
        _ ≃ q^n' * q    := pow_step
        _ ≥ 0 * q       := le_substL_mul_nonneg ‹q ≥ 0› ‹q^n' ≥ 0›
        _ ≃ 0           := mul_absorbL
      exact And.intro ‹p^(step n') > q^(step n')› ‹q^(step n') ≥ 0›

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
      _ ≃ 1⁻¹         := recip_subst pow_zero
      _ ≃ 1           := recip_sqrt1
      _ ≃ (p⁻¹)^(0:ℕ) := eqv_symm pow_zero
  case step =>
    intro (n' : ℕ) (ih : (p^n')⁻¹ ≃ (p⁻¹)^n')
    show (p^(step n'))⁻¹ ≃ (p⁻¹)^(step n')
    calc
      _ ≃ (p^(step n'))⁻¹ := eqv_refl
      _ ≃ (p^n' * p)⁻¹    := recip_subst pow_step
      _ ≃ (p^n')⁻¹ * p⁻¹  := recip_compat_mul
      _ ≃ (p⁻¹)^n' * p⁻¹  := mul_substL ih
      _ ≃ (p⁻¹)^(step n') := eqv_symm pow_step

/--
Absolute value is semicompatible with the base argument of exponentiation.

**Property intuition**: Absolute value is compatible with multiplication, so
applying it to repeated multiplication means that it gets applied to every
factor in the expression.

**Proof intuition**: Induction and algebra.
-/
theorem pow_scompatL_abs {p : ℚ} {n : ℕ} : abs (p^n) ≃ (abs p)^n := by
  apply Natural.ind_on n
  case zero =>
    show abs (p^0) ≃ (abs p)^0
    have : sgn (1:ℚ) ≃ 1 := sgn_one
    have : abs (1:ℚ) ≃ 1 := abs_positive this
    calc
      _ ≃ abs (p^0) := eqv_refl
      _ ≃ abs 1     := abs_subst pow_zero
      _ ≃ 1         := ‹abs (1:ℚ) ≃ 1›
      _ ≃ (abs p)^0 := eqv_symm pow_zero
  case step =>
    intro (n' : ℕ) (ih : abs (p^n') ≃ (abs p)^n')
    show abs (p^(step n')) ≃ (abs p)^(step n')
    calc
      _ ≃ abs (p^(step n'))  := eqv_refl
      _ ≃ abs (p^n' * p)     := abs_subst pow_step
      _ ≃ abs (p^n') * abs p := abs_compat_mul
      _ ≃ (abs p)^n' * abs p := mul_substL ih
      _ ≃ (abs p)^(step n')  := eqv_symm pow_step

end pow_nat

/-! ## Axioms for exponentiation to an integer -/

/-- Operations for raising rational numbers to integer powers. -/
class Exponentiation.Ops
    {ℕ : outParam Type} (ℚ ℤ : Type)
    [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Core (ℤ := ℤ) ℚ]
    :=
  /-- Exponentiation to an integer power. -/
  _pow (p : ℚ) [AP (p ≄ 0)] (a : ℤ) : ℚ

/-- Enables the use of the `· ^ ·` operator for exponentiation. -/
infixr:80 " ^ " => Exponentiation.Ops._pow

/-- Properties of exponentiation to an integer. -/
class Exponentiation.Props
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]
    [Negation ℚ] [Sign ℚ] [Ops ℚ ℤ]
    :=
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

/-- All integer exponentiation axioms. -/
class Exponentiation
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]
    [Negation ℚ] [Sign ℚ]
    :=
  toOps : Exponentiation.Ops ℚ ℤ
  toProps : Exponentiation.Props ℚ

attribute [instance] Exponentiation.toOps
attribute [instance] Exponentiation.toProps

/-! ## Derived properties for exponentiation to an integer -/

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Negation ℚ] [Reciprocation ℚ] [Division ℚ] [Sign ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (· * ·)] [Exponentiation ℚ]

/--
Rational number exponentiation to an integer respects equivalence of the base
values.

**Property intuition**: For integer exponentiation to make sense as a function
on rationals, this needs to be true.

**Proof intuition**: Uses "difference" induction of the integer exponent. This
simplifies the goal from proving a property for all integers, to proving a
property for all differences of natural numbers. But this is exactly what's
needed to make use of `pow_diff`! After that, `pow_substL` for _natural number_
exponents completes the proof.

For difference induction to work, it also needs the `motive` predicate to
respect equivalence of its argument. This can be shown using the `pow_substR`
axiom for integer exponentiation of rationals.
-/
theorem pow_substL
    {p₁ p₂ : ℚ} {a : ℤ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁^a ≃ p₂^a
    := by
  intro (_ : p₁ ≃ p₂)
  show p₁^a ≃ p₂^a

  let motive (x : ℤ) : Prop := p₁^x ≃ p₂^x
  have motive_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → motive a₁ → motive a₂ := by
    intro (_ : a₁ ≃ a₂) (_ : motive a₁)
    show motive a₂
    have : p₁^a₁ ≃ p₂^a₁ := ‹motive a₁›
    have : p₁^a₂ ≃ p₂^a₂ := calc
      _ = p₁^a₂ := rfl
      _ ≃ p₁^a₁ := pow_substR (Rel.symm ‹a₁ ≃ a₂›)
      _ ≃ p₂^a₁ := ‹p₁^a₁ ≃ p₂^a₁›
      _ ≃ p₂^a₂ := pow_substR ‹a₁ ≃ a₂›
    have : motive a₂ := this
    exact this
  let idx_fam_motive := idx_fam_prop motive_subst

  have on_diff (n m : ℕ) : motive (n - m) := by
    show p₁^((n:ℤ) - (m:ℤ)) ≃ p₂^((n:ℤ) - (m:ℤ))
    calc
      _ ≃ p₁^((n:ℤ) - (m:ℤ)) := eqv_refl
      _ ≃ p₁^n / p₁^m        := pow_diff
      _ ≃ p₂^n / p₁^m        := div_substL (Natural.pow_substL ‹p₁ ≃ p₂›)
      _ ≃ p₂^n / p₂^m        := div_substR (Natural.pow_substL ‹p₁ ≃ p₂›)
      _ ≃ p₂^((n:ℤ) - (m:ℤ)) := eqv_symm pow_diff
  let ind_ctx := Integer.ind_ctx_prop on_diff

  have : motive a := ind_ctx.ind_diff a
  have : p₁^a ≃ p₂^a := this
  exact this

/--
Raising a nonzero rational number to any integer power gives a nonzero result.

**Property intuition**: As the product of two nonzero rational numbers is
nonzero, this is simply an extension of that fact to any number of
multiplications. "Negative" multiplications are accounted for because
reciprocals are always nonzero.

**Proof intuition**: Uses "difference" induction on the integer exponent,
simplifying the goal to showing that raising a nonzero rational to a difference
of natural numbers is nonzero, or more precisely that assuming the result is
zero leads to a contradiction. Converting this into a quotient of natural
number powers using `pow_diff`, we can obtain a contradiction by showing the
numerator must be zero (from the assumption) and nonzero (from the analogous
theorem for natural number powers).
-/
theorem pow_preserves_nonzero {p : ℚ} {a : ℤ} [AP (p ≄ 0)] : p^a ≄ 0 := by
  let motive (x : ℤ) : Prop := p^x ≄ 0
  have motive_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → motive a₁ → motive a₂ := by
    intro (_ : a₁ ≃ a₂) (_ : motive a₁)
    show motive a₂
    have : p^a₁ ≃ p^a₂ := pow_substR ‹a₁ ≃ a₂›
    have : p^a₁ ≄ 0 := ‹motive a₁›
    have : p^a₂ ≄ 0 := AA.neqv_substL ‹p^a₁ ≃ p^a₂› this
    have : motive a₂ := this
    exact this
  let idx_fam_motive := idx_fam_prop motive_subst

  have on_diff (n m : ℕ) : motive (n - m) := by
    intro (_ : p^((n:ℤ) - m) ≃ 0)
    show False
    have : p^n / p^m ≃ 0 :=
      eqv_trans (eqv_symm pow_diff) ‹p^((n:ℤ) - m) ≃ 0›
    have : p^n ≃ 0 := div_eqv_0.mp this
    have : p^n ≄ 0 := Natural.pow_preserves_nonzero_base ‹AP (p ≄ 0)›.ev
    exact absurd ‹p^n ≃ 0› ‹p^n ≄ 0›
  let ind_ctx := Integer.ind_ctx_prop on_diff

  have : motive a := ind_ctx.ind_diff a
  have : p^a ≄ 0 := this
  exact this

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
  _ ≃ p^((n:ℤ) - 0) := pow_substR (Rel.symm Integer.sub_identR)
  _ ≃ p^n / p^(0:ℕ) := pow_diff
  _ ≃ p^n / 1       := div_substR Natural.pow_zero
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
  _ ≃ p^(0 - (n:ℤ)) := pow_substR (Rel.symm Integer.sub_identL)
  _ ≃ p^(0:ℕ) / p^n := pow_diff
  _ ≃ 1 / p^n       := div_substL Natural.pow_zero

end Lean4Axiomatic.Rational

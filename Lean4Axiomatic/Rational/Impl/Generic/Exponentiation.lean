import Lean4Axiomatic.Rational.Exponentiation

/-! # Generic implementation of exponentiation to integers, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Lean4Axiomatic.Logic (AP)
open Lean4Axiomatic.Relation.Equivalence (EqvOp)

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Reciprocation ℚ] [Division ℚ] [Sign ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (mul := (· * ·)) (ident := (1 : ℚ))]

/--
Raises a nonzero rational number to an integer power, represented as the
difference between two natural numbers.

This is a prerequisite for defining a function that raises rational numbers to
integer powers directly, using integer "difference" induction.

**Definition intuition**: By the following informal reasoning:
```
  p^(n - m)
≃ p^(n + (-m))
≃ p^n * p^(-m)
≃ p^n * p^(-1 * m)
≃ p^n * (p^m)^(-1)
≃ p^n * (p^m)⁻¹
≃ p^n / p^m
```
-/
def on_diff_pow (n m : ℕ) (p : ℚ) [AP (p ≄ 0)] : ℚ := p^n / p^m

/--
The `on_diff_pow` function respects equivalence between differences of natural
numbers.

This is a prerequisite for defining a function that raises rational numbers to
integer powers directly, using integer "difference" induction.

**Property intuition**: There are many pairs of natural numbers whose
differences are equivalent to the same integer. The results of `on_diff_pow`
must also be equivalent for those pairs, for it to be correct as a function.

**Proof intuition**: We need to show that two fractions of rational numbers
raised to natural number powers are equivalent. So, divide them and show that
they reduce via algebra to the value `1`; this can only be the case if they are
the same.
-/
theorem on_diff_subst_pow
    {n₁ m₁ n₂ m₂ : ℕ}
    : (n₁:ℤ) - m₁ ≃ n₂ - m₂ → on_diff_pow (ℚ := ℚ) n₁ m₁ ≃ on_diff_pow n₂ m₂
    := by
  intro (_ : (n₁:ℤ) - m₁ ≃ n₂ - m₂)
  show on_diff_pow n₁ m₁ ≃ on_diff_pow n₂ m₂
  intro (p : ℚ) (_ : AP (p ≄ 0))
  show p^n₁ / p^m₁ ≃ p^n₂ / p^m₂

  have : (n₁:ℤ) + m₂ ≃ n₂ + m₁ :=
    Integer.sub_swap_add.mp ‹(n₁:ℤ) - m₁ ≃ n₂ - m₂›
  have : ((n₁ + m₂:ℕ):ℤ) ≃ ((m₁ + n₂:ℕ):ℤ) := calc
    _ = ((n₁ + m₂:ℕ):ℤ) := rfl
    _ ≃ (n₁:ℤ) + m₂     := AA.compat₂
    _ ≃ n₂ + m₁         := ‹(n₁:ℤ) + m₂ ≃ n₂ + m₁›
    _ ≃ m₁ + n₂         := Integer.add_comm
    _ ≃ ((m₁ + n₂:ℕ):ℤ) := Rel.symm AA.compat₂
  have : n₁ + m₂ ≃ m₁ + n₂ := AA.inject ‹((n₁ + m₂:ℕ):ℤ) ≃ ((m₁ + n₂:ℕ):ℤ)›

  have : (p^n₁ / p^m₁) / (p^n₂ / p^m₂) ≃ 1 := calc
    _ = (p^n₁ / p^m₁) / (p^n₂ / p^m₂) := rfl
    _ ≃ (p^n₁ * p^m₂) / (p^m₁ * p^n₂) := div_div_div
    _ ≃ p^(n₁ + m₂) / (p^m₁ * p^n₂)   := by srw [←Natural.pow_compatL_add]
    _ ≃ p^(n₁ + m₂) / p^(m₁ + n₂)     := by srw [←Natural.pow_compatL_add]
    _ ≃ p^(m₁ + n₂) / p^(m₁ + n₂)     := by srw [‹n₁ + m₂ ≃ m₁ + n₂›]
    _ ≃ 1                             := div_same
  have : p^n₁ / p^m₁ ≃ p^n₂ / p^m₂ := div_eqv_1.mp this
  exact this

variable [Integer.Induction.{1} ℤ]

/--
A "context" value that will be used to both (1) define the operation of
rational exponentiation to an integer using integer "difference" induction, and
(2) prove properties about that operation.

This definition itself is not needed outside of this file; it's just a helper.

The motive in this case is a constant function returning the type of the
exponentiation operation we want to define. The operation's type does not
include the integer exponent; that will be determined when integer recursion is
invoked using this context. Instead, think of this type as exponentiation to a
specific, but unspecified, integer value.
-/
private def ind_ctx
    : Integer.Induction.Context (λ (_ : ℤ) => (p : ℚ) → [AP (p ≄ 0)] → ℚ)
    :=
  Integer.ind_ctx_const on_diff_subst_pow

/--
Raise a nonzero rational number to an integer power.

**Definition intuition**: Uses the context and the integer argument to invoke
"difference" recursion, generating an exponentiation function of the type
specified in the context's motive. The nonzero rational base of the
exponentiation is then provided to that function, giving the final result.
-/
def _pow (p : ℚ) [AP (p ≄ 0)] (a : ℤ) : ℚ := ind_ctx.rec_diff a p

/--
Definitions in this file satisfy the requirements for operations raising
rational numbers to integer powers.

We want to use exponentiation syntax in the rest of this file, but also avoid
conflicts with the instance provided by the `Rational` class.

The constraint for `ℤ` to be an integer is needed to ensure that this doesn't
also generate an `Exponentiation.Ops ℚ ℕ`, hiding the `· ^ ·` operator for
natural number exponentiation.
-/
local instance exponentiation_ops : Exponentiation.Ops ℚ ℤ := {
  _pow := _pow
}

/--
The most important property of rational exponentiation to an integer: how to
express it in simpler terms as rational exponentiation to natural numbers.

**Property intuition**: See documentation for
`Rational.Exponentiation.Props.pow_diff`.

**Proof intuition**: The context provides a theorem relating "difference"
recursion to its underlying `on_diff` function. Use that, and expansion of
definitions, to reduce the left-hand side to the right-hand side.
-/
theorem pow_diff
    {p : ℚ} {n m : ℕ} [AP (p ≄ 0)] : p^((n:ℤ) - m) ≃ p^n / p^m
    := by
  let ctx := ind_ctx (ℚ := ℚ)

  have : ctx.rec_diff ((n:ℤ) - m) ≃ ctx.on_diff n m := ctx.rec_diff_eval
  have rec_eval
    : (x : ℚ) → [AP (x ≄ 0)] → ctx.rec_diff ((n:ℤ) - m) x ≃ ctx.on_diff n m x
    := this
  calc
    _ = p^((n:ℤ) - m)              := rfl
    _ = _pow p ((n:ℤ) - m)         := rfl
    _ = ctx.rec_diff ((n:ℤ) - m) p := rfl
    _ ≃ ctx.on_diff n m p          := rec_eval p
    _ = on_diff_pow n m p          := rfl
    _ = p^n / p^m                  := rfl

/--
Rational exponentiation to an integer respects equivalence of the integer
exponents.

**Property intuition**: See documentation for
`Rational.Exponentiation.Props.pow_substR`.

**Proof intuition**: The context provides a theorem showing "difference"
recursion respects equivalence on its integer argument. Use that, and expansion
of definitions, to show the required equivalence for exponentiation.
-/
theorem pow_substR
    {p : ℚ} [AP (p ≄ 0)] {a₁ a₂ : ℤ} : a₁ ≃ a₂ → p^a₁ ≃ p^a₂
    := by
  intro (_ : a₁ ≃ a₂)
  show p^a₁ ≃ p^a₂
  let ctx := ind_ctx (ℚ := ℚ)

  have : ctx.rec_diff a₁ ≃ ctx.rec_diff a₂ := ctx.rec_diff_subst ‹a₁ ≃ a₂›
  have rec_subst
    : (x : ℚ) → [AP (x ≄ 0)] → ctx.rec_diff a₁ x ≃ ctx.rec_diff a₂ x
    := this
  calc
    _ = p^a₁              := rfl
    _ = _pow p a₁         := rfl
    _ = ctx.rec_diff a₁ p := rfl
    _ ≃ ctx.rec_diff a₂ p := rec_subst p
    _ = _pow p a₂         := rfl
    _ = p^a₂              := rfl

/--
This file proves the theorems necessary for showing that its implementation of
rational exponentiation to integer powers is correct.
-/
def exponentiation_props : Exponentiation.Props ℚ := {
  pow_diff := pow_diff
  pow_substR := pow_substR
}

/--
This file is a complete and correct implementation of rational exponentiation
to an integer.
-/
def integer_exponentiation : Exponentiation ℚ := {
  toOps := exponentiation_ops
  toProps := exponentiation_props
}

end Lean4Axiomatic.Rational.Impl.Generic

import Lean4Axiomatic.Natural.Multiplication

/-! # Natural numbers: Euclidean division -/

namespace Lean4Axiomatic.Natural

open Logic (AP)

/-! ## Axioms -/

/--
Demonstrates a valid [Euclidean division](https://w.wiki/CnLb) of the first
parameter by the second.
-/
structure EuclideanDivision
    {ℕ : Type} [Core ℕ] [Addition ℕ] [Order ℕ] [Multiplication ℕ] (n m : ℕ)
    where
  /--
  The [quotient](https://w.wiki/CnLh) is the number of `m`s that can be added
  together without exceeding `n`.
  -/
  quotient : ℕ

  /--
  The [remainder](https://w.wiki/CnLt) is the amount to add to `m * quotient`
  to reach `n`.
  -/
  remainder : ℕ

  /-- How `n` is split between divisor (`m`), quotient, and remainder. -/
  div_eqv : n ≃ m * quotient + remainder

  /--
  The remainder is smaller than the divisor (`m`).

  If this were not true, the quotient could be increased by one, and the
  divisor subtracted from the remainder to bring it under the limit.
  -/
  rem_ub : remainder < m

/-- All natural number Euclidean division axioms. -/
class Division
    (ℕ : Type) [Core ℕ] [Addition ℕ] [Order ℕ] [Multiplication ℕ]
    where
  /-- Computes the Euclidean division of the first argument by the second. -/
  divide (n m : ℕ) [AP (m ≄ 0)] : EuclideanDivision n m

export Division (divide)

/-! ## Derived properties -/

variable
  {ℕ : Type}
    [Core ℕ] [Addition ℕ] [Order ℕ] [Multiplication ℕ] [Induction.{0} ℕ]
    [Division ℕ]

/-- Enables the `· ÷ ·` operator to be used for natural number division. -/
instance divide_op_inst
    : Operators.DivisionSign (λ n m : ℕ => [AP (m ≄ 0)] → EuclideanDivision n m)
    := {
  divisionSign := divide
}

/--
The quotient and remainder of a division are zero when the dividend is zero,
and vice versa.
-/
theorem div_zero
    {n m : ℕ} [AP (m ≄ 0)]
    : let d := divide n m; n ≃ 0 ↔ d.quotient ≃ 0 ∧ d.remainder ≃ 0
    := by
  intro d
  let q := d.quotient; let r := d.remainder
  apply Iff.intro
  case mp =>
    intro (_ : n ≃ 0)
    show q ≃ 0 ∧ r ≃ 0

    have : m * q + r ≃ 0 := calc
      _ = m * q + r := rfl
      _ ≃ n         := Rel.symm d.div_eqv
      _ ≃ 0         := ‹n ≃ 0›
    have (And.intro (_ : m * q ≃ 0) (_ : r ≃ 0)) :=
      zero_sum_split.mp ‹m * q + r ≃ 0›
    have : m ≃ 0 ∨ q ≃ 0 := mul_split_zero.mp ‹m * q ≃ 0›
    have : q ≃ 0 := this.resolve_left ‹AP (m ≄ 0)›.ev
    have : q ≃ 0 ∧ r ≃ 0 := And.intro ‹q ≃ 0› ‹r ≃ 0›
    exact this
  case mpr =>
    intro (And.intro (_ : q ≃ 0) (_ : r ≃ 0))
    show n ≃ 0

    calc
      _ = n         := rfl
      _ ≃ m * q + r := d.div_eqv
      _ ≃ m * 0 + 0 := by srw [‹q ≃ 0›, ‹r ≃ 0›]
      _ ≃ 0 + 0     := by srw [mul_zero]
      _ ≃ 0         := AA.identL

end Lean4Axiomatic.Natural

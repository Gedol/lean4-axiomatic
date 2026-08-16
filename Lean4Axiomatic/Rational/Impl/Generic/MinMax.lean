import Lean4Axiomatic.Rational.MinMax

/-! # Generic implementation of rational min and max, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Ordered (max min)
open Relation.Equivalence (EqvOp)
open Signed (sgn)

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Order ℚ]

/-- Implementation of `min`. -/
def _min (p q : ℚ) : ℚ := if decide (p < q) then p else q

/-- Implementation of `max`. -/
def _max (p q : ℚ) : ℚ := if decide (p > q) then p else q

local instance minmax_ops : MinMax.Ops ℚ := {
  _min := _min
  _max := _max
}

/--
The `min` function's possible return values are just its arguments.

**Proof intuition**: Case split on the outcome of the conditional test. Show
that both options lead to one of the argument values.
-/
theorem min_cases {p q : ℚ} : min p q ≃ p ∨ min p q ≃ q := by
  show
    (if decide (p < q) then p else q) ≃ p ∨
    (if decide (p < q) then p else q) ≃ q
  match decide (p < q) with
  | true =>
    apply Or.inl
    show (if true then p else q) ≃ p
    show p ≃ p
    exact eqv_refl
  | false =>
    apply Or.inr
    show (if false then p else q) ≃ q
    show q ≃ q
    exact eqv_refl

/--
The `min` function's result is less than or equivalent to its first argument.

**Proof intuition**: Case split on the conditional test, extracting the order
relation between the arguments in each case. Use that order relation, if
needed, to show that the property is correct.
-/
theorem min_leL {p q : ℚ} : min p q ≤ p := by
  show (if decide (p < q) then p else q) ≤ p
  match eq : decide (p < q) with
  | true =>
    show (if true then p else q) ≤ p
    show p ≤ p
    exact le_refl
  | false =>
    show (if false then p else q) ≤ p
    show q ≤ p
    have : ¬(p < q) := of_toBoolUsing_eq_false eq
    have : sgn (p - q) ≄ -1 := mt lt_sgn.mpr this
    have : q ≤ p := ge_sgn.mpr this
    exact this

/--
The `min` function's result is less than or equivalent to its second argument.

**Proof intuition**: Case split on the conditional test, extracting the order
relation between the arguments in each case. Use that order relation, if
needed, to show that the property is correct.
-/
theorem min_leR {p q : ℚ} : min p q ≤ q := by
  show (if decide (p < q) then p else q) ≤ q
  match eq : decide (p < q) with
  | true =>
    show (if true then p else q) ≤ q
    show p ≤ q
    have : p < q := of_toBoolUsing_eq_true eq
    have : p ≤ q := le_cases.mpr (Or.inl this)
    exact this
  | false =>
    show (if false then p else q) ≤ q
    show q ≤ q
    exact le_refl

/--
The `max` function's possible return values are just its arguments.

**Proof intuition**: Case split on the outcome of the conditional test. Show
that both options lead to one of the argument values.
-/
theorem max_cases {p q : ℚ} : max p q ≃ p ∨ max p q ≃ q := by
  show
    (if decide (p > q) then p else q) ≃ p ∨
    (if decide (p > q) then p else q) ≃ q
  match decide (p > q) with
  | true =>
    apply Or.inl
    show (if true then p else q) ≃ p
    show p ≃ p
    exact eqv_refl
  | false =>
    apply Or.inr
    show (if false then p else q) ≃ q
    show q ≃ q
    exact eqv_refl

/--
The `max` function's first argument is less than or equivalent to its result.

**Proof intuition**: Case split on the conditional test, extracting the order
relation between the arguments in each case. Use that order relation, if
needed, to show that the property is correct.
-/
theorem max_leL {p q : ℚ} : p ≤ max p q := by
  show p ≤ (if decide (p > q) then p else q)
  match eq : decide (p > q) with
  | true =>
    show p ≤ (if true then p else q)
    show p ≤ p
    exact le_refl
  | false =>
    show p ≤ (if false then p else q)
    show p ≤ q
    have : ¬(p > q) := of_toBoolUsing_eq_false eq
    have : sgn (p - q) ≄ 1 := mt gt_sgn.mpr this
    have : p ≤ q := le_sgn.mpr this
    exact this

/--
The `max` function's second argument is less than or equivalent to its result.

**Proof intuition**: Case split on the conditional test, extracting the order
relation between the arguments in each case. Use that order relation, if
needed, to show that the property is correct.
-/
theorem max_leR {p q : ℚ} : q ≤ max p q := by
  show q ≤ (if decide (p > q) then p else q)
  match eq : decide (p > q) with
  | true =>
    show q ≤ (if true then p else q)
    show q ≤ p
    have : p > q := of_toBoolUsing_eq_true eq
    have : q ≤ p := le_cases.mpr (Or.inl ‹q < p›)
    exact this
  | false =>
    show q ≤ (if false then p else q)
    show q ≤ q
    exact le_refl

@[implicit_reducible]
def minmax_props : MinMax.Props ℚ := {
  min_cases := min_cases
  min_leL := min_leL
  min_leR := min_leR
  max_cases := max_cases
  max_leL := max_leL
  max_leR := max_leR
}

@[implicit_reducible]
def minmax : MinMax ℚ := {
  toOps := minmax_ops
  toProps := minmax_props
}

end Lean4Axiomatic.Rational.Impl.Generic

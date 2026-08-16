import Lean4Axiomatic.Rational.Order

/-! # Rational numbers: minimum and maximum functions -/

namespace Lean4Axiomatic.Rational

open Logic (and_mapL and_mapR iff_subst_covar)
open Ordered (max min)
open Rel (iff_subst_eqv)
open Signed (sgn)

/-! ## Axioms -/

/-- Minimum and maximum functions on rational numbers. -/
class MinMax.Ops (ℚ : Type) where
  /-- Minimum. -/
  _min : ℚ → ℚ → ℚ

  /-- Maximum. -/
  _max : ℚ → ℚ → ℚ

/-- Enables the use of the standard names `min` and `max`. -/
instance ordered_ops_inst {ℚ : Type} [MinMax.Ops ℚ] : Ordered.Ops ℚ := {
  min := MinMax.Ops._min
  max := MinMax.Ops._max
}

/-- Properties of rational number minimum and maximum. -/
class MinMax.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Order ℚ] [Ops ℚ]
    where
  /-- `min`'s result can only be one of its inputs. -/
  min_cases {p q : ℚ} : min p q ≃ p ∨ min p q ≃ q

  /-- `min`'s result is less than or equivalent to its first input. -/
  min_leL {p q : ℚ} : min p q ≤ p

  /-- `min`'s result is less than or equivalent to its second input. -/
  min_leR {p q : ℚ} : min p q ≤ q

  /-- `max`'s result can only be one of its inputs. -/
  max_cases {p q : ℚ} : max p q ≃ p ∨ max p q ≃ q

  /-- `max`'s result is greater than or equivalent to its first input. -/
  max_leL {p q : ℚ} : p ≤ max p q

  /-- `max`'s result is greater than or equivalent to its second input. -/
  max_leR {p q : ℚ} : q ≤ max p q

export MinMax.Props (max_cases max_leL max_leR min_cases min_leL min_leR)

/-- All rational number minimum and maximum axioms. -/
class MinMax
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Order ℚ]
    where
  toOps : MinMax.Ops ℚ
  toProps : MinMax.Props ℚ

attribute [implicit_reducible, instance] MinMax.toOps
attribute [instance] MinMax.toProps

/-! ## Derived properties -/

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
  [Sign ℚ] [Subtraction ℚ] [Order ℚ] [MinMax ℚ]

/--
Ties the ordering of `min`'s operands to its result.

**Property intuition**: By definition, `min`'s result is less than or
equivalent to the other operand.

**Proof intuition**: The forward direction follows immediately from
substitution. In the reverse direction, one of the possible results of `min`
satisfies the goal directly. The other one implies that `min`'s operands are
equivalent, also satisfying the goal.
-/
theorem min_le {p q : ℚ} : min p q ≃ p ↔ p ≤ q := by
  apply Iff.intro
  case mp =>
    intro (_ : min p q ≃ p)
    show p ≤ q
    have : min p q ≤ q := min_leR
    have : p ≤ q := by prw [‹min p q ≃ p›] ‹min p q ≤ q›
    exact this
  case mpr =>
    intro (_ : p ≤ q)
    show min p q ≃ p
    have : min p q ≃ p ∨ min p q ≃ q := min_cases
    match this with
    | Or.inl (_ : min p q ≃ p) =>
      have := ‹min p q ≃ p›
      exact this
    | Or.inr (_ : min p q ≃ q) =>
      have : min p q ≤ p := min_leL
      have : q ≤ p := by prw [‹min p q ≃ q›] ‹min p q ≤ p›
      have : q ≃ p := le_antisymm ‹q ≤ p› ‹p ≤ q›
      have : min p q ≃ p := eqv_trans ‹min p q ≃ q› ‹q ≃ p›
      exact this

/--
Ties the ordering of `max`'s operands to its result.

**Property intuition**: By definition, `max`'s result is greater than or
equivalent to its other operand.

**Proof intuition**: The forward direction follows immediately from
substitution. In the reverse direction, one of the possible results of `max`
satisfies the goal directly. The other one implies that `max`'s operands are
equivalent, also satisfying the goal.
-/
theorem max_le {p q : ℚ} : max p q ≃ q ↔ p ≤ q := by
  apply Iff.intro
  case mp =>
    intro (_ : max p q ≃ q)
    show p ≤ q
    have : p ≤ max p q := max_leL
    have : p ≤ q := by prw [‹max p q ≃ q›] ‹p ≤ max p q›
    exact this
  case mpr =>
    intro (_ : p ≤ q)
    show max p q ≃ q
    have : max p q ≃ p ∨ max p q ≃ q := max_cases
    match this with
    | Or.inl (_ : max p q ≃ p) =>
      have : q ≤ max p q := max_leR
      have : q ≤ p := by prw [‹max p q ≃ p›] ‹q ≤ max p q›
      have : p ≃ q := le_antisymm ‹p ≤ q› ‹q ≤ p›
      have : max p q ≃ q := eqv_trans ‹max p q ≃ p› ‹p ≃ q›
      exact this
    | Or.inr (_ : max p q ≃ q) =>
      have := ‹max p q ≃ q›
      exact this

/--
Combine two upper bounds into a single one, selected by `min`.

**Property and proof intuition**: Whichever is the minimum upper bound, we
already know that `p` is less than or equivalent to it.
-/
theorem min_le_both {p q r : ℚ} : p ≤ q → p ≤ r → p ≤ min q r := by
  intro (_ : p ≤ q) (_ : p ≤ r)
  show p ≤ min q r
  have : min q r ≃ q ∨ min q r ≃ r := min_cases
  match this with
  | Or.inl (_ : min q r ≃ q) =>
    have : p ≤ min q r := by prw [←‹min q r ≃ q›] ‹p ≤ q›
    exact this
  | Or.inr (_ : min q r ≃ r) =>
    have : p ≤ min q r := by prw [←‹min q r ≃ r›] ‹p ≤ r›
    exact this

/--
Combine two lower bounds into a single one, selected by `max`.

**Property and proof intuition**: Whichever is the maximum lower bound, we
already know that `r` is greater than or equivalent to it.
-/
theorem max_le_both {p q r : ℚ} : p ≤ r → q ≤ r → max p q ≤ r := by
  intro (_ : p ≤ r) (_ : q ≤ r)
  show max p q ≤ r
  have : max p q ≃ p ∨ max p q ≃ q := max_cases
  match this with
  | Or.inl (_ : max p q ≃ p) =>
    have : max p q ≤ r := by prw [←‹max p q ≃ p›] ‹p ≤ r›
    exact this
  | Or.inr (_ : max p q ≃ q) =>
    have : max p q ≤ r := by prw [←‹max p q ≃ q›] ‹q ≤ r›
    exact this

/--
The `min` function is commutative.

**Property intuition**: Which argument is smaller does not depend on the order
they are given to the function.

**Proof intuition**: Consider all possible outputs of both `min p q` and
`min q p`. In two cases, they are trivially equivalent. In the other two cases,
they are opposite, but because the minimum is less than or equivalent to both
of them, it can be shown using substitution that they actually are equivalent.
-/
theorem min_comm {p q : ℚ} : min p q ≃ min q p := by
  have opposite_eqv
      {r s x y : ℚ} : min r s ≃ x → min s r ≃ y → min r s ≤ y → min s r ≤ x →
      min r s ≃ min s r
      := by
    intro (_ : min r s ≃ x) (_ : min s r ≃ y)
    intro (_ : min r s ≤ y) (_ : min s r ≤ x)
    show min r s ≃ min s r
    have : x ≤ y := by prw [‹min r s ≃ x›] ‹min r s ≤ y›
    have : y ≤ x := by prw [‹min s r ≃ y›] ‹min s r ≤ x›
    have : x ≃ y := le_antisymm ‹x ≤ y› ‹y ≤ x›
    have : min r s ≃ min s r := calc
      _ ≃ min r s := eqv_refl
      _ ≃ x       := ‹min r s ≃ x›
      _ ≃ y       := ‹x ≃ y›
      _ ≃ min s r := eqv_symm ‹min s r ≃ y›
    exact this

  have pq_cases : min p q ≃ p ∨ min p q ≃ q := min_cases
  have qp_cases : min q p ≃ q ∨ min q p ≃ p := min_cases
  match pq_cases with
  | Or.inl (_ : min p q ≃ p) =>
    match qp_cases with
    | Or.inl (_ : min q p ≃ q) =>
      have : min p q ≤ q := min_leR
      have : min q p ≤ p := min_leR
      have : min p q ≃ min q p :=
        opposite_eqv ‹min p q ≃ p› ‹min q p ≃ q› ‹min p q ≤ q› ‹min q p ≤ p›
      exact this
    | Or.inr (_ : min q p ≃ p) =>
      have : min p q ≃ min q p := calc
        _ ≃ min p q := eqv_refl
        _ ≃ p       := ‹min p q ≃ p›
        _ ≃ min q p := eqv_symm ‹min q p ≃ p›
      exact this
  | Or.inr (_ : min p q ≃ q) =>
    match qp_cases with
    | Or.inl (_ : min q p ≃ q) =>
      have : min p q ≃ min q p := calc
        _ ≃ min p q := eqv_refl
        _ ≃ q       := ‹min p q ≃ q›
        _ ≃ min q p := eqv_symm ‹min q p ≃ q›
      exact this
    | Or.inr (_ : min q p ≃ p) =>
      have : min p q ≤ p := min_leL
      have : min q p ≤ q := min_leL
      have : min p q ≃ min q p :=
        opposite_eqv ‹min p q ≃ q› ‹min q p ≃ p› ‹min p q ≤ p› ‹min q p ≤ q›
      exact this

/--
The `max` function is commutative.

**Property intuition**: Which argument is larger does not depend on the order
they are given to the function.

**Proof intuition**: Consider all possible outputs of both `max p q` and
`max q p`. In two cases, they are trivially equivalent. In the other two cases,
they are opposite, but because the maximum is greater than or equivalent to
both of them, it can be shown using substitution that they actually are
equivalent.
-/
theorem max_comm {p q : ℚ} : max p q ≃ max q p := by
  have opposite_eqv
      {r s x y : ℚ} : max r s ≃ x → max s r ≃ y → y ≤ max r s → x ≤ max s r →
      max r s ≃ max s r
      := by
    intro (_ : max r s ≃ x) (_ : max s r ≃ y)
    intro (_ : y ≤ max r s) (_ : x ≤ max s r)
    show max r s ≃ max s r
    have : y ≤ x := by prw [‹max r s ≃ x›] ‹y ≤ max r s›
    have : x ≤ y := by prw [‹max s r ≃ y›] ‹x ≤ max s r›
    have : x ≃ y := le_antisymm ‹x ≤ y› ‹y ≤ x›
    have : max r s ≃ max s r := calc
      _ ≃ max r s := eqv_refl
      _ ≃ x       := ‹max r s ≃ x›
      _ ≃ y       := ‹x ≃ y›
      _ ≃ max s r := eqv_symm ‹max s r ≃ y›
    exact this

  have pq_cases : max p q ≃ p ∨ max p q ≃ q := max_cases
  have qp_cases : max q p ≃ q ∨ max q p ≃ p := max_cases
  match pq_cases with
  | Or.inl (_ : max p q ≃ p) =>
    match qp_cases with
    | Or.inl (_ : max q p ≃ q) =>
      have : q ≤ max p q := max_leR
      have : p ≤ max q p := max_leR
      have : max p q ≃ max q p :=
        opposite_eqv ‹max p q ≃ p› ‹max q p ≃ q› ‹q ≤ max p q› ‹p ≤ max q p›
      exact this
    | Or.inr (_ : max q p ≃ p) =>
      have : max p q ≃ max q p := calc
        _ ≃ max p q := eqv_refl
        _ ≃ p       := ‹max p q ≃ p›
        _ ≃ max q p := eqv_symm ‹max q p ≃ p›
      exact this
  | Or.inr (_ : max p q ≃ q) =>
    match qp_cases with
    | Or.inl (_ : max q p ≃ q) =>
      have : max p q ≃ max q p := calc
        _ ≃ max p q := eqv_refl
        _ ≃ q       := ‹max p q ≃ q›
        _ ≃ max q p := eqv_symm ‹max q p ≃ q›
      exact this
    | Or.inr (_ : max q p ≃ p) =>
      have : p ≤ max p q := max_leL
      have : q ≤ max q p := max_leL
      have : max p q ≃ max q p :=
        opposite_eqv ‹max p q ≃ q› ‹max q p ≃ p› ‹p ≤ max p q› ‹q ≤ max q p›
      exact this

/--
Convert "ordered betweenness" to and from a "min-max" representation of "full"
betweenness.

This theorem holds the common logic for the ordered/min-max corollaries below.

**Property intuition**: The hypothesis that provides the ordering of the
exterior values is only needed for the reverse direction, to simplify `min` and
`max`. The forward direction is true just from the ordering implied by
"ordered betweenness".

**Proof intuition**: Use the hypothesis that orders the exterior values to
create equivalences for the `min` and `max` expressions. Then substitute those
equivalences on one side of the iff to produce the other.
-/
theorem order_iff_min_max
    {p q r : ℚ} : p ≤ q → (p ≤ r ∧ r ≤ q ↔ min p q ≤ r ∧ r ≤ max p q)
    := by
  intro (_ : p ≤ q)
  show p ≤ r ∧ r ≤ q ↔ min p q ≤ r ∧ r ≤ max p q
  have : p ≃ min p q := eqv_symm (min_le.mpr ‹p ≤ q›)
  have : q ≃ max p q := eqv_symm (max_le.mpr ‹p ≤ q›)
  have p_min : p ≤ r ↔ min p q ≤ r := iff_subst_eqv le_substL_eqv ‹p ≃ min p q›
  have q_max : r ≤ q ↔ r ≤ max p q := iff_subst_eqv le_substR_eqv ‹q ≃ max p q›
  calc
    _ ↔ p ≤ r ∧ r ≤ q             := Iff.rfl
    _ ↔ min p q ≤ r ∧ r ≤ q       := iff_subst_covar and_mapL p_min
    _ ↔ min p q ≤ r ∧ r ≤ max p q := iff_subst_covar and_mapR q_max

/--
Convert the "min-max" form of betweenness to "ordered betweenness", given an
ordering of the exterior values.

**Property and proof intuition**: Directly follows from `order_iff_min_max`.
-/
theorem order_from_min_max
    {p q r : ℚ} : min p q ≤ r ∧ r ≤ max p q → p ≤ q → p ≤ r ∧ r ≤ q
    := by
  intro (_ : min p q ≤ r ∧ r ≤ max p q) (_ : p ≤ q)
  show p ≤ r ∧ r ≤ q
  exact (order_iff_min_max ‹p ≤ q›).mpr ‹min p q ≤ r ∧ r ≤ max p q›

/--
A lemma that reverses the order of the operands in the "min-max" form of
betweenness.

**Property and proof intuition**: We already know that the `min` and `max`
functions are commutative; this is a trivial application of that property and
substitution.
-/
theorem min_max_comm
    {p q r : ℚ} : min p r ≤ q ∧ q ≤ max p r → min r p ≤ q ∧ q ≤ max r p
    := by
  intro (And.intro (_ : min p r ≤ q) (_ : q ≤ max p r))
  show min r p ≤ q ∧ q ≤ max r p
  have : min r p ≤ q := by prw [min_comm] ‹min p r ≤ q›
  have : q ≤ max r p := by prw [max_comm] ‹q ≤ max p r›
  exact And.intro ‹min r p ≤ q› ‹q ≤ max r p›

variable [Reciprocation ℚ] [Division ℚ] [Induction.{1} ℚ]

/--
Convert "ordered betweenness" to the "min-max" form of betweenness.

**Property and proof intuition**: Directly follows from `order_iff_min_max`;
the exterior values ordering hypothesis of that theorem can be derived from
"ordered betweenness".
-/
theorem min_max_from_order
    {p q r : ℚ} : p ≤ r ∧ r ≤ q → min p q ≤ r ∧ r ≤ max p q
    := by
  intro (order : p ≤ r ∧ r ≤ q)
  show min p q ≤ r ∧ r ≤ max p q
  have (And.intro (_ : p ≤ r) (_ : r ≤ q)) := order
  have : p ≤ q := le_trans ‹p ≤ r› ‹r ≤ q›
  have : min p q ≤ r ∧ r ≤ max p q := (order_iff_min_max this).mp order
  exact this

end Lean4Axiomatic.Rational

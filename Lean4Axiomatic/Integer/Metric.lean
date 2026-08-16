import Lean4Axiomatic.Integer.Exponentiation
import Lean4Axiomatic.Metric

/-! # Integer: metric functions -/

namespace Lean4Axiomatic.Integer

open Logic (AP Either iff_subst_covar or_merge)
open Metric (abs dist MetricSpace)
open Signed (Positive)

/-! ## Axioms -/

/-- Metric operations on integers. -/
class Metric.Ops (ℤ : Type) where
  /-- Absolute value. -/
  _abs : ℤ → ℤ

  /-- Distance. -/
  _dist : ℤ → ℤ → ℤ

/-- Enable use of the standard names for absolute value and distance. -/
instance metric_space_inst {ℤ : Type} [Metric.Ops ℤ] : MetricSpace ℤ := {
  abs := Metric.Ops._abs
  dist := Metric.Ops._dist
}

/-- Integer metric operation properties. -/
class Metric.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
      [Ops ℤ]
    where
  /-- Express absolute value in terms of the signum function. -/
  abs_sgn {a : ℤ} : abs a ≃ a * sgn a

export Metric.Props (abs_sgn)

/-- All integer metric axioms. -/
class Metric
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
    where
  toOps : Metric.Ops ℤ
  toProps : Metric.Props ℤ

attribute [implicit_reducible, instance] Metric.toOps
attribute [instance] Metric.toProps

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
    [Metric ℤ]

/-- Zero is the only integer with absolute value zero. -/
theorem abs_zero {a : ℤ} : abs a ≃ 0 ↔ a ≃ 0 := calc
  _ ↔ abs a ≃ 0         := Iff.rfl
  _ ↔ a * sgn a ≃ 0     := by srw [abs_sgn]
  _ ↔ a ≃ 0 ∨ sgn a ≃ 0 := mul_split_zero
  _ ↔ a ≃ 0 ∨ a ≃ 0     := iff_subst_covar Or.imp_right sgn_zero
  _ ↔ a ≃ 0             := or_merge

/-- Products and absolute values can be exchanged. -/
theorem abs_compat_mul {a b : ℤ} : abs (a * b) ≃ abs a * abs b := calc
  _ = abs (a * b)             := rfl
  _ ≃ a * b * (sgn (a * b))   := abs_sgn
  _ ≃ a * b * (sgn a * sgn b) := by srw [sgn_compat_mul]
  _ ≃ a * sgn a * (b * sgn b) := AA.expr_xxfxxff_lr_swap_rl
  _ ≃ abs a * abs b           := by srw [←abs_sgn, ←abs_sgn]

/-- Equivalent integers have equivalent absolute values. -/
@[gcongr]
theorem abs_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → abs a₁ ≃ abs a₂ := by
  intro (_ : a₁ ≃ a₂)
  show abs a₁ ≃ abs a₂
  calc
    _ = abs a₁      := rfl
    _ ≃ a₁ * sgn a₁ := abs_sgn
    _ ≃ a₂ * sgn a₁ := by srw [‹a₁ ≃ a₂›]
    _ ≃ a₂ * sgn a₂ := by srw [‹a₁ ≃ a₂›]
    _ ≃ abs a₂      := Rel.symm abs_sgn

/-- Absolute value removes negations from integer expressions. -/
theorem abs_neg {a : ℤ} : abs (-a) ≃ abs a := calc
  _ = abs (-a)        := rfl
  _ ≃ -a * sgn (-a)   := abs_sgn
  _ ≃ -a * -sgn a     := by srw [sgn_compat_neg]
  _ ≃ -(a * -sgn a)   := Rel.symm AA.scompatL
  _ ≃ -(-(a * sgn a)) := by srw [←AA.scompatR]
  _ ≃ a * sgn a       := neg_involutive
  _ ≃ abs a           := Rel.symm abs_sgn

variable
  [Natural.Exponentiation ℕ (α := ℤ) (mul := (· * ·)) (ident := (1 : ℤ))
    (minst := integer_mul_monoid)]

/-- The absolute value of an integer's sign is that sign squared. -/
theorem abs_sgn_sqr {a : ℤ} : abs (sgn a) ≃ (sgn a)^2 := calc
  _ = abs (sgn a)         := rfl
  _ ≃ sgn a * sgn (sgn a) := abs_sgn
  _ ≃ sgn a * sgn a       := by srw [sgn_idemp]
  _ ≃ (sgn a)^2           := Rel.symm Natural.pow_two

/-- The sign of an integer's absolute value is that integer's sign squared. -/
theorem sgn_abs {a : ℤ} : sgn (abs a) ≃ (sgn a)^2 := calc
  _ = sgn (abs a)         := rfl
  _ ≃ sgn (a * sgn a)     := by srw [abs_sgn]
  _ ≃ sgn a * sgn (sgn a) := sgn_compat_mul
  _ ≃ sgn a * sgn a       := by srw [sgn_idemp]
  _ ≃ (sgn a)^2           := Rel.symm Natural.pow_two

variable [Order ℤ] [Subtraction ℤ]

/-- An integer can be factored into a sign and a magnitude. -/
theorem abs_mul_sgn {a : ℤ} : sgn a * abs a ≃ a := by
  have : a ≃ 0 ∨ (sgn a)^2 ≃ 1 :=
    have : a ≃ 0 ∨ a ≄ 0 := (eqv? a 0).em
    have : a ≃ 0 ∨ (sgn a)^2 ≃ 1 := this.imp_right sgn_sqr_nonzero.mpr
    this
  calc
    _ = sgn a * abs a       := rfl
    _ ≃ abs a * sgn a       := AA.comm
    _ ≃ a * sgn a * sgn a   := by srw [abs_sgn]
    _ ≃ a * (sgn a * sgn a) := AA.assoc
    _ ≃ a * (sgn a)^2       := by srw [←Natural.pow_two]
    _ ≃ a                   := mul_identR_reasons.mpr ‹a ≃ 0 ∨ (sgn a)^2 ≃ 1›

/-- Absolute value is an identity function when its argument is nonnegative. -/
theorem abs_ident {a : ℤ} : a ≥ 0 → abs a ≃ a := by
  intro (_ : a ≥ 0)
  show abs a ≃ a
  calc
    _ = abs a                   := rfl
    _ ≃ a * sgn a               := abs_sgn
    _ ≃ a * (sgn a)^3           := by srw [←sgn_cubed]
    _ ≃ a * (sgn a * (sgn a)^2) := by srw [cube_splitL]
    _ ≃ (a * sgn a) * (sgn a)^2 := Rel.symm AA.assoc
    _ ≃ abs a * (sgn a)^2       := by srw [←abs_sgn]
    _ ≃ abs a * sgn a           := by srw [sgn_sqr_nonneg.mpr ‹a ≥ 0›]
    _ ≃ sgn a * abs a           := AA.comm
    _ ≃ a                       := abs_mul_sgn

/-- Squaring a number's absolute value is the same as squaring the number. -/
theorem abs_sqr {a : ℤ} : (abs a)^2 ≃ a^2 := calc
    _ = (abs a)^2           := rfl
    _ ≃ abs a * abs a       := Natural.pow_two
    _ ≃ a * sgn a * abs a   := by srw [abs_sgn]
    _ ≃ a * (sgn a * abs a) := AA.assoc
    _ ≃ a * a               := by srw [abs_mul_sgn]
    _ ≃ a^2                 := Rel.symm Natural.pow_two

/-- An integer's absolute value is nonnegative. -/
theorem abs_nonneg {a : ℤ} : abs a ≥ 0 :=
  have : (sgn (abs a))^2 ≃ sgn (abs a) := calc
    _ = (sgn (abs a))^2 := rfl
    _ ≃ sgn ((abs a)^2) := Rel.symm sgn_pow
    _ ≃ sgn (a^2)       := by srw [abs_sqr]
    _ ≃ (sgn a)^2       := sgn_pow
    _ ≃ sgn (abs a)     := Rel.symm sgn_abs
  have : abs a ≥ 0 := sgn_sqr_nonneg.mp ‹(sgn (abs a))^2 ≃ sgn (abs a)›
  this

/-- Simplify a sum of integers with opposite `sgn` factors into a difference. -/
theorem abs_pos_neg_sum
    {a b c d : ℤ} : c * d < 0 → abs (a * sgn c + b * sgn d) ≃ abs (a - b)
    := by
  intro (_ : c * d < 0)
  show abs (a * sgn c + b * sgn d) ≃ abs (a - b)

  have : (sgn c)^2 ≃ 1 :=
    have (And.intro _ (_ : c * d ≄ 0)) := lt_iff_le_neqv.mp ‹c * d < 0›
    have (And.intro (_ : c ≄ 0) _) := mul_split_neqv_zero.mp ‹c * d ≄ 0›
    have : (sgn c)^2 ≃ 1 := sgn_sqr_nonzero.mpr ‹c ≄ 0›
    this

  have : sgn d ≃ -sgn c := calc
    _ = sgn d                   := rfl
    _ ≃ sgn d * 1               := Rel.symm AA.identR
    _ ≃ sgn d * (sgn c)^2       := by srw [←‹(sgn c)^2 ≃ 1›]
    _ ≃ sgn d * (sgn c * sgn c) := by srw [Natural.pow_two]
    _ ≃ (sgn d * sgn c) * sgn c := Rel.symm AA.assoc
    _ ≃ sgn (d * c) * sgn c     := by srw [←sgn_compat_mul]
    _ ≃ sgn (c * d) * sgn c     := by srw [AA.comm]
    _ ≃ -1 * sgn c              := by srw [lt_zero_sgn.mp ‹c * d < 0›]
    _ ≃ -sgn c                  := mul_neg_one

  calc
    _ = abs (a * sgn c + b * sgn d)    := rfl
    _ ≃ abs (a * sgn c + b * -sgn c)   := by srw [‹sgn d ≃ -sgn c›]
    _ ≃ abs (a * sgn c + -(b * sgn c)) := by srw [←neg_scompatR_mul]
    _ ≃ abs (a * sgn c - b * sgn c)    := by srw [←sub_defn]
    _ ≃ abs ((a - b) * sgn c)          := by srw [←mul_distribR_sub]
    _ ≃ abs (a - b) * abs (sgn c)      := by srw [abs_compat_mul]
    _ ≃ abs (a - b) * (sgn c)^2        := by srw [abs_sgn_sqr]
    _ ≃ abs (a - b) * 1                := by srw [‹(sgn c)^2 ≃ 1›]
    _ ≃ abs (a - b)                    := by srw [mul_identR]

/--
An integer's sign can't be changed by subtracting a value of smaller magnitude
from it.
-/
theorem sgn_sub_absorbR {a b : ℤ} : abs a > abs b → sgn (a - b) ≃ sgn a := by
  intro (_ : abs a > abs b)
  show sgn (a - b) ≃ sgn a

  have : (sgn a)^2 ≃ 1 :=
    have : abs a > 0 := trans ‹abs a > abs b› abs_nonneg
    calc
      _ = (sgn a)^2   := rfl
      _ ≃ sgn (abs a) := Rel.symm sgn_abs
      _ ≃ 1           := gt_zero_sgn.mp ‹abs a > 0›

  have : Either (a * b > 0) (a * b ≤ 0) := either_gt_le
  match ‹Either (a * b > 0) (a * b ≤ 0)› with
  | Either.inl (_ : a * b > 0) =>
    have : Positive (a * b) := gt_zero_iff_pos.mp ‹a * b > 0›
    have : sgn a ≃ sgn b := positive_mul_imp_sgn_eqv ‹Positive (a * b)›
    have sgn_abs_diff : sgn (abs a - abs b) ≃ 1 := gt_sgn.mp ‹abs a > abs b›
    calc
      _ = sgn (a - b)                         := rfl
      _ ≃ sgn (a - b) * 1                     := Rel.symm AA.identR
      _ ≃ sgn (a - b) * (sgn a)^2             := by srw [←‹(sgn a)^2 ≃ 1›]
      _ ≃ sgn (a - b) * (sgn a * sgn a)       := by srw [Natural.pow_two]
      _ ≃ sgn (a - b) * sgn a * sgn a         := Rel.symm AA.assoc
      _ ≃ sgn (a - b) * sgn (sgn a) * sgn a   := by srw [←sgn_idemp]
      _ ≃ sgn ((a - b) * sgn a) * sgn a       := by srw [←sgn_compat_mul]
      _ ≃ sgn (a * sgn a - b * sgn a) * sgn a := by srw [mul_distribR_sub]
      _ ≃ sgn (a * sgn a - b * sgn b) * sgn a := by srw [‹sgn a ≃ sgn b›]
      _ ≃ sgn (abs a - abs b) * sgn a         := by srw [←abs_sgn, ←abs_sgn]
      _ ≃ 1 * sgn a                           := by srw [sgn_abs_diff]
      _ ≃ sgn a                               := AA.identL
  | Either.inr (_ : a * b ≤ 0) =>
    have : -b * a ≥ 0 := calc
      _ = -b * a   := rfl
      _ ≃ -(b * a) := Rel.symm AA.scompatL
      _ ≃ -(a * b) := by srw [AA.comm]
      _ ≥ -0       := by srw [‹a * b ≤ 0›]
      _ ≃ 0        := Rel.symm (neg_zero.mp Rel.refl)
    calc
      _ = sgn (a - b)                             := rfl
      _ ≃ sgn (a + -b)                            := by srw [sub_defn]
      _ ≃ sgn (-b + a)                            := by srw [AA.comm]
      _ ≃ sum_sub_err (sgn (-b)) (sgn a)          := sgn_sum ‹-b * a ≥ 0›
      _ = sgn (-b) + sgn a - sgn (-b) * (sgn a)^2 := rfl
      _ ≃ sgn a + sgn (-b) - sgn (-b) * (sgn a)^2 := by srw [AA.comm]
      _ ≃ sgn a + sgn (-b) - sgn (-b) * 1         := by srw [‹(sgn a)^2 ≃ 1›]
      _ ≃ sgn a + sgn (-b) - sgn (-b)             := by srw [mul_identR]
      _ ≃ sgn a + (sgn (-b) - sgn (-b))           := sub_assoc_addL
      _ ≃ sgn a + 0                               := by srw [sub_same]
      _ ≃ sgn a                                   := AA.identR

/--
Convert between two expressions of one integer's magnitude being smaller than
another's.
-/
theorem abs_upper_bound {a b : ℤ} : abs a < b ↔ -b < a ∧ a < b := by
  apply Iff.intro
  case mp =>
    intro (_ : abs a < b)
    show -b < a ∧ a < b

    have : sgn b ≃ 1 := gt_zero_sgn.mp (trans ‹b > abs a› abs_nonneg)
    have : abs b > abs a := calc
      _ = abs b     := rfl
      _ ≃ b * sgn b := abs_sgn
      _ ≃ b * 1     := by srw [‹sgn b ≃ 1›]
      _ ≃ b         := AA.identR
      _ > abs a     := ‹b > abs a›

    have : a < b :=
      have : sgn (b - a) ≃ 1 := calc
        _ = sgn (b - a) := rfl
        _ ≃ sgn b       := sgn_sub_absorbR ‹abs b > abs a›
        _ ≃ 1           := ‹sgn b ≃ 1›
      have : a < b := gt_sgn.mpr ‹sgn (b - a) ≃ 1›
      this

    have : -b < a :=
      have : abs (-b) > abs a := calc
        _ = abs (-b) := rfl
        _ ≃ abs b    := abs_neg
        _ > abs a    := ‹abs b > abs a›
      have : sgn (-b - a) ≃ -1 := calc
        _ = sgn (-b - a) := rfl
        _ ≃ sgn (-b)     := sgn_sub_absorbR ‹abs (-b) > abs a›
        _ ≃ -sgn b       := sgn_compat_neg
        _ ≃ -1           := by srw [‹sgn b ≃ 1›]
      have : -b < a := lt_sgn.mpr ‹sgn (-b - a) ≃ -1›
      this

    exact And.intro ‹-b < a› ‹a < b›
  case mpr =>
    intro (_ : -b < a ∧ a < b)
    have (And.intro (_ : -b < a) (_ : a < b)) := ‹-b < a ∧ a < b›
    show abs a < b

    have : Either (a ≥ 0) (-a ≥ 0) := either_nonneg
    match ‹Either (a ≥ 0) (-a ≥ 0)› with
    | .inl (_ : a ≥ 0) =>
      calc
        _ = abs a := rfl
        _ ≃ a     := abs_ident ‹a ≥ 0›
        _ < b     := ‹a < b›
    | .inr (_ : -a ≥ 0) =>
      calc
        _ = abs a    := rfl
        _ ≃ abs (-a) := Rel.symm abs_neg
        _ ≃ -a       := abs_ident ‹-a ≥ 0›
        _ < -(-b)    := by srw [‹-b < a›]
        _ ≃ b        := neg_involutive

end Lean4Axiomatic.Integer

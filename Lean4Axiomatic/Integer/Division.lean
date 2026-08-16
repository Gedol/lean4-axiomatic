import Lean4Axiomatic.Integer.Metric

/-! # Integers: Division -/

namespace Lean4Axiomatic.Integer

open Lean4Axiomatic.Metric (abs)
open Logic (AP or_identR)
open Relation.Equivalence (EqvOp)
open Signed (Positive)

/-! ## Axioms -/

/--
Any division operation of the first parameter by the second must satisfy these
requirements.
-/
structure BaseDivision
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
      [Metric ℤ] [Order ℤ]
    (a b : ℤ)
    where
  /--
  The [quotient](https://w.wiki/CnLh) is the number of `b`s that can be added
  together without exceeding `a`.
  -/
  quotient : ℤ

  /--
  The [remainder](https://w.wiki/CnLt) is the amount to add to `b * quotient`
  to reach `a`.
  -/
  remainder : ℤ

  /-- How `a` is split between divisor (`b`), quotient, and remainder. -/
  div_eqv : a ≃ b * quotient + remainder

  /--
  The remainder is closer to zero than the divisor (`b`).

  If this were not true, the quotient could be increased or decreased by one,
  and the magnitude of the divisor subtracted from the remainder to bring it
  under the limit.
  -/
  rem_mag : abs remainder < abs b

/--
Demonstrates a valid [Euclidean division](https://w.wiki/CnLb) of the first
parameter by the second.
-/
structure EuclideanDivision
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
      [Metric ℤ] [Order ℤ]
    (a b : ℤ) extends BaseDivision a b
    where
  /-- The remainder is nonnegative. -/
  rem_sgn : remainder ≥ 0

/--
Demonstrates a valid [floored division](https://w.wiki/Cyft) of the first
parameter by the second.
-/
structure FlooredDivision
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
      [Metric ℤ] [Order ℤ]
    (a b : ℤ) extends BaseDivision a b
    where
  /-- The remainder is either zero or the same sign as the divisor. -/
  rem_sgn : remainder * b ≥ 0

/-- All integer division axioms. -/
class Division
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
      [Sign ℤ] [Metric ℤ]
    where
  /-- Computes the Euclidean division of the first argument by the second. -/
  div_euclidean (a b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b

  /-- Computes the floored division of the first argument by the second. -/
  div_floored (a b : ℤ) [AP (b ≄ 0)] : FlooredDivision a b

export Division (div_euclidean div_floored)

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Subtraction ℤ] [Sign ℤ] [Metric ℤ] [Natural.Exponentiation ℕ ℤ]

/-- Every `BaseDivision`'s divisor must be nonzero. -/
theorem baseDiv_nonzero_divisor {a b : ℤ} (d : BaseDivision a b) : b ≄ 0 := by
  have : abs b > 0 := calc
    _ = abs b           := rfl
    _ > abs d.remainder := d.rem_mag
    _ ≥ 0               := abs_nonneg
  have (And.intro _ (_ : 0 ≄ abs b)) := lt_iff_le_neqv.mp ‹abs b > 0›
  have : b ≄ 0 := mt abs_zero.mpr (Rel.symm ‹0 ≄ abs b›)
  exact this

/--
All `FlooredDivision` values with the same dividend and divisor also have the
same quotient and remainder.
-/
theorem flooredDiv_unique
    {a b : ℤ} (d₁ d₂ : FlooredDivision a b)
    : d₁.quotient ≃ d₂.quotient ∧ d₁.remainder ≃ d₂.remainder
    := by
  let q₁ := d₁.quotient; let q₂ := d₂.quotient
  let r₁ := d₁.remainder; let r₂ := d₂.remainder
  show q₁ ≃ q₂ ∧ r₁ ≃ r₂

  -- Subtract one `div_eqv` from the other and put the remainders on one side
  have : abs (r₂ - r₁) ≃ abs b * abs (q₁ - q₂) :=
    have eqv_rw {q r : ℤ} : a ≃ b * q + r ↔ r ≃ a - b * q := calc
      /- Shorten with future tactic -/
      _ ↔ a ≃ b * q + r                      := Iff.rfl
      _ ↔ b * q + r ≃ a                      := Iff.intro Rel.symm Rel.symm
      _ ↔ r + b * q ≃ a                      := by srw [AA.comm]
      _ ↔ r + b * q - b * q ≃ a - b * q      := sub_injectR.symm
      _ ↔ r + b * q + -(b * q) ≃ a - b * q   := by srw [sub_defn]
      _ ↔ r + (b * q + -(b * q)) ≃ a - b * q := by srw [AA.assoc]
      _ ↔ r + 0 ≃ a - b * q                  := by srw [neg_invR]
      _ ↔ r ≃ a - b * q                      := by srw [add_identR]
    have lr_swap_rr {w x y z : ℤ} : (w + x) + (y + z) ≃ (w + z) + (y + x) :=
      AA.expr_xxfxxff_lr_swap_rr
    calc
      _ = abs (r₂ - r₁)                       := rfl
      _ ≃ abs (a - b * q₂ - r₁)               := by srw [eqv_rw.mp d₂.div_eqv]
      _ ≃ abs (a - b * q₂ - (a - b * q₁))     := by srw [eqv_rw.mp d₁.div_eqv]
      -- ↓ shorten with future tactic ↓
      _ ≃ abs (a + -(b * q₂) + -(a - b * q₁)) := by srw [sub_defn, sub_defn]
      _ ≃ abs (a + -(b * q₂) + (b * q₁ - a))  := by srw [sub_neg_flip]
      _ ≃ abs (a + -(b * q₂) + (b * q₁ + -a)) := by srw [sub_defn]
      _ ≃ abs (a + -a + (b * q₁ + -(b * q₂))) := by srw [lr_swap_rr]
      _ ≃ abs (0 + (b * q₁ + -(b * q₂)))      := by srw [neg_invR]
      _ ≃ abs (b * q₁ + -(b * q₂))            := by srw [add_identL]
      _ ≃ abs (b * q₁ - b * q₂)               := by srw [←sub_defn]
      _ ≃ abs (b * (q₁ - q₂))                 := by srw [←mul_distribL_sub]
      -- ↑ shorten with future tactic ↑
      _ ≃ abs b * abs (q₁ - q₂)               := abs_compat_mul

  have : abs (q₁ - q₂) < 1 :=
    have : b ≄ 0 := baseDiv_nonzero_divisor d₁.toBaseDivision
    have : (sgn b)^2 ≃ 1 := sgn_sqr_nonzero.mpr ‹b ≄ 0›

    have rem_diff_bound
        (ds dt : FlooredDivision a b)
        : let s := ds.remainder; let t := dt.remainder
          -- Read as: abs b > (s - t) * sgn b
          sgn (abs b - (s - t) * sgn b) ≃ 1
        := by
      intro (s : ℤ) (t : ℤ)
      show sgn (abs b - (s - t) * sgn b) ≃ 1

      -- The remainder is too close to `b` to change its sign by subtraction
      have : sgn (b - s) ≃ sgn b := sgn_sub_absorbR ds.rem_mag
      have : t * (b - s) ≥ 0 :=
        have : sgn (t * (b - s)) ≃ sgn (t * b) := calc
          _ = sgn (t * (b - s))   := rfl
          _ ≃ sgn t * sgn (b - s) := sgn_compat_mul
          _ ≃ sgn t * sgn b       := by srw [‹sgn (b - s) ≃ sgn b›]
          _ ≃ sgn (t * b)         := Rel.symm sgn_compat_mul
        have : (sgn (t * (b - s)))^2 ≃ sgn (t * (b - s)) := calc
          _ = (sgn (t * (b - s)))^2 := rfl
          _ ≃ (sgn (t * b))^2       := by srw [‹sgn (t * (b-s)) ≃ sgn (t * b)›]
          _ ≃ sgn (t * b)           := sgn_sqr_nonneg.mpr dt.rem_sgn
          _ ≃ sgn (t * (b - s))     := Rel.symm ‹sgn (t * (b-s)) ≃ sgn (t * b)›
        have : t * (b - s) ≥ 0 :=
          sgn_sqr_nonneg.mp ‹(sgn (t * (b - s)))^2 ≃ sgn (t * (b - s))›
        this

      -- Abbreviations so the lines below fit within the margin
      let sb := sgn b; let st := sgn t
      /-
      The difference of remainders is too close to `b` to change its sign by
      subtraction.
      -/
      have : sgn (b - (s - t)) ≃ sgn b := calc
        _ = sgn (b - (s - t))                 := rfl
        -- ↓ shorten with future tactic ↓
        _ ≃ sgn (b + -(s - t))                := by srw [sub_defn]
        _ ≃ sgn (b + (t - s))                 := by srw [sub_neg_flip]
        _ ≃ sgn (b + t - s)                   := by srw [←sub_assoc_addL]
        _ ≃ sgn (t + b - s)                   := by srw [AA.comm]
        _ ≃ sgn (t + (b - s))                 := by srw [sub_assoc_addL]
        -- ↑ shorten with future tactic ↑
        _ ≃ sum_sub_err (sgn t) (sgn (b - s)) := sgn_sum ‹t * (b - s) ≥ 0›
        _ ≃ sum_sub_err st sb                 := by srw [‹sgn (b - s) ≃ sb›]
        _ = st + sb - st * sb^2               := rfl
        -- ↓ shorten with future tactic ↓
        _ ≃ sb + st - st * sb^2               := by srw [AA.comm]
        _ ≃ sb + st - st * 1                  := by srw [‹sb^2 ≃ 1›]
        _ ≃ sb + st - st                      := by srw [mul_identR]
        _ ≃ sb + (st - st)                    := by srw [sub_assoc_addL]
        _ ≃ sb + 0                            := by srw [sub_same]
        -- ↑ shorten with future tactic ↑
        _ ≃ sgn b                             := AA.identR
      calc
        _ = sgn (abs b - (s - t) * sb)  := rfl
        _ ≃ sgn (b * sb - (s - t) * sb) := by srw [abs_sgn]
        _ ≃ sgn ((b - (s - t)) * sb)    := by srw [←mul_distribR_sub]
        _ ≃ sgn (b - (s - t)) * sgn sb  := by srw [sgn_compat_mul]
        _ ≃ sb * sgn sb                 := by srw [‹sgn (b - (s - t)) ≃ sb›]
        _ ≃ sb * sb                     := by srw [sgn_idemp]
        _ ≃ sb^2                        := Rel.symm Natural.pow_two
        _ ≃ 1                           := ‹sb^2 ≃ 1›

    have : abs (r₂ - r₁) < abs b :=
      have : (r₂ - r₁) * sgn b < abs b :=
        have : sgn (abs b - (r₂ - r₁) * sgn b) ≃ 1 := rem_diff_bound d₂ d₁
        gt_sgn.mpr ‹sgn (abs b - (r₂ - r₁) * sgn b) ≃ 1›
      have : -abs b < (r₂ - r₁) * sgn b :=
        have : sgn ((r₂ - r₁) * sgn b - (-abs b)) ≃ 1 := calc
          /- Shorten with future tactic -/
          _ = sgn ((r₂ - r₁) * sgn b - (-abs b))  := rfl
          _ ≃ sgn ((r₂ - r₁) * sgn b + -(-abs b)) := by srw [sub_defn]
          _ ≃ sgn ((r₂ - r₁) * sgn b + abs b)     := by srw [neg_involutive]
          _ ≃ sgn (abs b + (r₂ - r₁) * sgn b)     := by srw [AA.comm]
          _ ≃ sgn (abs b + -(r₁ - r₂) * sgn b)    := by srw [←sub_neg_flip]
          _ ≃ sgn (abs b + -((r₁ - r₂) * sgn b))  := by srw [←AA.scompatL]
          _ ≃ sgn (abs b - (r₁ - r₂) * sgn b)     := by srw [←sub_defn]
          _ ≃ 1                                   := rem_diff_bound d₁ d₂
        have : -abs b < (r₂ - r₁) * sgn b :=
          gt_sgn.mpr ‹sgn ((r₂ - r₁) * sgn b - (-abs b)) ≃ 1›
        this
      have : abs ((r₂ - r₁) * sgn b) < abs b :=
        abs_upper_bound.mpr
          (And.intro ‹-abs b < (r₂ - r₁) * sgn b› ‹(r₂ - r₁) * sgn b < abs b›)
      calc
        _ = abs (r₂ - r₁)               := rfl
        _ ≃ abs (r₂ - r₁) * 1           := Rel.symm mul_identR
        _ ≃ abs (r₂ - r₁) * (sgn b)^2   := by srw [←‹(sgn b)^2 ≃ 1›]
        _ ≃ abs (r₂ - r₁) * abs (sgn b) := by srw [←abs_sgn_sqr]
        _ ≃ abs ((r₂ - r₁) * sgn b)     := Rel.symm abs_compat_mul
        _ < abs b                       := ‹abs ((r₂ - r₁) * sgn b) < abs b›

    have : abs (q₁ - q₂) < 1 :=
      -- Abbreviations so the lines below fit within the margin
      let mb := abs b; let dqs := abs (q₁ - q₂); let drs := abs (r₂ - r₁)
      have : sgn (1 - dqs) ≃ 1 := calc
        /- Shorten with future tactic -/
        _ = sgn (1 - dqs)             := rfl
        _ ≃ 1 * sgn (1 - dqs)         := Rel.symm AA.identL
        _ ≃ (sgn b)^2 * sgn (1 - dqs) := by srw [←‹(sgn b)^2 ≃ 1›]
        _ ≃ sgn mb * sgn (1 - dqs)    := by srw [←sgn_abs]
        _ ≃ sgn (mb * (1 - dqs))      := Rel.symm sgn_compat_mul
        _ ≃ sgn (mb * 1 - mb * dqs)   := by srw [mul_distribL_sub]
        _ ≃ sgn (mb - mb * dqs)       := by srw [mul_identR]
        _ ≃ sgn (mb - drs)            := by srw [←‹drs ≃ mb * dqs›]
        _ ≃ 1                         := gt_sgn.mp ‹drs < mb›
      have : abs (q₁ - q₂) < 1 := gt_sgn.mpr ‹sgn (1 - dqs) ≃ 1›
      this
    ‹abs (q₁ - q₂) < 1›

  have : abs (q₁ - q₂) ≃ 0 :=
    have : ¬(abs (q₁ - q₂) > 0) := λ (_ : abs (q₁ - q₂) > 0) =>
      have : abs (q₁ - q₂) ≥ 1 := calc
        _ = abs (q₁ - q₂) := rfl
        _ ≥ 0 + 1         := lt_iff_le_incL.mp ‹abs (q₁ - q₂) > 0›
        _ ≃ 1             := AA.identL
      show False from lt_ge_false ‹abs (q₁ - q₂) < 1› ‹abs (q₁ - q₂) ≥ 1›

    have : abs (q₁ - q₂) > 0 ∨ abs (q₁ - q₂) ≃ 0 := ge_split.mp abs_nonneg
    show abs (q₁ - q₂) ≃ 0 from this.resolve_left ‹¬(abs (q₁ - q₂) > 0)›

  have : r₂ ≃ r₁ :=
    have : abs (r₂ - r₁) ≃ 0 := calc
      _ = abs (r₂ - r₁)         := rfl
      _ ≃ abs b * abs (q₁ - q₂) := ‹abs (r₂ - r₁) ≃ abs b * abs (q₁ - q₂)›
      _ ≃ abs b * 0             := by srw [‹abs (q₁ - q₂) ≃ 0›]
      _ ≃ 0                     := AA.absorbR
    have : r₂ - r₁ ≃ 0 := abs_zero.mp ‹abs (r₂ - r₁) ≃ 0›
    have : r₂ ≃ r₁ := zero_diff_iff_eqv.mp ‹r₂ - r₁ ≃ 0›
    this
  have : q₁ ≃ q₂ :=
    have : q₁ - q₂ ≃ 0 := abs_zero.mp ‹abs (q₁ - q₂) ≃ 0›
    have : q₁ ≃ q₂ := zero_diff_iff_eqv.mp ‹q₁ - q₂ ≃ 0›
    this
  exact And.intro ‹q₁ ≃ q₂› (Rel.symm ‹r₂ ≃ r₁›)

/-- `FlooredDivision`'s quotient respects equivalence of the dividend. -/
theorem div_floored_substL_quot
    {a₁ a₂ b : ℤ} {d₁ : FlooredDivision a₁ b} {d₂ : FlooredDivision a₂ b}
    : a₁ ≃ a₂ → d₁.quotient ≃ d₂.quotient
    := by
  intro (_ : a₁ ≃ a₂)
  let q₁ := d₁.quotient; let q₂ := d₂.quotient
  show q₁ ≃ q₂

  let d₂' := { d₁ with div_eqv := Rel.trans (Rel.symm ‹a₁ ≃ a₂›) d₁.div_eqv }
  have (And.intro (_ : q₁ ≃ q₂) _) := flooredDiv_unique d₂' d₂
  exact ‹q₁ ≃ q₂›

/-- `FlooredDivision`'s quotient respects equivalence of the divisor. -/
theorem div_floored_substR_quot
    {a b₁ b₂ : ℤ} {d₁ : FlooredDivision a b₁} {d₂ : FlooredDivision a b₂}
    : b₁ ≃ b₂ → d₁.quotient ≃ d₂.quotient
    := by
  intro (_ : b₁ ≃ b₂)
  let q₁ := d₁.quotient; let r₁ := d₁.remainder; let q₂ := d₂.quotient
  show q₁ ≃ q₂

  have : a ≃ b₂ * q₁ + r₁ := calc
    _ = a            := rfl
    _ ≃ b₁ * q₁ + r₁ := d₁.div_eqv
    _ ≃ b₂ * q₁ + r₁ := by srw [‹b₁ ≃ b₂›]
  have : abs r₁ < abs b₂ := calc
    _ = abs r₁  := rfl
    _ < abs b₁  := d₁.rem_mag
    _ ≃ abs b₂  := by srw [‹b₁ ≃ b₂›]
  have : r₁ * b₂ ≥ 0 := calc
    _ = r₁ * b₂ := rfl
    _ ≃ r₁ * b₁ := by srw [←‹b₁ ≃ b₂›]
    _ ≥ 0       := d₁.rem_sgn
  let d₂' := { d₁ with
    div_eqv := ‹a ≃ b₂ * q₁ + r₁›
    rem_mag := ‹abs r₁ < abs b₂›
    rem_sgn := ‹r₁ * b₂ ≥ 0›
  }

  -- Directly using `q₁ ≃ q₂` here gives an `unknown free variable` error
  have (And.intro (_ : d₂'.quotient ≃ q₂) _) := flooredDiv_unique d₂' d₂
  have : q₁ ≃ q₂ := ‹d₂'.quotient ≃ q₂›
  exact this

/--
Adding or removing a common factor (on the right) from the dividend and divisor
of a floored division leaves the quotient unchanged.
-/
theorem div_floored_mulR_quot_eqv
    {a b c : ℤ}
    {d₁ : FlooredDivision (a * c) (b * c)} {d₂ : FlooredDivision a b}
    : d₁.quotient ≃ d₂.quotient
    := by
  let q₁ := d₁.quotient; let q₂ := d₂.quotient
  let r₂ := d₂.remainder

  -- Good candidate for algebra tactic
  have : a * c ≃ (b * c) * q₂ + r₂ * c := calc
    _ = a * c                 := rfl
    _ ≃ (b * q₂ + r₂) * c     := by srw [d₂.div_eqv]
    _ ≃ b * q₂ * c + r₂ * c   := AA.distribR
    _ ≃ b * (q₂ * c) + r₂ * c := by srw [AA.assoc]
    _ ≃ b * (c * q₂) + r₂ * c := by srw [AA.comm]
    _ ≃ (b * c) * q₂ + r₂ * c := by srw [←AA.assoc]
  have : Positive (abs c) := by
    have : b * c ≄ 0 := baseDiv_nonzero_divisor d₁.toBaseDivision
    have (And.intro _ (_ : c ≄ 0)) := mul_split_neqv_zero.mp ‹b * c ≄ 0›
    have : 0 ≄ abs c := Rel.symm $ mt abs_zero.mp ‹c ≄ 0›
    have : 0 ≤ abs c := abs_nonneg
    have : abs c > 0 := lt_iff_le_neqv.mpr (And.intro ‹0 ≤ abs c› ‹0 ≄ abs c›)
    have : Positive (abs c) := gt_zero_iff_pos.mp ‹abs c > 0›
    exact this
  have : abs (r₂ * c) < abs (b * c) := calc
    _ = abs (r₂ * c)   := rfl
    _ ≃ abs r₂ * abs c := abs_compat_mul
    _ < abs b * abs c  := by srw [d₂.rem_mag] -- uses Positive (abs c)
    _ ≃ abs (b * c)    := Rel.symm abs_compat_mul
  have : r₂ * c * (b * c) ≥ 0 := by
    have : r₂ * b ≥ 0 := d₂.rem_sgn
    calc
      _ = r₂ * c * (b * c) := rfl
      _ ≃ r₂ * c * (c * b) := by srw [AA.comm]
      _ ≃ r₂ * b * (c * c) := AA.expr_xxfxxff_lr_swap_rr
      _ ≃ r₂ * b * c^2     := by srw [←Natural.pow_two]
      _ ≥ r₂ * b * 0       := by srw [sqr_nonneg] -- uses r₂ * b ≥ 0
      _ ≃ 0                := AA.absorbR
  let d₁' : FlooredDivision (a * c) (b * c) := {
    quotient := q₂
    remainder := r₂ * c
    div_eqv := ‹(a * c) ≃ (b * c) * q₂ + r₂ * c›
    rem_mag := ‹abs (r₂ * c) < abs (b * c)›
    rem_sgn := ‹r₂ * c * (b * c) ≥ 0›
  }

  have (And.intro (_ : q₁ ≃ q₂) _) := flooredDiv_unique d₁ d₁'
  exact ‹q₁ ≃ q₂›

variable [Division ℤ]

/--
Sufficient condition for the quotients of two integer floored divisions to be
equivalent.
-/
theorem div_floored_quotient_eqv
    {a₁ a₂ b₁ b₂ : ℤ} [AP (b₁ ≄ 0)] [AP (b₂ ≄ 0)]
    : a₁ * b₂ ≃ a₂ * b₁ →
      (div_floored a₁ b₁).quotient ≃ (div_floored a₂ b₂).quotient
    := by
  intro (_ : a₁ * b₂ ≃ a₂ * b₁)
  show (div_floored a₁ b₁).quotient ≃ (div_floored a₂ b₂).quotient

  -- Instances needed for divisors in division operations below
  have : b₁ ≄ 0 ∧ b₂ ≄ 0 := And.intro ‹AP (b₁ ≄ 0)›.ev ‹AP (b₂ ≄ 0)›.ev
  have : AP (b₁ * b₂ ≄ 0) := AP.mk (mul_split_neqv_zero.mpr ‹b₁ ≄ 0 ∧ b₂ ≄ 0›)
  have : AP (b₂ * b₁ ≄ 0) := by prw [AA.comm] ‹AP (b₁ * b₂ ≄ 0)›

  -- Abbreviate quotient expression to keep the calc block inside margin
  let dfq (x y : ℤ) [AP (y ≄ 0)] : ℤ := (div_floored x y).quotient
  show dfq a₁ b₁ ≃ dfq a₂ b₂
  calc
    _ = dfq a₁ b₁               := rfl
    _ ≃ dfq (a₁ * b₂) (b₁ * b₂) := Rel.symm div_floored_mulR_quot_eqv
    _ ≃ dfq (a₂ * b₁) (b₁ * b₂) := div_floored_substL_quot ‹a₁ * b₂ ≃ a₂ * b₁›
    _ ≃ dfq (a₂ * b₁) (b₂ * b₁) := div_floored_substR_quot AA.comm
    _ ≃ dfq a₂ b₂               := div_floored_mulR_quot_eqv

end Lean4Axiomatic.Integer

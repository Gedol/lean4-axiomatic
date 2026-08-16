import Lean4Axiomatic.Rational.FloorCeil

/-! # Generic implementation of rational floor and ceiling, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Logic (AP)
open Metric (abs)
open Signed (Positive sgn)

variable
  {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ] [Sign ℚ]
  [Reciprocation ℚ] [Division ℚ] [Induction.{1} ℚ]

/-- The greatest integer less than or equivalent to the given value. -/
def _floor (p : ℚ) : ℤ :=
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) _) := as_ratio p
  (Integer.div_floored a b).quotient

/-- The least integer greater than or equivalent to the given value. -/
def _ceil (p : ℚ) : ℤ := -_floor (-p)

local instance floor_ceil_ops : FloorCeil.Ops ℤ ℚ := {
  floor := _floor
  ceil := _ceil
}

variable [Subtraction ℚ]

/--
Evaluate `floor` in the common case where we know the integer components of the
rational input.
-/
theorem floor_ratio
    {a b : ℤ} [AP (b ≄ 0)]
    : floor ((a:ℚ)/b) ≃ (Integer.div_floored a b).quotient
    := by
  let ar := as_ratio ((a:ℚ)/b); let a' := ar.a; let b' := ar.b
  have : AP (b' ≄ 0) := ar.b_nonzero
  have : (a:ℚ)/b ≃ a'/b' := ar.p_eqv
  have : a' * b ≃ a * b' := div_int_eqv_div_int.mp (eqv_symm ‹(a:ℚ)/b ≃ a'/b'›)
  let d := Integer.div_floored a b
  let d' := Integer.div_floored a' b'

  -- ↓ begin key lines ↓
  calc
    _ = floor ((a:ℚ)/b) := rfl
    _ = d'.quotient     := rfl
    _ ≃ d.quotient      := Integer.div_floored_quotient_eqv ‹a' * b ≃ a * b'›
  -- ↑  end key lines  ↑

/-- `floor` is a legitimate function on rationals; it respects equivalence. -/
@[gcongr]
theorem floor_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → floor p₁ ≃ floor p₂ := by
  intro (_ : p₁ ≃ p₂)
  show floor p₁ ≃ floor p₂

  /-
  Convert the rational arguments into integer ratios. Can't use pattern
  matching because the matched variables are not considered judgmentally equal
  to the fields of the `AsRatio` structure they came from.
  -/
  let ar₁ := as_ratio p₁; let a₁ := ar₁.a; let b₁ := ar₁.b
  let ar₂ := as_ratio p₂; let a₂ := ar₂.a; let b₂ := ar₂.b
  have : AP (b₁ ≄ 0) := ar₁.b_nonzero
  have : AP (b₂ ≄ 0) := ar₂.b_nonzero
  have : p₁ ≃ a₁/b₁ := ar₁.p_eqv
  have : p₂ ≃ a₂/b₂ := ar₂.p_eqv

  /-
  Convert the hypothesis from an equivalence of rationals to an equivalence of
  their integer components.
  -/
  have : (a₁:ℚ)/b₁ ≃ a₂/b₂ := calc
    _ = (a₁:ℚ)/b₁ := rfl
    _ ≃ p₁        := eqv_symm ‹p₁ ≃ a₁/b₁›
    _ ≃ p₂        := ‹p₁ ≃ p₂›
    _ ≃ a₂/b₂     := ‹p₂ ≃ a₂/b₂›
  have : a₁ * b₂ ≃ a₂ * b₁ := div_int_eqv_div_int.mp ‹(a₁:ℚ)/b₁ ≃ a₂/b₂›
  let d₁ := Integer.div_floored a₁ b₁
  let d₂ := Integer.div_floored a₂ b₂

  calc
    _ = floor p₁    := rfl
    -- ↓ begin key lines ↓
    _ = d₁.quotient := rfl
    _ ≃ d₂.quotient := Integer.div_floored_quotient_eqv ‹a₁ * b₂ ≃ a₂ * b₁›
    -- ↑  end key lines  ↑
    _ = floor p₂    := rfl

variable [Order ℚ]

/-- A rational is no smaller than its floor. -/
theorem floor_ub {p : ℚ} : floor p ≤ p := by
  -- We want a positive denominator to avoid reversing the main inequality
  have (AsHalfPosRatio.mk (a:ℤ) (b:ℤ) (_ : b > 0) p_eqv) := as_half_pos_ratio p
  have : AP (b ≄ 0) := AP.mk (Integer.neqv_zero_from_gt_zero ‹b > 0›)
  have : p ≃ a/b := p_eqv
  have : (b:ℚ) > 0 := lt_respects_from_integer.mp ‹b > 0›

  -- Use integer division properties to set up the main inequality
  let d := Integer.div_floored a b; let q := d.quotient; let r := d.remainder
  have : r * b ≥ 0 := d.rem_sgn
  have : (sgn (r * b))^2 ≃ sgn (r * b) := Integer.sgn_sqr_nonneg.mpr ‹r * b ≥ 0›
  have : sgn b ≃ 1 := Integer.gt_zero_sgn.mp ‹b > 0›
  have : (sgn r)^2 ≃ sgn r := calc
    _ = (sgn r)^2             := rfl
    _ ≃ (sgn r)^2 * 1         := Rel.symm AA.identR
    _ ≃ (sgn r)^2 * 1^2       := by srw [←Natural.pow_absorbL]
    _ ≃ (sgn r)^2 * (sgn b)^2 := by srw [←‹sgn b ≃ 1›]
    _ ≃ (sgn r * sgn b)^2     := Rel.symm Natural.pow_distribR_mul
    _ ≃ (sgn (r * b))^2       := by srw [←Integer.sgn_compat_mul]
    _ ≃ sgn (r * b)           := ‹(sgn (r * b))^2 ≃ sgn (r * b)›
    _ ≃ sgn r * sgn b         := Integer.sgn_compat_mul
    _ ≃ sgn r * 1             := by srw [‹sgn b ≃ 1›]
    _ ≃ sgn r                 := AA.identR
  have : r ≥ 0 := Integer.sgn_sqr_nonneg.mp ‹(sgn r)^2 ≃ sgn r›
  have : b * q ≤ a := calc
    _ = b * q     := rfl
    -- ↓ begin key lines ↓
    _ ≃ b * q + 0 := Rel.symm AA.identR
    _ ≤ b * q + r := Integer.ge_addL.mp ‹r ≥ 0›
    -- ↑  end key lines  ↑
    _ ≃ a         := Rel.symm d.div_eqv
  have : ((b * q : ℤ):ℚ)/b ≤ (a:ℚ)/b :=
    le_substN_div_gt_zero ‹(b:ℚ) > 0› (le_respects_from_integer.mp ‹b * q ≤ a›)

  calc
    _ = (floor p : ℚ)     := rfl
    _ ≃ floor ((a:ℚ)/b)   := by srw [‹p ≃ a/b›]
    _ ≃ q                 := by srw [floor_ratio]
    _ ≃ (b * q)/b         := eqv_symm mulL_div_same
    -- ↓ begin key lines ↓
    _ ≃ ((b * q : ℤ):ℚ)/b := by srw [←mul_compat_from_integer]
    _ ≤ (a:ℚ)/b           := ‹((b * q : ℤ):ℚ)/b ≤ (a:ℚ)/b›
    -- ↑  end key lines  ↑
    _ ≃ p                 := eqv_symm ‹p ≃ a/b›

/--
A rational's floor is the greatest integer not greater than the rational
itself.
-/
theorem floor_lb {p : ℚ} {c : ℤ} : c ≤ p → c ≤ floor p := by
  intro (_ : c ≤ p)
  show c ≤ floor p

  -- We want a positive denominator to avoid reversing the main inequality
  have (AsHalfPosRatio.mk (a:ℤ) (b:ℤ) (_ : b > 0) p_eqv) := as_half_pos_ratio p
  have : AP (b ≄ 0) := AP.mk (Integer.neqv_zero_from_gt_zero ‹b > 0›)
  have : p ≃ a/b := p_eqv
  have : sgn (b:ℚ) ≃ 1 := calc
    _ = sgn (b:ℚ) := rfl
    _ ≃ sgn b     := sgn_from_integer
    _ ≃ 1         := Integer.gt_zero_sgn.mp ‹b > 0›
  have : b ≥ 0 := Integer.le_split.mpr (Or.inl ‹b > 0›)

  -- Use integer division properties to set up the main inequality
  let d := Integer.div_floored a b; let q := d.quotient; let r := d.remainder
  have : abs r < abs b := d.rem_mag
  have (And.intro _ (_ : r < abs b)) :=
    Integer.abs_upper_bound.mp ‹abs r < abs b›
  have : a < b * (q + 1) := calc
    _ = a             := rfl
    -- ↓ begin key lines ↓
    _ ≃ b * q + r     := d.div_eqv
    _ < b * q + abs b := by srw [‹r < abs b›]
    -- ↑  end key lines  ↑
    _ ≃ b * q + b     := by srw [Integer.abs_ident ‹b ≥ 0›]
    _ ≃ b * q + b * 1 := by srw [←Integer.mul_identR]
    _ ≃ b * (q + 1)   := Rel.symm AA.distribL
  have : (a:ℚ) < (b * (q+1) : ℤ) := lt_respects_from_integer.mp ‹a < b * (q+1)›
  have : (a:ℚ)/b < ((b * (q + 1) : ℤ):ℚ)/b :=
    lt_substN_div_pos ‹sgn (b:ℚ) ≃ 1› ‹(a:ℚ) < (b * (q+1) : ℤ)›

  have : (c:ℚ) < (q + 1 : ℤ) := calc
    _ = (c:ℚ)                   := rfl
    _ ≤ p                       := ‹c ≤ p›
    -- ↓ begin key lines ↓
    _ ≃ a/b                     := ‹p ≃ a/b›
    _ < ((b * (q + 1) : ℤ):ℚ)/b := ‹(a:ℚ)/b < ((b * (q + 1) : ℤ):ℚ)/b›
    -- ↑  end key lines  ↑
    _ ≃ (b * (q + 1 : ℤ))/b     := by srw [mul_compat_from_integer]
    _ ≃ (q + 1 : ℤ)             := mulL_div_same
  have : c < q + 1 := lt_respects_from_integer.mpr ‹(c:ℚ) < (q + 1 : ℤ)›
  calc
    -- ↓ begin key lines ↓
    _ = c               := rfl
    _ ≤ q               := Integer.le_iff_lt_incR.mpr ‹c < q + 1›
    -- ↑  end key lines  ↑
    _ ≃ floor ((a:ℚ)/b) := Rel.symm floor_ratio
    _ ≃ floor p         := by srw [←‹p ≃ a/b›]

/-- A rational is no larger than its ceiling. -/
theorem ceil_lb {p : ℚ} : p ≤ ceil p := by
  -- ↓ begin key lines ↓
  have : floor (-p) ≤ -p := floor_ub
  -- ↑  end key lines  ↑
  calc
    _ = p                 := rfl
    _ ≃ -(-p)             := eqv_symm neg_involutive
    _ ≤ -(floor (-p) : ℤ) := by srw [‹floor (-p) ≤ -p›]
    _ ≃ (-floor (-p) : ℤ) := eqv_symm neg_compat_from_integer
    _ = ceil p            := rfl

/--
A rational's ceiling is the least integer not less than the rational itself.
-/
theorem ceil_ub {p : ℚ} {a : ℤ} : p ≤ a → ceil p ≤ a := by
  intro (_ : p ≤ a)
  show ceil p ≤ a
  have : (-a:ℤ) ≤ -p := calc
    _ = ((-a:ℤ):ℚ) := rfl
    _ ≃ -(a:ℚ)     := neg_compat_from_integer
    _ ≤ -p         := by srw [‹p ≤ a›]
  -- ↓ begin key lines ↓
  have : -a ≤ floor (-p) := floor_lb ‹(-a:ℤ) ≤ -p›
  -- ↑  end key lines  ↑
  calc
    _ = ceil p      := rfl
    _ = -floor (-p) := rfl
    _ ≤ -(-a)       := Integer.le_neg_flip.mp ‹-a ≤ floor (-p)›
    _ ≃ a           := Integer.neg_involutive

@[implicit_reducible]
def floor_ceil_props : FloorCeil.Props ℚ := {
  floor_ub := floor_ub
  floor_lb := floor_lb
  ceil_lb := ceil_lb
  ceil_ub := ceil_ub
}

@[implicit_reducible]
def floor_ceil : FloorCeil ℚ := {
  toOps := floor_ceil_ops
  toProps := floor_ceil_props
}

end Lean4Axiomatic.Rational.Impl.Generic

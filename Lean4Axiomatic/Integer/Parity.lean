import Lean4Axiomatic.Integer.Division

/-! # Integer parity (evenness and oddness) -/

namespace Lean4Axiomatic.Integer

open Lean4Axiomatic.Logic (Either)
open Lean4Axiomatic.Metric (abs)

/-! ## Axioms -/

/-- Predicates and functions relating to parity. -/
class Parity.Ops (α : Type) where
  /-- The value has **even** parity. -/
  Even : α → Prop

  /-- The value has **odd** parity. -/
  Odd : α → Prop

  /-- The greatest whole-number value no larger than half of the input. -/
  half_floored : α → α

export Parity.Ops (Even Odd half_floored)

/-- Defining properties of integer parity. -/
class Parity.Props
    {ℕ : Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
      [Sign ℤ] [Metric ℤ] [Division ℤ] [Ops ℤ]
    where
  /-- Even integers have remainder zero when divided by two. -/
  even_rem {a : ℤ} : Even a ↔ (div_floored a 2).remainder ≃ 0

  /-- Odd integers have remainder one when divided by two. -/
  odd_rem {a : ℤ} : Odd a ↔ (div_floored a 2).remainder ≃ 1

  /--
  The quotient when an integer is divided by two is its half-floored value.
  -/
  half_floored_eqv {a : ℤ} : half_floored a ≃ (div_floored a 2).quotient

export Parity.Props (even_rem half_floored_eqv odd_rem)

/-- All integer parity axioms. -/
class Parity
    {ℕ : Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
      [Sign ℤ] [Metric ℤ] [Division ℤ] where
  toOps : Parity.Ops ℤ
  toProps : Parity.Props ℤ

attribute [implicit_reducible, instance] Parity.toOps
attribute [instance] Parity.toProps

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Sign ℤ] [Metric ℤ] [Division ℤ] [Parity ℤ]

/-- Even integers can be written in the form `2 * b`. -/
theorem even_eqv {a : ℤ} : Even a → a ≃ 2 * half_floored a := by
  intro (_ : Even a)
  show a ≃ 2 * half_floored a

  let d := div_floored a 2; let q := d.quotient; let r := d.remainder
  calc
    _ = a                      := rfl
    _ ≃ 2 * q + r              := d.div_eqv
    _ ≃ 2 * half_floored a + r := by srw [←half_floored_eqv]
    _ ≃ 2 * half_floored a + 0 := by srw [even_rem.mp ‹Even a›]
    _ ≃ 2 * half_floored a     := AA.identR

/-- Odd integers can be written in the form `2 * b + 1`. -/
theorem odd_eqv {a : ℤ} : Odd a → a ≃ 2 * half_floored a + 1 := by
  intro (_ : Odd a)
  show a ≃ 2 * half_floored a + 1

  let d := div_floored a 2; let q := d.quotient; let r := d.remainder
  calc
    _ = a                      := rfl
    _ ≃ 2 * q + r              := d.div_eqv
    _ ≃ 2 * half_floored a + r := by srw [←half_floored_eqv]
    _ ≃ 2 * half_floored a + 1 := by srw [odd_rem.mp ‹Odd a›]

variable
  [Subtraction ℤ]
  [Natural.Exponentiation ℕ (α := ℤ) (mul := (· * ·)) (ident := (1 : ℤ))
    (minst := integer_mul_monoid)]

/-- Equivalent integers have equivalent floored halves. -/
@[gcongr]
theorem half_floored_subst
    {a₁ a₂ : ℤ} : a₁ ≃ a₂ → half_floored a₁ ≃ half_floored a₂
    := by
  intro (_ : a₁ ≃ a₂)
  show half_floored a₁ ≃ half_floored a₂

  let d₁ := div_floored a₁ 2; let q₁ := d₁.quotient
  let d₂ := div_floored a₂ 2; let q₂ := d₂.quotient
  calc
    _ = half_floored a₁ := rfl
    _ ≃ q₁              := half_floored_eqv
    _ ≃ q₂              := div_floored_substL_quot ‹a₁ ≃ a₂›
    _ ≃ half_floored a₂ := Rel.symm half_floored_eqv

/-- Any integer of the form `2 * b` is even. -/
def even_from_eqv {a b : ℤ} : a ≃ 2 * b → Even a := by
  intro (_ : a ≃ 2 * b)
  show Even a

  let d₁ := div_floored a 2; let r := d₁.remainder
  let d₂ : FlooredDivision a 2 :=
    -- Could use a numeric tactic for these
    have : a ≃ 2 * b + 0 := calc
      _ = a         := rfl
      _ ≃ 2 * b     := ‹a ≃ 2 * b›
      _ ≃ 2 * b + 0 := Rel.symm AA.identR
    have : abs (0:ℤ) < abs 2 := calc
      _ = abs (0:ℤ) := rfl
      _ ≃ 0         := abs_zero.mpr Rel.refl
      _ < 2         := two_gt_zero
      _ ≃ abs (2:ℤ) := Rel.symm $ abs_ident two_ge_zero
    have : (0:ℤ) * 2 ≥ 0 := calc
      _ = (0:ℤ) * 2 := rfl
      _ ≃ 0         := AA.absorbL
      _ ≥ 0         := le_refl
    show FlooredDivision a 2 from {
      quotient := b
      remainder := 0
      div_eqv := ‹a ≃ 2 * b + 0›
      rem_mag := ‹abs (0:ℤ) < abs 2›
      rem_sgn := ‹(0:ℤ) * 2 ≥ 0›
    }

  have (And.intro _ (_ : r ≃ 0)) := flooredDiv_unique d₁ d₂
  have : Even a := even_rem.mpr ‹r ≃ 0›
  exact this

/-- Any integer of the form `2 * b + 1` is odd. -/
def odd_from_eqv {a b : ℤ} : a ≃ 2 * b + 1 → Odd a := by
  intro (_ : a ≃ 2 * b + 1)
  show Odd a

  let d₁ := div_floored a 2; let r := d₁.remainder
  let d₂ : FlooredDivision a 2 :=
    -- Could use a numeric tactic for these
    have : abs (1:ℤ) < abs 2 := calc
      _ = abs (1:ℤ) := rfl
      _ ≃ 1         := abs_ident one_ge_zero
      _ < 2         := two_gt_one
      _ ≃ abs (2:ℤ) := Rel.symm $ abs_ident two_ge_zero
    have : (1:ℤ) * 2 ≥ 0 := calc
      _ = (1:ℤ) * 2 := rfl
      _ ≃ 2         := AA.identL
      _ ≥ 0         := two_ge_zero
    show FlooredDivision a 2 from {
      quotient := b
      remainder := 1
      div_eqv := ‹a ≃ 2 * b + 1›
      rem_mag := ‹abs (1:ℤ) < abs 2›
      rem_sgn := ‹(1:ℤ) * 2 ≥ 0›
    }
  have (And.intro _ (_ : r ≃ 1)) := flooredDiv_unique d₁ d₂
  have : Odd a := odd_rem.mpr ‹r ≃ 1›
  exact this

/-- Every integer is either even or odd, but not both. -/
def parity (a : ℤ) : AA.ExactlyOneOfTwo₁ (Even a) (Odd a) :=
  let d := div_floored a 2; let q := d.quotient; let r := d.remainder

  have : Either (Even a) (Odd a) :=
    have : Either (r ≃ 0) (r ≃ 1) :=
      have : r * 2 ≥ 0 * 2 := calc
        _ = r * 2 := rfl
        _ ≥ 0     := d.rem_sgn
        _ ≃ 0 * 2 := Rel.symm AA.absorbL
      have : r ≥ 0 := mul_cancelR_le two_gt_zero ‹r * 2 ≥ 0 * 2›
      have : Either (r ≃ 0) (r > 0) := (ge_split_either ‹r ≥ 0›).swap
      match ‹Either (r ≃ 0) (r > 0)› with
      | .inl (_ : r ≃ 0) =>
        show Either (r ≃ 0) (r ≃ 1) from .inl ‹r ≃ 0›
      | .inr (_ : r > 0) =>
        have : r ≥ 1 := pos_gt_iff_ge.mp ‹r > 0›
        have : Either (r ≃ 1) (r > 1) := (ge_split_either ‹r ≥ 1›).swap
        match ‹Either (r ≃ 1) (r > 1)› with
        | .inl (_ : r ≃ 1) =>
          show Either (r ≃ 0) (r ≃ 1) from .inr ‹r ≃ 1›
        | .inr (_ : r > 1) =>
          have : r ≥ 2 := calc
            _ = r     := rfl
            _ ≥ 1 + 1 := lt_iff_le_incL.mp ‹r > 1›
            _ ≃ 2     := add_one_one
          have : r < 2 := calc
            _ = r     := rfl
            _ ≃ abs r := Rel.symm (abs_ident ‹r ≥ 0›)
            _ < abs 2 := d.rem_mag
            _ ≃ 2     := abs_ident two_ge_zero
          show Either (r ≃ 0) (r ≃ 1) from (lt_ge_false ‹r < 2› ‹r ≥ 2›).elim

    match ‹Either (r ≃ 0) (r ≃ 1)› with
    | .inl (_ : r ≃ 0) =>
      have : Even a := even_rem.mpr ‹r ≃ 0›
      show Either (Even a) (Odd a) from .inl ‹Even a›
    | .inr (_ : r ≃ 1) =>
      have : Odd a := odd_rem.mpr ‹r ≃ 1›
      show Either (Even a) (Odd a) from .inr ‹Odd a›

  have : ¬(Even a ∧ Odd a) := λ (And.intro (_ : Even a) (_ : Odd a)) =>
    have : (1:ℤ) ≃ 0 := calc
      _ = (1:ℤ) := rfl
      _ ≃ r     := Rel.symm (odd_rem.mp ‹Odd a›)
      _ ≃ 0     := even_rem.mp ‹Even a›
    show False from absurd ‹(1:ℤ) ≃ 0› one_neqv_zero

  show AA.ExactlyOneOfTwo₁ (Even a) (Odd a) from {
    atLeastOne := ‹Either (Even a) (Odd a)›
    atMostOne := ‹¬(Even a ∧ Odd a)›
  }

/-- Only even integers have even squares. -/
def even_from_sqr_even {a : ℤ} : Even (a^2) → Even a := by
  intro (_ : Even (a^2))
  show Even a

  let even_xor_odd : AA.ExactlyOneOfTwo₁ (Even a) (Odd a) := parity a
  match even_xor_odd.atLeastOne with
  | .inl (_ : Even a) =>
    exact ‹Even a›
  | .inr (_ : Odd a) =>
    have : Odd (a^2) :=
      let b := half_floored a
      have : a ≃ 2 * b + 1 := odd_eqv ‹Odd a›

      let b' := 2 * b^2 + 2 * b
      have : a^2 ≃ 2 * b' + 1 := calc
        _ = a^2                           := rfl
        _ ≃ (2*b + 1)^2                   := by srw [‹a ≃ 2 * b + 1›]
        _ ≃ (2*b)^2 + 2 * (2*b) * 1 + 1^2 := binom_sqr
        _ ≃ (2*b)^2 + 2 * (2*b) + 1^2     := by srw [mul_identR]
        _ ≃ (2*b)^2 + 2 * (2*b) + 1       := by srw [Natural.pow_absorbL]
        _ ≃ 2^2 * b^2 + 2 * (2*b) + 1     := by srw [Natural.pow_distribR_mul]
        _ ≃ 2 * 2*b^2 + 2 * (2*b) + 1     := by srw [Natural.pow_two]
        _ ≃ 2 * (2*b^2) + 2 * (2*b) + 1   := by srw [AA.assoc]
        _ ≃ 2 * (2*b^2 + 2*b) + 1         := by srw [←mul_distribL]
        _ = 2 * b' + 1                    := rfl
      show Odd (a^2) from odd_from_eqv ‹a^2 ≃ 2 * b' + 1›

    have : Even a :=
      have : Even (a^2) ∧ Odd (a^2) := And.intro ‹Even (a^2)› ‹Odd (a^2)›
      let even_xor_odd_sqr : AA.ExactlyOneOfTwo₁ (Even (a^2)) (Odd (a^2)) :=
        parity (a^2)
      have : False := even_xor_odd_sqr.atMostOne ‹Even (a^2) ∧ Odd (a^2)›
      show Even a from ‹False›.elim
    exact ‹Even a›

end Lean4Axiomatic.Integer

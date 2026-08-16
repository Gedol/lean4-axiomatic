import Lean4Axiomatic.Natural.Division

/-! # Generic implementation of natural number division and properties -/

namespace Lean4Axiomatic.Natural.Impl.Generic

open Logic (AP Either)
open Signed (Positive)

variable
  {ℕ : Type}
    [Core ℕ] [Addition ℕ] [Order ℕ] [Compare ℕ] [Multiplication ℕ]
    [Induction.{0} ℕ] [Induction.{1} ℕ] [Sign ℕ]

/-- Computes the Euclidean division of the first argument by the second. -/
def divide (n m : ℕ) [AP (m ≄ 0)] : EuclideanDivision n m := by
  have : Positive m := Signed.positive_defn.mpr ‹AP (m ≄ 0)›.ev
  have : m > 0 := lt_zero_pos.mp ‹Positive m›

  apply ind_on n
  case zero =>
    show EuclideanDivision 0 m

    let q := 0
    let r := 0
    have : 0 ≃ m * q + r := calc
      _ = 0         := rfl
      _ ≃ m * 0     := Rel.symm AA.absorbR
      _ ≃ m * 0 + 0 := Rel.symm AA.identR
      _ = m * q + r := rfl
    have : r < m := ‹m > 0›

    exact show EuclideanDivision 0 m from {
      quotient := q
      remainder := r
      div_eqv := ‹0 ≃ m * q + r›
      rem_ub := ‹r < m›
    }
  case step =>
    intro (n' : ℕ) (ih : EuclideanDivision n' m)
    show EuclideanDivision (step n') m

    let q' := ih.quotient
    let r' := ih.remainder
    have : n' ≃ m * q' + r' := ih.div_eqv
    have : r' < m := ih.rem_ub

    have : step r' ≤ m := lt_step_le.mp ‹r' < m›
    have : Either (step r' < m) (step r' ≃ m) := le_split_either ‹step r' ≤ m›
    match ‹Either (step r' < m) (step r' ≃ m)› with
    | .inl (_ : step r' < m) =>
      /- We can add one more to the remainder without reaching `m`. -/
      let q := q'
      let r := step r'
      have : step n' ≃ m * q + r := calc
        _ = step n'            := rfl
        _ ≃ step (m * q' + r') := by srw [‹n' ≃ m * q' + r'›]
        _ ≃ m * q' + step r'   := AA.scompatR
        _ = m * q + r          := rfl
      have : r < m := ‹step r' < m›

      exact show EuclideanDivision (step n') m from {
        quotient := q
        remainder := r
        div_eqv := ‹step n' ≃ m * q + r›
        rem_ub := ‹r < m›
      }

    | .inr (_ : step r' ≃ m) =>
      /-
      Adding one to the remainder has reached `m`, so increment the quotient
      instead.
      -/
      let q := step q'
      let r := 0
      have : step n' ≃ m * q + r := calc
        _ = step n'            := rfl
        _ ≃ step (m * q' + r') := by srw [‹n' ≃ m * q' + r'›]
        _ ≃ m * q' + step r'   := AA.scompatR
        _ ≃ m * q' + m         := by srw [‹step r' ≃ m›]
        _ ≃ m * q' + m * 1     := by srw [←mul_identR]
        _ ≃ m * (q' + 1)       := Rel.symm AA.distribL
        _ ≃ m * step q'        := by srw [add_one_step]
        _ ≃ m * step q' + 0    := Rel.symm AA.identR
        _ = m * q + r          := rfl
      have : r < m := ‹m > 0›

      exact show EuclideanDivision (step n') m from {
        quotient := q
        remainder := r
        div_eqv := ‹step n' ≃ m * q + r›
        rem_ub := ‹r < m›
      }

@[implicit_reducible]
def division : Division ℕ := {
  divide := divide
}

end Lean4Axiomatic.Natural.Impl.Generic

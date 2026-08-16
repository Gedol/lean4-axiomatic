import Lean4Axiomatic.Integer.Division

/-! # Generic implementation of integer division functions and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

open Lean4Axiomatic.Metric (abs)
open Logic (AP Either)
open Signed (Positive)

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ]
    [Subtraction ℤ] [Induction.{1} ℤ] [Order ℤ] [Sign ℤ] [Metric ℤ]
    [Natural.Exponentiation ℕ ℤ]

/-- Integer Euclidean division with a nonnegative dividend. -/
def div_euclidean_nonneg
    {a : ℤ} (a_nonneg : a ≥ 0) (b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b
    :=
  /- Find the natural number equivalent to the nonnegative dividend -/
  let an : { n : ℕ // a ≃ n } := nonneg_to_natural ‹a ≥ 0›
  let n := an.val
  have : a ≃ n := an.property

  /- Find the natural number equivalent to the divisor's absolute value -/
  have : 0 ≤ abs b := abs_nonneg
  have : 0 ≄ abs b := Rel.symm (mt abs_zero.mp ‹AP (b ≄ 0)›.ev)
  have : abs b > 0 := lt_from_le_neqv ‹0 ≤ abs b› ‹0 ≄ abs b›
  let bn : { m : ℕ // abs b ≃ m ∧ m > 0 } := pos_to_natural ‹abs b > 0›
  let m := bn.val
  have : (m:ℤ) ≃ abs b := Rel.symm bn.property.left
  have : m > 0 := bn.property.right
  have : AP (m ≄ 0) := AP.mk (Natural.neqv_zero_from_gt_zero ‹m > 0›)

  /- Natural number division and results -/
  let d' := n ÷ m
  let q' := d'.quotient
  let r' := d'.remainder
  have : n ≃ m * q' + r' := d'.div_eqv
  have : r' ≥ 0 := Natural.ge_zero
  have : r' < m := d'.rem_ub

  /- Adjust results to obtain integer division -/
  let q := sgn b * q'
  let r := (r':ℤ)
  have : a ≃ b * q + r := calc
    _ = a                         := rfl
    _ ≃ (n:ℤ)                     := ‹a ≃ n›
    _ ≃ ((m * q' + r' : ℕ):ℤ)     := by srw [‹n ≃ m * q' + r'›]
    _ ≃ ((m * q' : ℕ):ℤ) + (r':ℤ) := AA.compat₂
    _ ≃ (m:ℤ) * (q':ℤ) + (r':ℤ)   := by srw [AA.compat₂]
    _ = (m:ℤ) * q' + r'           := rfl
    _ ≃ abs b * q' + r'           := by srw [‹(m:ℤ) ≃ abs b›]
    _ ≃ b * sgn b * q' + r'       := by srw [abs_sgn]
    _ ≃ b * (sgn b * q') + r'     := by srw [AA.assoc]
    _ = b * q + r                 := rfl
  have : r ≥ 0 := calc
    _ = r         := rfl
    _ = (r':ℤ)    := rfl
    _ ≥ ((0:ℕ):ℤ) := by srw [‹r' ≥ 0›]
    _ = 0         := rfl
  have : abs r < abs b := calc
    _ = abs r  := rfl
    _ ≃ r      := abs_ident ‹r ≥ 0›
    _ = (r':ℤ) := rfl
    _ < (m:ℤ)  := by srw [‹r' < m›]
    _ ≃ abs b  := ‹(m:ℤ) ≃ abs b›

  show EuclideanDivision a b from {
    quotient := q
    remainder := r
    div_eqv := ‹a ≃ b * q + r›
    rem_mag := ‹abs r < abs b›
    rem_sgn := ‹r ≥ 0›
  }

/-- Definition of integer Euclidean division. -/
def div_euclidean (a b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b :=
  match show Either (a ≥ 0) (-a ≥ 0) from either_nonneg with
  | .inl (_ : a ≥ 0) =>
    show EuclideanDivision a b from div_euclidean_nonneg ‹a ≥ 0› b
  | .inr (_ : -a ≥ 0) =>
    let d' : EuclideanDivision (-a) b := div_euclidean_nonneg ‹-a ≥ 0› b
    let q' := d'.quotient
    let r' := d'.remainder
    have : a ≃ b * -q' + -r' := calc
      _ = a               := rfl
      _ ≃ -(-a)           := Rel.symm neg_involutive
      _ ≃ -(b * q' + r')  := by srw [d'.div_eqv]
      _ ≃ -(b * q') + -r' := neg_compat_add
      _ ≃ b * -q' + -r'   := by srw [AA.scompatR]
    have : r' ≥ 0 := d'.rem_sgn

    match show Either (r' > 0) (r' ≃ 0) from ge_split_either ‹r' ≥ 0› with
    | .inl (_ : r' > 0) =>
      /-
      Define or prove all fields of the result structure.

      Although `a ≃ b * -q' + -r'`, we can't have a remainder of `-r'` because
      it's negative. Find an equivalent positive remainder and adjust the
      quotient to compensate.
      -/
      let q := -(q' + sgn b)
      let r := abs b - r'
      have : a ≃ b * q + r := Rel.symm $ calc
        _ = b * q + r                        := rfl
        _ = b * -(q' + sgn b) + r            := rfl
        _ ≃ b * (-q' + -sgn b) + r           := by srw [neg_compat_add]
        _ ≃ b * -q' + b * -sgn b + r         := by srw [mul_distribL]
        _ ≃ b * -q' + -(b * sgn b) + r       := by srw [←AA.scompatR]
        _ ≃ b * -q' + -abs b + r             := by srw [←abs_sgn]
        _ = b * -q' + -abs b + (abs b - r')  := rfl
        _ ≃ b * -q' + -abs b + (abs b + -r') := by srw [sub_defn]
        _ ≃ b * -q' + -abs b + abs b + -r'   := by srw [←AA.assoc]
        _ ≃ b * -q' + (-abs b + abs b) + -r' := by srw [AA.assoc]
        _ ≃ b * -q' + 0 + -r'                := by srw [neg_invL]
        _ ≃ b * -q' + -r'                    := by srw [add_identR]
        _ ≃ a                                := Rel.symm ‹a ≃ b * -q' + -r'›
      have : r' ≤ abs b := calc
        _ = r'     := rfl
        _ ≃ abs r' := Rel.symm (abs_ident ‹r' ≥ 0›)
        _ ≤ abs b  := le_split.mpr (Or.inl d'.rem_mag)
      have : r ≥ 0 := calc
        _ = r             := rfl
        _ = abs b - r'    := rfl
        _ ≥ abs b - abs b := by srw [‹r' ≤ abs b›]
        _ ≃ 0             := sub_same
      have : abs r < abs b := calc
        _ = abs r      := rfl
        _ ≃ r          := abs_ident ‹r ≥ 0›
        _ = abs b - r' := rfl
        _ < abs b - 0  := by srw [‹r' > 0›]
        _ ≃ abs b      := sub_identR

      show EuclideanDivision a b from {
        quotient := q
        remainder := r
        div_eqv := ‹a ≃ b * q + r›
        rem_mag := ‹abs r < abs b›
        rem_sgn := ‹r ≥ 0›
      }

    | .inr (_ : r' ≃ 0) =>
      -- Define or prove all fields of the result structure
      let q := -q'
      let r := 0
      have : a ≃ b * q + r := calc
        _ = a             := rfl
        _ ≃ b * -q' + -r' := ‹a ≃ b * -q' + -r'›
        _ = b * q + -r'   := rfl
        _ ≃ b * q + -0    := by srw [‹r' ≃ 0›]
        _ ≃ b * q + 0     := by srw [←neg_zero.mp Rel.refl]
        _ = b * q + r     := rfl
      have : r ≥ 0 := le_refl
      have : r ≤ abs b := abs_nonneg
      have : abs b ≄ 0 := mt abs_zero.mp ‹AP (b ≄ 0)›.ev
      have : r ≄ abs b := Rel.symm ‹abs b ≄ 0›
      have : abs r < abs b := calc
        _ = abs r := rfl
        _ ≃ r     := abs_ident ‹r ≥ 0›
        _ < abs b := lt_from_le_neqv ‹r ≤ abs b› ‹r ≄ abs b›

      show EuclideanDivision a b from {
        quotient := q
        remainder := r
        div_eqv := ‹a ≃ b * q + r›
        rem_mag := ‹abs r < abs b›
        rem_sgn := ‹r ≥ 0›
      }

/-- Definition of integer floored division. -/
def div_floored (a b : ℤ) [AP (b ≄ 0)] : FlooredDivision a b :=
  /- Find the natural number equivalent to the dividend's absolute value -/
  have : abs a ≥ 0 := abs_nonneg
  let an : { n : ℕ // abs a ≃ n } := nonneg_to_natural ‹abs a ≥ 0›
  let n := an.val
  have : (n:ℤ) ≃ abs a := Rel.symm an.property

  /- Find the natural number equivalent to the divisor's absolute value -/
  let mb := abs b
  have : 0 ≤ mb := abs_nonneg
  have : 0 ≄ mb := Rel.symm (mt abs_zero.mp ‹AP (b ≄ 0)›.ev)
  have : mb > 0 := lt_from_le_neqv ‹0 ≤ mb› ‹0 ≄ mb›
  let bn : { m : ℕ // mb ≃ m ∧ m > 0 } := pos_to_natural ‹mb > 0›
  let m := bn.val
  have : (m:ℤ) ≃ mb := Rel.symm bn.property.left
  have : m > 0 := bn.property.right
  have : AP (m ≄ 0) := AP.mk (Natural.neqv_zero_from_gt_zero ‹m > 0›)

  /- Natural number division and results -/
  let d' := Natural.divide n m
  let q' := d'.quotient
  let r' := d'.remainder
  have : n ≃ m * q' + r' := d'.div_eqv
  have : r' ≥ 0 := Natural.ge_zero
  have : (r':ℤ) ≥ 0 := calc
    _ = (r':ℤ)    := rfl
    _ ≥ ((0:ℕ):ℤ) := by srw [‹r' ≥ 0›]
    _ = 0         := rfl
  have : r' < m := d'.rem_ub

  let sa := sgn a; let sb := sgn b
  have expand_a : a ≃ (mb * q') * sa + r' * sa := calc
    _ = a                                := rfl
    _ ≃ sa * abs a                       := Rel.symm abs_mul_sgn
    _ ≃ sa * (n:ℤ)                       := by srw [←‹(n:ℤ) ≃ abs a›]
    _ ≃ sa * ((m * q' + r' : ℕ):ℤ)       := by srw [d'.div_eqv]
    _ ≃ sa * (((m * q' : ℕ):ℤ) + (r':ℤ)) := by srw [AA.compat₂]
    _ ≃ sa * ((m:ℤ) * (q':ℤ) + (r':ℤ))   := by srw [AA.compat₂]
    _ ≃ sa * (mb * q' + r')              := by srw [‹(m:ℤ) ≃ mb›]
    _ ≃ (mb * q' + r') * sa              := AA.comm
    _ ≃ (mb * q') * sa + r' * sa         := AA.distribR

  /-
  The solutions for `a * b` nonnegative vs. negative are different enough that
  handling them separately keeps the definitions of `q` and `r` simpler, and
  reduces the complexity of the proofs.
  -/
  match show Either (a * b ≥ 0) (a * b < 0) from either_ge_lt with
  | .inl (_ : a * b ≥ 0) =>
    let q : ℤ := q'
    let r : ℤ := r' * sa

    /- Prove div_eqv -/
    have : sa * sb * q' ≃ q' :=
      match show a * b > 0 ∨ a * b ≃ 0 from ge_split.mp ‹a * b ≥ 0› with
      | .inl (_ : a * b > 0) =>
        calc
          _ = sa * sb * q'     := rfl
          _ ≃ sgn (a * b) * q' := by srw [←sgn_compat_mul]
          _ ≃ 1 * q'           := by srw [gt_zero_sgn.mp ‹a * b > 0›]
          _ ≃ q'               := AA.identL
      | .inr (_ : a * b ≃ 0) =>
        have : a ≃ 0 ∨ b ≃ 0 := mul_split_zero.mp ‹a * b ≃ 0›
        have : a ≃ 0 := match ‹a ≃ 0 ∨ b ≃ 0› with
        | .inl (_ : a ≃ 0) => ‹a ≃ 0›
        | .inr (_ : b ≃ 0) => absurd ‹b ≃ 0› ‹AP (b ≄ 0)›.ev
        have : (n:ℤ) ≃ 0 := calc
          _ = (n:ℤ) := rfl
          _ ≃ abs a := ‹(n:ℤ) ≃ abs a›
          _ ≃ 0     := abs_zero.mpr ‹a ≃ 0›
        have : n ≃ 0 := AA.inject ‹(n:ℤ) ≃ (0:ℕ)›
        have (And.intro (_ : q' ≃ 0) _) := Natural.div_zero.mp ‹n ≃ 0›
        have : (q':ℤ) ≃ (0:ℕ) := by srw [‹q' ≃ 0›]
        calc
          _ = sa * sb * q' := rfl
          _ ≃ sa * sb * 0  := by srw [‹(q':ℤ) ≃ 0›]
          _ ≃ 0            := AA.absorbR
          _ ≃ q'           := Rel.symm ‹(q':ℤ) ≃ 0›
    have : a ≃ b * q + r := Rel.symm $ calc
      _ = b * q + r                := rfl
      _ = b * q' + r               := rfl
      _ ≃ b * (sa * sb * q') + r   := by srw [←‹sa * sb * q' ≃ q'›]
      _ ≃ b * (sa * (sb * q')) + r := by srw [AA.assoc]
      _ ≃ b * (sb * q' * sa) + r   := by srw [AA.comm]
      _ ≃ b * (sb * q') * sa + r   := by srw [←AA.assoc]
      _ ≃ b * sb * q' * sa + r     := by srw [←AA.assoc]
      _ ≃ mb * q' * sa + r         := by srw [←abs_sgn]
      _ = mb * q' * sa + r' * sa   := rfl
      _ ≃ a                        := Rel.symm expand_a

    /- Prove rem_mag -/
    have : abs r < mb := calc
      _ = abs r               := rfl
      _ = abs (r' * sa)       := rfl
      _ ≃ abs (r':ℤ) * abs sa := abs_compat_mul
      _ ≃ r' * abs sa         := by srw [abs_ident ‹(r':ℤ) ≥ 0›]
      _ ≃ r' * sa^2           := by srw [abs_sgn_sqr]
      _ ≃ r' * (sgn (a^2))    := by srw [←sgn_pow]
      _ ≤ r' * 1              := by srw [sgn_max] -- uses (r':ℤ) ≥ 0
      _ ≃ r'                  := AA.identR
      _ < m                   := by srw [‹r' < m›]
      _ ≃ mb                  := ‹(m:ℤ) ≃ mb›

    /- Prove rem_sgn -/
    have : sa * sb ≥ 0 := calc
      _ = sa * sb     := rfl
      _ ≃ sgn (a * b) := Rel.symm sgn_compat_mul
      _ ≥ 0           := sgn_preserves_ge_zero.mp ‹a * b ≥ 0›
    have : r' * mb ≥ 0 := mul_preserves_nonneg ‹(r':ℤ) ≥ 0› abs_nonneg
    have : r * b ≥ 0 := calc
      _ = r * b               := rfl
      _ = r' * sa * b         := rfl
      _ ≃ r' * sa * (sb * mb) := by srw [←abs_mul_sgn]
      _ ≃ sa * r' * (sb * mb) := by srw [AA.comm]
      _ ≃ sa * sb * (r' * mb) := AA.expr_xxfxxff_lr_swap_rl
      _ ≥ sa * sb * 0         := by srw [‹r' * mb ≥ 0›]
      _ ≃ 0                   := mul_absorbR

    show FlooredDivision a b from {
      quotient := q
      remainder := r
      div_eqv := ‹a ≃ b * q + r›
      rem_mag := ‹abs r < mb›
      rem_sgn := ‹r * b ≥ 0›
    }

  | .inr (_ : a * b < 0) =>
    have : sa * sb ≃ -1 := calc
      _ = sa * sb     := rfl
      _ ≃ sgn (a * b) := Rel.symm sgn_compat_mul
      _ ≃ -1          := lt_zero_sgn.mp ‹a * b < 0›

    let sr' := sgn (r':ℤ)
    let q := -(q' + sr')
    let r := b * sr' + r' * sa

    /- Prove div_eqv -/
    have : a ≃ b * q + r := Rel.symm $ calc
      _ = b * q + r                                := rfl
      _ = b * -(q' + sr') + (b * sr' + r' * sa)    := rfl
      _ ≃ b * -(q' + sr') + b * sr' + r' * sa      := Rel.symm AA.assoc
      _ ≃ b * (-q' + -sr') + b * sr' + r' * sa     := by srw [neg_compat_add]
      _ ≃ b * -q' + b * -sr' + b * sr' + r' * sa   := by srw [mul_distribL]
      _ ≃ b * -q' + (b * -sr' + b * sr') + r' * sa := by srw [AA.assoc]
      _ ≃ b * -q' + b * (-sr' + sr') + r' * sa     := by srw [←mul_distribL]
      _ ≃ b * -q' + b * 0 + r' * sa                := by srw [neg_invL]
      _ ≃ b * -q' + 0 + r' * sa                    := by srw [mul_absorbR]
      _ ≃ b * -q' + r' * sa                        := by srw [add_identR]
      _ ≃ -(b * q') + r' * sa                      := by srw [←AA.scompatR]
      _ ≃ -1 * (b * q') + r' * sa                  := by srw [←mul_neg_one]
      _ ≃ sa * sb * (b * q') + r' * sa             := by srw [←‹sa * sb ≃ -1›]
      _ ≃ sa * (sb * (b * q')) + r' * sa           := by srw [AA.assoc]
      _ ≃ sb * (b * q') * sa + r' * sa             := by srw [AA.comm]
      _ ≃ (sb * b * q') * sa + r' * sa             := by srw [←AA.assoc]
      _ ≃ (b * sb * q') * sa + r' * sa             := by srw [AA.comm]
      _ ≃ (mb * q') * sa + r' * sa                 := by srw [←abs_sgn]
      _ ≃ a                                        := Rel.symm expand_a

    /- Prove rem_mag -/
    have : b * a < 0 := trans AA.comm ‹a * b < 0›
    have : mb - r' ≥ 0 := calc
      _ = mb - r' := rfl
      _ ≥ mb - m  := by srw [Natural.le_split.mpr (Or.inl ‹r' < m›)]
      _ ≃ mb - mb := by srw [‹(m:ℤ) ≃ mb›]
      _ ≃ 0       := sub_same
    have : sr'^2 ≃ sr' := sgn_sqr_nonneg.mpr ‹(r':ℤ) ≥ 0›
    have : (mb - r') * sr' < mb :=
      match show (r':ℤ) > 0 ∨ (r':ℤ) ≃ 0 from ge_split.mp ‹(r':ℤ) ≥ 0› with
      | .inl (_ : (r':ℤ) > 0) =>
        calc
          _ = (mb - r') * sr' := rfl
          _ ≃ (mb - r') * 1   := by srw [gt_zero_sgn.mp ‹(r':ℤ) > 0›]
          _ ≃ mb - r'         := AA.identR
          _ < mb - 0          := by srw [‹0 < (r':ℤ)›]
          _ ≃ mb              := sub_identR
      | .inr (_ : (r':ℤ) ≃ 0) =>
        have : mb ≄ 0 := mt abs_zero.mp ‹AP (b ≄ 0)›.ev
        have : 0 ≤ mb ∧ 0 ≄ mb := And.intro abs_nonneg ‹0 ≄ mb›
        calc
          _ = (mb - r') * sr' := rfl
          _ ≃ (mb - r') * 0   := by srw [sgn_zero.mpr ‹(r':ℤ) ≃ 0›]
          _ ≃ 0               := AA.absorbR
          _ < mb              := lt_iff_le_neqv.mpr ‹0 ≤ mb ∧ 0 ≄ mb›
    have : abs r < mb := calc
      _ = abs r                           := rfl
      _ = abs (b * sr' + r' * sa)         := rfl
      _ ≃ abs (sb * mb * sr' + r' * sa)   := by srw [←abs_mul_sgn]
      _ ≃ abs (sb * (mb * sr') + r' * sa) := by srw [AA.assoc]
      _ ≃ abs (mb * sr' * sb + r' * sa)   := by srw [AA.comm]
      _ ≃ abs (mb * sr' - r')             := abs_pos_neg_sum ‹b * a < 0›
      _ ≃ abs (mb * sr' - abs (r':ℤ))     := by srw [←abs_ident ‹(r':ℤ) ≥ 0›]
      _ ≃ abs (mb * sr' - r' * sr')       := by srw [abs_sgn]
      _ ≃ abs ((mb - r') * sr')           := by srw [←mul_distribR_sub]
      _ ≃ abs (mb - r') * abs sr'         := abs_compat_mul
      _ ≃ (mb - r') * abs sr'             := by srw [abs_ident ‹mb - r' ≥ 0›]
      _ ≃ (mb - r') * sr'^2               := by srw [abs_sgn_sqr]
      _ ≃ (mb - r') * sr'                 := by srw [‹sr'^2 ≃ sr'›]
      _ < mb                              := ‹(mb - r') * sr' < mb›

    /- Prove rem_sgn -/
    have : abs (r':ℤ) ≃ r' := abs_ident ‹(r':ℤ) ≥ 0›
    have : sr' ≥ 0 := sgn_preserves_ge_zero.mp ‹(r':ℤ) ≥ 0›
    have : r * b ≥ 0 := calc
      _ = r * b                                 := rfl
      _ = (b * sr' + r' * sa) * b               := rfl
      _ ≃ b * sr' * b + r' * sa * b             := AA.distribR
      _ ≃ b * (b * sr') + r' * sa * b           := by srw [AA.comm]
      _ ≃ b * b * sr' + r' * sa * b             := by srw [←AA.assoc]
      _ ≃ b^2 * sr' + r' * sa * b               := by srw [←Natural.pow_two]
      _ ≃ mb^2 * sr' + r' * sa * b              := by srw [←abs_sqr]
      _ ≃ mb * mb * sr' + r' * sa * b           := by srw [Natural.pow_two]
      _ ≃ mb * (mb * sr') + r' * sa * b         := by srw [AA.assoc]
      _ ≃ mb * sr' * mb + r' * sa * b           := by srw [AA.comm]
      _ ≃ mb * sr' * mb + r' * (sa * b)         := by srw [AA.assoc]
      _ ≃ mb * sr' * mb + r' * (sa * (sb * mb)) := by srw [←abs_mul_sgn]
      _ ≃ mb * sr' * mb + r' * (sa * sb * mb)   := by srw [←AA.assoc]
      _ ≃ mb * sr' * mb + r' * (-1 * mb)        := by srw [‹sa * sb ≃ -1›]
      _ ≃ mb * sr' * mb + r' * -mb              := by srw [mul_neg_one]
      _ ≃ mb * sr' * mb + -mb * r'              := by srw [AA.comm]
      _ ≃ mb * sr' * mb + -mb * abs (r':ℤ)      := by srw [←‹abs (r':ℤ) ≃ r'›]
      _ ≃ mb * sr' * mb + -mb * (r' * sr')      := by srw [abs_sgn]
      _ ≃ mb * sr' * mb + -mb * (sr' * r')      := by srw [AA.comm]
      _ ≃ mb * sr' * mb + -(mb * (sr' * r'))    := by srw [←AA.scompatL]
      _ ≃ mb * sr' * mb + -(mb * sr' * r')      := by srw [←AA.assoc]
      _ ≃ mb * sr' * mb - mb * sr' * r'         := Rel.symm sub_defn
      _ ≃ mb * sr' * (mb - r')                  := Rel.symm AA.distribL
      _ ≥ 0 * sr' * (mb - r')                   := by srw [‹mb ≥ 0›]
      _ ≃ 0 * (mb - r')                         := by srw [mul_absorbL]
      _ ≃ 0                                     := mul_absorbL

    show FlooredDivision a b from {
      quotient := q
      remainder := r
      div_eqv := ‹a ≃ b * q + r›
      rem_mag := ‹abs r < mb›
      rem_sgn := ‹r * b ≥ 0›
    }

@[implicit_reducible]
def division : Division ℤ := {
  div_euclidean := div_euclidean
  div_floored := div_floored
}

end Lean4Axiomatic.Integer.Impl.Generic

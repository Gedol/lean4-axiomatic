import Lean4Axiomatic.Integer.Induction
import Lean4Axiomatic.Sequence

/-! # Integer order -/

namespace Lean4Axiomatic.Integer

open AA.TwoOfThree (oneAndThree twoAndThree)
open Coe (coe)
open Logic (
  AP and_mapL and_mapR Either iff_subst_contra iff_subst_covar or_mapL or_mapR
)
open Natural (step)
open Sequence (InfiniteDescent)
open Signed (Negative Positive)

/-! ## Axioms -/

/-- Class defining the basic ordering relations on integers. -/
class Order
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ]
    where
  /-- Definition of and syntax for the _less than or equal to_ relation. -/
  leOp : LE ℤ

  /--
  One integer is less than or equal to another iff adding a natural number to
  the lesser value produces the greater value.
  -/
  le_iff_add_nat {a b : ℤ} : a ≤ b ↔ ∃ k : ℕ, b ≃ a + coe k

  /-- Definition of and syntax for the _less than_ relation. -/
  ltOp : LT ℤ

  /-- The intuitive meaning of _less than_ in terms of _less than or equal_. -/
  lt_iff_le_neqv {a b : ℤ} : a < b ↔ a ≤ b ∧ a ≄ b

attribute [implicit_reducible, instance] Order.leOp
attribute [implicit_reducible, instance] Order.ltOp

export Order (le_iff_add_nat leOp lt_iff_le_neqv ltOp)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Order ℤ]

/-! ## Derived properties -/

/--
Extract nonequivalence of integers from a _greater than_ relation between them.
-/
theorem gt_neqv {a b : ℤ} : a > b → a ≄ b := by
  intro (_ : a > b)
  show a ≄ b

  have (And.intro _ (_ : b ≄ a)) := lt_iff_le_neqv.mp ‹b < a›
  have : a ≄ b := Rel.symm ‹b ≄ a›
  exact this

/--
Construct a _less than_ relation on integers from a
_less than or equivalent to_ relation and a _not equivalent to_ relation.
-/
theorem lt_from_le_neqv {a b : ℤ} : a ≤ b → a ≄ b → a < b := by
  intro (_ : a ≤ b) (_ : a ≄ b)
  show a < b
  exact lt_iff_le_neqv.mpr (And.intro ‹a ≤ b› ‹a ≄ b›)

/--
Construct a _greater than_ relation on integers from a
_greater than or equivalent to_ relation and a _not equivalent to_ relation.
-/
theorem gt_from_ge_neqv {a b : ℤ} : a ≥ b → a ≄ b → a > b := by
  intro (_ : a ≥ b) (_ : a ≄ b)
  show a > b

  have : b < a := lt_from_le_neqv ‹b ≤ a› (Rel.symm ‹a ≄ b›)
  exact this

/--
Natural numbers maintain their _less than or equivalent to_ relationship when
converted to integers.
-/
theorem from_natural_respects_le {n m : ℕ} : n ≤ m ↔ (n:ℤ) ≤ (m:ℤ) := by
  /-
  This proof could be much simpler if `(· ≤ ·)` for integers was defined in
  terms of `sgn`.
  -/
  apply Iff.intro
  case mp =>
    intro (_ : n ≤ m)
    show (n:ℤ) ≤ (m:ℤ)
    have (Exists.intro (k : ℕ) (_ : n + k ≃ m)) := Natural.le_defn.mp ‹n ≤ m›
    have : (m:ℤ) ≃ (n:ℤ) + k := calc
      _ = (m:ℤ)           := rfl
      _ ≃ ((n + k : ℕ):ℤ) := by srw [←‹n + k ≃ m›]
      _ ≃ (n:ℤ) + k       := AA.compat₂
    have : ∃ (k : ℕ), (m:ℤ) ≃ (n:ℤ) + k := Exists.intro k ‹(m:ℤ) ≃ (n:ℤ) + k›
    have : (n:ℤ) ≤ (m:ℤ) := le_iff_add_nat.mpr ‹∃ (k : ℕ), (m:ℤ) ≃ (n:ℤ) + k›
    exact this
  case mpr =>
    intro (_ : (n:ℤ) ≤ (m:ℤ))
    show n ≤ m
    have (Exists.intro (k : ℕ) (_ : (m:ℤ) ≃ (n:ℤ) + k)) :=
      le_iff_add_nat.mp ‹(n:ℤ) ≤ (m:ℤ)›
    have : ((n + k : ℕ):ℤ) ≃ (m:ℤ) := calc
      _ = ((n + k : ℕ):ℤ) := rfl
      _ ≃ (n:ℤ) + k       := AA.compat₂
      _ ≃ (m:ℤ)           := Rel.symm ‹(m:ℤ) ≃ (n:ℤ) + k›
    have : n + k ≃ m := AA.inject ‹((n + k : ℕ):ℤ) ≃ (m:ℤ)›
    have : n ≤ m := Natural.le_defn.mpr (Exists.intro k ‹n + k ≃ m›)
    exact this

/-- Immediate corollary for use with `gcongr`. -/
@[gcongr]
theorem from_natural_respects_le_mp {n m : ℕ} : n ≤ m → (n:ℤ) ≤ (m:ℤ) :=
  from_natural_respects_le.mp

/--
Natural numbers maintain their _less than_ relationship when converted to
integers.
-/
theorem from_natural_respects_lt {n m : ℕ} : n < m ↔ (n:ℤ) < (m:ℤ) := by
  have : n ≤ m ↔ (n:ℤ) ≤ m := from_natural_respects_le
  have : n ≄ m ↔ (n:ℤ) ≄ m := Iff.intro (mt AA.inject) (mt AA.subst₁)
  calc
    _ ↔ n < m                 := Iff.rfl
    _ ↔ n ≤ m ∧ n ≄ m         := Natural.lt_defn
    _ ↔ (n:ℤ) ≤ m ∧ n ≄ m     := iff_subst_covar and_mapL ‹n ≤ m ↔ (n:ℤ) ≤ m›
    _ ↔ (n:ℤ) ≤ m ∧ (n:ℤ) ≄ m := iff_subst_covar and_mapR ‹n ≄ m ↔ (n:ℤ) ≄ m›
    _ ↔ (n:ℤ) < (m:ℤ)         := lt_iff_le_neqv.symm

/-- Immediate corollary for use with `gcongr`. -/
@[gcongr]
theorem from_natural_respects_lt_mp {n m : ℕ} : n < m → (n:ℤ) < (m:ℤ) :=
  from_natural_respects_lt.mp

/-- The integer two is greater than one. -/
theorem two_gt_one : (2:ℤ) > 1 := by
  have : ((1:ℕ):ℤ) < ((2:ℕ):ℤ) := by srw [Natural.two_gt_one]
  exact this

/--
Equivalent integers can be substituted on the left of the `· ≤ ·` relation.

**Property intuition**: This must be true for `· ≤ ·` to be a valid integer
relation.

**Proof intuition**: The result follows from transitivity and substitution on
the underlying definition of `· ≤ ·`.
-/
@[gcongr]
theorem le_substL_eqv {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ ≤ b → a₂ ≤ b := by
  intro (_ : a₁ ≃ a₂) (_ : a₁ ≤ b)
  show a₂ ≤ b
  have (Exists.intro (k : ℕ) (_ : b ≃ a₁ + k)) := le_iff_add_nat.mp ‹a₁ ≤ b›
  apply le_iff_add_nat.mpr
  show ∃ (k : ℕ), b ≃ a₂ + k
  have : b ≃ a₂ + k := calc
    _ = b      := rfl
    _ ≃ a₁ + k := ‹b ≃ a₁ + k›
    _ ≃ a₂ + k := by srw [‹a₁ ≃ a₂›]
  exact Exists.intro k ‹b ≃ a₂ + coe k›

/--
Equivalent integers can be substituted on the right of the `· ≤ ·` relation.

**Property intuition**: This must be true for `· ≤ ·` to be a valid integer
relation.

**Proof intuition**: The result follows from transitivity and substitution on
the underlying definition of `· ≤ ·`.
-/
@[gcongr]
theorem le_substR_eqv {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b ≤ a₁ → b ≤ a₂ := by
  intro (_ : a₁ ≃ a₂) (_ : b ≤ a₁)
  show b ≤ a₂
  have (Exists.intro (k : ℕ) (_ : a₁ ≃ b + coe k)) :=
    le_iff_add_nat.mp ‹b ≤ a₁›
  apply le_iff_add_nat.mpr
  show ∃ (k : ℕ), a₂ ≃ b + coe k
  have : a₂ ≃ b + coe k := Rel.trans (Rel.symm ‹a₁ ≃ a₂›) ‹a₁ ≃ b + coe k›
  exact Exists.intro k ‹a₂ ≃ b + coe k›

instance le_substitutive_eqv
    : AA.Substitutive₂ (α := ℤ) (· ≤ ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => le_substL_eqv }
  substitutiveR := { subst₂ := λ (_ : True) => le_substR_eqv }
}

/--
Equivalent integers can be substituted on the left of the `· < ·` relation.

**Property intuition**: This must be true for `· < ·` to be a valid integer
relation.

**Proof intuition**: The result follows from substitution on the underlying
definition of `· < ·`.
-/
@[gcongr]
theorem lt_substL_eqv {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ < b → a₂ < b := by
  intro (_ : a₁ ≃ a₂) (_ : a₁ < b)
  show a₂ < b
  have (And.intro (_ : a₁ ≤ b) (_ : a₁ ≄ b)) := lt_iff_le_neqv.mp ‹a₁ < b›
  apply lt_iff_le_neqv.mpr
  show a₂ ≤ b ∧ a₂ ≄ b
  have : a₂ ≤ b := by prw [‹a₁ ≃ a₂›] ‹a₁ ≤ b›
  have : a₂ ≄ b := by prw [‹a₁ ≃ a₂›] ‹a₁ ≄ b›
  exact And.intro ‹a₂ ≤ b› ‹a₂ ≄ b›

/--
Equivalent integers can be substituted on the right of the `· < ·` relation.

**Property intuition**: This must be true for `· < ·` to be a valid integer
relation.

**Proof intuition**: The result follows from substitution on the underlying
definition of `· < ·`.
-/
@[gcongr]
theorem lt_substR_eqv {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b < a₁ → b < a₂ := by
  intro (_ : a₁ ≃ a₂) (_ : b < a₁)
  show b < a₂
  have (And.intro (_ : b ≤ a₁) (_ : b ≄ a₁)) := lt_iff_le_neqv.mp ‹b < a₁›
  apply lt_iff_le_neqv.mpr
  show b ≤ a₂ ∧ b ≄ a₂
  have : b ≤ a₂ := by prw [‹a₁ ≃ a₂›] ‹b ≤ a₁›
  have : b ≄ a₂ := by prw [‹a₁ ≃ a₂›] ‹b ≄ a₁›
  exact And.intro ‹b ≤ a₂› ‹b ≄ a₂›

instance lt_substitutive_eqv
    : AA.Substitutive₂ (α := ℤ) (· < ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => lt_substL_eqv }
  substitutiveR := { subst₂ := λ (_ : True) => lt_substR_eqv }
}

instance gt_substitutive_eqv
    : AA.Substitutive₂ (α := ℤ) (· > ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => lt_substR_eqv }
  substitutiveR := { subst₂ := λ (_ : True) => lt_substL_eqv }
}

/--
_Less than or equivalent to_ is reflexive.

**Property intuition**: Equivalence is already reflexive.

**Proof intuition**: The difference between the two operands of _less than or
equivalent to_ must be a natural number; zero in this case.
-/
theorem le_refl {a : ℤ} : a ≤ a := by
  apply le_iff_add_nat.mpr
  show ∃ (k : ℕ), a ≃ a + coe k
  have : a ≃ a + coe (0 : ℕ) := calc
    a               ≃ _ := Rel.symm AA.identR
    a + 0           ≃ _ := Rel.refl
    a + coe (0 : ℕ) ≃ _ := Rel.refl
  exact Exists.intro 0 ‹a ≃ a + coe (0 : ℕ)›

/--
Transitivity of _less than_ with equivalence on the left.

**Property and proof intuition**: Follows from the substituitive property of
equivalence on _less than_.
-/
theorem trans_eqv_lt_lt {a b c : ℤ} : a ≃ b → b < c → a < c := by
  intro (_ : a ≃ b) (_ : b < c)
  show a < c
  prw [←‹a ≃ b›] ‹b < c›

/-- Enable `trans_eqv_lt_lt` use by `calc` tactics. -/
instance trans_eqv_lt_lt_inst : Trans (α := ℤ) (· ≃ ·) (· < ·) (· < ·) := {
  trans := trans_eqv_lt_lt
}

/--
Transitivity of _less than_ with equivalence on the right.

**Property and proof intuition**: Follows from the substituitive property of
equivalence on _less than_.
-/
theorem trans_lt_eqv_lt {a b c : ℤ} : a < b → b ≃ c → a < c := by
  intro (_ : a < b) (_ : b ≃ c)
  show a < c
  prw [‹b ≃ c›] ‹a < b›

/-- Enable `trans_lt_eqv_lt` use by `calc` tactics. -/
instance trans_lt_eqv_lt_inst : Trans (α := ℤ) (· < ·) (· ≃ ·) (· < ·) := {
  trans := trans_lt_eqv_lt
}

/--
Transitivity of _greater than_ with equivalence on the left.

**Property and proof intuition**: Follows from transitivity of _less than_ and
equivalence.
-/
theorem trans_eqv_gt_gt {a b c : ℤ} : a ≃ b → b > c → a > c := by
  intro (_ : a ≃ b) (_ : b > c)
  show a > c
  have : c < a := by prw [←‹a ≃ b›] ‹c < b›
  exact this

/-- Enable `trans_eqv_gt_gt` use by `calc` tactics. -/
instance trans_eqv_gt_gt_inst : Trans (α := ℤ) (· ≃ ·) (· > ·) (· > ·) := {
  trans := trans_eqv_gt_gt
}

/--
Transitivity of _greater than_ with equivalence on the left.

**Property and proof intuition**: Follows from transitivity of _less than_ and
equivalence.
-/
theorem trans_gt_eqv_gt {a b c : ℤ} : a > b → b ≃ c → a > c := by
  intro (_ : a > b) (_ : b ≃ c)
  show a > c
  have : c < a := by prw [‹b ≃ c›] ‹b < a›
  exact this

/-- Enable `trans_gt_eqv_gt` use by `calc` tactics. -/
instance trans_gt_eqv_gt_inst : Trans (α := ℤ) (· > ·) (· ≃ ·) (· > ·) := {
  trans := trans_gt_eqv_gt
}

variable [Multiplication (ℕ := ℕ) ℤ] [Negation ℤ] [Subtraction ℤ] [Sign ℤ]

/--
Equivalence between the _greater than_ relation on integers and their
difference being positive.

**Property intuition**: For nonnegative values, this makes sense: taking away a
smaller value from a larger one should leave a positive amount behind. Taking
away a negative value is the same as adding its positive equivalent, which will
always give a positive result because the other number was "less negative".

**Proof intuition**: No special insight here; assumptions and goals are
expanded into their underlying properties, and then connected.
-/
theorem gt_iff_pos_diff {a b : ℤ} : a > b ↔ Positive (a - b) := by
  apply Iff.intro
  case mp =>
    intro (_ : b < a)
    show Positive (a - b)
    have (And.intro (_ : b ≤ a) (_ : b ≄ a)) := lt_iff_le_neqv.mp ‹b < a›
    have (Exists.intro (k : ℕ) (_ : a ≃ b + coe k)) :=
      le_iff_add_nat.mp ‹b ≤ a›
    have : a - b ≃ coe k := subR_moveR_addL.mpr ‹a ≃ b + coe k›
    have : a - b ≄ 0 := mt zero_diff_iff_eqv.mp (Rel.symm ‹b ≄ a›)
    have : (k:ℤ) ≄ 0 := by prw [‹a - b ≃ coe k›] ‹a - b ≄ 0›
    have : k ≄ 0 := AA.inject ‹coe k ≄ coe (0 : ℕ)›
    have : Positive k := Signed.positive_defn.mpr ‹k ≄ 0›
    have : Positive (a - b) := positive_intro_nat ‹Positive k› ‹a - b ≃ coe k›
    exact this
  case mpr =>
    intro (_ : Positive (a - b))
    show b < a
    have
      (Exists.intro (k : ℕ) (And.intro (_ : Positive k) (_ : a - b ≃ coe k)))
        := positive_elim_nat ‹Positive (a - b)›
    apply lt_iff_le_neqv.mpr
    show b ≤ a ∧ b ≄ a
    have : a ≃ b + coe k := subR_moveR_addL.mp ‹a - b ≃ coe k›
    have : b ≤ a := le_iff_add_nat.mpr (Exists.intro k ‹a ≃ b + coe k›)
    have : k ≄ 0 := Signed.positive_defn.mp ‹Positive k›
    have : (k:ℤ) ≄ ((0:ℕ):ℤ) := AA.subst_neqv ‹k ≄ 0›
    have : a - b ≄ 0 := by prw [←‹a - b ≃ coe k›] ‹(coe k : ℤ) ≄ 0›
    have : b ≄ a := Rel.symm (mt zero_diff_iff_eqv.mpr ‹a - b ≄ 0›)
    exact And.intro ‹b ≤ a› ‹b ≄ a›

/--
Integers greater than zero are positive.

**Proof intuition**: Follows directly from `gt_iff_pos_diff`.
-/
theorem gt_zero_iff_pos {a : ℤ} : a > 0 ↔ Positive a := calc
  _ ↔ a > 0            := Iff.rfl
  _ ↔ Positive (a - 0) := gt_iff_pos_diff
  _ ↔ Positive a       := Rel.iff_subst_eqv positive_subst sub_identR

/-- A positive integer is nonzero. -/
theorem neqv_zero_from_gt_zero {a : ℤ} : a > 0 → a ≄ 0 := by
  intro (_ : a > 0)
  have : Positive a := gt_zero_iff_pos.mp ‹a > 0›
  have : a ≄ 0 := neqv_zero_from_positive ‹Positive a›
  exact this

/--
Equivalence between the _less than_ relation on integers and their
difference being negative.

**Property intuition**: For nonnegative values, this makes sense: taking away a
larger value from a smaller one should leave a negative amount behind. Taking
away a negative value is the same as adding its positive equivalent, which will
still give a negative result because the other number was "more negative".

**Proof intuition**: Flip the ordering around to be _greater than_, and derive
a positive difference. Then swap the operands of the difference back, and show
that it's now negative.
-/
theorem lt_iff_neg_diff {a b : ℤ} : a < b ↔ Negative (a - b) := by
  apply Iff.intro
  case mp =>
    intro (_ : a < b)
    show Negative (a - b)
    have : Positive (b - a) := gt_iff_pos_diff.mp ‹a < b›
    have : Positive (-(a - b)) := by prw [←sub_neg_flip] ‹Positive (b - a)›
    have : Negative (a - b) :=
      negative_iff_negated_positive.mpr ‹Positive (-(a - b))›
    exact this
  case mpr =>
    intro (_ : Negative (a - b))
    show a < b
    have : Negative (-(b - a)) := by prw [←sub_neg_flip] ‹Negative (a - b)›
    have : Positive (b - a) :=
      positive_iff_negated_negative.mpr ‹Negative (-(b - a))›
    have : a < b := gt_iff_pos_diff.mpr ‹Positive (b - a)›
    exact this

/--
The `· < ·` relation is preserved when the same value is added on the right to
both sides.

**Property intuition**: Both values are changed by the same amount, so their
ordering won't be affected.

**Proof intuition**: Convert the `· < ·` relation into subtraction; then the
common value gets canceled out.
-/
@[gcongr]
theorem add_substL_lt {a b c : ℤ} : a < b → a + c < b + c := by
  intro (_ : a < b)
  show a + c < b + c
  have : Positive (b - a) := gt_iff_pos_diff.mp ‹a < b›
  apply gt_iff_pos_diff.mpr
  show Positive (b + c - (a + c))
  have : b - a ≃ b + c - (a + c) := Rel.symm sub_sums_sameR
  prw [‹b - a ≃ b + c - (a + c)›] ‹Positive (b - a)›

/--
The `· < ·` relation is preserved when the same value is added on the left to
both sides.

**Property intuition**: Both values are changed by the same amount, so their
ordering won't be affected.

**Proof intuition**: Use substitution on the other side and commutativity of
addition.
-/
@[gcongr]
theorem add_substR_lt {a b c : ℤ} : a < b → c + a < c + b := by
  intro (_ : a < b)
  show c + a < c + b
  calc
    _ = c + a := rfl
    _ ≃ a + c := AA.comm
    _ < b + c := by srw [‹a < b›]
    _ ≃ c + b := AA.comm

instance add_substitutive_lt
    : AA.Substitutive₂ (α := ℤ) (· + ·) AA.tc (· < ·) (· < ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => add_substL_lt }
  substitutiveR := { subst₂ := λ (_ : True) => add_substR_lt }
}

/--
The `· < ·` relation on sums with the same left operand is preserved when that
operand is removed from both.

**Property intuition**: Both remaining values had been changed by the same
amount due to the sums, so their ordering won't be affected.

**Proof intuition**: Convert the `· < ·` relation into subtraction; then the
common value gets canceled out.
-/
theorem add_cancelL_lt {a b c : ℤ} : c + a < c + b → a < b := by
  intro (_ : c + a < c + b)
  show a < b
  have : Positive (c + b - (c + a)) := gt_iff_pos_diff.mp ‹c + a < c + b›
  apply gt_iff_pos_diff.mpr
  show Positive (b - a)
  have : c + b - (c + a) ≃ b - a := calc
    c + b - (c + a) ≃ _ := by srw [AA.comm]
    b + c - (c + a) ≃ _ := by srw [AA.comm]
    b + c - (a + c) ≃ _ := sub_sums_sameR
    b - a           ≃ _ := Rel.refl
  prw [‹c + b - (c + a) ≃ b - a›] ‹Positive (c + b - (c + a))›

@[implicit_reducible]
def add_cancellativeL_lt
    : AA.CancellativeOn Hand.L (α := ℤ) (· + ·) AA.tc (· < ·) (· < ·)
    := {
  cancel := λ (_ : True) => add_cancelL_lt
}

instance add_cancellative_lt
    : AA.Cancellative (α := ℤ) (· + ·) AA.tc (· < ·) (· < ·)
    := {
  cancellativeL := add_cancellativeL_lt
  cancellativeR := AA.cancelR_from_cancelL add_cancellativeL_lt
}

/--
The `· < ·` relation is preserved when both sides are multiplied on the right
by the same positive value.

**Property intuition**: Both values are scaled away from zero by the same
factor, so their ordering won't be affected; positive values become more
positive and negative values become more negative.

**Proof intuition**: The goal `a * c < b * c` can be expressed as
`Positive (b * c - a * c)`, which factors into `Positive ((b - a) * c)`. The
result follows by showing that the two factors being positive means that their
product is positive.
-/
@[gcongr]
theorem mul_substL_lt {a b c : ℤ} : Positive c → a < b → a * c < b * c := by
  intro (_ : Positive c) (_ : a < b)
  show a * c < b * c
  have : Positive (b - a)         := gt_iff_pos_diff.mp ‹a < b›
  have : Positive ((b - a) * c)   := mul_preserves_positive this ‹Positive c›
  have : Positive (b * c - a * c) := by prw [mul_distribR_sub] this
  have : a * c < b * c            := gt_iff_pos_diff.mpr this
  exact this

/--
The `· < ·` relation is preserved when both sides are multiplied on the left
by the same positive value.

**Property intuition**: Both values are scaled away from zero by the same
factor, so their ordering won't be affected; positive values become more
positive and negative values become more negative.

**Proof intuition**: Use commutativity and substitute on the other side.
-/
@[gcongr]
theorem mul_substR_lt {a b c : ℤ} : Positive c → a < b → c * a < c * b := by
  intro (_ : Positive c) (_ : a < b)
  show c * a < c * b
  calc
    _ = c * a := rfl
    _ ≃ a * c := AA.comm
    _ < b * c := by srw [‹a < b›]
    _ ≃ c * b := AA.comm

instance mul_substitutive_lt
    : AA.Substitutive₂ (α := ℤ) (· * ·) Positive (· < ·) (· < ·)
    := {
  substitutiveL := { subst₂ := mul_substL_lt }
  substitutiveR := { subst₂ := mul_substR_lt }
}

/--
The `· < ·` relation on products with the same (positive) left factor is
preserved when that factor is removed from both products.

**Property intuition**: Both values are scaled towards zero by the same factor,
so their ordering won't be affected; positive values become less positive and
negative values become less negative.

**Proof intuition**: The assumption `c * a < c * b` can be expressed as
`Positive (c * b - c * a)`, which factors into `Positive (c * (b - a))`. Thus
`c` and `b - a` must have the same sign, and since `c` is positive, `b - a` is
as well, giving the result.
-/
theorem mul_cancelL_lt {a b c : ℤ} : Positive c → c * a < c * b → a < b := by
  intro (_ : Positive c) (_ : c * a < c * b)
  show a < b
  have : Positive (c * b - c * a) := gt_iff_pos_diff.mp ‹c * a < c * b›
  apply gt_iff_pos_diff.mpr
  show Positive (b - a)
  have : Positive (c * (b - a)) :=
    by prw [←mul_distribL_sub] ‹Positive (c * b - c * a)›
  have : SameSign c (b - a) :=
    positive_mul_iff_same_sign.mp ‹Positive (c * (b - a))›
  have : Positive (b - a) :=
    same_sign_positive ‹SameSign c (b - a)› ‹Positive c›
  exact this

@[implicit_reducible]
def mul_cancellativeL_lt
    : AA.CancellativeOn Hand.L (α := ℤ) (· * ·) Positive (· < ·) (· < ·)
    := {
  cancel := mul_cancelL_lt
}

instance mul_cancellative_lt
    : AA.Cancellative (α := ℤ) (· * ·) Positive (· < ·) (· < ·)
    := {
  cancellativeL := mul_cancellativeL_lt
  cancellativeR := AA.cancelR_from_cancelL mul_cancellativeL_lt
}

/--
Negation reverses order.

**Property intuition**: The sequence of negative integers, in the standard
order, is backwards compared to the positive integers: counting upwards,
negative integers reduce in magnitude (get closer to zero) while positive
integers increase in magnitude (get farther from zero).

**Proof intuition**: Expanding the definition of ordering into a property about
positive integers, the proof just requires showing that two integer expressions
are the same.
-/
theorem lt_neg_flip {a b : ℤ} : a < b ↔ -b < -a := by
  have : -a - -b ≃ b - a := calc
    (-a) - -b    ≃ _ := sub_defn
    (-a) + -(-b) ≃ _ := by srw [neg_involutive]
    (-a) + b     ≃ _ := AA.comm
    b + -a       ≃ _ := Rel.symm sub_defn
    b - a        ≃ _ := Rel.refl
  apply Iff.intro
  case mp =>
    intro (_ : a < b)
    show -b < -a
    have : Positive (b - a) := gt_iff_pos_diff.mp ‹a < b›
    apply gt_iff_pos_diff.mpr
    show Positive (-a - -b)
    prw [←‹-a - -b ≃ b - a›] ‹Positive (b - a)›
  case mpr =>
    intro (_ : -b < -a)
    show a < b
    have : Positive (-a - -b) := gt_iff_pos_diff.mp ‹-b < -a›
    apply gt_iff_pos_diff.mpr
    show Positive (b - a)
    prw [‹-a - -b ≃ b - a›] ‹Positive (-a - -b)›

instance lt_substitutive_neg
    : AA.Substitutive₁ (α := ℤ) (-·) (· < ·) (· > ·)
    := {
  subst₁ := lt_neg_flip.mp
}

/-- Corollary of `lt_neg_flip` for use with `gcongr`. -/
@[gcongr]
theorem lt_neg_subst {a b : ℤ} : a < b → -b < -a := lt_neg_flip.mp

instance lt_injective_neg : AA.Injective (α := ℤ) (-·) (· < ·) (· > ·) := {
  inject := lt_neg_flip.mpr
}

/--
_Less than or equivalent to_ is literally the same as _less than_ OR
_equivalent to_.

**Proof intuition**: For the forwards direction, if `a ≃ b` then we are done;
if `a ≄ b` then `a ≤ b` lets us conclude `a < b`. The reverse direction follows
directly from definitions.
-/
theorem le_split {a b : ℤ} : a ≤ b ↔ a < b ∨ a ≃ b := by
  apply Iff.intro
  case mp =>
    intro (_ : a ≤ b)
    show a < b ∨ a ≃ b
    have : Decidable (a ≃ b) := eqv? a b
    have : a < b ∨ a ≃ b := match this with
    | isTrue (_ : a ≃ b) =>
      Or.inr ‹a ≃ b›
    | isFalse (_ : a ≄ b) =>
      have : a < b := lt_iff_le_neqv.mpr (And.intro ‹a ≤ b› ‹a ≄ b›)
      Or.inl ‹a < b›
    exact this
  case mpr =>
    intro (_ : a < b ∨ a ≃ b)
    show a ≤ b
    have : a ≤ b := match ‹a < b ∨ a ≃ b› with
    | Or.inl (_ : a < b) =>
      have (And.intro (_ : a ≤ b) _) := lt_iff_le_neqv.mp ‹a < b›
      ‹a ≤ b›
    | Or.inr (_ : a ≃ b) =>
      have : a ≤ a := le_refl
      have : a ≤ b := by prw [‹a ≃ b›] ‹a ≤ a›
      ‹a ≤ b›
    exact this

/--
The _greater than or equivalent to_ relation can be formed from, or split into,
the two relations in its name.

**Proof intuition**: Follows directly from `le_split`.
-/
theorem ge_split {a b : ℤ} : a ≥ b ↔ a > b ∨ a ≃ b := calc
  _ ↔ a ≥ b         := Iff.rfl
  _ ↔ b < a ∨ b ≃ a := le_split
  _ ↔ a > b ∨ a ≃ b := iff_subst_covar or_mapR Fn.swap

/--
Convert the _less than_ relation to and from its representation as the sign
value of the difference of its operands.

**Property intuition**: If a subtraction's result is negative, then its first
operand must be less than its second.

**Proof intuition**: Use `Negative` as an intermediate step in the conversion.
-/
theorem lt_sgn {a b : ℤ} : a < b ↔ sgn (a - b) ≃ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : a < b)
    show sgn (a - b) ≃ -1
    have : Negative (a - b) := lt_iff_neg_diff.mp ‹a < b›
    have : sgn (a - b) ≃ -1 := sgn_negative.mp this
    exact this
  case mpr =>
    intro (_ : sgn (a - b) ≃ -1)
    show a < b
    have : Negative (a - b) := sgn_negative.mpr ‹sgn (a - b) ≃ -1›
    have : a < b := lt_iff_neg_diff.mpr this
    exact this

/--
Integers are less than zero iff they have sign `-1`.

**Proof intuition**: Follows directly from `lt_sgn`.
-/
theorem lt_zero_sgn {a : ℤ} : a < 0 ↔ sgn a ≃ -1 := calc
  _ ↔ a < 0            := Iff.rfl
  _ ↔ sgn (a - 0) ≃ -1 := lt_sgn
  _ ↔ sgn a ≃ -1       := by srw [sub_identR]

/--
Convert the _greater than_ relation to and from its representation as the sign
value of the difference of its operands.

**Property intuition**: If a subtraction's result is positive, then its first
operand must be greater than its second.

**Proof intuition**: Use `Positive` as an intermediate step in the conversion.
-/
theorem gt_sgn {a b : ℤ} : a > b ↔ sgn (a - b) ≃ 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : a > b)
    show sgn (a - b) ≃ 1
    have : Positive (a - b) := gt_iff_pos_diff.mp ‹a > b›
    have : sgn (a - b) ≃ 1 := sgn_positive.mp this
    exact this
  case mpr =>
    intro (_ : sgn (a - b) ≃ 1)
    show a > b
    have : Positive (a - b) := sgn_positive.mpr ‹sgn (a - b) ≃ 1›
    have : a > b := gt_iff_pos_diff.mpr this
    exact this

/--
Integers are greater than zero iff they have sign `1`.

**Proof intuition**: Follows directly from `gt_sgn`.
-/
theorem gt_zero_sgn {a : ℤ} : a > 0 ↔ sgn a ≃ 1 := calc
  _ ↔ a > 0           := Iff.rfl
  _ ↔ sgn (a - 0) ≃ 1 := gt_sgn
  _ ↔ sgn a ≃ 1       := by srw [sub_identR]

/--
Converts the _greater than or equivalent to_ relation on integers to and from
its _signum_ function representation.

**Property intuition**: The result of subtracting a smaller (or equivalent)
value from a larger one will never be negative.

**Proof intuition**: In the forward direction, assume the sign of the
difference _is_ `-1` and attempt to reach a contradiction. Split `a ≥ b` into
`a > b` and `a ≃ b`. In either case, the sign of `a - b` is different from `-1`
which is impossible. In the reverse direction, consider the three `sgn` values
of `a - b`: zero and one both imply `a ≥ b`, while negative one contradicts the
assumption that `sgn (a - b) ≄ -1`.
-/
theorem ge_sgn {a b : ℤ} : a ≥ b ↔ sgn (a - b) ≄ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : a ≥ b) (_ : sgn (a - b) ≃ -1)
    show False
    have : a > b ∨ a ≃ b := ge_split.mp ‹a ≥ b›
    let TwoSgns :=
      AA.TwoOfThree (sgn (a - b) ≃ 0) (sgn (a - b) ≃ 1) (sgn (a - b) ≃ -1)
    have : TwoSgns :=
      match ‹a > b ∨ a ≃ b› with
      | Or.inl (_ : a > b) =>
        have : sgn (a - b) ≃ 1 := gt_sgn.mp ‹a > b›
        twoAndThree ‹sgn (a - b) ≃ 1› ‹sgn (a - b) ≃ -1›
      | Or.inr (_ : a ≃ b) =>
        have : sgn (a - b) ≃ 0 := eqv_sgn.mp ‹a ≃ b›
        oneAndThree ‹sgn (a - b) ≃ 0› ‹sgn (a - b) ≃ -1›
    have : ¬TwoSgns := signs_distinct
    exact absurd ‹TwoSgns› ‹¬TwoSgns›
  case mpr =>
    intro (_ : sgn (a - b) ≄ -1)
    show a ≥ b
    match sgn_trichotomy (a - b) with
    | AA.OneOfThree₁.first (_ : sgn (a - b) ≃ 0) =>
      have : a ≃ b := eqv_sgn.mpr ‹sgn (a - b) ≃ 0›
      have : a ≥ b := ge_split.mpr (Or.inr ‹a ≃ b›)
      exact this
    | AA.OneOfThree₁.second (_ : sgn (a - b) ≃ 1) =>
      have : a > b := gt_sgn.mpr ‹sgn (a - b) ≃ 1›
      have : a ≥ b := ge_split.mpr (Or.inl ‹a > b›)
      exact this
    | AA.OneOfThree₁.third (_ : sgn (a - b) ≃ -1) =>
      exact absurd ‹sgn (a - b) ≃ -1› ‹sgn (a - b) ≄ -1›

/--
Converts the _less than or equivalent to_ relation on integers to and from
its _signum_ function representation.

**Property intuition**: The result of subtracting a larger (or equivalent)
value from a smaller one will never be positive.

**Proof intuition**: Follows from `ge_sgn` and properties of negation.
-/
theorem le_sgn {a b : ℤ} : a ≤ b ↔ sgn (a - b) ≄ 1 := by
  have reduce_neg : -sgn (b - a) ≃ -(-1) ↔ sgn (a - b) ≃ 1 := calc
    _ ↔ -sgn (b - a) ≃ -(-1)   := Iff.rfl
    _ ↔ sgn (a - b) ≃ -(-1)    := by srw [←sgn_compat_neg, sub_neg_flip]
    _ ↔ sgn (a - b) ≃ 1        := by srw [neg_involutive]
  calc
    _ ↔ a ≤ b                  := Iff.rfl
    _ ↔ sgn (b - a) ≄ -1       := ge_sgn
    _ ↔ -sgn (b - a) ≄ -(-1)   := Iff.intro AA.subst₁ AA.inject
    _ ↔ sgn (a - b) ≄ 1        := iff_subst_contra mt reduce_neg

/--
Integers are greater than or equivalent to zero iff they don't have sign `-1`.

**Proof intuition**: Follows directly from `ge_sgn`.
-/
theorem ge_zero_sgn {a : ℤ} : a ≥ 0 ↔ sgn a ≄ -1 := calc
  _ ↔ a ≥ 0            := Iff.rfl
  _ ↔ sgn (a - 0) ≄ -1 := ge_sgn
  _ ↔ sgn a ≄ -1       := iff_subst_contra mt (by srw [sub_identR])

/--
The only sign value greater than zero, is one.

**Property intuition**: The only sign values are `1`, `0`, and `-1`.

**Proof intuition**: The sign of any number greater than zero is one; taking
the sign of a sign leaves it unchanged.
-/
theorem sgn_gt_zero_iff_pos {a : ℤ} : sgn a > 0 ↔ sgn a ≃ 1 := calc
  _ ↔ sgn a > 0       := Iff.rfl
  _ ↔ sgn (sgn a) ≃ 1 := gt_zero_sgn
  _ ↔ sgn a ≃ 1       := by srw [sgn_idemp]

/--
Negative one is the only sign value that's not greater than or equivalent to
zero.

**Property intuition**: The only sign values are `1`, `0`, and `-1`.

**Proof intuition**: The sign of any number greater than or equivalent to zero
is not `-1`; taking the sign of a sign leaves it unchanged.
-/
theorem sgn_ge_zero_iff_nonneg {a : ℤ} : sgn a ≥ 0 ↔ sgn a ≄ -1 := calc
  _ ↔ sgn a ≥ 0        := Iff.rfl
  _ ↔ sgn (sgn a) ≄ -1 := ge_zero_sgn
  _ ↔ sgn a ≄ -1       := iff_subst_contra mt (by srw [sgn_idemp])

/--
An integer is greater than zero iff its sign is greater than zero.

**Property and proof intuition**: Integers greater than zero have sign value
`1`; this is the only sign value that's greater than zero.
-/
theorem sgn_preserves_gt_zero {a : ℤ} : a > 0 ↔ sgn a > 0 := calc
  _ ↔ a > 0     := Iff.rfl
  _ ↔ sgn a ≃ 1 := gt_zero_sgn
  _ ↔ sgn a > 0 := sgn_gt_zero_iff_pos.symm

/--
An integer is greater than or equivalent to zero iff its sign is greater than
or equivalent to zero.

**Property intuition**: Integers greater than or equivalent to zero have sign
values of `1` and `0`, which are the only ones that are also greater than or
equivalent to zero.

**Proof intuition**: Split the _greater than or equivalent to_ relation into
_greater than_ or _equivalent to_. The theorem `sgn_preserves_gt_zero` covers
the _greater than_ relation, while `sgn_zero` covers _equivalent to_.
-/
theorem sgn_preserves_ge_zero {a : ℤ} : a ≥ 0 ↔ sgn a ≥ 0 := calc
  _ ↔ a ≥ 0                 := Iff.rfl
  _ ↔ a > 0 ∨ a ≃ 0         := ge_split
  _ ↔ sgn a > 0 ∨ a ≃ 0     := iff_subst_covar or_mapL sgn_preserves_gt_zero
  _ ↔ sgn a > 0 ∨ sgn a ≃ 0 := iff_subst_covar or_mapR sgn_zero.symm
  _ ↔ sgn a ≥ 0             := ge_split.symm

/--
Expresses _greater than or equivalent to_ in terms of the sign value of a
difference being nonnegative.

This is a useful lemma because it enables adding or removing usage of `sgn`
while staying in the context of the _greater than or equivalent to_ relation.

**Property intuition**: If `a ≥ b`, then their difference is `≥ 0`, and so is
the sign value of that difference.

**Proof intuition**: By previous lemmas for `sgn`.
-/
theorem sgn_diff_ge_zero {a b : ℤ} : a ≥ b ↔ sgn (a - b) ≥ 0 := calc
  _ ↔ a ≥ b            := Iff.rfl
  _ ↔ sgn (a - b) ≄ -1 := ge_sgn
  _ ↔ sgn (a - b) ≥ 0  := sgn_ge_zero_iff_nonneg.symm

/--
The less-than relation is transitive.

**Property intuition**: This is a fundamental property of total ordering
relations: all elements of the ordered type are covered by the relation, and
orderings of nearby elements can be chained to give orderings of distant
elements.

**Proof intuition**: Expanding the definition of less-than into a property of
integer subtraction being positive, the result follows from adding the two
smaller properties and using algebra to show that it produces the conclusion.
-/
theorem trans_lt_lt_lt {a b c : ℤ} : a < b → b < c → a < c := by
  intro (_ : a < b) (_ : b < c)
  show a < c
  have : Positive (b - a) := gt_iff_pos_diff.mp ‹a < b›
  have : Positive (c - b) := gt_iff_pos_diff.mp ‹b < c›
  apply gt_iff_pos_diff.mpr
  show Positive (c - a)
  have : Positive ((c - b) + (b - a)) :=
    add_preserves_positive ‹Positive (c - b)› ‹Positive (b - a)›
  have : (c - b) + (b - a) ≃ c - a := add_sub_telescope
  have : Positive (c - a) :=
    by prw [‹(c - b) + (b - a) ≃ c - a›] ‹Positive ((c - b) + (b - a))›
  exact this

/-- Enable `trans_lt_lt_lt` use by `calc` tactics. -/
instance trans_lt_lt_lt_inst : Relation.Transitive (α := ℤ) (· < ·) := {
  trans := trans_lt_lt_lt
}

/--
Transitivity of _less than_ with _less than or equivalent to_ on the left.

**Property and proof intuition**: Split _less than or equivalent to_ into
_less than_ or _equivalent to_. Transitivity holds for both of those simpler
relations, so it holds for this one as well.
-/
theorem trans_le_lt_lt {a b c : ℤ} : a ≤ b → b < c → a < c := by
  intro (_ : a ≤ b) (_ : b < c)
  show a < c
  have : a < b ∨ a ≃ b := le_split.mp ‹a ≤ b›
  match ‹a < b ∨ a ≃ b› with
  | Or.inl (_ : a < b) =>
    have : a < c := trans_lt_lt_lt ‹a < b› ‹b < c›
    exact this
  | Or.inr (_ : a ≃ b) =>
    have : a < c := trans_eqv_lt_lt ‹a ≃ b› ‹b < c›
    exact this

/-- Enable `trans_le_lt_lt` use by `calc` tactics. -/
instance trans_le_lt_lt_inst : Trans (α := ℤ) (· ≤ ·) (· < ·) (· < ·) := {
  trans := trans_le_lt_lt
}

/--
Transitivity of _less than_ with _less than or equivalent to_ on the right.

**Property and proof intuition**: Split _less than or equivalent to_ into
_less than_ or _equivalent to_. Transitivity holds for both of those simpler
relations, so it holds for this one as well.
-/
theorem trans_lt_le_lt {a b c : ℤ} : a < b → b ≤ c → a < c := by
  intro (_ : a < b) (_ : b ≤ c)
  show a < c
  have : b < c ∨ b ≃ c := le_split.mp ‹b ≤ c›
  match ‹b < c ∨ b ≃ c› with
  | Or.inl (_ : b < c) =>
    have : a < c := trans_lt_lt_lt ‹a < b› ‹b < c›
    exact this
  | Or.inr (_ : b ≃ c) =>
    have : a < c := trans_lt_eqv_lt ‹a < b› ‹b ≃ c›
    exact this

/-- Enable `trans_lt_le_lt` use by `calc` tactics. -/
instance trans_lt_le_lt_inst : Trans (α := ℤ) (· < ·) (· ≤ ·) (· < ·) := {
  trans := trans_lt_le_lt
}

/--
Transitivity of _less than or equivalent to_.

**Property and proof intuition**: Split each input relation into its
_less than_ case and its equivalence case. Delegate to a previous transitivity
result for each combination of cases. Note that this turns out to be easier
than expanding the relation into its `sgn`-based definition, because that
involves a `· ≄ ·` operation which is more difficult to deal with.
-/
theorem trans_le_le_le {a b c : ℤ} : a ≤ b → b ≤ c → a ≤ c := by
  intro (_ : a ≤ b) (_ : b ≤ c)
  show a ≤ c
  have : a < b ∨ a ≃ b := le_split.mp ‹a ≤ b›
  have : b < c ∨ b ≃ c := le_split.mp ‹b ≤ c›
  match And.intro ‹a < b ∨ a ≃ b› ‹b < c ∨ b ≃ c› with
  | (And.intro (Or.inl (_ : a < b)) (Or.inl (_ : b < c))) =>
    have : a < c := trans_lt_lt_lt ‹a < b› ‹b < c›
    have : a ≤ c := le_split.mpr (Or.inl ‹a < c›)
    exact this
  | (And.intro (Or.inl (_ : a < b)) (Or.inr (_ : b ≃ c))) =>
    have : a < c := trans_lt_eqv_lt ‹a < b› ‹b ≃ c›
    have : a ≤ c := le_split.mpr (Or.inl ‹a < c›)
    exact this
  | (And.intro (Or.inr (_ : a ≃ b)) (Or.inl (_ : b < c))) =>
    have : a < c := trans_eqv_lt_lt ‹a ≃ b› ‹b < c›
    have : a ≤ c := le_split.mpr (Or.inl ‹a < c›)
    exact this
  | (And.intro (Or.inr (_ : a ≃ b)) (Or.inr (_ : b ≃ c))) =>
    have : a ≃ c := Rel.trans ‹a ≃ b› ‹b ≃ c›
    have : a ≤ c := le_split.mpr (Or.inr ‹a ≃ c›)
    exact this

/-- Enable `trans_le_le_le` use by `calc` tactics. -/
instance trans_le_le_le_inst : Trans (α := ℤ) (· ≤ ·) (· ≤ ·) (· ≤ ·) := {
  trans := trans_le_le_le
}

/--
Transitivity of _less than or equivalent to_ with equivalence on the left.

**Property and proof intuition**: Convert equivalence to _less than or
equivalent to_; follows from transitivity of that relation.
-/
theorem trans_eqv_le_le {a b c : ℤ} : a ≃ b → b ≤ c → a ≤ c := by
  intro (_ : a ≃ b) (_ : b ≤ c)
  show a ≤ c
  have : a ≤ b := le_split.mpr (Or.inr ‹a ≃ b›)
  have : a ≤ c := trans_le_le_le ‹a ≤ b› ‹b ≤ c›
  exact this

/-- Enable `trans_eqv_le_le` use by `calc` tactics. -/
instance trans_eqv_le_le_inst : Trans (α := ℤ) (· ≃ ·) (· ≤ ·) (· ≤ ·) := {
  trans := trans_eqv_le_le
}

/--
Transitivity of _less than or equivalent to_ with equivalence on the right.

**Property and proof intuition**: Convert equivalence to _less than or
equivalent to_; follows from transitivity of that relation.
-/
theorem trans_le_eqv_le {a b c : ℤ} : a ≤ b → b ≃ c → a ≤ c := by
  intro (_ : a ≤ b) (_ : b ≃ c)
  show a ≤ c
  have : b ≤ c := le_split.mpr (Or.inr ‹b ≃ c›)
  have : a ≤ c := trans_le_le_le ‹a ≤ b› ‹b ≤ c›
  exact this

/-- Enable `trans_le_eqv_le` use by `calc` tactics. -/
instance trans_le_eqv_le_inst : Trans (α := ℤ) (· ≤ ·) (· ≃ ·) (· ≤ ·) := {
  trans := trans_le_eqv_le
}

/--
Transitivity of the _greater than_ relation.

**Property and proof intuition**: Follows from _less than_ transitivity.
-/
theorem trans_gt_gt_gt {a b c : ℤ} : a > b → b > c → a > c := by
  intro (_ : a > b) (_ : b > c)
  show a > c
  have : c < a := trans_lt_lt_lt ‹c < b› ‹b < a›
  exact this

/-- Enable `trans_gt_gt_gt` use by `calc` tactics. -/
instance trans_gt_gt_gt_inst : Trans (α := ℤ) (· > ·) (· > ·) (· > ·) := {
  trans := trans_gt_gt_gt
}

/--
Transitivity of _greater than_ with _greater than or equivalent to_ on the
left.

**Property and proof intuition**: Follows from transitivity of _less than_ and
_less than or equivalent to_.
-/
theorem trans_ge_gt_gt {a b c : ℤ} : a ≥ b → b > c → a > c := by
  intro (_ : a ≥ b) (_ : b > c)
  show a > c
  have : c < a := trans_lt_le_lt ‹c < b› ‹b ≤ a›
  exact this

/-- Enable `trans_ge_gt_gt` use by `calc` tactics. -/
instance trans_ge_gt_gt_inst : Trans (α := ℤ) (· ≥ ·) (· > ·) (· > ·) := {
  trans := trans_ge_gt_gt
}

/--
Transitivity of _greater than_ with _greater than or equivalent to_ on the
right.

**Property and proof intuition**: Follows from transitivity of _less than_ and
_less than or equivalent to_.
-/
theorem trans_gt_ge_gt {a b c : ℤ} : a > b → b ≥ c → a > c := by
  intro (_ : a > b) (_ : b ≥ c)
  show a > c
  have : c < a := trans_le_lt_lt ‹c ≤ b› ‹b < a›
  exact this

/-- Enable `trans_gt_ge_gt` use by `calc` tactics. -/
instance trans_gt_ge_gt_inst : Trans (α := ℤ) (· > ·) (· ≥ ·) (· > ·) := {
  trans := trans_gt_ge_gt
}

/--
Transitivity of _greater than or equivalent to_.

**Property and proof intuition**: Follows from transitivity of _less than or
equivalent to_.
-/
theorem trans_ge_ge_ge {a b c : ℤ} : a ≥ b → b ≥ c → a ≥ c := by
  intro (_ : a ≥ b) (_ : b ≥ c)
  show a ≥ c
  have : c ≤ a := trans_le_le_le ‹c ≤ b› ‹b ≤ a›
  exact this

/-- Enable `trans_ge_ge_ge` use by `calc` tactics. -/
instance trans_ge_ge_ge_inst : Trans (α := ℤ) (· ≥ ·) (· ≥ ·) (· ≥ ·) := {
  trans := trans_ge_ge_ge
}

/--
Transitivity of _greater than or equivalent to_ with equivalence on the left.

**Property and proof intuition**: Follows from transitivity of _less than or
equivalent to_ with equivalence.
-/
theorem trans_eqv_ge_ge {a b c : ℤ} : a ≃ b → b ≥ c → a ≥ c := by
  intro (_ : a ≃ b) (_ : b ≥ c)
  show a ≥ c
  have : c ≤ a := trans_le_eqv_le ‹c ≤ b› (Rel.symm ‹a ≃ b›)
  exact this

/-- Enable `trans_eqv_ge_ge` use by `calc` tactics. -/
instance trans_eqv_ge_ge_inst : Trans (α := ℤ) (· ≃ ·) (· ≥ ·) (· ≥ ·) := {
  trans := trans_eqv_ge_ge
}

/--
Transitivity of _greater than or equivalent to_ with equivalence on the right.

**Property and proof intuition**: Follows from transitivity of _less than or
equivalent to_ with equivalence.
-/
theorem trans_ge_eqv_ge {a b c : ℤ} : a ≥ b → b ≃ c → a ≥ c := by
  intro (_ : a ≥ b) (_ : b ≃ c)
  show a ≥ c
  have : c ≤ a := trans_eqv_le_le (Rel.symm ‹b ≃ c›) ‹b ≤ a›
  exact this

/-- Enable `trans_ge_eqv_ge` use by `calc` tactics. -/
instance trans_ge_eqv_ge_inst : Trans (α := ℤ) (· ≥ ·) (· ≃ ·) (· ≥ ·) := {
  trans := trans_ge_eqv_ge
}

/--
An integer is _greater than or equivalent to_ another iff the larger minus the
smaller is nonnegative.

**Proof intuition**: Converts through an intermediate expression involving
`sgn`. It's more obscure than a proof via substitution of subtraction on both
sides of the relation, but that's because it uses more primitive theorems.
-/
theorem ge_iff_diff_nonneg {a b : ℤ} : a ≥ b ↔ a - b ≥ 0 := calc
  _ ↔ a ≥ b           := Iff.rfl
  _ ↔ sgn (a - b) ≥ 0 := sgn_diff_ge_zero
  _ ↔ a - b ≥ 0       := sgn_preserves_ge_zero.symm

/--
A common term can be added to or removed from the right-hand side of both
operands of _greater than or equivalent to_.

**Property intuition**: Adjusting two values by the same amount doesn't affect
their relative ordering.

**Proof intuition**: Move both operands to the same side of the relation, then
use algebra.
-/
theorem ge_addR {a₁ a₂ b : ℤ} : a₁ ≥ a₂ ↔ a₁ + b ≥ a₂ + b := by
  have expand_sub : a₁ - a₂ ≃ (a₁ + b) - (a₂ + b) := Rel.symm sub_sums_sameR
  calc
    _ ↔ a₁ ≥ a₂                 := Iff.rfl
    _ ↔ a₁ - a₂ ≥ 0             := ge_iff_diff_nonneg
    _ ↔ (a₁ + b) - (a₂ + b) ≥ 0 := Rel.iff_subst_eqv le_substR_eqv expand_sub
    _ ↔ a₁ + b ≥ a₂ + b         := ge_iff_diff_nonneg.symm

/-- Immediate corollary of `ge_addR`, just to help `gcongr`. -/
@[gcongr]
theorem ge_addR_mp {a₁ a₂ b : ℤ} : a₁ ≥ a₂ → a₁ + b ≥ a₂ + b := ge_addR.mp

/--
A common term can be added to or removed from the left-hand side of both
operands of _greater than or equivalent to_.

**Property intuition**: Adjusting two values by the same amount doesn't affect
their relative ordering.

**Proof intuition**: Use the right-hand version of this theorem, then use
commutativity to swap the operands to addition.
-/
theorem ge_addL {a₁ a₂ b : ℤ} : a₁ ≥ a₂ ↔ b + a₁ ≥ b + a₂ := calc
  _ ↔ a₁ ≥ a₂         := Iff.rfl
  _ ↔ a₁ + b ≥ a₂ + b := ge_addR
  _ ↔ b + a₁ ≥ a₂ + b := Rel.iff_subst_eqv le_substR_eqv AA.comm
  _ ↔ b + a₁ ≥ b + a₂ := Rel.iff_subst_eqv le_substL_eqv AA.comm

/-- Immediate corollary of `ge_addL`, just to help `gcongr`. -/
@[gcongr]
theorem ge_addL_mp {a₁ a₂ b : ℤ} : a₁ ≥ a₂ → b + a₁ ≥ b + a₂ := ge_addL.mp

/--
Any pair of integers can only be in one of three relations: _less than_,
_greater than_, or _equivalence_.

**Property intuition**: We expect this to be true because we know the integers
are totally ordered.

**Proof intuition**: Convert into sign trichotomy on `a - b`.
-/
theorem order_trichotomy
    (a b : ℤ) : AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
    := by
  have abTri
    : AA.ExactlyOneOfThree (a - b ≃ 0) (Positive (a - b)) (Negative (a - b))
    := Signed.trichotomy (a - b)
  apply AA.ExactlyOneOfThree.mk
  case atLeastOne =>
    show AA.OneOfThree (a < b) (a ≃ b) (a > b)
    match abTri.atLeastOne with
    | AA.OneOfThree.first (_ : a - b ≃ 0) =>
      have : a ≃ b := zero_diff_iff_eqv.mp ‹a - b ≃ 0›
      exact AA.OneOfThree.second ‹a ≃ b›
    | AA.OneOfThree.second (_ : Positive (a - b)) =>
      have : a > b := gt_iff_pos_diff.mpr ‹Positive (a - b)›
      exact AA.OneOfThree.third ‹a > b›
    | AA.OneOfThree.third (_ : Negative (a - b)) =>
      have : a < b := lt_iff_neg_diff.mpr ‹Negative (a - b)›
      exact AA.OneOfThree.first ‹a < b›
  case atMostOne =>
    intro (_ : AA.TwoOfThree (a < b) (a ≃ b) (a > b))
    show False
    let ab := a - b
    have abTwo : AA.TwoOfThree (ab ≃ 0) (Positive ab) (Negative ab) :=
      match ‹AA.TwoOfThree (a < b) (a ≃ b) (a > b)› with
      | AA.TwoOfThree.oneAndTwo (_ : a < b) (_ : a ≃ b) =>
        have : Negative ab := lt_iff_neg_diff.mp ‹a < b›
        have : ab ≃ 0 := zero_diff_iff_eqv.mpr ‹a ≃ b›
        AA.TwoOfThree.oneAndThree ‹ab ≃ 0› ‹Negative ab›
      | AA.TwoOfThree.oneAndThree (_ : a < b) (_ : a > b) =>
        have : Negative ab := lt_iff_neg_diff.mp ‹a < b›
        have : Positive ab := gt_iff_pos_diff.mp ‹a > b›
        AA.TwoOfThree.twoAndThree ‹Positive ab› ‹Negative ab›
      | AA.TwoOfThree.twoAndThree (_ : a ≃ b) (_ : a > b) =>
        have : ab ≃ 0 := zero_diff_iff_eqv.mpr ‹a ≃ b›
        have : Positive ab := gt_iff_pos_diff.mp ‹a > b›
        AA.TwoOfThree.oneAndTwo ‹ab ≃ 0› ‹Positive ab›
    have abNotTwo
      : ¬ AA.TwoOfThree (ab ≃ 0) (Positive ab) (Negative ab)
      := abTri.atMostOne
    exact absurd abTwo abNotTwo

/--
Two integers are either in a _less than or equivalent to_ relation, or a
_greater than_ relation.
-/
theorem le_or_gt {a b : ℤ} : a ≤ b ∨ a > b := by
  have : AA.OneOfThree (a < b) (a ≃ b) (a > b) :=
    (order_trichotomy a b).atLeastOne
  match ‹AA.OneOfThree (a < b) (a ≃ b) (a > b)› with
  | AA.OneOfThree.first (_ : a < b) =>
    have : a ≤ b := le_split.mpr (Or.inl ‹a < b›)
    exact Or.inl ‹a ≤ b›
  | AA.OneOfThree.second (_ : a ≃ b) =>
    have : a ≤ b := le_split.mpr (Or.inr ‹a ≃ b›)
    exact Or.inl ‹a ≤ b›
  | AA.OneOfThree.third (_ : a > b) =>
    exact Or.inr ‹a > b›

/--
Two integers are either in a _less than_ relation, or a
_greater than or equivalent to_ relation.
-/
theorem lt_or_ge {a b : ℤ} : a < b ∨ a ≥ b := le_or_gt.symm

/--
The _less than or equivalent to_ relation is reversed with negated operands.

**Property and proof intuition**: Equivalence is symmetric and preserved by
negation, so the order-reversal comes solely from the _less than_ component of
the relation. And that is already known via `lt_neg_flip`.
-/
theorem le_neg_flip {a b : ℤ} : a ≤ b ↔ -b ≤ -a := by
  apply Iff.intro
  case mp =>
    intro (_ : a ≤ b)
    show -b ≤ -a
    have : a < b ∨ a ≃ b := le_split.mp ‹a ≤ b›
    match this with
    | Or.inl (_ : a < b) =>
      have : -b < -a := lt_neg_flip.mp ‹a < b›
      have : -b ≤ -a := le_split.mpr (Or.inl this)
      exact this
    | Or.inr (_ : a ≃ b) =>
      have : -b ≃ -a := by srw [←‹a ≃ b›]
      have : -b ≤ -a := le_split.mpr (Or.inr this)
      exact this
  case mpr =>
    intro (_ : -b ≤ -a)
    show a ≤ b
    have : -b < -a ∨ -b ≃ -a := le_split.mp ‹-b ≤ -a›
    match this with
    | Or.inl (_ : -b < -a) =>
      have : a < b := lt_neg_flip.mpr ‹-b < -a›
      have : a ≤ b := le_split.mpr (Or.inl this)
      exact this
    | Or.inr (_ : -b ≃ -a) =>
      have : a ≃ b := AA.inject (Rel.symm ‹-b ≃ -a›)
      have : a ≤ b := le_split.mpr (Or.inr this)
      exact this

/--
Negation swaps the arguments to _less than or equivalent to_.

Corollary of `le_neg_flip` for use with `gcongr`.
-/
@[gcongr]
theorem le_neg_subst {a b : ℤ} : a ≤ b → -b ≤ -a := le_neg_flip.mp

/--
Two integers cannot be both _less than or equivalent to_ and _greater than_
each other.

**Property and proof intuition**: A direct consequence of trichotomy.
-/
theorem le_gt_false {a b : ℤ} : a ≤ b → a > b → False := by
  intro (_ : a ≤ b) (_ : a > b)
  show False
  have : a < b ∨ a ≃ b := le_split.mp ‹a ≤ b›
  have notTwo : ¬AA.TwoOfThree (a < b) (a ≃ b) (a > b) :=
    (order_trichotomy a b).atMostOne
  have two : AA.TwoOfThree (a < b) (a ≃ b) (a > b) :=
    match ‹a < b ∨ a ≃ b› with
    | Or.inl (_ : a < b) => AA.TwoOfThree.oneAndThree ‹a < b› ‹a > b›
    | Or.inr (_ : a ≃ b) => AA.TwoOfThree.twoAndThree ‹a ≃ b› ‹a > b›
  exact absurd two notTwo

/--
Two integers cannot be both _less than_ and _greater than or equivalent to_
each other.

**Property and proof intuition**: A direct consequence of trichotomy, via
`le_gt_false`.
-/
theorem lt_ge_false {a b : ℤ} : a < b → a ≥ b → False := by
  intro (_ : b > a) (_ : b ≤ a)
  show False
  exact le_gt_false ‹b ≤ a› ‹b > a›

/-- _Less than_ is logically opposite _greater than or equivalent to_. -/
theorem not_ge_iff_lt {a b : ℤ} : ¬(a ≥ b) ↔ a < b := by
  apply Iff.intro
  case mp =>
    show ¬(a ≥ b) → a < b
    exact lt_or_ge.resolve_right
  case mpr =>
    show a < b → ¬(a ≥ b)
    show a < b → a ≥ b → False
    exact lt_ge_false

/--
Incrementing an integer always increases it.

**Proof intuition**: For the _less than_ relation to hold, the difference of
the operands, `a - (a + 1)`, must be negative. Algebra shows that it's
equivalent to `-1`, so the proof follows.
-/
theorem lt_inc {a : ℤ} : a < a + 1 := by
  apply lt_iff_neg_diff.mpr
  show Negative (a - (a + 1))
  have : a - (a + 1) ≃ -1 := calc
    a - (a + 1)   ≃ _ := sub_defn
    a + -(a + 1)  ≃ _ := by srw [neg_compat_add]
    a + (-a + -1) ≃ _ := Rel.symm AA.assoc
    (a + -a) + -1 ≃ _ := by srw [neg_invR]
    (0 : ℤ) + -1  ≃ _ := AA.identL
    (-1)          ≃ _ := Rel.refl
  prw [←‹a - (a + 1) ≃ -1›] neg_one_negative

/--
Zero is less than one (in the integers).

**Property and proof definition**: A direct consequence of `lt_inc`.
-/
theorem zero_lt_one : (0:ℤ) < 1 := by
  have : (0:ℤ) < 0 + 1 := lt_inc
  prw [add_identL] ‹(0:ℤ) < 0 + 1›

/-- The integer one is greater than or equivalent to zero. -/
theorem one_ge_zero : (1:ℤ) ≥ 0 := ge_split.mpr (.inl zero_lt_one)

/--
Negative one is less than zero (in the integers).

**Property and proof definition**: A direct consequence of `lt_inc`.
-/
theorem neg_one_lt_zero : (-1:ℤ) < 0 := by
  have : (-1:ℤ) < -1 + 1 := lt_inc
  prw [neg_invL] ‹(-1:ℤ) < -1 + 1›

/-- The integer two is greater than zero. -/
theorem two_gt_zero : (2:ℤ) > 0 :=
  have : (1:ℤ) > 0 := zero_lt_one
  show (2:ℤ) > 0 from Trans.trans two_gt_one ‹(1:ℤ) > 0›

/-- The integer two is greater than or equivalent to zero. -/
theorem two_ge_zero : (2:ℤ) ≥ 0 := ge_split.mpr (.inl two_gt_zero)

/--
Convert between _less than_ and _less than or equivalent to_ by incrementing or
decrementing the left operand.
-/
theorem lt_iff_le_incL {a b : ℤ} : a < b ↔ a + 1 ≤ b := by
  apply Iff.intro
  case mp =>
    intro (_ : a < b)
    show a + 1 ≤ b
    have (And.intro (_ : a ≤ b) (_ : a ≄ b)) := lt_iff_le_neqv.mp ‹a < b›
    have (Exists.intro (n : ℕ) (_ : b ≃ a + n)) := le_iff_add_nat.mp ‹a ≤ b›
    have : n ≃ 0 ∨ ∃ (m : ℕ), n ≃ step m := Natural.split_cases n
    match ‹n ≃ 0 ∨ ∃ (m : ℕ), n ≃ step m› with
    | Or.inl (_ : n ≃ 0) =>
      have : a ≃ b := Rel.symm $ calc
        _ = b         := rfl
        _ ≃ a + n     := ‹b ≃ a + n›
        _ ≃ a + (0:ℕ) := by srw [‹n ≃ 0›]
        _ ≃ a         := AA.identR
      exact absurd ‹a ≃ b› ‹a ≄ b›
    | Or.inr (Exists.intro (m : ℕ) (_ : n ≃ step m)) =>
      have : step m ≃ m + 1 := Rel.symm Natural.add_one_step
      have : b ≃ (a + 1) + m := calc
        _ = b               := rfl
        _ ≃ a + n           := ‹b ≃ a + n›
        _ ≃ a + (m + 1 : ℕ) := by srw [‹n ≃ step m›, ‹step m ≃ m + 1›]
        _ ≃ a + (m + (1:ℕ)) := by srw [AA.compat₂]
        _ ≃ a + ((1:ℕ) + m) := by srw [AA.comm]
        _ ≃ (a + 1) + m     := Rel.symm AA.assoc
      have : ∃ (m : ℕ), b ≃ (a + 1) + m := Exists.intro m ‹b ≃ (a + 1) + m›
      have : a + 1 ≤ b := le_iff_add_nat.mpr ‹∃ (m : ℕ), b ≃ (a + 1) + m›
      exact this
  case mpr =>
    intro (_ : a + 1 ≤ b)
    show a < b
    calc
      _ = a     := rfl
      _ < a + 1 := lt_inc
      _ ≤ b     := ‹a + 1 ≤ b›

/--
Convert between _less than or equivalent to_ and _less than_ by incrementing or
decrementing the right operand.
-/
theorem le_iff_lt_incR {a b : ℤ} : a ≤ b ↔ a < b + 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : a ≤ b)
    show a < b + 1
    calc
      _ = a     := rfl
      _ ≤ b     := ‹a ≤ b›
      _ < b + 1 := lt_inc
  case mpr =>
    intro (_ : a < b + 1)
    show a ≤ b
    have : a + 1 ≤ b + 1 := lt_iff_le_incL.mp ‹a < b + 1›
    have : a ≤ b := ge_addR.mpr ‹a + 1 ≤ b + 1›
    exact this

/--
Equivalent expressions of positive integers, using _less than_ and _less than
or equivalent to_.
-/
theorem pos_gt_iff_ge {a : ℤ} : a > 0 ↔ a ≥ 1 := calc
  _ ↔ a > 0     := Iff.rfl
  _ ↔ a ≥ 0 + 1 := lt_iff_le_incL
  _ ↔ a ≥ 1     := Rel.iff_subst_eqv le_substL_eqv AA.identL

/--
Every nonnegative integer is equivalent to a natural number.

**Proof intuition**: Split the nonnegative condition into positive and zero
cases. The zero case is trivial; the positive case follows from the theorem
`positive_elim_nat`.
-/
theorem ge_zero_eqv_nat {a : ℤ} : a ≥ 0 → ∃ (n : ℕ), a ≃ (n:ℤ) := by
  intro (_ : a ≥ 0)
  show ∃ (n : ℕ), a ≃ (n:ℤ)
  have : a > 0 ∨ a ≃ 0 := ge_split.mp ‹a ≥ 0›
  match ‹a > 0 ∨ a ≃ 0› with
  | Or.inl (_ : a > 0) =>
    have : Positive a := gt_zero_iff_pos.mp ‹a > 0›
    have Exists.intro (n : ℕ) (And.intro (_ : Positive n) (_ : a ≃ (n:ℤ))) :=
      positive_elim_nat ‹Positive a›
    exact Exists.intro n ‹a ≃ (n:ℤ)›
  | Or.inr (_ : a ≃ 0) =>
    exact Exists.intro 0 ‹a ≃ 0›

/--
The sum of two nonnegative integers is zero iff they are both zero as well.

**Property and proof intuition**: There is an identical result for natural
numbers, and nonnegative integers are equivalent to natural numbers.
-/
theorem zero_sum_split
    {a b : ℤ} : a ≥ 0 → b ≥ 0 → (a + b ≃ 0 ↔ a ≃ 0 ∧ b ≃ 0)
    := by
  intro (_ : a ≥ 0) (_ : b ≥ 0)
  have (Exists.intro (n : ℕ) (_ : a ≃ (n:ℤ))) := ge_zero_eqv_nat ‹a ≥ 0›
  have (Exists.intro (m : ℕ) (_ : b ≃ (m:ℤ))) := ge_zero_eqv_nat ‹b ≥ 0›
  have from_natural_eqv {k j : ℕ} : k ≃ j ↔ (k:ℤ) ≃ (j:ℤ) :=
    Iff.intro AA.subst₁ AA.inject
  have nat_int_eqvL {k j : ℕ} {c : ℤ} : c ≃ (k:ℤ) → (k ≃ j ↔ c ≃ (j:ℤ)) := by
    intro (_ : c ≃ (k:ℤ))
    show k ≃ j ↔ c ≃ (j:ℤ)
    calc
      _ ↔ k ≃ j         := Iff.rfl
      _ ↔ (k:ℤ) ≃ (j:ℤ) := from_natural_eqv
      _ ↔ c ≃ (j:ℤ)     := by srw [←‹c ≃ (k:ℤ)›]
  have : n ≃ 0 ↔ a ≃ 0 := nat_int_eqvL ‹a ≃ (n:ℤ)›
  have : m ≃ 0 ↔ b ≃ 0 := nat_int_eqvL ‹b ≃ (m:ℤ)›
  calc
    _ ↔ a + b ≃ 0                   := Iff.rfl
    _ ↔ (n:ℤ) + (m:ℤ) ≃ 0           := by srw [‹a ≃ (n:ℤ)›, ‹b ≃ (m:ℤ)›]
    _ ↔ ((n + m : ℕ):ℤ) ≃ ((0:ℕ):ℤ) := by srw [←AA.compat₂]
    _ ↔ n + m ≃ 0                   := from_natural_eqv.symm
    _ ↔ n ≃ 0 ∧ m ≃ 0               := Natural.zero_sum_split
    _ ↔ a ≃ 0 ∧ m ≃ 0               := iff_subst_covar and_mapL ‹n ≃ 0 ↔ a ≃ 0›
    _ ↔ a ≃ 0 ∧ b ≃ 0               := iff_subst_covar and_mapR ‹m ≃ 0 ↔ b ≃ 0›

/--
The product of two integers is positive iff their product is nonzero and they
have the same sign.

**Property intuition**: The product cannot be negative, because the product of
like signs is always positive.

**Proof intuition**: In the forward direction, use `mul_sqrt1_eqv` to show the
signs are equivalent. Assume the product is zero and reach a contradiction with
`a * b > 0`. In the reverse direction, use the assumption that the integers'
signs are equivalent, along with `nonneg_square`, to show that their product is
nonnegative. Use the assumption that the product is nonzero to conclude it's
strictly positive.
-/
theorem mul_gt_zero_iff_sgn_same
    {a b : ℤ} : a * b > 0 ↔ sgn a ≃ sgn b ∧ a * b ≄ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : a * b > 0)
    show sgn a ≃ sgn b ∧ a * b ≄ 0
    have : sgn a * sgn b ≃ 1 := calc
      _ = sgn a * sgn b := rfl
      _ ≃ sgn (a * b)   := Rel.symm sgn_compat_mul
      _ ≃ 1             := gt_zero_sgn.mp ‹a * b > 0›
    have (And.intro _ (_ : sgn a ≃ sgn b)) :=
      mul_sqrt1_eqv.mp ‹sgn a * sgn b ≃ 1›
    have : a * b ≄ 0 := by
      intro (_ : a * b ≃ 0)
      show False
      have : a * b ≤ 0 := le_split.mpr (Or.inr ‹a * b ≃ 0›)
      exact le_gt_false ‹a * b ≤ 0› ‹a * b > 0›
    exact And.intro ‹sgn a ≃ sgn b› ‹a * b ≄ 0›
  case mpr =>
    intro (And.intro (_ : sgn a ≃ sgn b) (_ : a * b ≄ 0))
    show a * b > 0
    have : sgn (a * b) ≥ 0 := calc
      _ = sgn (a * b)   := rfl
      _ ≃ sgn a * sgn b := sgn_compat_mul
      _ ≃ sgn b * sgn b := by srw [‹sgn a ≃ sgn b›]
      _ ≥ 0             := ge_zero_sgn.mpr nonneg_square
    have : a * b ≥ 0 := sgn_preserves_ge_zero.mpr ‹sgn (a * b) ≥ 0›
    have : 0 ≄ a * b := Rel.symm ‹a * b ≄ 0›
    have : a * b > 0 := lt_iff_le_neqv.mpr (And.intro ‹a * b ≥ 0› ‹0 ≄ a * b›)
    exact this

/--
The _greater than or equivalent to_ relation between two integers is preserved
when both are multiplied by a nonnegative integer on the right.

**Property intuition**: Multiplication scales the integers by the same amount,
so their location relative to each other doesn't change.

**Proof intuition**: Convert the ordering relations into their `sgn`-based
equivalents. The goal becomes showing that `sgn (a₁ - a₂) * sgn b ≥ 0`. If `b`
is zero, this is trivially true; if `b` is positive then this follows by the
`a₁ ≥ a₂` assumption.
-/
@[gcongr]
theorem ge_mulR_nonneg {a₁ a₂ b : ℤ} : b ≥ 0 → a₁ ≥ a₂ → a₁ * b ≥ a₂ * b := by
  intro (_ : b ≥ 0) (_ : a₁ ≥ a₂)
  show a₁ * b ≥ a₂ * b
  have : b > 0 ∨ b ≃ 0 := ge_split.mp ‹b ≥ 0›
  have : sgn (a₁ - a₂) * sgn b ≥ 0 := match ‹b > 0 ∨ b ≃ 0› with
  | Or.inl (_ : b > 0) =>
    calc
      _ = sgn (a₁ - a₂) * sgn b := rfl
      _ ≃ sgn (a₁ - a₂) * 1     := by srw [gt_zero_sgn.mp ‹b > 0›]
      _ ≃ sgn (a₁ - a₂)         := AA.identR
      _ ≥ 0                     := sgn_diff_ge_zero.mp ‹a₁ ≥ a₂›
  | Or.inr (_ : b ≃ 0) =>
    calc
      _ = sgn (a₁ - a₂) * sgn b := rfl
      _ ≃ sgn (a₁ - a₂) * 0     := by srw [sgn_zero.mpr ‹b ≃ 0›]
      _ ≃ 0                     := AA.absorbR
      _ ≥ 0                     := le_refl
  have : sgn (a₁ * b - a₂ * b) ≥ 0 := calc
    _ = sgn (a₁ * b - a₂ * b) := rfl
    _ ≃ sgn ((a₁ - a₂) * b)   := by srw [←mul_distribR_sub]
    _ ≃ sgn (a₁ - a₂) * sgn b := sgn_compat_mul
    _ ≥ 0                     := ‹sgn (a₁ - a₂) * sgn b ≥ 0›
  have : a₁ * b ≥ a₂ * b := sgn_diff_ge_zero.mpr ‹sgn (a₁ * b - a₂ * b) ≥ 0›
  exact this

/--
The _less than or equivalent to_ relation between two integers is preserved
when both are multiplied by a nonnegative integer on the left.
-/
@[gcongr]
theorem le_mulL_nonneg {a₁ a₂ b : ℤ} : b ≥ 0 → a₁ ≤ a₂ → b * a₁ ≤ b * a₂ := by
  intro (_ : b ≥ 0) (_ : a₁ ≤ a₂)
  show b * a₁ ≤ b * a₂

  calc
    _ = b * a₁ := rfl
    _ ≃ a₁ * b := AA.comm
    _ ≤ a₂ * b := ge_mulR_nonneg ‹b ≥ 0› ‹a₁ ≤ a₂›
    _ ≃ b * a₂ := AA.comm

/--
The product of two nonnegative integers is also nonnegative.

**Property intuition**: The worst that can happen is one factor is zero, making
the product zero.

**Proof intuition**: Trivial corollary of `ge_mulR_nonneg`.
-/
theorem mul_preserves_nonneg {a b : ℤ} : a ≥ 0 → b ≥ 0 → a * b ≥ 0 := by
  intro (_ : a ≥ 0) (_ : b ≥ 0)
  show a * b ≥ 0
  calc
    _ = a * b := rfl
    _ ≥ 0 * b := by srw [‹a ≥ 0›]
    _ ≃ 0     := AA.absorbL

/-- Induction on integers greater than or equivalent to a starting value. -/
theorem ind_from
    {motive : ℤ → Prop}
    (motive_subst : {c₁ c₂ : ℤ} → c₁ ≃ c₂ → motive c₁ → motive c₂)
    {a b : ℤ} (a_ge_b : a ≥ b)
    (base : motive b) (next : {c : ℤ} → c ≥ b → motive c → motive (c + 1))
    : motive a
    := by
  /- Proof strategy: natural number induction -/

  -- Introduce induction variable
  have : a - b ≥ 0 := ge_iff_diff_nonneg.mp ‹a ≥ b›
  have (Exists.intro (n : ℕ) (_ : a - b ≃ n)) := ge_zero_eqv_nat ‹a - b ≥ 0›
  have : n + b ≃ a := Rel.symm (subR_moveR_addR.mp ‹a - b ≃ n›)

  -- Motive, base case, and successor case for the induction
  let motive' := λ (k : ℕ) => motive (k + b)
  have : motive (0 + b) := motive_subst (Rel.symm AA.identL) base
  have zero_case : motive' 0 := ‹motive (0 + b)›
  have step_case (m : ℕ) : motive' m → motive' (step m) := by
    intro (_ : motive' m)
    show motive' (step m)
    have : m + b ≥ b := calc
      _ = m + b     := rfl
      _ ≥ (0:ℕ) + b := by srw [Natural.ge_zero]
      _ ≃ b         := AA.identL
    have : (m + b) + 1 ≃ step m + b := calc
      _ = (m + b) + 1     := rfl
      _ ≃ m + (b + 1)     := add_assoc
      _ ≃ m + (1 + b)     := by srw [add_comm]
      _ ≃ (m + (1:ℕ)) + b := Rel.symm add_assoc
      _ ≃ step m + b      := by srw [←add_compat_nat, Natural.add_one_step]
    have : motive (m + b)       := ‹motive' m›
    have : motive ((m + b) + 1) := next ‹m + b ≥ b› this
    have : motive (step m + b)  := motive_subst ‹(m + b) + 1 ≃ step m + b› this
    have : motive' (step m)     := this
    exact this

  -- Perform the induction and convert the result into the expected form
  have : motive' n := Natural.ind zero_case step_case n
  have : motive (n + b) := ‹motive' n›
  have : motive a := motive_subst ‹n + b ≃ a› ‹motive (n + b)›
  exact this

/--
An integer sequence cannot decrease forever while staying above a fixed value.
-/
theorem bounded_inf_desc_impossible
    {s : Sequence ℤ} {b : ℤ} (bounded : (n : ℕ) → s[n] > b)
    : ¬(InfiniteDescent s)
    := by
  intro (_ : InfiniteDescent s)
  have desc_at (n : ℕ) : s[n] > s[step n] := ‹InfiniteDescent s› n
  show False

  have : s[0] > s[1] := calc
    _ = s[0]      := rfl
    _ > s[step 0] := desc_at 0
    _ ≃ s[1]      := by srw [←Natural.literal_step]

  have : s[0] ≤ s[1] :=
    let motive x := (n : ℕ) → s[n] ≥ x

    have motive_subst {x₁ x₂ : ℤ} : x₁ ≃ x₂ → motive x₁ → motive x₂ := by
      intro (_ : x₁ ≃ x₂) (m₁ : (n : ℕ) → s[n] ≥ x₁) (n : ℕ)
      show s[n] ≥ x₂

      calc
        _ = s[n] := rfl
        _ ≥ x₁ := m₁ n
        _ ≃ x₂ := ‹x₁ ≃ x₂›

    have lower_bound_at_index (a : ℤ) : a ≥ b → (n : ℕ) → s[n] ≥ a := by
      intro (_ : a ≥ b)
      show motive a

      apply ind_from motive_subst ‹a ≥ b›
      case base =>
        show motive b
        intro (n : ℕ)
        show s[n] ≥ b

        have : s[n] > b := bounded n
        have : s[n] ≥ b := ge_split.mpr (.inl ‹s[n] > b›)
        exact this
      case next =>
        intro (c : ℤ) (_ : c ≥ b) (ih : (n : ℕ) → s[n] ≥ c) (n : ℕ)
        show s[n] ≥ c + 1
        have : s[n] > c := calc
          _ = s[n]      := rfl
          _ > s[step n] := desc_at n
          _ ≥ c         := ih (step n)
        have : s[n] ≥ c + 1 := lt_iff_le_incL.mp ‹s[n] > c›
        exact this
    have : s[0] > b := bounded 0
    have : s[0] ≥ b := ge_split.mpr (.inl ‹s[0] > b›)
    show s[0] ≤ s[1] from lower_bound_at_index s[0] ‹s[0] ≥ b› 1

  have : False := le_gt_false ‹s[0] ≤ s[1]› ‹s[0] > s[1]›
  exact this

/--
Compute whether two integers are in a _greater than or equivalent to_ relation.
-/
def ge_decidable (a b : ℤ) : Decidable (a ≥ b) :=
  match show Decidable (sgn (a - b) ≃ -1) from eqv? (sgn (a - b)) (-1:ℤ) with
  | .isTrue (_ : sgn (a - b) ≃ -1) =>
    have : a < b := lt_sgn.mpr ‹sgn (a - b) ≃ -1›
    have : ¬(a ≥ b) := lt_ge_false ‹a < b›
    show Decidable (a ≥ b) from .isFalse ‹¬(a ≥ b)›
  | .isFalse (_ : sgn (a - b) ≄ -1) =>
    have : a ≥ b := ge_sgn.mpr ‹sgn (a - b) ≄ -1›
    show Decidable (a ≥ b) from .isTrue ‹a ≥ b›

/--
For two integers obeying the _greater than or equivalent to_ relation, compute
which more precise relation they obey: _greater than_ or _equivalent to_.
-/
def ge_split_either {a b : ℤ} : a ≥ b → Either (a > b) (a ≃ b) := by
  intro (_ : a ≥ b)
  show Either (a > b) (a ≃ b)
  match show Decidable (a ≃ b) from eqv? a b with
  | .isTrue (_ : a ≃ b) =>
    exact show Either (a > b) (a ≃ b) from .inr ‹a ≃ b›
  | .isFalse (_ : a ≄ b) =>
    have : a > b := lt_iff_le_neqv.mpr (And.intro ‹a ≥ b› (Rel.symm ‹a ≄ b›))
    exact show Either (a > b) (a ≃ b) from .inl ‹a > b›

/--
Compute whether an integer is _greater than or equivalent to_ another, or
_less than_ another.
-/
def either_ge_lt {a b : ℤ} : Either (a ≥ b) (a < b) :=
  have : Decidable (a ≥ b) := ge_decidable a b
  match this with
  | .isTrue (_ : a ≥ b) =>
    .inl ‹a ≥ b›
  | .isFalse (_ : ¬(a ≥ b)) =>
    have : a < b := not_ge_iff_lt.mp ‹¬(a ≥ b)›
    .inr ‹a < b›

/--
Compute whether an integer is _greater than_ another, or
_less than or equivalent to_ another.
-/
def either_gt_le {a b : ℤ} : Either (a > b) (a ≤ b) :=
  have : Either (a ≤ b) (a > b) := either_ge_lt
  this.swap

/-- Compute whether an integer or its negation is nonnegative. -/
def either_nonneg {a : ℤ} : Either (a ≥ 0) (-a ≥ 0) :=
  match show Decidable (a ≥ 0) from ge_decidable a 0 with
  | .isTrue (_ : a ≥ 0) =>
    show Either (a ≥ 0) (-a ≥ 0) from Either.inl ‹a ≥ 0›
  | .isFalse (_ : ¬(a ≥ 0)) =>
    have : a < 0 := match show a < 0 ∨ a ≥ 0 from lt_or_ge with
    | .inl (_ : a < 0) => ‹a < 0›
    | .inr (_ : a ≥ 0) => show a < 0 from absurd ‹a ≥ 0› ‹¬(a ≥ 0)›
    have : a ≤ 0 := le_split.mpr (Or.inl ‹a < 0›)
    have : -a ≥ 0 := calc
      _ = -a := rfl
      _ ≥ -0 := le_neg_flip.mp ‹a ≤ 0›
      _ ≃ 0  := Rel.symm (neg_zero.mp Rel.refl)
    show Either (a ≥ 0) (-a ≥ 0) from Either.inr ‹-a ≥ 0›

/--
Subtraction preserves _less than or equivalent to_ relations between its
left-hand arguments.
-/
@[gcongr]
theorem le_substL_sub {a₁ a₂ b : ℤ} : a₁ ≤ a₂ → a₁ - b ≤ a₂ - b := by
  intro (_ : a₁ ≤ a₂)
  show a₁ - b ≤ a₂ - b

  calc
    _ = a₁ - b  := rfl
    _ ≃ a₁ + -b := sub_defn
    _ ≤ a₂ + -b := by srw [‹a₁ ≤ a₂›]
    _ ≃ a₂ - b  := Rel.symm sub_defn

/--
Subtraction flips _less than or equivalent to_ relations between its right-hand
arguments.
-/
@[gcongr]
theorem le_substR_sub {a₁ a₂ b : ℤ} : a₁ ≤ a₂ → b - a₂ ≤ b - a₁ := by
  intro (_ : a₁ ≤ a₂)
  show b - a₂ ≤ b - a₁

  calc
    _ = b - a₂  := rfl
    _ ≃ b + -a₂ := sub_defn
    _ ≤ b + -a₁ := by srw [‹a₁ ≤ a₂›]
    _ ≃ b - a₁  := Rel.symm sub_defn

/--
Subtraction preserves _less than_ relations between its left-hand arguments.
-/
@[gcongr]
theorem lt_substL_sub {a₁ a₂ b : ℤ} : a₁ < a₂ → a₁ - b < a₂ - b := by
  intro (_ : a₁ < a₂)
  show a₁ - b < a₂ - b

  calc
    _ = a₁ - b  := rfl
    _ ≃ a₁ + -b := sub_defn
    _ < a₂ + -b := by srw [‹a₁ < a₂›]
    _ ≃ a₂ - b  := Rel.symm sub_defn

/--
Subtraction flips _less than_ relations between its right-hand arguments.
-/
@[gcongr]
theorem lt_substR_sub {a₁ a₂ b : ℤ} : a₁ < a₂ → b - a₂ < b - a₁ := by
  intro (_ : a₁ < a₂)
  show b - a₂ < b - a₁

  calc
    _ = b - a₂  := rfl
    _ ≃ b + -a₂ := sub_defn
    _ < b + -a₁ := by srw [‹a₁ < a₂›]
    _ ≃ b - a₁  := Rel.symm sub_defn

variable [Induction.{1} ℤ]

/-- Extract the equivalent natural number from a nonnegative integer. -/
def nonneg_to_natural {a : ℤ} : a ≥ 0 → { n : ℕ // a ≃ n } := by
  intro (_ : a ≥ 0)
  show { n : ℕ // a ≃ n }

  have (Subtype.mk (Prod.mk (n : ℕ) (m : ℕ)) (_ : a ≃ n - m)) := as_diff a
  have (Subtype.mk (d : ℕ) (_ : m + d ≃ n)) :=
    have : (n:ℤ) - m ≥ 0 := calc
      _ = (n:ℤ) - m := rfl
      _ ≃ a         := Rel.symm ‹a ≃ n - m›
      _ ≥ 0         := ‹a ≥ 0›
    have : (n:ℤ) ≥ (m:ℤ) := ge_iff_diff_nonneg.mpr ‹(n:ℤ) - m ≥ 0›
    have : n ≥ m := from_natural_respects_le.mpr ‹(n:ℤ) ≥ (m:ℤ)›
    show { d : ℕ // m + d ≃ n } from Natural.le_diff ‹n ≥ m›

  have : a ≃ d := calc
    _ = a                   := rfl
    _ ≃ n - m               := ‹a ≃ n - m›
    _ ≃ ((m + d : ℕ):ℤ) - m := by srw [←‹m + d ≃ n›]
    _ ≃ m + d - m           := by srw [add_compat_nat]
    _ ≃ d + m - m           := by srw [AA.comm]
    _ ≃ d + (m - m)         := sub_assoc_addL
    _ ≃ d + 0               := by srw [sub_same]
    _ ≃ d                   := AA.identR

  have : { n : ℕ // a ≃ n } := Subtype.mk d ‹a ≃ d›
  exact this

/-- Extract the equivalent natural number from a positive integer. -/
def pos_to_natural {a : ℤ} : a > 0 → { n : ℕ // a ≃ n ∧ n > 0 } := by
  intro (_ : a > 0)
  show { n : ℕ // a ≃ n ∧ n > 0 }

  have : a ≥ 0 := ge_split.mpr (Or.inl ‹a > 0›)
  have (Subtype.mk (n : ℕ) (_ : a ≃ n)) := nonneg_to_natural ‹a ≥ 0›
  have : (n:ℤ) > 0 := calc
    _ = (n:ℤ) := rfl
    _ ≃ a     := Rel.symm ‹a ≃ n›
    _ > 0     := ‹a > 0›
  have : n > 0 := from_natural_respects_lt.mpr ‹(n:ℤ) > 0›
  exact Subtype.mk n (And.intro ‹a ≃ n› ‹n > 0›)

end Lean4Axiomatic.Integer

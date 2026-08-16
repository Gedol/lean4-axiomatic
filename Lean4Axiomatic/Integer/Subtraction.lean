import Lean4Axiomatic.Integer.Sign

/-! # Integer subtraction -/

namespace Lean4Axiomatic.Integer

open Logic (iff_subst_covar or_mapR)

/-! ## Axioms -/

/-- Operations pertaining to integer subtraction. -/
class Subtraction.Ops (ℤ : Type) where
  /-- Subtraction of integers. -/
  sub : ℤ → ℤ → ℤ

export Subtraction.Ops (sub)

/-- Enables the use of the `· - ·` operator for subtraction. -/
instance sub_op_inst {ℤ : Type} [Subtraction.Ops ℤ] : Sub ℤ := {
  sub := sub
}

/-- Properties of integer subtraction. -/
class Subtraction.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Ops ℤ]
    where
  /-- Subtraction is equivalent to addition of a negated second argument. -/
  sub_defn {a b : ℤ} : a - b ≃ a + (-b)

export Subtraction.Props (sub_defn)

/-- All integer subtraction axioms. -/
class Subtraction
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ]
    where
  toOps : Subtraction.Ops ℤ
  toProps : Subtraction.Props ℤ

attribute [implicit_reducible, instance] Subtraction.toOps
attribute [instance] Subtraction.toProps

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]

/--
Subtraction is left-substitutive.

**Proof intuition**: Trivial; just substitutes on the underlying addition.
-/
@[gcongr]
theorem sub_substL {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ - b ≃ a₂ - b := by
  intro (_ : a₁ ≃ a₂)
  show a₁ - b ≃ a₂ - b
  calc
    a₁ - b    ≃ _ := sub_defn
    a₁ + (-b) ≃ _ := by srw [‹a₁ ≃ a₂›]
    a₂ + (-b) ≃ _ := Rel.symm sub_defn
    a₂ - b    ≃ _ := Rel.refl

/--
Subtraction is right-substitutive.

**Proof intuition**: Trivial; just substitutes on the underlying addition and
negation.
-/
@[gcongr]
theorem sub_substR {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b - a₁ ≃ b - a₂ := by
  intro (_ : a₁ ≃ a₂)
  show b - a₁ ≃ b - a₂
  calc
    b - a₁    ≃ _ := sub_defn
    b + (-a₁) ≃ _ := by srw [‹a₁ ≃ a₂›]
    b + (-a₂) ≃ _ := Rel.symm sub_defn
    b - a₂    ≃ _ := Rel.refl

instance sub_substitutive
    : AA.Substitutive₂ (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ _ => sub_substL }
  substitutiveR := { subst₂ := λ _ => sub_substR }
}

/--
Integer subtraction (on the left) can be removed (or added) from both sides of
an integer equivalence.
-/
theorem sub_injectL {a b₁ b₂ : ℤ} : a - b₁ ≃ a - b₂ ↔ b₁ ≃ b₂ := calc
  _ ↔ a - b₁ ≃ a - b₂   := Iff.rfl
  _ ↔ a + -b₁ ≃ a + -b₂ := by srw [sub_defn, sub_defn]
  _ ↔ -b₁ ≃ -b₂         := add_injectL
  _ ↔ b₁ ≃ b₂           := Iff.intro neg_inject neg_subst

/--
Integer subtraction (on the right) can be removed (or added) from both sides of
an integer equivalence.
-/
theorem sub_injectR {a₁ a₂ b : ℤ} : a₁ - b ≃ a₂ - b ↔ a₁ ≃ a₂ := calc
  _ ↔ a₁ - b ≃ a₂ - b   := Iff.rfl
  _ ↔ a₁ + -b ≃ a₂ + -b := by srw [sub_defn, sub_defn]
  _ ↔ a₁ ≃ a₂           := add_injectR

/--
Subtracting an integer from itself yields zero.

**Property and proof intuition**: This is equivalent to the additive inverse
property.
-/
theorem sub_same {a : ℤ} : a - a ≃ 0 := calc
  a - a  ≃ _ := sub_defn
  a + -a ≃ _ := AA.inverseR
  0      ≃ _ := Rel.refl

/--
Subtraction with the additive identity on the left negates the right operand.

**Property and proof intuition**: By definition of subtraction and the additive
identity.
-/
theorem sub_identL {a : ℤ} : 0 - a ≃ -a := calc
  _ = 0 - a  := rfl
  _ ≃ 0 + -a := sub_defn
  _ ≃ -a     := AA.identL

/--
Subtraction with the additive identity on the right gives the left operand.

**Property and proof intuition**: By definition of subtraction and the additive
identity.
-/
theorem sub_identR {a : ℤ} : a - 0 ≃ a := calc
  _ = a - 0        := rfl
  _ ≃ a + -0       := sub_defn
  _ ≃ a + (-0 + 0) := by srw [←add_identR]
  _ ≃ a + 0        := by srw [neg_invL]
  _ ≃ a            := AA.identR

/--
Equivalent integers are the only ones to differ by zero.

**Proof intuition**: The reverse direction is trivial; the forward direction
uses the additive inverse property and the assumption `a - b ≃ 0` to replace
`a` with `b`.
-/
theorem zero_diff_iff_eqv {a b : ℤ} : a - b ≃ 0 ↔ a ≃ b := by
  apply Iff.intro
  case mp =>
    intro (_ : a - b ≃ 0)
    show a ≃ b
    calc
      a            ≃ _ := Rel.symm AA.identR
      a + 0        ≃ _ := by srw [←neg_invL]
      a + (-b + b) ≃ _ := Rel.symm AA.assoc
      (a + -b) + b ≃ _ := by srw [←sub_defn]
      (a - b) + b  ≃ _ := by srw [‹a - b ≃ 0›]
      0 + b        ≃ _ := AA.identL
      b            ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ b)
    show a - b ≃ 0
    calc
      a - b  ≃ _ := by srw [‹a ≃ b›]
      b - b  ≃ _ := sub_same
      0      ≃ _ := Rel.refl

/--
Subtraction associates with addition to its left.

**Property intuition**: In the integers, these expressions are equivalent
because there's only a single subtraction happening: no matter what order the
operations happen, the end result will be the same.

**Proof intuition**: Expand subtraction into addition, then use addition's
associativity.
-/
theorem sub_assoc_addL {a b c : ℤ} : (a + b) - c ≃ a + (b - c) := calc
  _ = (a + b) - c  := rfl
  _ ≃ (a + b) + -c := sub_defn
  _ ≃ a + (b + -c) := AA.assoc
  _ ≃ a + (b - c)  := by srw [←sub_defn]

/--
Subtraction "associates" with addition to its right.

**Property intuition**: This is not true associativity, but resembles it in
the grouping of terms. What is actually happening is that, because the same
value `b` is being subtracted on both sides of the equivalence, it doesn't
matter in what order that occurs.

**Proof intuition**: Expand subtraction into addition; rearrange.
-/
theorem sub_assoc_addR {a b c : ℤ} : (a - b) + c ≃ a + (c - b) := calc
  _ = (a - b) + c  := rfl
  _ ≃ (a + -b) + c := by srw [sub_defn]
  _ ≃ a + (-b + c) := AA.assoc
  _ ≃ a + (c + -b) := by srw [AA.comm]
  _ ≃ a + (c - b)  := by srw [←sub_defn]

/--
Move a subtraction's right operand to an addition's right operand, from left to
right across an equivalence (or the reverse).

**Property intuition**: This is a fundamental algebraic operation,
which follows directly from addition obeying substitution and cancellation.

**Proof intuition**: Add `b` to both sides (substitution/cancellation), then
simplify.
-/
theorem subR_moveR_addR {a b c : ℤ} : a - b ≃ c ↔ a ≃ c + b := calc
  _ ↔       a - b ≃ c     := Iff.rfl
  _ ↔ (a - b) + b ≃ c + b := add_injectR.symm
  _ ↔           a ≃ c + b := by srw [sub_assoc_addR, sub_same, add_identR]

/--
Move a subtraction's right operand to an addition's left operand, from left to
right across an equivalence (or the reverse).

**Property intuition**: This is a fundamental algebraic operation,
which follows directly from addition obeying substitution and cancellation.

**Proof intuition**: Trivial corollary to `subR_moveR_addR`.
-/
theorem subR_moveR_addL {a b c : ℤ} : a - b ≃ c ↔ a ≃ b + c := calc
  _ ↔ a - b ≃ c     := Iff.rfl
  _ ↔     a ≃ c + b := subR_moveR_addR
  _ ↔     a ≃ b + c := by srw [AA.comm]

/--
Move a subtraction's right operand to an addition's right operand, from right
to left across an equivalence (or the reverse).

**Property intuition**: This is a fundamental algebraic operation,
which follows directly from addition obeying substitution and cancellation.

**Proof intuition**: Trivial corollary to `subR_moveR_addR`.
-/
theorem subR_moveL_addR {a b c : ℤ} : a ≃ b - c ↔ a + c ≃ b := calc
  _ ↔     a ≃ b - c := Iff.rfl
  _ ↔ b - c ≃ a     := Fn.swap
  _ ↔     b ≃ a + c := subR_moveR_addR
  _ ↔ a + c ≃ b     := Fn.swap

/--
Move a subtraction's right operand to an addition's left operand, from right to
left across an equivalence (or the reverse).

**Property intuition**: This is a fundamental algebraic operation,
which follows directly from addition obeying substitution and cancellation.

**Proof intuition**: Trivial corollary to `subR_moveL_addR`.
-/
theorem subR_moveL_addL {a b c : ℤ} : a ≃ b - c ↔ c + a ≃ b := calc
  _ ↔     a ≃ b - c := Iff.rfl
  _ ↔ a + c ≃ b     := subR_moveL_addR
  _ ↔ c + a ≃ b     := by srw [AA.comm]

/--
Convert an equivalence of subtractions to one of additions by exchanging
operands.

**Property intuition**: Add the subtracted operands to both sides and simplify.

**Proof intuition**: Uses lemmas to carry out the strategy from the property
intuition in fewer steps.
-/
theorem sub_swap_add {a b c d : ℤ} : a - b ≃ c - d ↔ a + d ≃ c + b := calc
  _ ↔ a - b ≃ c - d       := Iff.rfl
  _ ↔     a ≃ (c - d) + b := subR_moveR_addR
  _ ↔     a ≃ c + (b - d) := by srw [sub_assoc_addR]
  _ ↔     a ≃ (c + b) - d := by srw [←sub_assoc_addL]
  _ ↔ a + d ≃ c + b       := subR_moveL_addR

/--
The simplest example of a "telescoping" sum: adding two differences with a
common middle value results in the difference of the endpoints.

**Property and proof intuition**: The middle value is positive in one of the
sum's arguments, and negative in the other. Those are additive inverses so they
sum to zero and disappear from the result.
-/
theorem add_sub_telescope {a b c : ℤ} : (a - b) + (b - c) ≃ a - c := calc
  (a - b) + (b - c)   ≃ _ := by srw [sub_defn, sub_defn]
  (a + -b) + (b + -c) ≃ _ := AA.expr_xxfxxff_lr_swap_rr
  (a + -c) + (b + -b) ≃ _ := by srw [neg_invR]
  (a + -c) + 0        ≃ _ := AA.identR
  a + -c              ≃ _ := Rel.symm sub_defn
  a - c               ≃ _ := Rel.refl

variable [Multiplication ℤ]

/--
Subtraction "associates" with subtraction to its right.

**Property intuition**: Subtracting `b` from `a`, and then `c` from the result,
is equivalent to subtracting `b` and `c` from `a` together.

**Proof intuition**: Expand subtraction into addition; rearrange.
-/
theorem sub_assoc_subR {a b c : ℤ} : (a - b) - c ≃ a - (b + c) := calc
  _ = (a - b) - c   := rfl
  _ ≃ (a - b) + -c  := sub_defn
  _ ≃ (a + -b) + -c := by srw [sub_defn]
  _ ≃ a + (-b + -c) := AA.assoc
  _ ≃ a + -(b + c)  := by srw [←neg_compat_add]
  _ ≃ a - (b + c)   := Rel.symm sub_defn

/--
A sum of differences is equivalent to a difference of sums.

**Property and proof intuition**: Differences are just sums of negated
quantities, so all terms can be rearranged at will. Group the terms by their
"negated" status.
-/
theorem sub_xchg_add
    {a b c d : ℤ} : (a - b) + (c - d) ≃ (a + c) - (b + d)
    := calc
  _ = (a - b) + (c - d)       := rfl
  _ ≃ (a + (-b)) + (c + (-d)) := by srw [sub_defn, sub_defn]
  _ ≃ (a + c) + ((-b) + (-d)) := AA.expr_xxfxxff_lr_swap_rl
  _ ≃ (a + c) + (-(b + d))    := by srw [←neg_compat_add]
  _ ≃ (a + c) - (b + d)       := Rel.symm sub_defn

/--
Multiplication distributes over subtraction (on the left).

**Property and proof intuition**: This is the same as multiplication
distributing over addition: just expand the definition of subtraction.
-/
theorem mul_distribL_sub {a b c : ℤ} : a * (b - c) ≃ a * b - a * c := calc
  a * (b - c)      ≃ _ := by srw [sub_defn]
  a * (b + -c)     ≃ _ := AA.distribL
  a * b + a * -c   ≃ _ := by srw [←AA.scompatR]
  a * b + -(a * c) ≃ _ := Rel.symm sub_defn
  a * b - a * c    ≃ _ := Rel.refl

/--
Multiplication distributes over subtraction (on the right).

**Property and proof intuition**: Use left distribution and commutativity.
-/
theorem mul_distribR_sub {a b c : ℤ} : (b - c) * a ≃ b * a - c * a := calc
  _ = (b - c) * a   := rfl
  _ ≃ a * (b - c)   := AA.comm
  _ ≃ a * b - a * c := mul_distribL_sub
  _ ≃ b * a - a * c := by srw [AA.comm]
  _ ≃ b * a - c * a := by srw [AA.comm]

instance mul_distributive_sub : AA.Distributive (α := ℤ) (· * ·) (· - ·) := {
  distributiveL := { distrib := mul_distribL_sub }
  distributiveR := { distrib := mul_distribR_sub }
}

/--
When subtracting two sums, if they both have the same right-hand operand, it
can be removed, leaving just the difference of the left-hand operands.

**Intuition**: This follows from the basic algebraic properties of integers.
-/
theorem sub_sums_sameR {a b c : ℤ} : a + c - (b + c) ≃ a - b := calc
  a + c - (b + c)           ≃ _ := sub_defn
  a + c + -(b + c)          ≃ _ := by srw [←mul_neg_one]
  a + c + -1 * (b + c)      ≃ _ := by srw [mul_distribL]
  a + c + (-1 * b + -1 * c) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
  a + -1 * b + (c + -1 * c) ≃ _ := by srw [mul_neg_one]
  a + -1 * b + (c + -c)     ≃ _ := by srw [neg_invR]
  a + -1 * b + 0            ≃ _ := AA.identR
  a + -1 * b                ≃ _ := by srw [mul_neg_one]
  a + -b                    ≃ _ := Rel.symm sub_defn
  a - b                     ≃ _ := Rel.refl

/--
Negation of subtraction swaps the operands.

**Property intuition**: The result of subtraction depends on the ordering of
the two operands. Negating the result is equivalent to reversing the operands'
order.

**Proof intuition**: Represent subtraction as addition; the negation operator
distributes to both operands. It undoes the negation of one operand, and adds
negation to the other. With negation swapped, the sum is still equivalent to
subtraction, but in the opposite order.
-/
theorem sub_neg_flip {a b : ℤ} : -(a - b) ≃ b - a := calc
  (-(a - b))   ≃ _ := by srw [sub_defn]
  (-(a + -b))  ≃ _ := neg_compat_add
  (-a) + -(-b) ≃ _ := by srw [neg_involutive]
  (-a) + b     ≃ _ := AA.comm
  b + -a       ≃ _ := Rel.symm sub_defn
  b - a        ≃ _ := Rel.refl

variable [Sign ℤ]

/--
The only way for multiplication on the right to have no effect on the left
value, is if the left value is zero or the right value is one.

**Property intuition**: The reverse direction is trivial. The forward direction
makes sense because multiplication by any values that are not zero or one will
change the magnitude of the result or the sign of the result.

**Proof intuition**: Rewrite the equivalence into `a * (b - 1) ≃ 0` using
algebra. Then `mul_split_zero` implies at least one of the factors is zero, and
with trivial algebra this gives the result.
-/
theorem mul_identR_reasons {a b : ℤ} : a * b ≃ a ↔ a ≃ 0 ∨ b ≃ 1 := calc
  _ ↔ a * b ≃ a         := Iff.rfl
  _ ↔ a * b ≃ a * 1     := by srw [←mul_identR]
  _ ↔ a * b - a * 1 ≃ 0 := zero_diff_iff_eqv.symm
  _ ↔ a * (b - 1) ≃ 0   := by srw [←mul_distribL_sub]
  _ ↔ a ≃ 0 ∨ b - 1 ≃ 0 := mul_split_zero
  _ ↔ a ≃ 0 ∨ b ≃ 1     := iff_subst_covar or_mapR zero_diff_iff_eqv

/--
Multiplication by a nonzero value on the left is injective.

**Property and proof intuition**: Viewing multiplication as a scaling
operation, this says that if two values are equivalent after being scaled by
the same amount, then their unscaled values must have been equivalent as well.
This seems to be consistent with our intuitive understanding of multiplication.
-/
theorem mul_cancelL {a b c : ℤ} : a ≄ 0 → a * b ≃ a * c → b ≃ c := by
  intro (_ : a ≄ 0) (_ : a * b ≃ a * c)
  show b ≃ c
  have : a * b - a * c ≃ 0 := zero_diff_iff_eqv.mpr ‹a * b ≃ a * c›
  have : a * (b - c) ≃ 0 := Rel.trans AA.distribL ‹a * b - a * c ≃ 0›
  have : a ≃ 0 ∨ b - c ≃ 0 := mul_split_zero.mp ‹a * (b - c) ≃ 0›
  match ‹a ≃ 0 ∨ b - c ≃ 0› with
  | Or.inl (_ : a ≃ 0) =>
    show b ≃ c
    exact absurd ‹a ≃ 0› ‹a ≄ 0›
  | Or.inr (_ : b - c ≃ 0) =>
    show b ≃ c
    exact zero_diff_iff_eqv.mp ‹b - c ≃ 0›

@[implicit_reducible]
def mul_cancellativeL
    : AA.CancellativeOn Hand.L (α := ℤ) (· * ·) (· ≄ 0) (· ≃ ·) (· ≃ ·)
    := {
  cancel := mul_cancelL
}

instance mul_cancellative
    : AA.Cancellative (α := ℤ) (· * ·) (· ≄ 0) (· ≃ ·) (· ≃ ·)
    := {
  cancellativeL := mul_cancellativeL
  cancellativeR := AA.cancelR_from_cancelL mul_cancellativeL
}

/--
Multiplication by a nonzero value on the right is injective.

**Property and proof intuition**: See `mul_cancelL`.
-/
theorem mul_cancelR {a b c : ℤ} : a ≄ 0 → b * a ≃ c * a → b ≃ c :=
  AA.cancelRC (C := (· ≄ 0))

/--
Two integers are equivalent iff the sign of their difference is zero.

This lemma can save some lines in proofs of sign or order trichotomy.

**Property and proof intution**: Follows directly from `zero_diff_iff_eqv` and
`sgn_zero`.
-/
theorem eqv_sgn {a b : ℤ} : a ≃ b ↔ sgn (a - b) ≃ 0 := calc
  _ ↔ a ≃ b           := Iff.rfl
  _ ↔ a - b ≃ 0       := zero_diff_iff_eqv.symm
  _ ↔ sgn (a - b) ≃ 0 := sgn_zero.symm

/--
Decidable equivalence for integers.

**Property intuition**: Every integer has a finite value, so it should be
possible for an algorithm to decide if two of them are equivalent.

**Proof intuition**: The result of `sgn` is already decidable, so compute it
for `a - b` and rewrite the result into `a ≃ b` or `a ≄ b` depending on whether
the sign is zero or not.
-/
instance eqv? (a b : ℤ) : Decidable (a ≃ b) := by
  let Sgn3 := AA.OneOfThree₁ (sgn (a-b) ≃ 0) (sgn (a-b) ≃ 1) (sgn (a-b) ≃ -1)
  have : Sgn3 := sgn_trichotomy (a-b)
  match this with
  | AA.OneOfThree₁.first (_ : sgn (a-b) ≃ 0) =>
    have : a ≃ b := eqv_sgn.mpr ‹sgn (a-b) ≃ 0›
    have : Decidable (a ≃ b) := isTrue this
    exact this
  | AA.OneOfThree₁.second (_ : sgn (a-b) ≃ 1) =>
    have : (1:ℤ) ≄ 0 := one_neqv_zero
    have : sgn (a-b) ≄ 0 := by prw [←‹sgn (a-b) ≃ 1›] ‹(1:ℤ) ≄ 0›
    have : a-b ≄ 0 := mt sgn_zero.mpr this
    have : a ≄ b := mt zero_diff_iff_eqv.mpr this
    have : Decidable (a ≃ b) := isFalse this
    exact this
  | AA.OneOfThree₁.third (_ : sgn (a-b) ≃ -1) =>
    have : (-1:ℤ) ≄ 0 := neg_one_neqv_zero
    have : sgn (a-b) ≄ 0 := by prw [←‹sgn (a-b) ≃ -1›] ‹(-1:ℤ) ≄ 0›
    have : a-b ≄ 0 := mt sgn_zero.mpr this
    have : a ≄ b := mt zero_diff_iff_eqv.mpr this
    have : Decidable (a ≃ b) := isFalse this
    exact this

end Lean4Axiomatic.Integer

import Lean4Axiomatic.Integer.Negation
import Lean4Axiomatic.Logic
import Lean4Axiomatic.Sign

/-!
# Integer signedness
-/

namespace Lean4Axiomatic.Integer

open Coe (coe)
open Signed (Negative Positive)

/-!
## Preliminary definitions and theorems
-/

section prelim

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ]
variable [Addition ℕ ℤ] [Multiplication ℕ ℤ] [Negation ℕ ℤ]

/--
A positive or negative integer of unit magnitude.

Only `1` and `-1` satisfy this property. It's formulated using multiplication
to be easy to use with algebra.

**Named parameters**
- `a`: The integer satisfying the property.
-/
def SquareRootOfUnity (a : ℤ) : Prop := a * a ≃ 1

/--
The `SquareRootOfUnity` predicate respects equivalence.

**Property intuition**: This must be true for `SquareRootOfUnity` to make sense
as a predicate.

**Proof intuition**: Expand the definition of `SquareRootOfUnity` to obtain an
equivalence involving multiplication. Since multiplication is substitutive, the
result follows easily.
-/
theorem sqrt1_subst
    {a₁ a₂ : ℤ} : a₁ ≃ a₂ → SquareRootOfUnity a₁ → SquareRootOfUnity a₂
    := by
  intro (_ : a₁ ≃ a₂) (_ : a₁ * a₁ ≃ 1)
  show a₂ * a₂ ≃ 1
  calc
    a₂ * a₂ ≃ _ := AA.substL (Rel.symm ‹a₁ ≃ a₂›)
    a₁ * a₂ ≃ _ := AA.substR (Rel.symm ‹a₁ ≃ a₂›)
    a₁ * a₁ ≃ _ := ‹a₁ * a₁ ≃ 1›
    1       ≃ _ := Rel.refl

instance sqrt1_substitutive
    : AA.Substitutive₁ SquareRootOfUnity (· ≃ ·) (· → ·)
    := {
  subst₁ := sqrt1_subst
}

/-- One is a square root of unity. -/
theorem sqrt1_one : SquareRootOfUnity 1 := by
  show 1 * 1 ≃ 1
  exact AA.identL

/--
Negative one is a square root of unity.

**Property and proof intuition**: Multiplying two negative numbers gives a
positive result, and if the magnitudes are `1`, the result will also be `1`.
-/
theorem sqrt1_neg_one : SquareRootOfUnity (-1) := by
  show (-1) * (-1) ≃ 1
  calc
    (-1) * (-1)   ≃ _ := Rel.symm AA.scompatL
    (-(1 * (-1))) ≃ _ := AA.subst₁ (Rel.symm AA.scompatR)
    (-(-(1 * 1))) ≃ _ := neg_involutive
    1 * 1         ≃ _ := sqrt1_one
    1             ≃ _ := Rel.refl

/--
The product of square roots of unity is also a square root of unity.

This is an important result; it means that positive and negative signs can be
represented by integers, allowing derivations using algebra.

**Property intuition**: A factor of `1` or `-1` in a product does not change
the magnitude of the result. Thus, regardless of the signs involved, a product
of two square roots of unity can only be `1` or `-1`.

**Proof intuition**: Rearrange factors with associativity to isolate `a` and
`b` into products with themselves. By the definition of `SquareRootOfUnity`,
those products must each be `1`; thus the product of the products is also `1`.
-/
theorem mul_preserves_sqrt1
    {a b : ℤ}
    : SquareRootOfUnity a → SquareRootOfUnity b → SquareRootOfUnity (a * b)
    := by
  intro (_ : a * a ≃ 1) (_ : b * b ≃ 1)
  show (a * b) * (a * b) ≃ 1
  calc
    (a * b) * (a * b) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (a * a) * (b * b) ≃ _ := AA.substL ‹a * a ≃ 1›
    1 * (b * b)       ≃ _ := AA.substR ‹b * b ≃ 1›
    1 * 1             ≃ _ := sqrt1_one
    1                 ≃ _ := Rel.refl

/--
Demonstrates that an integer can be factored into _sign_ and _magnitude_
components.

The sign value is either positive (represented by `1`) or negative (represented
by `-1`). The magnitude must be a positive natural number.

This data structure is a foundation for defining the `Positive`, `Negative`,
and `Nonzero` predicates on integers.

**Parameters**
- `a`: The integer to represent in signed-magnitude form.
- `s`: The sign value.
- `SquareRootOfUnity s`: Ensures that `s` is either `1` or `-1`.
-/
inductive SignedMagnitude (a : ℤ) {s : ℤ} (_ : SquareRootOfUnity s) : Prop
| /--
  `SignedMagnitude`'s only constructor.

  **Parameters**
  - `m`: The magnitude value.
  - `pos`: Ensures a positive magnitude.
  - `eqv`: Proof that `a` is a product of the sign and the magnitude.
  -/
  intro (m : ℕ) (pos : Positive m) (eqv : a ≃ s * coe m)

/--
`SignedMagnitude` respects equivalence of signs.

**Property intuition**: If signs `s₁` and `s₂` are equivalent, and we have a
`SignedMagnitude` for `s₁`, then that can be converted into a `SignedMagnitude`
for `s₂`. This _must_ be true for `SignedMagnitude` to be a valid predicate.

**Proof intuition**: Extract the equivalence for `s₁`, substitute `s₂` into it,
and build a new `SignedMagnitude` on `s₂`.
-/
theorem signedMagnitude_sqrt1_subst
    {a s₁ s₂ : ℤ} {_ : SquareRootOfUnity s₁} (_ : s₁ ≃ s₂)
    : SignedMagnitude a ‹SquareRootOfUnity s₁›
    → have : SquareRootOfUnity s₂ :=
        AA.subst₁ (rβ := (· → ·)) ‹s₁ ≃ s₂› ‹SquareRootOfUnity s₁›
      SignedMagnitude a ‹SquareRootOfUnity s₂›
    := by
  intro (SignedMagnitude.intro (m : ℕ) (_ : Positive m) (_ : a ≃ s₁ * coe m))
  have : a ≃ s₂ * coe m := Rel.trans ‹a ≃ s₁ * coe m› (AA.substL ‹s₁ ≃ s₂›)
  exact SignedMagnitude.intro m ‹Positive m› ‹a ≃ s₂ * coe m›

/--
Given two integers in signed-magnitude form, we can put their product in
signed-magnitude form as well.

**Property intuition**: This seems plausible, if only because every integer can
be put into signed-magnitude form.

**Proof intuition**: From previous results, we know that multiplication
preserves `SquareRootOfUnity`, and `Positive` on natural numbers. Then we just
need to show that the product of two signed-magnitude forms can itself be put
into signed-magnitude form; this follows mostly from algebra on multiplication.
-/
theorem mul_preserves_signedMagnitude
    {a b as bs : ℤ}
    {a_sqrt1 : SquareRootOfUnity as} {b_sqrt1 : SquareRootOfUnity bs}
    : SignedMagnitude a a_sqrt1 → SignedMagnitude b b_sqrt1
    → have : SquareRootOfUnity (as * bs) := mul_preserves_sqrt1 a_sqrt1 b_sqrt1
      SignedMagnitude (a * b) ‹SquareRootOfUnity (as * bs)›
    := by
  intro
    (SignedMagnitude.intro (am : ℕ) (_ : Positive am) (_ : a ≃ as * coe am))
  intro
    (SignedMagnitude.intro (bm : ℕ) (_ : Positive bm) (_ : b ≃ bs * coe bm))
  have : SquareRootOfUnity (as * bs) := mul_preserves_sqrt1 a_sqrt1 b_sqrt1
  show SignedMagnitude (a * b) ‹SquareRootOfUnity (as * bs)›
  have : Positive (am * bm) := Natural.mul_positive ‹Positive am› ‹Positive bm›
  have : a * b ≃ (as * bs) * coe (am * bm) := calc
    a * b                         ≃ _ := AA.substL ‹a ≃ as * coe am›
    (as * coe am) * b             ≃ _ := AA.substR ‹b ≃ bs * coe bm›
    (as * coe am) * (bs * coe bm) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (as * bs) * (coe am * coe bm) ≃ _ := AA.substR (Rel.symm AA.compat₂)
    (as * bs) * coe (am * bm)     ≃ _ := Rel.refl
  exact SignedMagnitude.intro
    (am * bm) ‹Positive (am * bm)› ‹a * b ≃ (as * bs) * coe (am * bm)›

/--
A positive or negative integer.

Represents nonzero integers as the product of a nonzero sign (`1` or `-1`) and
a positive magnitude. This is convenient for use in algebraic proofs.

**Parameters**
- `a`: The integer that is positive or negative.
-/
inductive Nonzero (a : ℤ) : Prop :=
| /--
  Construct evidence that the integer `a` is nonzero.

  **Parameters**
  - See `Nonzero` for the class-level parameters.
  - `sign`: Has value `1` if `a` is positive, or `-1` if `a` is negative.
  - `sqrt1`: Evidence that `sign` is `1` or `-1`.
  - `sm`: Evidence that `sign` denotes the sign of `a`.
  -/
  intro
    (sign : ℤ)
    (sqrt1 : SquareRootOfUnity sign)
    (sm : SignedMagnitude a sqrt1)

/--
Convenience constructor that infers early arguments of `Nonzero.intro` from the
last, `SignedMagnitude` argument.
-/
def Nonzero.mk
    {a s : ℤ} {sqrt1 : SquareRootOfUnity s}
    : SignedMagnitude a sqrt1 → Nonzero a :=
  Nonzero.intro s sqrt1

/--
The product of nonzero integers is nonzero.

**Property and proof intuition**: `Nonzero` can be decomposed into a sign value
and a `SignedMagnitude` value. Previous results have shown that both of those
components are preserved under multiplication, so a `Nonzero` value for the
product of `Nonzero` integers can always be constructed.
-/
theorem mul_preserves_nonzero
    {a b : ℤ} : Nonzero a → Nonzero b → Nonzero (a * b)
    := by
  intro (Nonzero.intro as
      (a_sqrt1 : SquareRootOfUnity as) (a_sm : SignedMagnitude a a_sqrt1))
  intro (Nonzero.intro bs
      (b_sqrt1 : SquareRootOfUnity bs) (b_sm : SignedMagnitude b b_sqrt1))
  show Nonzero (a * b)
  have : SquareRootOfUnity (as * bs) :=
    mul_preserves_sqrt1 ‹SquareRootOfUnity as› ‹SquareRootOfUnity bs›
  have : SignedMagnitude (a * b) ‹SquareRootOfUnity (as * bs)› :=
    mul_preserves_signedMagnitude a_sm b_sm
  exact Nonzero.mk ‹SignedMagnitude (a * b) ‹SquareRootOfUnity (as * bs)››

end prelim

/-!
## Axioms
-/

/-- Class defining integer signedness, and properties that it must satisfy. -/
class Sign
    (ℕ : Type) [outParam (Natural ℕ)]
    (ℤ : Type)
      [outParam (Core ℕ ℤ)] [outParam (Addition ℕ ℤ)]
      [outParam (Multiplication ℕ ℤ)] [outParam (Negation ℕ ℤ)]
    :=
  /-- Definitions of `Positive` and `Negative`, and their basic properties. -/
  signed : Signed ℤ

  /-- An integer is positive iff it has sign `1` in signed-magnitude form. -/
  positive_defn {a : ℤ} : Positive a ↔ SignedMagnitude a sqrt1_one

  /-- An integer is negative iff it has sign `-1` in signed-magnitude form. -/
  negative_defn {a : ℤ} : Negative a ↔ SignedMagnitude a sqrt1_neg_one

attribute [instance] Sign.signed

export Sign (negative_defn positive_defn)

/-!
## Derived properties
-/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ] [Addition ℕ ℤ] [Multiplication ℕ ℤ]
variable [Negation ℕ ℤ] [Sign ℕ ℤ]

/-- An integer is positive if it's equivalent to a positive natural number. -/
def positive_intro_nat
    {m : ℕ} {a : ℤ} : Positive m → a ≃ coe m → Positive a
    := by
  intro (_ : Positive m) (_ : a ≃ coe m)
  show Positive a
  have : a ≃ 1 * coe m := Rel.trans ‹a ≃ coe m› (Rel.symm AA.identL)
  have : SignedMagnitude a sqrt1_one :=
    SignedMagnitude.intro m ‹Positive m› ‹a ≃ 1 * coe m›
  exact positive_defn.mpr ‹SignedMagnitude a sqrt1_one›

/--
Extract evidence that a positive integer is equivalent to a positive natural
number.
-/
def positive_elim_nat
    {a : ℤ} : Positive a → ∃ n : ℕ, Positive n ∧ a ≃ coe n
    := by
  intro (_ : Positive a)
  show ∃ n, Positive n ∧ a ≃ coe n
  have (SignedMagnitude.intro (n : ℕ) (_ : Positive n) (_ : a ≃ 1 * coe n)) :=
    positive_defn.mp ‹Positive a›
  have : a ≃ coe n := Rel.trans ‹a ≃ 1 * coe n› AA.identL
  exact Exists.intro n (And.intro ‹Positive n› ‹a ≃ coe n›)

/--
An integer is negative if it's equivalent to the negation of a positive natural
number.
-/
def negative_intro_nat
    {m : ℕ} {a : ℤ} : Positive m → a ≃ -(coe m) → Negative a
    := by
  intro (_ : Positive m) (_ : a ≃ -(coe m))
  show Negative a
  have : a ≃ -1 * coe m := Rel.trans ‹a ≃ -(coe m)› (Rel.symm mul_neg_one)
  have : SignedMagnitude a sqrt1_neg_one :=
    SignedMagnitude.intro m ‹Positive m› ‹a ≃ -1 * coe m›
  exact negative_defn.mpr ‹SignedMagnitude a sqrt1_neg_one›

/--
Extract evidence that a negative integer is equivalent to the negation of a
positive natural number.
-/
def negative_elim_nat
    {a : ℤ} : Negative a → ∃ n : ℕ, Positive n ∧ a ≃ -(coe n)
    := by
  intro (_ : Negative a)
  show ∃ n, Positive n ∧ a ≃ -(coe n)
  have (SignedMagnitude.intro (n : ℕ) (_ : Positive n) (_ : a ≃ -1 * coe n)) :=
    negative_defn.mp ‹Negative a›
  have : a ≃ -(coe n) := Rel.trans ‹a ≃ -1 * coe n› mul_neg_one
  exact Exists.intro n (And.intro ‹Positive n› ‹a ≃ -(coe n)›)

/-- Corollary of trichotomy that saves space in proofs. -/
theorem not_positive_and_negative {a : ℤ} : ¬(Positive a ∧ Negative a) := by
  intro (And.intro (_ : Positive a) (_ : Negative a))
  have two : AA.TwoOfThree (a ≃ 0) (Positive a) (Negative a) :=
    AA.TwoOfThree.twoAndThree ‹Positive a› ‹Negative a›
  have not_two : ¬ AA.TwoOfThree (a ≃ 0) (Positive a) (Negative a) :=
    (Signed.trichotomy a).atMostOne
  exact absurd two not_two

/--
The only square roots of unity in the integers are `1` and `-1`.

**Property and proof intuition**: This follows from similar reasoning as
`Natural.sqrt1`. Zero squared is zero, and integers greater than one or less
than negative one all have squares that are greater than one.
-/
theorem sqrt1_cases {a : ℤ} : SquareRootOfUnity a ↔ a ≃ 1 ∨ a ≃ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : a * a ≃ 1)
    show a ≃ 1 ∨ a ≃ -1
    match (Signed.trichotomy a).atLeastOne with
    | AA.OneOfThree.first (_ : a ≃ 0) =>
      apply False.elim
      show False
      have : 1 ≃ 0 := calc
        1     ≃ _ := Rel.symm ‹a * a ≃ 1›
        a * a ≃ _ := AA.substL ‹a ≃ 0›
        0 * a ≃ _ := AA.absorbL
        0     ≃ _ := Rel.refl
      exact absurd ‹(1 : ℤ) ≃ 0› one_neqv_zero
    | AA.OneOfThree.second (_ : Positive a) =>
      apply Or.inl
      show a ≃ 1
      have (Exists.intro (n : ℕ) (And.intro _ (_ : a ≃ coe n))) :=
        positive_elim_nat ‹Positive a›
      have : coe (n * n) ≃ coe 1 := calc
        coe (n * n)   ≃ _ := AA.compat₂
        coe n * coe n ≃ _ := AA.substL (Rel.symm ‹a ≃ coe n›)
        a * coe n     ≃ _ := AA.substR (Rel.symm ‹a ≃ coe n›)
        a * a         ≃ _ := ‹a * a ≃ 1›
        1             ≃ _ := Rel.refl
      have : n * n ≃ 1 := AA.inject ‹coe (n * n) ≃ coe (1 : ℕ)›
      have : n ≃ 1 := Natural.sqrt1.mp ‹n * n ≃ 1›
      show a ≃ 1
      calc
        a       ≃ _ := ‹a ≃ coe n›
        coe n   ≃ _ := AA.subst₁ ‹n ≃ 1›
        coe 1   ≃ _ := Rel.refl
        (1 : ℤ) ≃ _ := Rel.refl
    | AA.OneOfThree.third (_ : Negative a) =>
      apply Or.inr
      show a ≃ -1
      have (Exists.intro (n : ℕ) (And.intro _ (_ : a ≃ -(coe n)))) :=
        negative_elim_nat ‹Negative a›
      have : coe (n * n) ≃ coe 1 := calc
        coe (n * n)             ≃ _ := AA.compat₂
        coe n * coe n           ≃ _ := Rel.symm neg_involutive
        (-(-(coe n * coe n)))   ≃ _ := AA.subst₁ AA.scompatR
        (-(coe n * -(coe n)))   ≃ _ := AA.scompatL
        (-(coe n)) * (-(coe n)) ≃ _ := AA.substL (Rel.symm ‹a ≃ -(coe n)›)
        a * (-(coe n))          ≃ _ := AA.substR (Rel.symm ‹a ≃ -(coe n)›)
        a * a                   ≃ _ := ‹a * a ≃ 1›
        1                       ≃ _ := Rel.refl
      have : n * n ≃ 1 := AA.inject ‹coe (n * n) ≃ coe (1 : ℕ)›
      have : n ≃ 1 := Natural.sqrt1.mp ‹n * n ≃ 1›
      show a ≃ -1
      calc
        a          ≃ _ := ‹a ≃ -(coe n)›
        (-(coe n)) ≃ _ := AA.subst₁ (AA.subst₁ ‹n ≃ 1›)
        (-(coe 1)) ≃ _ := Rel.refl
        (-1)       ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ 1 ∨ a ≃ -1)
    show SquareRootOfUnity a
    match ‹a ≃ 1 ∨ a ≃ -1› with
    | Or.inl (_ : a ≃ 1) =>
      have : SquareRootOfUnity 1 := sqrt1_one
      exact AA.subst₁ (rβ := (· → ·)) (Rel.symm ‹a ≃ 1›) this
    | Or.inr (_ : a ≃ -1) =>
      have : SquareRootOfUnity (-1) := sqrt1_neg_one
      exact AA.subst₁ (rβ := (· → ·)) (Rel.symm ‹a ≃ -1›) this

/--
Every `SignedMagnitude` has a sign value that's either `1` or `-1`.

This is a lemma that's useful for the proof of `nonzero_defn`.

**Property and proof intuition**: We already know from `sqrt1_cases` that sign
values can only be `1` or `-1`. So this result just uses that fact to show what
the precise type of `SignedMagnitude` is allowed to be.
-/
theorem signedMagnitude_cases
    {a s : ℤ} {sqrt1 : SquareRootOfUnity s}
    : SignedMagnitude a sqrt1 →
    SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one
    := by
  intro (_ : SignedMagnitude a sqrt1)
  show SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one
  have : s ≃ 1 ∨ s ≃ -1 := sqrt1_cases.mp ‹SquareRootOfUnity s›
  match ‹s ≃ 1 ∨ s ≃ -1› with
  | Or.inl (_ : s ≃ 1) =>
    apply Or.inl
    show SignedMagnitude a sqrt1_one
    exact signedMagnitude_sqrt1_subst ‹s ≃ 1› ‹SignedMagnitude a sqrt1›
  | Or.inr (_ : s ≃ -1) =>
    apply Or.inr
    show SignedMagnitude a sqrt1_neg_one
    exact signedMagnitude_sqrt1_subst ‹s ≃ -1› ‹SignedMagnitude a sqrt1›

/--
All signed-magnitude representations of the same integer have the same sign.

**Property intuition**: From trichotomy, all nonzero integers are either
positive or negative, not both.

**Proof intuition**: Case split on all possible combinations of sign values. If
the signs are equal, we are done. Otherwise, the integer must be both
positive and negative, contradiction.
-/
theorem signedMagnitude_sqrt1_inject
    {a s₁ s₂ : ℤ}
    {sqrt1₁ : SquareRootOfUnity s₁} {sqrt1₂ : SquareRootOfUnity s₂}
    : SignedMagnitude a sqrt1₁ → SignedMagnitude a sqrt1₂ → s₁ ≃ s₂
    := by
  intro (_ : SignedMagnitude a sqrt1₁) (_ : SignedMagnitude a sqrt1₂)
  show s₁ ≃ s₂
  have : s₁ ≃ 1 ∨ s₁ ≃ -1 := sqrt1_cases.mp sqrt1₁
  have : s₂ ≃ 1 ∨ s₂ ≃ -1 := sqrt1_cases.mp sqrt1₂
  have
    : s₁ ≃ s₂ ∨ (SignedMagnitude a sqrt1_one ∧ SignedMagnitude a sqrt1_neg_one)
    := match ‹s₁ ≃ 1 ∨ s₁ ≃ -1› with
  | Or.inl (_ : s₁ ≃ 1) =>
    match ‹s₂ ≃ 1 ∨ s₂ ≃ -1› with
    | Or.inl (_ : s₂ ≃ 1) =>
      have : s₁ ≃ s₂ := Rel.trans ‹s₁ ≃ 1› (Rel.symm ‹s₂ ≃ 1›)
      Or.inl ‹s₁ ≃ s₂›
    | Or.inr (_ : s₂ ≃ -1) =>
      have sm_pos : SignedMagnitude a sqrt1_one :=
        signedMagnitude_sqrt1_subst ‹s₁ ≃ 1› ‹SignedMagnitude a sqrt1₁›
      have sm_neg : SignedMagnitude a sqrt1_neg_one :=
        signedMagnitude_sqrt1_subst ‹s₂ ≃ -1› ‹SignedMagnitude a sqrt1₂›
      Or.inr (And.intro sm_pos sm_neg)
  | Or.inr (_ : s₁ ≃ -1) =>
    match ‹s₂ ≃ 1 ∨ s₂ ≃ -1› with
    | Or.inl (_ : s₂ ≃ 1) =>
      have sm_neg : SignedMagnitude a sqrt1_neg_one :=
        signedMagnitude_sqrt1_subst ‹s₁ ≃ -1› ‹SignedMagnitude a sqrt1₁›
      have sm_pos : SignedMagnitude a sqrt1_one :=
        signedMagnitude_sqrt1_subst ‹s₂ ≃ 1› ‹SignedMagnitude a sqrt1₂›
      Or.inr (And.intro sm_pos sm_neg)
    | Or.inr (_ : s₂ ≃ -1) =>
      have : s₁ ≃ s₂ := Rel.trans ‹s₁ ≃ -1› (Rel.symm ‹s₂ ≃ -1›)
      Or.inl ‹s₁ ≃ s₂›
  match this with
  | Or.inl (_ : s₁ ≃ s₂) =>
    exact ‹s₁ ≃ s₂›
  | Or.inr (And.intro
      (_ : SignedMagnitude a sqrt1_one)
      (_ : SignedMagnitude a sqrt1_neg_one)) =>
    have : Positive a := positive_defn.mpr ‹SignedMagnitude a sqrt1_one›
    have : Negative a := negative_defn.mpr ‹SignedMagnitude a sqrt1_neg_one›
    have : Positive a ∧ Negative a := And.intro ‹Positive a› ‹Negative a›
    exact absurd ‹Positive a ∧ Negative a› not_positive_and_negative

/-- Evidence that two integers have the same sign. -/
inductive SameSqrt1 (a b : ℤ) : Prop :=
| /--
  Create an instance of `SameSqrt1`.

  **Parameters**:
  - `sign`: The sign value of `a` and `b`, as an integer.
  - `sqrt1`: Ensures that `sign` is a valid sign (i.e., has value `1` or `-1`).
  - `sm_a`: Evidence that `a` has sign `sign`.
  - `sm_b`: Evidence that `b` has sign `sign`.
  -/
  intro
    (sign : ℤ)
    (sqrt1 : SquareRootOfUnity sign)
    (sm_a : SignedMagnitude a sqrt1)
    (sm_b : SignedMagnitude b sqrt1)

/--
If two integers have the same sign, and one is positive, the other _must_ be
positive.

**Proof intuition**: Expand all definitions; use properties of
`SignedMagnitude`.
-/
theorem same_sqrt1_positive
    {a b : ℤ} : SameSqrt1 a b → Positive a → Positive b
    := by
  intro (SameSqrt1.intro
    (s : ℤ)
    (sqrt1 : SquareRootOfUnity s)
    (sm_a : SignedMagnitude a sqrt1)
    (sm_b : SignedMagnitude b sqrt1))
  intro (_ : Positive a)
  show Positive b
  have sm_1 : SignedMagnitude a sqrt1_one := positive_defn.mp ‹Positive a›
  have : s ≃ 1 := signedMagnitude_sqrt1_inject sm_a sm_1
  have : SignedMagnitude b sqrt1_one :=
    signedMagnitude_sqrt1_subst ‹s ≃ 1› sm_b
  have : Positive b := positive_defn.mpr ‹SignedMagnitude b sqrt1_one›
  exact this

/--
Nonzero integers are either, and only, positive or negative.

**Property intuition**: As the name `nonzero_defn` implies, this captures our
intuitive notion of what a nonzero integer is.

**Proof intuition**: Converts `Nonzero`, `Positive`, and `Negative` to and from
their `SignedMagnitude` representations via `signedMagnitude_cases`,
`positive_defn`, and `negative_defn`.
-/
theorem nonzero_defn {a : ℤ} : Nonzero a ↔ Positive a ∨ Negative a := by
  apply Iff.intro
  case mp =>
    intro (_ : Nonzero a)
    show Positive a ∨ Negative a
    have (Nonzero.intro
        (s : ℤ) (sqrt1 : SquareRootOfUnity s) (_ : SignedMagnitude a sqrt1)) :=
      ‹Nonzero a›
    have : SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one :=
      signedMagnitude_cases ‹SignedMagnitude a sqrt1›
    match ‹SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one› with
    | Or.inl (_ : SignedMagnitude a sqrt1_one) =>
      have : Positive a := positive_defn.mpr ‹SignedMagnitude a sqrt1_one›
      exact Or.inl ‹Positive a›
    | Or.inr (_ : SignedMagnitude a sqrt1_neg_one) =>
      have : Negative a := negative_defn.mpr ‹SignedMagnitude a sqrt1_neg_one›
      exact Or.inr ‹Negative a›
  case mpr =>
    intro (_ : Positive a ∨ Negative a)
    show Nonzero a
    match ‹Positive a ∨ Negative a› with
    | Or.inl (_ : Positive a) =>
      have : SignedMagnitude a sqrt1_one := positive_defn.mp ‹Positive a›
      exact Nonzero.mk ‹SignedMagnitude a sqrt1_one›
    | Or.inr (_ : Negative a) =>
      have : SignedMagnitude a sqrt1_neg_one := negative_defn.mp ‹Negative a›
      exact Nonzero.mk ‹SignedMagnitude a sqrt1_neg_one›

/--
Provide evidence that an integer is equivalent, or not equivalent, to zero.

**Property and proof intuition**: We already know from trichotomy of integers
that every integer is either zero, positive, or negative, and never more than
one of those at the same time. Combine the positive and negative categories to
obtain this result.
-/
theorem zero? (a : ℤ) : AA.ExactlyOneOfTwo (a ≃ 0) (Nonzero a) := by
  have tri : AA.ExactlyOneOfThree (a ≃ 0) (Positive a) (Negative a) :=
    Signed.trichotomy a
  apply And.intro
  case left =>
    show a ≃ 0 ∨ Nonzero a
    match tri.atLeastOne with
    | AA.OneOfThree.first (_ : a ≃ 0) =>
      exact Or.inl ‹a ≃ 0›
    | AA.OneOfThree.second (_ : Positive a) =>
      have : Nonzero a := nonzero_defn.mpr (Or.inl ‹Positive a›)
      exact Or.inr ‹Nonzero a›
    | AA.OneOfThree.third (_ : Negative a) =>
      have : Nonzero a := nonzero_defn.mpr (Or.inr ‹Negative a›)
      exact Or.inr ‹Nonzero a›
  case right =>
    intro (And.intro (_ : a ≃ 0) (_ : Nonzero a))
    show False
    apply tri.atMostOne
    show AA.TwoOfThree (a ≃ 0) (Positive a) (Negative a)
    have : Positive a ∨ Negative a := nonzero_defn.mp ‹Nonzero a›
    match ‹Positive a ∨ Negative a› with
    | Or.inl (_ : Positive a) =>
      exact AA.TwoOfThree.oneAndTwo ‹a ≃ 0› ‹Positive a›
    | Or.inr (_ : Negative a) =>
      exact AA.TwoOfThree.oneAndThree ‹a ≃ 0› ‹Negative a›

/--
The predicates `Nonzero` and `· ≄ 0` are equivalent characterizations of
integers.

**Proof intuition**: A simple corollary of
`AA.ExactlyOneOfTwo (a ≃ 0) (Nonzero a)`.
-/
theorem nonzero_iff_neqv_zero {a : ℤ} : Nonzero a ↔ a ≄ 0 := by
  have (And.intro (_ : a ≃ 0 ∨ Nonzero a) (_ : ¬(a ≃ 0 ∧ Nonzero a))) :=
    zero? a
  apply Iff.intro
  case mp =>
    intro (_ : Nonzero a) (_ : a ≃ 0)
    show False
    have : a ≃ 0 ∧ Nonzero a := And.intro ‹a ≃ 0› ‹Nonzero a›
    exact absurd ‹a ≃ 0 ∧ Nonzero a› ‹¬(a ≃ 0 ∧ Nonzero a)›
  case mpr =>
    intro (_ : a ≄ 0)
    show Nonzero a
    match ‹a ≃ 0 ∨ Nonzero a› with
    | Or.inl (_ : a ≃ 0) =>
      exact absurd ‹a ≃ 0› ‹a ≄ 0›
    | Or.inr (_ : Nonzero a) =>
      exact ‹Nonzero a›

/--
For a product of integers to be zero, at least one of its factors must be zero.

**Property and proof intuition**: This property alone is not very intuitive, or
at least the forward direction isn't. But eliminating the obvious cases where
either `a` or `b` are zero reduces the problem to showing that if `a` and `b`
are both nonzero, then their product must be nonzero as well. And that has some
intuitive justification; see `mul_preserves_nonzero`.
-/
theorem mul_split_zero {a b : ℤ} : a * b ≃ 0 ↔ a ≃ 0 ∨ b ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : a * b ≃ 0)
    show a ≃ 0 ∨ b ≃ 0
    have : a ≃ 0 ∨ Nonzero a := (zero? a).left
    match ‹a ≃ 0 ∨ Nonzero a› with
    | Or.inl (_ : a ≃ 0) =>
      exact Or.inl ‹a ≃ 0›
    | Or.inr (_ : Nonzero a) =>
      have : b ≃ 0 ∨ Nonzero b := (zero? b).left
      match ‹b ≃ 0 ∨ Nonzero b› with
      | Or.inl (_ : b ≃ 0) =>
        exact Or.inr ‹b ≃ 0›
      | Or.inr (_ : Nonzero b) =>
        apply False.elim
        show False
        have : ¬ (a * b ≃ 0 ∧ Nonzero (a * b)) := (zero? (a * b)).right
        apply this
        show a * b ≃ 0 ∧ Nonzero (a * b)
        apply And.intro
        · exact ‹a * b ≃ 0›
        · exact mul_preserves_nonzero ‹Nonzero a› ‹Nonzero b›
  case mpr =>
    intro (_ : a ≃ 0 ∨ b ≃ 0)
    show a * b ≃ 0
    match ‹a ≃ 0 ∨ b ≃ 0› with
    | Or.inl (_ : a ≃ 0) => calc
      a * b ≃ _ := AA.substL ‹a ≃ 0›
      0 * b ≃ _ := AA.absorbL
      0     ≃ _ := Rel.refl
    | Or.inr (_ : b ≃ 0) => calc
      a * b ≃ _ := AA.substR ‹b ≃ 0›
      a * 0 ≃ _ := AA.absorbR
      0     ≃ _ := Rel.refl

/--
If a product of integers is nonzero, then both factors must be nonzero.

**Property and proof intuition**: This follows immediately from the
contrapositive of the zero product property (`a ≃ 0 ∨ b ≃ 0 → a * b ≃ 0`).
-/
theorem nonzero_factors_if_nonzero_product
    {a b : ℤ} : Nonzero (a * b) → Nonzero a ∧ Nonzero b
    := by
  intro (_ : Nonzero (a * b))
  show Nonzero a ∧ Nonzero b
  have : a * b ≄ 0 := nonzero_iff_neqv_zero.mp ‹Nonzero (a * b)›
  have : ¬(a ≃ 0 ∨ b ≃ 0) := mt mul_split_zero.mpr ‹a * b ≄ 0›
  have (And.intro (_ : a ≄ 0) (_ : b ≄ 0)) :=
    not_or_iff_and_not.mp ‹¬(a ≃ 0 ∨ b ≃ 0)›
  have : Nonzero a := nonzero_iff_neqv_zero.mpr ‹a ≄ 0›
  have : Nonzero b := nonzero_iff_neqv_zero.mpr ‹b ≄ 0›
  exact And.intro ‹Nonzero a› ‹Nonzero b›

/--
The product of two integers is positive if and only if they have the same sign.

**Property intuition**: This really boils down to `1 * 1` and `-1 * -1` being
the only products of signs that result in `1`.

**Proof intuition**: The forward direction splits the product into its two
nonzero factors, and then accounts for all possible combinations of their
signs. The reverse direction follows easily from the fact that a sign squared
is always `1`.
-/
theorem positive_mul_iff_same_sqrt1
    {a b : ℤ} : Positive (a * b) ↔ SameSqrt1 a b
    := by
  let ab := a * b
  apply Iff.intro
  case mp =>
    intro (_ : Positive ab)
    show SameSqrt1 a b
    have : Nonzero ab := nonzero_defn.mpr (Or.inl ‹Positive ab›)
    have (And.intro (_ : Nonzero a) (_ : Nonzero b)) :=
      nonzero_factors_if_nonzero_product ‹Nonzero ab›
    have (Nonzero.intro _ sqrt1a (_ : SignedMagnitude a sqrt1a)) := ‹Nonzero a›
    have (Nonzero.intro _ sqrt1b (_ : SignedMagnitude b sqrt1b)) := ‹Nonzero b›
    have smac : SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one
      := signedMagnitude_cases ‹SignedMagnitude a sqrt1a›
    have smbc : SignedMagnitude b sqrt1_one ∨ SignedMagnitude b sqrt1_neg_one
      := signedMagnitude_cases ‹SignedMagnitude b sqrt1b›
    have : SameSqrt1 a b ∨ SignedMagnitude ab sqrt1_neg_one := match smac with
    | Or.inl (sm_a : SignedMagnitude a sqrt1_one) =>
      match smbc with
      | Or.inl (sm_b : SignedMagnitude b sqrt1_one) =>
        Or.inl (SameSqrt1.intro 1 sqrt1_one sm_a sm_b)
      | Or.inr (sm_b : SignedMagnitude b sqrt1_neg_one) =>
        have sqrt1 : SquareRootOfUnity (1 * -1) :=
          mul_preserves_sqrt1 sqrt1_one sqrt1_neg_one
        have sm_ab : SignedMagnitude ab sqrt1 :=
          mul_preserves_signedMagnitude sm_a sm_b
        have : SignedMagnitude ab sqrt1_neg_one :=
          signedMagnitude_sqrt1_subst AA.identL ‹SignedMagnitude ab sqrt1›
        Or.inr ‹SignedMagnitude ab sqrt1_neg_one›
    | Or.inr (sm_a : SignedMagnitude a sqrt1_neg_one) =>
      match smbc with
      | Or.inl (sm_b : SignedMagnitude b sqrt1_one) =>
        have sqrt1 : SquareRootOfUnity (-1 * 1) :=
          mul_preserves_sqrt1 sqrt1_neg_one sqrt1_one
        have sm_ab : SignedMagnitude ab sqrt1 :=
          mul_preserves_signedMagnitude sm_a sm_b
        have : SignedMagnitude ab sqrt1_neg_one :=
          signedMagnitude_sqrt1_subst AA.identR ‹SignedMagnitude ab sqrt1›
        Or.inr ‹SignedMagnitude ab sqrt1_neg_one›
      | Or.inr (sm_b : SignedMagnitude b sqrt1_neg_one) =>
        Or.inl (SameSqrt1.intro (-1) sqrt1_neg_one sm_a sm_b)
    match ‹SameSqrt1 a b ∨ SignedMagnitude ab sqrt1_neg_one› with
    | Or.inl (_ : SameSqrt1 a b) =>
      exact ‹SameSqrt1 a b›
    | Or.inr (_ : SignedMagnitude ab sqrt1_neg_one) =>
      have : Negative ab :=
        negative_defn.mpr ‹SignedMagnitude ab sqrt1_neg_one›
      have positive_and_negative : Positive ab ∧ Negative ab :=
        And.intro ‹Positive ab› ‹Negative ab›
      exact absurd positive_and_negative not_positive_and_negative
  case mpr =>
    intro (_ : SameSqrt1 a b)
    show Positive (a * b)
    have (SameSqrt1.intro
      (s : ℤ) (sqrt1 : SquareRootOfUnity s)
      (sm_a : SignedMagnitude a sqrt1) (sm_b : SignedMagnitude b sqrt1)) :=
        ‹SameSqrt1 a b›
    have : s * s ≃ 1 := sqrt1
    have : SquareRootOfUnity (s * s) := mul_preserves_sqrt1 sqrt1 sqrt1
    have sm_ab : SignedMagnitude (a * b) ‹SquareRootOfUnity (s * s)› :=
      mul_preserves_signedMagnitude sm_a sm_b
    have : SignedMagnitude (a * b) sqrt1_one :=
      signedMagnitude_sqrt1_subst ‹s * s ≃ 1› sm_ab
    have : Positive (a * b) :=
      positive_defn.mpr ‹SignedMagnitude (a * b) sqrt1_one›
    exact this

/--
The product of positive integers is positive.

**Property intuition**: Since this holds for natural numbers, it must hold for
integers as well.

**Proof intuition**: This is a corollary of the result that the product of
integers having the same sign is positive.
-/
theorem mul_preserves_positive
    {a b : ℤ} : Positive a → Positive b → Positive (a * b)
    := by
  intro (_ : Positive a) (_ : Positive b)
  show Positive (a * b)
  have sm_a : SignedMagnitude a sqrt1_one := positive_defn.mp ‹Positive a›
  have sm_b : SignedMagnitude b sqrt1_one := positive_defn.mp ‹Positive b›
  have : SameSqrt1 a b := SameSqrt1.intro 1 sqrt1_one sm_a sm_b
  have : Positive (a * b) := positive_mul_iff_same_sqrt1.mpr ‹SameSqrt1 a b›
  exact this

end Lean4Axiomatic.Integer

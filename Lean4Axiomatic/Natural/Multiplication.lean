import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Logic
import Lean4Axiomatic.Natural.Order
import Lean4Axiomatic.ClassicalAlgebra.MonoidOpsAsParams

/-!
# Natural number multiplication
-/

namespace Lean4Axiomatic.Natural

open Signed (Positive positive_defn)

/-!
## Axioms
-/

/--
Definition of multiplication, and properties that it must satisfy.

All other properties of multiplication can be derived from these.
-/
class Multiplication (ℕ : Type) [Core ℕ] [Addition ℕ] where
  /-- Definition of and syntax for multiplication. -/
  mulOp : Mul ℕ

  /-- Multiplying by zero on the left always gives zero. -/
  zero_mul {m : ℕ} : 0 * m ≃ 0

  /--
  Take a product and increment the left-hand factor. This gives the same result
  as adding a copy of the right-hand factor to the original product.
  -/
  step_mul {n m : ℕ} : step n * m ≃ (n * m) + m

attribute [instance] Multiplication.mulOp

export Multiplication (mulOp step_mul zero_mul)

/-!
## Derived properties
-/

variable {ℕ : Type} [Core ℕ] [Addition ℕ] [Multiplication ℕ] [Induction.{0} ℕ]

/--
Multiplying by zero on the right always gives zero.

Intuition: the multiplication `count * value` is defined as `count` copies of
`value` added together. So `n * 0` is `n` copies of `0` added together, which
by properties of addition must always give `0`.
-/
theorem mul_zero {n : ℕ} : n * 0 ≃ 0 := by
  apply ind_on (motive := λ x => x * 0 ≃ 0) n
  case zero =>
    show 0 * 0 ≃ 0
    exact zero_mul
  case step =>
    intro n (ih : n * 0 ≃ 0)
    show step n * 0 ≃ 0
    calc
      step n * 0 ≃ _ := step_mul
      n * 0 + 0  ≃ _ := by srw [ih]
      0 + 0      ≃ _ := Addition.zero_add
      0          ≃ _ := Rel.refl

instance mul_absorbing : AA.Absorbing (α := ℕ) 0 (· * ·) := {
  absorbingL := AA.AbsorbingOn.mk zero_mul
  absorbingR := AA.AbsorbingOn.mk mul_zero
}

/--
Take a product and increment the right-hand factor. This gives the same result
as adding a copy of the left-hand factor to the original product.

This is a key lemma towards proving the commutativity of multiplication. Even
though multiplication is defined as `count * value`, this result shows that it
works just as well to swap the roles of `count` and `value`.

Intuition: `n` copies of `step m` added together can be rearranged into the sum
of `n` copies of `m`, plus the sum of `n` copies of `1`. Since adding `n`
copies of `1` together is just `n`, the whole result is `n * m + n`.
-/
theorem mul_step {n m : ℕ} : n * step m ≃ n * m + n := by
  apply ind_on (motive := λ x => x * step m ≃ x * m + x) n
  case zero =>
    show 0 * step m ≃ 0 * m + 0
    calc
      0 * step m ≃ _ := zero_mul
      0          ≃ _ := Rel.symm Addition.zero_add
      0 + 0      ≃ _ := by srw [←zero_mul]
      0 * m + 0  ≃ _ := Rel.refl
  case step =>
    intro n (ih : n * step m ≃ n * m + n)
    show step n * step m ≃ step n * m + step n
    calc
      step n * step m        ≃ _ := step_mul
      n * step m + step m    ≃ _ := by srw [ih]
      (n * m + n) + step m   ≃ _ := add_step
      step ((n * m + n) + m) ≃ _ := by srw [AA.assoc]
      step (n * m + (n + m)) ≃ _ := by srw [AA.comm]
      step (n * m + (m + n)) ≃ _ := by srw [←AA.assoc]
      step ((n * m + m) + n) ≃ _ := by srw [←step_mul]
      step (step n * m + n)  ≃ _ := Rel.symm add_step
      step n * m + step n    ≃ _ := Rel.refl

/--
The order of the factors in a product doesn't matter.

Intuition: combine the results from `mul_zero` and `mul_step`.
-/
theorem mul_comm {n m : ℕ} : n * m ≃ m * n := by
  apply ind_on (motive := λ x => x * m ≃ m * x) n
  case zero =>
    show 0 * m ≃ m * 0
    calc
      0 * m ≃ _ := zero_mul
      0     ≃ _ := Rel.symm mul_zero
      m * 0 ≃ _ := Rel.refl
  case step =>
    intro n (ih : n * m ≃ m * n)
    show step n * m ≃ m * step n
    calc
      step n * m ≃ _ := step_mul
      n * m + m  ≃ _ := by srw [ih]
      m * n + m  ≃ _ := Rel.symm mul_step
      m * step n ≃ _ := Rel.refl

instance mul_commutative : AA.Commutative (α := ℕ) (· * ·) := {
  comm := mul_comm
}

/--
Multiplication by a fixed value as the right-hand operand preserves equality.

Intuition: addition preserves equality; multiplication is repeated addition.
-/
@[gcongr]
theorem mul_substL_eqv {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ * m ≃ n₂ * m := by
  apply ind_on (motive := λ x => ∀ y, x ≃ y → x * m ≃ y * m) n₁
  case zero =>
    intro n₂
    show 0 ≃ n₂ → 0 * m ≃ n₂ * m
    apply cases_on (motive := λ y => 0 ≃ y → 0 * m ≃ y * m)
    case zero =>
      intro (_ : 0 ≃ (0 : ℕ))
      show 0 * m ≃ 0 * m
      exact Rel.refl
    case step =>
      intro n₂ (_ : 0 ≃ step n₂)
      exact absurd (Rel.symm ‹0 ≃ step n₂›) step_neqv_zero
  case step =>
    intro n₁ (ih : ∀ y, n₁ ≃ y → n₁ * m ≃ y * m) n₂
    show step n₁ ≃ n₂ → step n₁ * m ≃ n₂ * m
    apply cases_on (motive := λ y => step n₁ ≃ y → step n₁ * m ≃ y * m)
    case zero =>
      intro (_ : step n₁ ≃ 0)
      exact absurd ‹step n₁ ≃ 0› step_neqv_zero
    case step =>
      intro n₂ (_ : step n₁ ≃ step n₂)
      show step n₁ * m ≃ step n₂ * m
      have : n₁ ≃ n₂ := AA.inject ‹step n₁ ≃ step n₂›
      have : n₁ * m ≃ n₂ * m := ih n₂ ‹n₁ ≃ n₂›
      calc
        step n₁ * m  ≃ _ := step_mul
        (n₁ * m) + m ≃ _ := by srw [‹n₁ * m ≃ n₂ * m›]
        (n₂ * m) + m ≃ _ := Rel.symm step_mul
        step n₂ * m  ≃ _ := Rel.refl

/--
Multiplication by a fixed value as the left-hand operand preserves equality.

Intuition: addition preserves equality; multiplication is repeated addition.
-/
@[gcongr]
theorem mul_substR_eqv {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → m * n₁ ≃ m * n₂ := by
  intro (_ : n₁ ≃ n₂)
  show m * n₁ ≃ m * n₂
  calc
    _ = m * n₁ := rfl
    _ ≃ n₁ * m := mul_comm
    _ ≃ n₂ * m := by srw [‹n₁ ≃ n₂›]
    _ ≃ m * n₂ := mul_comm

instance mul_substitutive_eqv
    : AA.Substitutive₂ (α := ℕ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => mul_substL_eqv }
  substitutiveR := { subst₂ := λ (_ : True) => mul_substR_eqv }
}

/--
A product is zero iff at least one of its factors is zero.

Intuition
- forwards: if one factor is nonzero, then the product is a nonempty sum that
  results in zero. By `Addition.zero_sum_split`, the terms of the sum must be
  zero.
- backwards: by `Base.zero_mul` or `Derived.mul_zero`.
-/
theorem mul_split_zero {n m : ℕ} : n * m ≃ 0 ↔ n ≃ 0 ∨ m ≃ 0 := by
  apply Iff.intro
  · show n * m ≃ 0 → n ≃ 0 ∨ m ≃ 0
    apply cases_on (motive := λ x => x * m ≃ 0 → x ≃ 0 ∨ m ≃ 0) n
    case zero =>
      intro (_ : 0 * m ≃ 0)
      show 0 ≃ 0 ∨ m ≃ 0
      exact Or.inl Rel.refl
    case step =>
      intro n (_ : step n * m ≃ 0)
      show step n ≃ 0 ∨ m ≃ 0
      apply Or.inr
      show m ≃ 0
      have : n * m + m ≃ 0 := calc
        n * m + m  ≃ _ := Rel.symm step_mul
        step n * m ≃ _ := ‹step n * m ≃ 0›
        0          ≃ _ := Rel.refl
      have (And.intro _ (_ : m ≃ 0)) := zero_sum_split.mp ‹n * m + m ≃ 0›
      exact ‹m ≃ 0›
  · intro (_ : n ≃ 0 ∨ m ≃ 0)
    show n * m ≃ 0
    apply Or.elim ‹n ≃ 0 ∨ m ≃ 0›
    · intro (_ : n ≃ 0)
      show n * m ≃ 0
      calc
        n * m ≃ _ := by srw [‹n ≃ 0›]
        0 * m ≃ _ := zero_mul
        0     ≃ _ := Rel.refl
    · intro (_ : m ≃ 0)
      show n * m ≃ 0
      calc
        n * m ≃ _ := by srw [‹m ≃ 0›]
        n * 0 ≃ _ := mul_zero
        0     ≃ _ := Rel.refl

/-- Natural numbers satisfy the zero-product property. -/
instance zero_product_inst : AA.ZeroProduct (α := ℕ) (· * ·) := {
  zero_prod := mul_split_zero.mp
}

/--
Multiplication on the left distributes over addition.

**Intuition**: Viewing `a * b` as the sum of `a` copies of `b`, this theorem
says that the sum of `n` copies of `m + k` is the same as the sum of `n` copies
of `m` added to the sum of `n` copies of `k`. Using the commutativity and
associativity of addition to rearrange the sums shows this is clearly true.
-/
theorem mul_distribL_add {n m k : ℕ} : n * (m + k) ≃ n * m + n * k := by
  apply ind_on (motive := λ x => x * (m + k) ≃ x * m + x * k) n
  case zero =>
    show 0 * (m + k) ≃ 0 * m + 0 * k
    calc
      _ = 0 * (m + k)   := rfl
      _ ≃ 0             := zero_mul
      _ ≃ 0 + 0         := Rel.symm zero_add
      _ ≃ 0 * m + 0     := by srw [←zero_mul]
      _ ≃ 0 * m + 0 * k := by srw [←zero_mul]
  case step =>
    intro n (ih : n * (m + k) ≃ n * m + n * k)
    show step n * (m + k) ≃ step n * m + step n * k
    calc
      _ = step n * (m + k)          := rfl
      _ ≃ n * (m + k) + (m + k)     := step_mul
      _ ≃ n * m + n * k + (m + k)   := by srw [ih]
      _ ≃ n * m + (n * k + (m + k)) := AA.assoc
      _ ≃ n * m + ((n * k + m) + k) := by srw [←AA.assoc]
      _ ≃ n * m + ((m + n * k) + k) := by srw [AA.comm]
      _ ≃ n * m + (m + (n * k + k)) := by srw [AA.assoc]
      _ ≃ (n * m + m) + (n * k + k) := Rel.symm AA.assoc
      _ ≃ step n * m + step n * k   := by srw [←step_mul, ←step_mul]

/--
Multiplication on the right distributes over addition.

**Intuition**: Use commutativity and left distributivity.
-/
theorem mul_distribR_add {n m k : ℕ} : (m + k) * n ≃ m * n + k * n := calc
  _ = (m + k) * n   := rfl
  _ ≃ n * (m + k)   := mul_comm
  _ ≃ n * m + n * k := mul_distribL_add
  _ ≃ m * n + k * n := by srw [mul_comm, mul_comm]

instance mul_distributive : AA.Distributive (α := ℕ) (· * ·) (· + ·) := {
  distributiveL := { distrib := mul_distribL_add }
  distributiveR := { distrib := mul_distribR_add }
}

/--
The natural number `1` is a left multiplicative identity element.

**Property intuition**: A sum of a single instance of a number should be equal
to that number.

**Proof intuition**: Expand the definition of multiplication into addition to
see that multiplying by one is the same as adding zero.
-/
theorem mul_identL {n : ℕ} : 1 * n ≃ n := calc
  1 * n      ≃ _ := by srw [Literals.literal_step]
  step 0 * n ≃ _ := step_mul
  0 * n + n  ≃ _ := by srw [zero_mul]
  0 + n      ≃ _ := AA.identL
  n          ≃ _ := Rel.refl

/--
The natural number `1` is a right multiplicative identity element.

**Intuition**: Multiplication has a left identity element, and is commutative.
-/
theorem mul_identR {n : ℕ} : n * 1 ≃ n := calc
  _ = n * 1 := rfl
  _ ≃ 1 * n := mul_comm
  _ ≃ n     := mul_identL

instance mul_identity : AA.Identity (α := ℕ) 1 (· * ·) := {
  identityL := { ident := mul_identL }
  identityR := { ident := mul_identR }
}

/--
The grouping of the factors in a product doesn't matter.

**Intuition**: Imagine a collection of identical objects arranged into a
rectangle `n * m` objects long and `k` objects high. Partition this into `m`
smaller rectangles having length `n` and height `k`. Clearly the number of
objects remains the same in both arrangements.
-/
theorem mul_assoc {n m k : ℕ} : (n * m) * k ≃ n * (m * k) := by
  apply ind_on (motive := λ x => (x * m) * k ≃ x * (m * k))
  case zero =>
    show (0 * m) * k ≃ 0 * (m * k)
    calc
      (0 * m) * k ≃ _ := by srw [zero_mul]
      0 * k       ≃ _ := zero_mul
      0           ≃ _ := Rel.symm zero_mul
      0 * (m * k) ≃ _ := Rel.refl
  case step =>
    intro n (ih : (n * m) * k ≃ n * (m * k))
    show (step n * m) * k ≃ step n * (m * k)
    calc
      (step n * m) * k    ≃ _ := by srw [step_mul]
      (n * m + m) * k     ≃ _ := AA.distribR
      (n * m) * k + m * k ≃ _ := by srw [ih]
      n * (m * k) + m * k ≃ _ := Rel.symm step_mul
      step n * (m * k)    ≃ _ := Rel.refl

instance mul_associative : AA.Associative (α := ℕ) (· * ·) := {
  assoc := mul_assoc
}

variable [Sign ℕ]

/--
A product is positive iff both of its factors are positive.

**Property and proof intuition**: If either factor was zero, the product would
have to be zero as well, due to `mul_split_zero`.
-/
theorem mul_preserves_positive
    {n m : ℕ} : Positive (n * m) ↔ Positive n ∧ Positive m
    := by
  apply Iff.intro
  case mp =>
    intro (_ : Positive (n * m))
    show Positive n ∧ Positive m
    have : n * m ≄ 0 := positive_defn.mp ‹Positive (n * m)›
    have : ¬(n ≃ 0 ∨ m ≃ 0) := mt mul_split_zero.mpr this
    have (And.intro (_ : n ≄ 0) (_ : m ≄ 0)) :=
      Logic.not_or_iff_and_not.mp this
    have : Positive n := positive_defn.mpr ‹n ≄ 0›
    have : Positive m := positive_defn.mpr ‹m ≄ 0›
    exact And.intro ‹Positive n› ‹Positive m›
  case mpr =>
    intro (And.intro (_ : Positive n) (_ : Positive m))
    show Positive (n * m)
    have : n ≄ 0 := positive_defn.mp ‹Positive n›
    have : m ≄ 0 := positive_defn.mp ‹Positive m›
    have : n ≄ 0 ∧ m ≄ 0 := And.intro ‹n ≄ 0› ‹m ≄ 0›
    have : ¬(n ≃ 0 ∨ m ≃ 0) := Logic.not_or_iff_and_not.mpr this
    have : n * m ≄ 0 := mt mul_split_zero.mp this
    have : Positive (n * m) := positive_defn.mpr this
    exact this

/--
The product of positive natural numbers is positive.

Corollary of `mul_preserves_positive` that curries the hypotheses for
convenience.
-/
theorem mul_positive {n m : ℕ}
    : Positive n → Positive m → Positive (n * m) := by
  intro (_ : Positive n) (_ : Positive m)
  show Positive (n * m)
  exact mul_preserves_positive.mpr (And.intro ‹Positive n› ‹Positive m›)

variable [Order ℕ]

/--
Multiplication on the right by a positive natural number preserves the strict
ordering of any two natural numbers.

**Proof intuition**: two strictly ordered natural numbers have a positive
difference between them. Multiplying them by another positive natural number
also multiplies their difference, which remains positive.
-/
@[gcongr]
theorem mul_substL_lt
    {n₁ n₂ m : ℕ} : Positive m → n₁ < n₂ → n₁ * m < n₂ * m
    := by
  intro (_ : Positive m) (_ : n₁ < n₂)
  show n₁ * m < n₂ * m
  have ⟨(d : ℕ), (_ : Positive d), (_ : n₂ ≃ n₁ + d)⟩ :=
    lt_defn_add.mp ‹n₁ < n₂›
  have : n₂ * m ≃ n₁ * m + d * m := calc
    n₂ * m         ≃ _ := by srw [‹n₂ ≃ n₁ + d›]
    (n₁ + d) * m   ≃ _ := AA.distribR
    n₁ * m + d * m ≃ _ := Rel.refl
  have : Positive (d * m) := mul_positive ‹Positive d› ‹Positive m›
  exact lt_defn_add.mpr
    ⟨d * m, ‹Positive (d * m)›, ‹n₂ * m ≃ n₁ * m + d * m›⟩

/--
Multiplication on the left by a positive natural number preserves the strict
ordering of any two natural numbers.
-/
@[gcongr]
theorem mul_substR_lt
    {n₁ n₂ m : ℕ} : Positive m → n₁ < n₂ → m * n₁ < m * n₂
    := by
  intro (_ : Positive m) (_ : n₁ < n₂)
  show m * n₁ < m * n₂
  calc
    _ = m * n₁ := rfl
    _ ≃ n₁ * m := mul_comm
    _ < n₂ * m := by srw [‹n₁ < n₂›]
    _ ≃ m * n₂ := mul_comm

instance mul_substitutive_lt
    : AA.Substitutive₂ (α := ℕ) (· * ·) Positive (· < ·) (· < ·)
    := {
  substitutiveL := { subst₂ := mul_substL_lt }
  substitutiveR := { subst₂ := mul_substR_lt }
}

/--
Multiplication on the left by a nonzero natural number is an injection.

**Proof intuition**: If one of the right-hand factors is greater than the other,
then multiplying them both by a nonzero (i.e., positive) natural number will
preserve their ordering (by `mul_substitutive_lt`), contradicting the hypothesis
that the products are equal. Thus the right-hand factors must be equal.
-/
def mul_cancelL
    : AA.CancellativeOn Hand.L (α := ℕ) (· * ·) (· ≄ 0) (· ≃ ·) (· ≃ ·)
    := by
  apply AA.CancellativeOn.mk
  intro x y₁ y₂ (_ : x ≄ 0) (_ : x * y₁ ≃ x * y₂)
  show y₁ ≃ y₂
  have : Positive x := Signed.positive_defn.mpr ‹x ≄ 0›
  have notTwoOfThree := (trichotomy (x * y₁) (x * y₂)).atMostOne
  match (trichotomy y₁ y₂).atLeastOne with
  | AA.OneOfThree.first (_ : y₁ < y₂) =>
    have : x * y₁ < x * y₂ := by srw [‹y₁ < y₂›]
    have twoOfThree :=
      AA.TwoOfThree.oneAndTwo
        (γ := x * y₁ > x * y₂) ‹x * y₁ < x * y₂› ‹x * y₁ ≃ x * y₂›
    exact absurd twoOfThree notTwoOfThree
  | AA.OneOfThree.second (_ : y₁ ≃ y₂) =>
    exact ‹y₁ ≃ y₂›
  | AA.OneOfThree.third (_ : y₁ > y₂) =>
    have : y₂ < y₁ := ‹y₁ > y₂›
    have : x * y₂ < x * y₁ := by srw [‹y₂ < y₁›]
    have twoOfThree :=
      AA.TwoOfThree.twoAndThree
        (α := x * y₁ < x * y₂) ‹x * y₁ ≃ x * y₂› ‹x * y₂ < x * y₁›
    exact absurd twoOfThree notTwoOfThree

instance mul_cancellative
    : AA.Cancellative (α := ℕ) (· * ·) (· ≄ 0) (· ≃ ·) (· ≃ ·)
    := {
  cancellativeL := mul_cancelL
  cancellativeR := AA.cancelR_from_cancelL mul_cancelL
}

/--
The only way that two natural numbers can multiply to one is if they are both
one as well.

**Property and proof intuition**: If a factor was zero, the product would be
zero; if a factor was greater than one, the product would be greater than one.
-/
theorem factors_eqv_1 {n m : ℕ} : n * m ≃ 1 ↔ n ≃ 1 ∧ m ≃ 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : n * m ≃ 1)
    show n ≃ 1 ∧ m ≃ 1
    have : Positive (n * m) := by prw [←‹n * m ≃ 1›] one_positive
    have (And.intro (_ : Positive n) (_ : Positive m)) :=
      mul_preserves_positive.mp this
    have : n ≥ 1 := positive_ge.mp ‹Positive n›
    have : n > 1 ∨ n ≃ 1 := ge_split this
    match this with
    | Or.inl (_ : n > 1) =>
      have : 1 < n * m := calc
        1     ≤ _ := positive_ge.mp ‹Positive m›
        m     ≃ _ := Rel.symm AA.identL
        1 * m < _ := by srw [‹1 < n›]
        n * m ≃ _ := Rel.refl
      have two : AA.TwoOfThree (n * m < 1) (n * m ≃ 1) (n * m > 1) :=
        AA.TwoOfThree.twoAndThree ‹n * m ≃ 1› ‹n * m > 1›
      have notTwo : ¬AA.TwoOfThree (n * m < 1) (n * m ≃ 1) (n * m > 1) :=
        (trichotomy (n * m) 1).atMostOne
      exact absurd two notTwo
    | Or.inr (_ : n ≃ 1) =>
      have : m ≃ 1 := calc
        m     ≃ _ := Rel.symm AA.identL
        1 * m ≃ _ := by srw [←‹n ≃ 1›]
        n * m ≃ _ := ‹n * m ≃ 1›
        1     ≃ _ := Rel.refl
      exact And.intro ‹n ≃ 1› ‹m ≃ 1›
  case mpr =>
    intro (And.intro (_ : n ≃ 1) (_ : m ≃ 1))
    show n * m ≃ 1
    calc
      n * m ≃ _ := by srw [‹n ≃ 1›]
      1 * m ≃ _ := AA.identL
      m     ≃ _ := ‹m ≃ 1›
      1     ≃ _ := Rel.refl

/--
The only square root of unity in the natural numbers is `1`.

This is a corollary of `factors_eqv_1`.
-/
theorem sqrt1 {n : ℕ} : n * n ≃ 1 ↔ n ≃ 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : n * n ≃ 1)
    show n ≃ 1
    have (And.intro (_ : n ≃ 1) _) := factors_eqv_1.mp ‹n * n ≃ 1›
    exact ‹n ≃ 1›
  case mpr =>
    intro (_ : n ≃ 1)
    show n * n ≃ 1
    have : n * n ≃ 1 := factors_eqv_1.mpr (And.intro ‹n ≃ 1› ‹n ≃ 1›)
    exact this

def mul_monoid_props : CA.Monoid.Props (α := ℕ) (· * ·) 1 := {
  substL  := AA.substL
  substR  := AA.substR
  assoc   := mul_associative.assoc
  identL  := AA.identL
  identR  := AA.identR
}

/--
Naturals numbers with multiplication form a monoid.  This allow us to avoid
reproving basic facts about naturals that are true of all monoids.
-/
instance mul_monoid : CA.Monoid.Monoid (α := ℕ) (· * ·) 1 := {
  toProps := mul_monoid_props
}

end Lean4Axiomatic.Natural

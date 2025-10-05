import Lean4Axiomatic.Natural.Core
import Lean4Axiomatic.ClassicalAlgebra.MonoidOpsAsParams

/-!
# Natural number addition
-/

namespace Lean4Axiomatic.Natural

/-!
## Axioms
-/

/--
Definition of addition, and properties that it must satisfy.

All other properties of addition can be derived from these.
-/
class Addition (ℕ : Type) [Core ℕ] where
  /-- Definition of and syntax for addition. -/
  addOp : Add ℕ

  /-- Adding zero to any natural number (on the left) leaves it unchanged. -/
  zero_add {m : ℕ} : 0 + m ≃ m

  /-- Incrementing the left term in a sum increments the result. -/
  step_add {n m : ℕ} : step n + m ≃ step (n + m)

attribute [instance] Addition.addOp

export Addition (addOp step_add zero_add)

/-!
## Derived properties
-/

variable {ℕ : Type} [Core ℕ] [Induction.{0} ℕ] [Addition ℕ]

/-- Adding zero to any natural number (on the right) leaves it unchanged. -/
theorem add_zero {n : ℕ} : n + 0 ≃ n := by
  apply ind_on (motive := λ n => n + 0 ≃ n) n
  case zero =>
    show 0 + 0 ≃ 0
    calc
      0 + (0 : ℕ) ≃ _ := zero_add
      0           ≃ _ := Rel.refl
  case step =>
    intro n (ih : n + 0 ≃ n)
    show step n + 0 ≃ step n
    calc
      _ = step n + 0   := rfl
      _ ≃ step (n + 0) := step_add
      _ ≃ step n       := by srw [ih]

instance add_identity : AA.Identity (α := ℕ) 0 (· + ·) := {
  identityL := AA.IdentityOn.mk zero_add
  identityR := AA.IdentityOn.mk add_zero
}

/-- Convenience lemma for several integer proofs. -/
theorem add_swapped_zeros_eqv {n m : ℕ} : n + 0 ≃ 0 + m ↔ n ≃ m := by
  apply Iff.intro
  case mp =>
    intro (_ : n + 0 ≃ 0 + m)
    show n ≃ m
    calc
      n     ≃ _ := Rel.symm AA.identR
      n + 0 ≃ _ := ‹n + 0 ≃ 0 + m›
      0 + m ≃ _ := AA.identL
      m     ≃ _ := Rel.refl
  case mpr =>
    intro (_ : n ≃ m)
    show n + 0 ≃ 0 + m
    calc
      n + 0 ≃ _ := AA.identR
      n     ≃ _ := ‹n ≃ m›
      m     ≃ _ := Rel.symm AA.identL
      0 + m ≃ _ := Rel.refl

/-- Incrementing the right term in a sum increments the result. -/
theorem add_step {n m : ℕ} : n + step m ≃ step (n + m) := by
  apply ind_on (motive := λ n => n + step m ≃ step (n + m)) n
  case zero =>
    show 0 + step m ≃ step (0 + m)
    calc
      _ = 0 + step m   := rfl
      _ ≃ step m       := zero_add
      _ ≃ step (0 + m) := by srw [←zero_add]
  case step =>
    intro n (ih : n + step m ≃ step (n + m))
    show step n + step m ≃ step (step n + m)
    calc
      _ = step n + step m     := rfl
      _ ≃ step (n + step m)   := step_add
      _ ≃ step (step (n + m)) := by srw [ih]
      _ ≃ step (step n + m)   := by srw [←step_add]

instance add_semicompatible_step : AA.Semicompatible (α := ℕ) step (· + ·) := {
  semicompatibleL := AA.SemicompatibleOn.mk (Rel.symm step_add)
  semicompatibleR := AA.SemicompatibleOn.mk (Rel.symm add_step)
}

/--
The `step` operation can be exchanged between the operands of an addition.

**Property intuition**: It doesn't matter which operand is incremented; the
result will be the same.

**Proof intuition**: Use `step_add` and `add_step` to bring the increment to
the outside of the sum and then back to the other operand.
-/
theorem step_add_swap {n m : ℕ} : step n + m ≃ n + step m := calc
  step n + m   ≃ _ := step_add
  step (n + m) ≃ _ := Rel.symm add_step
  n + step m   ≃ _ := Rel.refl

/-- Exchanging the operands of an addition does not change the result. -/
theorem add_comm {n m : ℕ} : n + m ≃ m + n := by
  apply ind_on (motive := λ n => n + m ≃ m + n) n
  case zero =>
    show 0 + m ≃ m + 0
    calc
      0 + m ≃ _ := zero_add
      m     ≃ _ := Rel.symm add_zero
      m + 0 ≃ _ := Rel.refl
  case step =>
    intro n (ih : n + m ≃ m + n)
    show step n + m ≃ m + step n
    calc
      step n + m   ≃ _ := step_add
      step (n + m) ≃ _ := by srw [ih]
      step (m + n) ≃ _ := Rel.symm add_step
      m + step n   ≃ _ := Rel.refl

instance add_commutative : AA.Commutative (α := ℕ) (· + ·) := {
  comm := add_comm
}

/--
Addition preserves equivalence of natural numbers; two equivalent natural
numbers are still equivalent after the same quantity is added to both (on the
right).
-/
@[gcongr]
theorem add_substL {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ + m ≃ n₂ + m := by
  apply ind_on (motive := λ x => ∀ y, x ≃ y → x + m ≃ y + m) n₁
  case zero =>
    intro n₂
    show 0 ≃ n₂ → 0 + m ≃ n₂ + m
    apply cases_on (motive := λ y => 0 ≃ y → 0 + m ≃ y + m)
    case zero =>
      intro (_ : 0 ≃ (0 : ℕ))
      show 0 + m ≃ 0 + m
      exact Rel.refl
    case step =>
      intro n₂ (_ : 0 ≃ step n₂)
      exact absurd (Rel.symm ‹0 ≃ step n₂›) step_neqv_zero
  case step =>
    intro n₁ (ih : ∀ y, n₁ ≃ y → n₁ + m ≃ y + m) n₂
    show step n₁ ≃ n₂ → step n₁ + m ≃ n₂ + m
    apply cases_on (motive := λ y => step n₁ ≃ y → step n₁ + m ≃ y + m)
    case zero =>
      intro (_ : step n₁ ≃ 0)
      show step n₁ + m ≃ 0 + m
      exact absurd ‹step n₁ ≃ 0› step_neqv_zero
    case step =>
      intro n₂ (_ : step n₁ ≃ step n₂)
      show step n₁ + m ≃ step n₂ + m
      have : n₁ ≃ n₂ := AA.inject ‹step n₁ ≃ step n₂›
      calc
        step n₁ + m   ≃ _ := step_add
        step (n₁ + m) ≃ _ := by srw [ih _ ‹n₁ ≃ n₂›]
        step (n₂ + m) ≃ _ := Rel.symm step_add
        step n₂ + m   ≃ _ := Rel.refl

/--
Addition preserves equivalence of natural numbers; two equivalent natural
numbers are still equivalent after the same quantity is added to both (on the
left).
-/
@[gcongr]
theorem add_substR {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → m + n₁ ≃ m + n₂ := by
  intro (_ : n₁ ≃ n₂)
  show m + n₁ ≃ m + n₂
  calc
    _ = m + n₁ := rfl
    _ ≃ n₁ + m := add_comm
    _ ≃ n₂ + m := by srw [‹n₁ ≃ n₂›]
    _ ≃ m + n₂ := add_comm

instance add_substitutive
    : AA.Substitutive₂ (α := ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => add_substL }
  substitutiveR := { subst₂ := λ (_ : True) => add_substR }
}

/-- Adding one is the same as incrementing. -/
theorem add_one_step {n : ℕ} : n + 1 ≃ step n := by
  calc
    n + 1        ≃ _ := by srw [Literals.literal_step]
    n + step 0   ≃ _ := add_step
    step (n + 0) ≃ _ := by srw [add_zero]
    step n       ≃ _ := Rel.refl

/--
One plus one is two.

**Property and proof intuition**: Two is defined to be the successor of one.
Adding one is equivalent to the successor function.
-/
theorem add_one_one : (1:ℕ) + 1 ≃ 2 := calc
  _ ≃ (1:ℕ) + 1 := Rel.refl
  _ ≃ step 1    := add_one_step
  _ ≃ 2         := Rel.symm literal_step

/--
The grouping of the terms in a sum doesn't matter.

**Intuition**: the `step_add` and `add_step` properties allow `step`s to be
moved arbitrarily between terms. Given any particular grouping of a sum, all of
the `step`s can be moved over to the first term, always producing the same
result.
-/
theorem add_assoc {n m k : ℕ} : (n + m) + k ≃ n + (m + k) := by
  apply ind_on (motive := λ n => (n + m) + k ≃ n + (m + k)) n
  case zero =>
    show (0 + m) + k ≃ 0 + (m + k)
    calc
      (0 + m) + k ≃ _ := by srw [zero_add]
      m + k       ≃ _ := Rel.symm zero_add
      0 + (m + k) ≃ _ := Rel.refl
  case step =>
    intro n (ih : (n + m) + k ≃ n + (m + k))
    show (step n + m) + k ≃ step n + (m + k)
    calc
      (step n + m) + k   ≃ _ := by srw [step_add]
      step (n + m) + k   ≃ _ := step_add
      step ((n + m) + k) ≃ _ := by srw [ih]
      step (n + (m + k)) ≃ _ := Rel.symm step_add
      step n + (m + k)   ≃ _ := Rel.refl

instance add_associative : AA.Associative (α := ℕ) (· + ·) := {
  assoc := add_assoc
}

/--
The right-hand sides of two equal sums are equal if their left-hand sides are.

**Proof intuition**: the left-hand sides can be removed one `step` at a time by
applying `step_injective` and finally `zero_add`, leaving the desired result.
-/
theorem cancel_add {n m k : ℕ} : n + m ≃ n + k → m ≃ k := by
  apply ind_on (motive := λ n => n + m ≃ n + k → m ≃ k) n
  case zero =>
    intro (_ : 0 + m ≃ 0 + k)
    show m ≃ k
    calc
      m     ≃ _ := Rel.symm zero_add
      0 + m ≃ _ := ‹0 + m ≃ 0 + k›
      0 + k ≃ _ := zero_add
      k     ≃ _ := Rel.refl
  case step =>
    intro n (ih : n + m ≃ n + k → m ≃ k) (_ : step n + m ≃ step n + k)
    show m ≃ k
    apply ih
    show n + m ≃ n + k
    apply AA.inject (β := ℕ) (f := step) (rβ := (· ≃ ·))
    show step (n + m) ≃ step (n + k)
    calc
      step (n + m) ≃ _ := Rel.symm step_add
      step n + m   ≃ _ := ‹step n + m ≃ step n + k›
      step n + k   ≃ _ := step_add
      step (n + k) ≃ _ := Rel.refl

def add_cancelL
    : AA.CancellativeOn Hand.L (α := ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  cancel := λ (_ : True) => cancel_add
}

instance add_cancellative
    : AA.Cancellative (α := ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  cancellativeL := add_cancelL
  cancellativeR := AA.cancelR_from_cancelL add_cancelL
}

/--
The only way to have two natural numbers that sum to zero is if both of them
are themselves zero.

**Property intuition**: Zero is the smallest natural number; including it in a
sum doesn't increase the result, unlike all non-zero naturals.

**Proof intuition**: The forward direction is a case analysis on the sum's
first operand. When it's zero, the second operand must also be zero. When it's
`step` of some other natural, the result must also contain `step`, which
contradicts the assumption that the result is zero. The reverse direction holds
because zero is the additive identity.
-/
theorem zero_sum_split {n m : ℕ} : n + m ≃ 0 ↔ n ≃ 0 ∧ m ≃ 0 := by
  apply Iff.intro
  case mp =>
    apply cases_on (motive := λ x => x + m ≃ 0 → x ≃ 0 ∧ m ≃ 0) n
    case zero =>
      intro (_ : 0 + m ≃ 0)
      show 0 ≃ 0 ∧ m ≃ 0
      have : m ≃ 0 := calc
        _ = m     := rfl
        _ ≃ 0 + m := Rel.symm zero_add
        _ ≃ 0     := ‹0 + m ≃ 0›
      exact And.intro Rel.refl ‹m ≃ 0›
    case step =>
      intro k (_ : step k + m ≃ 0)
      show step k ≃ 0 ∧ m ≃ 0
      have : step (k + m) ≃ 0 := calc
        _ = step (k + m) := rfl
        _ ≃ step k + m   := Rel.symm step_add
        _ ≃ 0            := ‹step k + m ≃ 0›
      have : step (k + m) ≄ 0 := step_neqv_zero
      exact absurd ‹step (k + m) ≃ 0› ‹step (k + m) ≄ 0›
  case mpr =>
    intro (And.intro (_ : n ≃ 0) (_ : m ≃ 0))
    show n + m ≃ 0
    calc
      _ = n + m := rfl
      _ ≃ 0 + m := by srw [‹n ≃ 0›]
      _ ≃ m     := AA.identL
      _ ≃ 0     := ‹m ≃ 0›


/-
Example showing that naturals numbers with addition form a Monoid and use
that fact to prove something.
-/

def add_monoid_props : CA.Monoid.Props (α := ℕ) (· + ·) 0 :=
  let subst_addL {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ + m ≃ n₂ + m := AA.substL;
  let subst_addR {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → m + n₁ ≃ m + n₂ := AA.substR;
{
  substL  := subst_addL
  substR  := subst_addR
  assoc   := add_associative.assoc
  identL  := add_identity.identityL.ident
  identR  := add_identity.identityR.ident
}

instance add_monoid : CA.Monoid.Monoid (α := ℕ) (binop := (· + ·)) (ident := 0) := {
  toProps := add_monoid_props
}

example : (x : ℕ) → ((y : ℕ) → (x + y ≃ y)) → x ≃ 0 := by
  intro x x_ident_prop
  exact CA.Monoid.identity_unique (binop := (· + ·)) x_ident_prop  -- annoying that we must specify binop.


end Lean4Axiomatic.Natural

import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Eqv
import Lean4Axiomatic.Operators

open Operators (TildeDash)
open Relation (EqvOp?)

namespace Natural

class Constructors (ℕ : Type) where
  zero : ℕ
  step : ℕ → ℕ

export Constructors (zero step)

def ofNatImpl {ℕ : Type} [Constructors ℕ] : Nat → ℕ
| 0 => zero
| n+1 => step (ofNatImpl n)

instance instOfNat {ℕ : Type} [Constructors ℕ] {n : Nat} : OfNat ℕ n where
  ofNat := ofNatImpl n

class Equality (ℕ : Type) where
  eqvOp? : EqvOp? ℕ

attribute [instance] Equality.eqvOp?

class Axioms (ℕ : Type) extends Constructors ℕ, Equality ℕ where
  step_substitutive : AA.Substitutive step (· ≃ ·) (· ≃ ·)
  step_injective : AA.Injective step (· ≃ ·) (· ≃ ·)
  step_neq_zero {n : ℕ} : step n ≄ 0

  ind {motive : ℕ → Prop}
    : motive 0 → (∀ n, motive n → motive (step n)) → ∀ n, motive n

attribute [instance] Axioms.step_substitutive
attribute [instance] Axioms.step_injective

class AxiomProperties (ℕ : Type) [Axioms ℕ] where
  step_neq {n : ℕ} : step n ≄ n

class AdditionBase (ℕ : Type) extends Axioms ℕ where
  addOp : Add ℕ

  zero_add {m : ℕ} : 0 + m ≃ m
  step_add {n m : ℕ} : step n + m ≃ step (n + m)

attribute [instance] AdditionBase.addOp

class AdditionProperties (ℕ : Type) extends AdditionBase ℕ where
  add_zero {n : ℕ} : n + 0 ≃ n
  add_step {n m : ℕ} : n + step m ≃ step (n + m)
  add_subst : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·)
  add_one_step {n : ℕ} : n + 1 ≃ step n
  add_comm : AA.Commutative (α := ℕ) (· + ·)
  add_assoc {n m k : ℕ} : (n + m) + k ≃ n + (m + k)
  cancel_add {n m k : ℕ} : n + m ≃ n + k → m ≃ k
  zero_sum_split {n m : ℕ} : n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0

class Addition (ℕ : Type) extends AdditionProperties ℕ

class SignBase (ℕ : Type) [Constructors ℕ] [Equality ℕ] where
  Positive (n : ℕ) : Prop := n ≄ 0
  positive_defn {n : ℕ} : Positive n ↔ n ≄ 0

export SignBase (Positive)

class SignProperties (ℕ : Type) [AdditionBase ℕ] extends SignBase ℕ where
  positive_subst : AA.Substitutive Positive (· ≃ ·) (· → ·)
  positive_step {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n
  positive_add {n m : ℕ} : Positive n → Positive (n + m)

class OrderBase (ℕ : Type) [AdditionBase ℕ] where
  leOp : LE ℕ := LE.mk λ n m => ∃ k : ℕ, n + k ≃ m
  le_defn {n m : ℕ} : n ≤ m ↔ ∃ k : ℕ, n + k ≃ m

  ltOp : LT ℕ := LT.mk λ n m => n ≤ m ∧ n ≄ m
  lt_defn {n m : ℕ} : n < m ↔ n ≤ m ∧ n ≄ m

-- Higher priority than the stdlib definitions
attribute [instance default+1] OrderBase.leOp
attribute [instance default+1] OrderBase.ltOp

class OrderProperties (ℕ : Type) [AdditionBase ℕ] extends OrderBase ℕ where
  le_subst_step : AA.Substitutive (α := ℕ) step (· ≤ ·) (· ≤ ·)
  le_inject_step : AA.Injective (α := ℕ) step (· ≤ ·) (· ≤ ·)
  le_subst_eqv : AA.Substitutive₂ (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·)
  le_refl : Relation.Refl (α := ℕ) (· ≤ ·)
  le_trans : Relation.Trans (α := ℕ) (· ≤ ·)
  le_antisymm {n m : ℕ} : n ≤ m → m ≤ n → n ≃ m
  le_subst_add : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·)
  le_cancel_add : AA.Cancellative₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·)
  le_from_eqv {n m : ℕ} : n ≃ m → n ≤ m
  le_from_lt {n m : ℕ} : n < m → n ≤ m
  le_split {n m : ℕ} : n ≤ m → n < m ∨ n ≃ m

  lt_subst_eqv : AA.Substitutive₂ (α := ℕ) (· < ·) (· ≃ ·) (· → ·)
  lt_trans : Relation.Trans (α := ℕ) (· < ·)
  lt_zero {n : ℕ} : n ≮ 0
  lt_step {n : ℕ} : n < step n
  lt_step_le {n m : ℕ} : n < m ↔ step n ≤ m
  lt_split {n m : ℕ} : n < step m → n < m ∨ n ≃ m
  trichotomy {n m : ℕ} : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)

attribute [instance] OrderProperties.le_subst_eqv

class Decl (ℕ : Type) where
  [toAddition : Addition ℕ]
  [toSignProperties : SignProperties ℕ]
  [toOrderProperties : OrderProperties ℕ]

attribute [instance] Decl.toAddition
attribute [instance] Decl.toSignProperties
attribute [instance] Decl.toOrderProperties

namespace Derived

variable {ℕ : Type}

def recOn
    [Axioms ℕ] {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ m, motive m → motive (step m)) : motive n :=
  Axioms.ind zero step n

def casesOn
    [Axioms ℕ] {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ n, motive (step n)) : motive n :=
  recOn n zero (λ n ih => step n)

instance [Axioms ℕ] : AxiomProperties ℕ where
  step_neq {n : ℕ} : step n ≄ n := by
    apply recOn (motive := λ n => step n ≄ n) n
    case zero =>
      show step 0 ≄ 0
      exact Axioms.step_neq_zero
    case step =>
      intro n (ih : step n ≄ n)
      show step (step n) ≄ step n
      intro (_ : step (step n) ≃ step n)
      show False
      apply ih
      show step n ≃ n
      exact AA.inject ‹step (step n) ≃ step n›

theorem add_zero [AdditionBase ℕ] {n : ℕ} : n + 0 ≃ n := by
  apply recOn (motive := λ n => n + 0 ≃ n) n
  case zero =>
    show 0 + 0 ≃ 0
    calc
      _ ≃ 0 + (0 : ℕ) := Eqv.refl
      _ ≃ 0           := AdditionBase.zero_add
  case step =>
    intro n (ih : n + 0 ≃ n)
    show step n + 0 ≃ step n
    calc
      _ ≃ step n + 0   := Eqv.refl
      _ ≃ step (n + 0) := AdditionBase.step_add
      _ ≃ step n       := AA.subst ih

theorem add_step [AdditionBase ℕ] {n m : ℕ} : n + step m ≃ step (n + m) := by
  apply recOn (motive := λ n => n + step m ≃ step (n + m)) n
  case zero =>
    show 0 + step m ≃ step (0 + m)
    calc
      _ ≃ 0 + step m   := Eqv.refl
      _ ≃ step m       := AdditionBase.zero_add
      _ ≃ step (0 + m) := AA.subst (Eqv.symm AdditionBase.zero_add)
  case step =>
    intro n (ih : n + step m ≃ step (n + m))
    show step n + step m ≃ step (step n + m)
    calc
      _ ≃ step n + step m     := Eqv.refl
      _ ≃ step (n + step m)   := AdditionBase.step_add
      _ ≃ step (step (n + m)) := AA.subst ih
      _ ≃ step (step n + m)   := AA.subst (Eqv.symm AdditionBase.step_add)

theorem add_comm [AdditionBase ℕ] {n m : ℕ} : n + m ≃ m + n := by
  apply recOn (motive := λ n => n + m ≃ m + n) n
  case zero =>
    show 0 + m ≃ m + 0
    calc
      _ ≃ 0 + m := Eqv.refl
      _ ≃ m     := AdditionBase.zero_add
      _ ≃ m + 0 := Eqv.symm add_zero
  case step =>
    intro n (ih : n + m ≃ m + n)
    show step n + m ≃ m + step n
    calc
      _ ≃ step n + m   := Eqv.refl
      _ ≃ step (n + m) := AdditionBase.step_add
      _ ≃ step (m + n) := AA.subst ih
      _ ≃ m + step n   := Eqv.symm add_step

instance [AdditionBase ℕ] : AA.Commutative (α := ℕ) (· + ·) where
  comm := add_comm

theorem subst_add
    [AdditionBase ℕ] {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ + m ≃ n₂ + m := by
  apply recOn (motive := λ x => ∀ y, x ≃ y → x + m ≃ y + m) n₁
  case zero =>
    intro n₂
    show 0 ≃ n₂ → 0 + m ≃ n₂ + m
    apply casesOn (motive := λ y => 0 ≃ y → 0 + m ≃ y + m)
    case zero =>
      intro (_ : 0 ≃ (0 : ℕ))
      show 0 + m ≃ 0 + m
      exact Eqv.refl
    case step =>
      intro n₂ (_ : 0 ≃ step n₂)
      show 0 + m ≃ step n₂ + m
      apply False.elim
      show False
      exact Axioms.step_neq_zero (Eqv.symm ‹0 ≃ step n₂›)
  case step =>
    intro n₁ (ih : ∀ y, n₁ ≃ y → n₁ + m ≃ y + m) n₂
    show step n₁ ≃ n₂ → step n₁ + m ≃ n₂ + m
    apply casesOn (motive := λ y => step n₁ ≃ y → step n₁ + m ≃ y + m)
    case zero =>
      intro (_ : step n₁ ≃ 0)
      show step n₁ + m ≃ 0 + m
      apply False.elim
      show False
      exact Axioms.step_neq_zero ‹step n₁ ≃ 0›
    case step =>
      intro n₂ (_ : step n₁ ≃ step n₂)
      show step n₁ + m ≃ step n₂ + m
      have : n₁ ≃ n₂ := AA.inject ‹step n₁ ≃ step n₂›
      calc
        _ ≃ step n₁ + m   := Eqv.refl
        _ ≃ step (n₁ + m) := AdditionBase.step_add
        _ ≃ step (n₂ + m) := AA.subst (ih _ ‹n₁ ≃ n₂›)
        _ ≃ step n₂ + m   := Eqv.symm AdditionBase.step_add

instance [AdditionBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·) where
  subst₂ := subst_add

instance [AdditionBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·) :=
  AA.substR_from_substL_swap

instance
    [AdditionBase ℕ] : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·) :=
  AA.Substitutive₂.mk

theorem add_one_step [AdditionBase ℕ] {n : ℕ} : n + 1 ≃ step n := by
  calc
    _ ≃ n + 1        := Eqv.refl
    _ ≃ n + step 0   := AA.substR Eqv.refl
    _ ≃ step (n + 0) := add_step
    _ ≃ step n       := AA.subst add_zero

theorem add_assoc
    [AdditionBase ℕ] {n m k : ℕ} : (n + m) + k ≃ n + (m + k) := by
  apply recOn (motive := λ n => (n + m) + k ≃ n + (m + k)) n
  case zero =>
    show (0 + m) + k ≃ 0 + (m + k)
    calc
      _ ≃ (0 + m) + k := Eqv.refl
      _ ≃ m + k       := AA.substL AdditionBase.zero_add
      _ ≃ 0 + (m + k) := Eqv.symm (AdditionBase.zero_add)
  case step =>
    intro n (ih : (n + m) + k ≃ n + (m + k))
    show (step n + m) + k ≃ step n + (m + k)
    calc
      _ ≃ (step n + m) + k   := Eqv.refl
      _ ≃ step (n + m) + k   := AA.substL AdditionBase.step_add
      _ ≃ step ((n + m) + k) := AdditionBase.step_add
      _ ≃ step (n + (m + k)) := AA.subst ih
      _ ≃ step n + (m + k)   := Eqv.symm AdditionBase.step_add

theorem cancel_add [AdditionBase ℕ] {n m k : ℕ} : n + m ≃ n + k → m ≃ k := by
  apply recOn (motive := λ n => n + m ≃ n + k → m ≃ k) n
  case zero =>
    intro (_ : 0 + m ≃ 0 + k)
    show m ≃ k
    calc
      _ ≃ m     := Eqv.refl
      _ ≃ 0 + m := Eqv.symm AdditionBase.zero_add
      _ ≃ 0 + k := ‹0 + m ≃ 0 + k›
      _ ≃ k     := AdditionBase.zero_add
  case step =>
    intro n (ih : n + m ≃ n + k → m ≃ k) (_ : step n + m ≃ step n + k)
    show m ≃ k
    apply ih
    show n + m ≃ n + k
    apply AA.inject (β := ℕ) (f := step) (rβ := (· ≃ ·))
    show step (n + m) ≃ step (n + k)
    calc
      _ ≃ step (n + m) := Eqv.refl
      _ ≃ step n + m   := Eqv.symm AdditionBase.step_add
      _ ≃ step n + k   := ‹step n + m ≃ step n + k›
      _ ≃ step (n + k) := AdditionBase.step_add

theorem zero_sum_split
    [AdditionBase ℕ] {n m : ℕ} : n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0 := by
  apply casesOn (motive := λ n => n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0) n
  case zero =>
    intro (_ : 0 + m ≃ 0)
    show 0 ≃ 0 ∧ m ≃ 0
    have : m ≃ 0 := Eqv.trans (Eqv.symm AdditionBase.zero_add) ‹0 + m ≃ 0›
    exact ⟨Eqv.refl, ‹m ≃ 0›⟩
  case step =>
    intro n (_ : step n + m ≃ 0)
    show step n ≃ 0 ∧ m ≃ 0
    apply False.elim
    show False
    have : step (n + m) ≃ 0 :=
      Eqv.trans (Eqv.symm AdditionBase.step_add) ‹step n + m ≃ 0›
    exact Axioms.step_neq_zero ‹step (n + m) ≃ 0›

instance additionProperties [AdditionBase ℕ] : AdditionProperties ℕ where
  add_zero := add_zero
  add_step := add_step
  add_subst := inferInstance
  add_one_step := add_one_step
  add_comm := inferInstance
  add_assoc := add_assoc
  cancel_add := cancel_add
  zero_sum_split := zero_sum_split

instance [Constructors ℕ] [Equality ℕ] : SignBase ℕ where
  positive_defn := Iff.intro id id

theorem positive_subst
    [Constructors ℕ] [Equality ℕ] [SignBase ℕ] {n₁ n₂ : ℕ}
    : n₁ ≃ n₂ → Positive n₁ → Positive n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : Positive n₁)
  show Positive n₂
  have : n₁ ≄ 0 := SignBase.positive_defn.mp ‹Positive n₁›
  apply SignBase.positive_defn.mpr
  show n₂ ≄ 0
  exact AA.substL (self := AA.neq.substL) ‹n₁ ≃ n₂› ‹n₁ ≄ 0›

instance
    [Constructors ℕ] [Equality ℕ] [SignBase ℕ]
    : AA.Substitutive (α := ℕ) Positive (· ≃ ·) (· → ·) where
  subst := positive_subst

theorem positive_step
    [Axioms ℕ] [SignBase ℕ] {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n := by
  apply casesOn (motive := λ n => Positive n → ∃ m, step m ≃ n) n
  case zero =>
    intro (_ : Positive (0 : ℕ))
    apply False.elim
    show False
    have : 0 ≄ 0 := SignBase.positive_defn.mp ‹Positive (0 : ℕ)›
    apply this
    show 0 ≃ 0
    exact Eqv.refl
  case step =>
    intro n (_ : Positive (step n))
    exists n
    show step n ≃ step n
    exact Eqv.refl

theorem positive_add
    [AdditionBase ℕ] [SignBase ℕ] {n m : ℕ}
    : Positive n → Positive (n + m) := by
  intro (_ : Positive n)
  show Positive (n + m)
  apply casesOn (motive := λ m => Positive (n + m)) m
  case zero =>
    show Positive (n + 0)
    apply AA.subst (rβ := (· → ·)) (Eqv.symm AdditionProperties.add_zero)
    exact ‹Positive n›
  case step =>
    intro m
    show Positive (n + step m)
    apply AA.subst (rβ := (· → ·)) (Eqv.symm AdditionProperties.add_step)
    show Positive (step (n + m))
    apply SignBase.positive_defn.mpr
    show step (n + m) ≄ 0
    exact Axioms.step_neq_zero

instance signProperties [AdditionBase ℕ] [SignBase ℕ] : SignProperties ℕ where
  positive_subst := inferInstance
  positive_step := positive_step
  positive_add := positive_add

instance [AdditionBase ℕ] : OrderBase ℕ where
  le_defn {n m : ℕ} := Iff.intro id id
  lt_defn {n m : ℕ} := Iff.intro id id

theorem le_subst_step
    [AdditionBase ℕ] [OrderBase ℕ] {n₁ n₂ : ℕ}
    : n₁ ≤ n₂ → step n₁ ≤ step n₂ := by
  intro (_ : n₁ ≤ n₂)
  show step n₁ ≤ step n₂
  have ⟨d, (_ : n₁ + d ≃ n₂)⟩ := OrderBase.le_defn.mp ‹n₁ ≤ n₂›
  apply OrderBase.le_defn.mpr
  exists d
  show step n₁ + d ≃ step n₂
  calc
    _ ≃ step n₁ + d := Eqv.refl
    _ ≃ step (n₁ + d) := AdditionBase.step_add
    _ ≃ step n₂ := AA.subst ‹n₁ + d ≃ n₂›

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.Substitutive (α := ℕ) step (· ≤ ·) (· ≤ ·) where
  subst := le_subst_step

theorem le_inject_step
    [AdditionBase ℕ] [OrderBase ℕ] {n₁ n₂ : ℕ}
    : step n₁ ≤ step n₂ → n₁ ≤ n₂ := by
  intro (_ : step n₁ ≤ step n₂)
  show n₁ ≤ n₂
  have ⟨d, (_ : step n₁ + d ≃ step n₂)⟩ :=
    OrderBase.le_defn.mp ‹step n₁ ≤ step n₂›
  apply OrderBase.le_defn.mpr
  exists d
  show n₁ + d ≃ n₂
  have : step (n₁ + d) ≃ step n₂ := calc
    _ ≃ step (n₁ + d) := Eqv.refl
    _ ≃ step n₁ + d := Eqv.symm AdditionBase.step_add
    _ ≃ step n₂ := ‹step n₁ + d ≃ step n₂›
  exact AA.inject ‹step (n₁ + d) ≃ step n₂›

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.Injective (α := ℕ) step (· ≤ ·) (· ≤ ·) where
  inject := le_inject_step

theorem le_subst_eqv
    [AdditionBase ℕ] [OrderBase ℕ] {n₁ n₂ m : ℕ}
    : n₁ ≃ n₂ → n₁ ≤ m → n₂ ≤ m := by
  intro (_ : n₁ ≃ n₂) (_ : n₁ ≤ m)
  show n₂ ≤ m
  have ⟨d, (_ : n₁ + d ≃ m)⟩ := OrderBase.le_defn.mp ‹n₁ ≤ m›
  apply OrderBase.le_defn.mpr
  exists d
  show n₂ + d ≃ m
  calc
    _ ≃ n₂ + d := Eqv.refl
    _ ≃ n₁ + d := Eqv.symm (AA.substL ‹n₁ ≃ n₂›)
    _ ≃ m      := ‹n₁ + d ≃ m›

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·) where
  subst₂ := le_subst_eqv

theorem le_eqv_subst
    [AdditionBase ℕ] [OrderBase ℕ] {n m₁ m₂ : ℕ}
    : m₁ ≃ m₂ → n ≤ m₁ → n ≤ m₂ := by
  intro (_ : m₁ ≃ m₂) (_ : n ≤ m₁)
  show n ≤ m₂
  have ⟨d, (_ : n + d ≃ m₁)⟩ := OrderBase.le_defn.mp ‹n ≤ m₁›
  apply OrderBase.le_defn.mpr
  exists d
  show n + d ≃ m₂
  exact Eqv.trans ‹n + d ≃ m₁› ‹m₁ ≃ m₂›

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·) where
  subst₂ := le_eqv_subst

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.Substitutive₂ (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·) :=
  AA.Substitutive₂.mk

theorem le_refl [AdditionBase ℕ] [OrderBase ℕ] {n : ℕ} : n ≤ n := by
  apply OrderBase.le_defn.mpr
  exists (0 : ℕ)
  show n + 0 ≃ n
  exact AdditionProperties.add_zero

instance [AdditionBase ℕ] [OrderBase ℕ] : Relation.Refl (α := ℕ) (· ≤ ·) where
  refl := le_refl

theorem le_step_split
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ}
    : n ≤ step m → n ≤ m ∨ n ≃ step m := by
  intro (_ : n ≤ step m)
  show n ≤ m ∨ n ≃ step m
  have ⟨d, (_ : n + d ≃ step m)⟩ := OrderBase.le_defn.mp ‹n ≤ step m›
  apply (casesOn (motive := λ x => d ≃ x → n ≤ m ∨ n ≃ step m) d · · Eqv.refl)
  · intro (_ : d ≃ 0)
    apply Or.inr
    show n ≃ step m
    calc
      _ ≃ n      := Eqv.refl
      _ ≃ n + 0  := Eqv.symm AdditionProperties.add_zero
      _ ≃ n + d  := Eqv.symm (AA.substR ‹d ≃ 0›)
      _ ≃ step m := ‹n + d ≃ step m›
  · intro e (_ : d ≃ step e)
    apply Or.inl
    show n ≤ m
    apply OrderBase.le_defn.mpr
    exists e
    show n + e ≃ m
    apply AA.inject (β := ℕ) (f := step) (rβ := (· ≃ ·))
    show step (n + e) ≃ step m
    calc
      _ ≃ step (n + e) := Eqv.refl
      _ ≃ n + step e   := Eqv.symm AdditionProperties.add_step
      _ ≃ n + d        := Eqv.symm (AA.substR ‹d ≃ step e›)
      _ ≃ step m       := ‹n + d ≃ step m›

theorem le_step
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ} : n ≤ m → n ≤ step m := by
  intro (_ : n ≤ m)
  show n ≤ step m
  have ⟨d, (_ : n + d ≃ m)⟩ := OrderBase.le_defn.mp ‹n ≤ m›
  apply OrderBase.le_defn.mpr
  exists step d
  show n + step d ≃ step m
  calc
    _ ≃ n + step d   := Eqv.refl
    _ ≃ step (n + d) := AdditionProperties.add_step
    _ ≃ step m       := AA.subst ‹n + d ≃ m›

theorem le_trans
    [AdditionBase ℕ] [OrderBase ℕ] {n m k : ℕ} : n ≤ m → m ≤ k → n ≤ k := by
  intro (_ : n ≤ m)
  have ⟨d, (_ : n + d ≃ m)⟩ := OrderBase.le_defn.mp ‹n ≤ m›
  apply recOn (motive := λ k => m ≤ k → n ≤ k) k
  case zero =>
    intro (_ : m ≤ 0)
    have ⟨e, (_ : m + e ≃ 0)⟩ := OrderBase.le_defn.mp ‹m ≤ 0›
    show n ≤ 0
    apply OrderBase.le_defn.mpr
    exists d + e
    show n + (d + e) ≃ 0
    calc
      _ ≃ n + (d + e) := Eqv.refl
      _ ≃ (n + d) + e := Eqv.symm AdditionProperties.add_assoc
      _ ≃ m + e       := AA.substL ‹n + d ≃ m›
      _ ≃ 0           := ‹m + e ≃ 0›
  case step =>
    intro k (ih : m ≤ k → n ≤ k) (_ : m ≤ step k)
    show n ≤ step k
    match le_step_split ‹m ≤ step k› with
    | Or.inl (_ : m ≤ k) =>
      exact le_step (ih ‹m ≤ k›)
    | Or.inr (_ : m ≃ step k) =>
      exact AA.substR (rβ := (· → ·)) ‹m ≃ step k› ‹n ≤ m›

instance [AdditionBase ℕ] [OrderBase ℕ] : Relation.Trans (α := ℕ) (· ≤ ·) where
  trans := le_trans

theorem le_subst_add
    [AdditionBase ℕ] [OrderBase ℕ] {n₁ n₂ m : ℕ}
    : n₁ ≤ n₂ → n₁ + m ≤ n₂ + m := by
  intro (_ : n₁ ≤ n₂)
  show n₁ + m ≤ n₂ + m
  have ⟨d, (_ : n₁ + d ≃ n₂)⟩ := OrderBase.le_defn.mp ‹n₁ ≤ n₂›
  apply OrderBase.le_defn.mpr
  exists d
  show (n₁ + m) + d ≃ n₂ + m
  calc
    _ ≃ (n₁ + m) + d := Eqv.refl
    _ ≃ n₁ + (m + d) := AdditionProperties.add_assoc
    _ ≃ n₁ + (d + m) := AA.substR AA.comm
    _ ≃ (n₁ + d) + m := Eqv.symm AdditionProperties.add_assoc
    _ ≃ n₂ + m       := AA.substL ‹n₁ + d ≃ n₂›

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) where
  subst₂ := le_subst_add

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) :=
  AA.substR_from_substL_swap

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) :=
  AA.Substitutive₂.mk

theorem le_cancel_add
    [AdditionBase ℕ] [OrderBase ℕ] {n m₁ m₂ : ℕ}
    : n + m₁ ≤ n + m₂ → m₁ ≤ m₂ := by
  intro (_ : n + m₁ ≤ n + m₂)
  show m₁ ≤ m₂
  have ⟨d, (_ : (n + m₁) + d ≃ n + m₂)⟩ :=
    OrderBase.le_defn.mp ‹n + m₁ ≤ n + m₂›
  apply OrderBase.le_defn.mpr
  exists d
  show m₁ + d ≃ m₂
  have : n + (m₁ + d) ≃ n + m₂ := calc
    _ ≃ n + (m₁ + d) := Eqv.refl
    _ ≃ (n + m₁) + d := Eqv.symm AdditionProperties.add_assoc
    _ ≃ n + m₂       := ‹(n + m₁) + d ≃ n + m₂›
  exact AdditionProperties.cancel_add ‹n + (m₁ + d) ≃ n + m₂›

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.Cancellative AA.Hand.L (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) where
  cancel := le_cancel_add

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.Cancellative AA.Hand.R (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) :=
  AA.cancelR_from_cancelL

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.Cancellative₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) := AA.Cancellative₂.mk

theorem le_antisymm
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ} : n ≤ m → m ≤ n → n ≃ m := by
  intro (_ : n ≤ m) (_ : m ≤ n)
  show n ≃ m
  have ⟨d₁, (_ : n + d₁ ≃ m)⟩ := OrderBase.le_defn.mp ‹n ≤ m›
  have ⟨d₂, (_ : m + d₂ ≃ n)⟩ := OrderBase.le_defn.mp ‹m ≤ n›
  have : n + (d₁ + d₂) ≃ n + 0 := calc
    _ ≃ n + (d₁ + d₂) := Eqv.refl
    _ ≃ (n + d₁) + d₂ := Eqv.symm AdditionProperties.add_assoc
    _ ≃ m + d₂        := AA.substL ‹n + d₁ ≃ m›
    _ ≃ n             := ‹m + d₂ ≃ n›
    _ ≃ n + 0         := Eqv.symm AdditionProperties.add_zero
  have : d₁ + d₂ ≃ 0 := AdditionProperties.cancel_add ‹n + (d₁ + d₂) ≃ n + 0›
  have ⟨(_ : d₁ ≃ 0), _⟩ := AdditionProperties.zero_sum_split ‹d₁ + d₂ ≃ 0›
  calc
    _ ≃ n      := Eqv.refl
    _ ≃ n + 0  := Eqv.symm AdditionProperties.add_zero
    _ ≃ n + d₁ := Eqv.symm (AA.substR ‹d₁ ≃ 0›)
    _ ≃ m      := ‹n + d₁ ≃ m›

theorem lt_subst_eqv
    [AdditionBase ℕ] [OrderBase ℕ] {n₁ n₂ m : ℕ}
    : n₁ ≃ n₂ → n₁ < m → n₂ < m := by
  intro (_ : n₁ ≃ n₂) (_ : n₁ < m)
  show n₂ < m
  have ⟨(_ : n₁ ≤ m), (_ : n₁ ≄ m)⟩ := OrderBase.lt_defn.mp ‹n₁ < m›
  have : n₂ ≤ m := AA.substL (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹n₁ ≤ m›
  have : n₂ ≄ m := AA.substL (f := (· ≄ ·)) (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹n₁ ≄ m›
  apply OrderBase.lt_defn.mpr
  exact ⟨‹n₂ ≤ m›, ‹n₂ ≄ m›⟩

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· < ·) (· ≃ ·) (· → ·) where
  subst₂ := lt_subst_eqv

theorem lt_eqv_subst
    [AdditionBase ℕ] [OrderBase ℕ] {n₁ n₂ m : ℕ}
    : n₁ ≃ n₂ → m < n₁ → m < n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : m < n₁)
  show m < n₂
  have ⟨(_ : m ≤ n₁), (_ : m ≄ n₁)⟩ := OrderBase.lt_defn.mp ‹m < n₁›
  have : m ≤ n₂ := AA.substR (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹m ≤ n₁›
  have : m ≄ n₂ := AA.substR (f := (· ≄ ·)) (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹m ≄ n₁›
  apply OrderBase.lt_defn.mpr
  exact ⟨‹m ≤ n₂›, ‹m ≄ n₂›⟩

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· < ·) (· ≃ ·) (· → ·) where
  subst₂ := lt_eqv_subst

instance [AdditionBase ℕ] [OrderBase ℕ]
    : AA.Substitutive₂ (α := ℕ) (· < ·) (· ≃ ·) (· → ·) := AA.Substitutive₂.mk

theorem lt_step [AdditionBase ℕ] [OrderBase ℕ] {n : ℕ} : n < step n := by
  show n < step n
  apply OrderBase.lt_defn.mpr
  apply And.intro
  · show n ≤ step n
    apply OrderBase.le_defn.mpr
    exists (1 : ℕ)
    show n + 1 ≃ step n
    exact add_one_step
  · show n ≄ step n
    exact Eqv.symm AxiomProperties.step_neq

theorem lt_step_le
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ} : n < m ↔ step n ≤ m := by
  apply Iff.intro
  · intro (_ : n < m)
    show step n ≤ m
    have ⟨(_ : n ≤ m), (_ : n ≄ m)⟩ := OrderBase.lt_defn.mp ‹n < m›
    have ⟨d, (_ : n + d ≃ m)⟩ := OrderBase.le_defn.mp ‹n ≤ m›
    have : d ≄ 0 := by
      intro (_ : d ≃ 0)
      show False
      apply ‹n ≄ m›
      show n ≃ m
      calc
        _ ≃ n     := Eqv.refl
        _ ≃ n + 0 := Eqv.symm AdditionProperties.add_zero
        _ ≃ n + d := Eqv.symm (AA.substR ‹d ≃ 0›)
        _ ≃ m     := ‹n + d ≃ m›
    have : Positive d := SignBase.positive_defn.mpr ‹d ≄ 0›
    have ⟨d', (_ : step d' ≃ d)⟩ := SignProperties.positive_step ‹Positive d›
    show step n ≤ m
    apply OrderBase.le_defn.mpr
    exists d'
    show step n + d' ≃ m
    calc
      _ ≃ step n + d'   := Eqv.refl
      _ ≃ step (n + d') := AdditionBase.step_add
      _ ≃ n + step d'   := Eqv.symm AdditionProperties.add_step
      _ ≃ n + d         := AA.substR ‹step d' ≃ d›
      _ ≃ m             := ‹n + d ≃ m›
  · intro (_ : step n ≤ m)
    show n < m
    have ⟨d, (_ : step n + d ≃ m)⟩ := OrderBase.le_defn.mp ‹step n ≤ m›
    have : n + step d ≃ m := calc
      _ ≃ n + step d   := Eqv.refl
      _ ≃ step (n + d) := AdditionProperties.add_step
      _ ≃ step n + d   := Eqv.symm AdditionBase.step_add
      _ ≃ m            := ‹step n + d ≃ m›
    have : ∃ d, n + d ≃ m := ⟨step d, ‹n + step d ≃ m›⟩
    have : n ≤ m := OrderBase.le_defn.mpr ‹∃ d, n + d ≃ m›
    have : n ≄ m := by
      intro (_ : n ≃ m)
      show False
      have : n + step d ≃ n + 0 := calc
        _ ≃ n + step d := Eqv.refl
        _ ≃ m := ‹n + step d ≃ m›
        _ ≃ n := Eqv.symm ‹n ≃ m›
        _ ≃ n + 0 := Eqv.symm AdditionProperties.add_zero
      have : step d ≃ 0 := AdditionProperties.cancel_add ‹n + step d ≃ n + 0›
      exact absurd this Axioms.step_neq_zero
    show n < m
    apply OrderBase.lt_defn.mpr
    exact ⟨‹n ≤ m›, ‹n ≄ m›⟩

theorem lt_zero [AdditionBase ℕ] [OrderBase ℕ] {n : ℕ} : n ≮ 0 := by
  intro (_ : n < 0)
  show False
  have : step n ≤ 0 := lt_step_le.mp ‹n < 0›
  have ⟨d, (_ : step n + d ≃ 0)⟩ := OrderBase.le_defn.mp ‹step n ≤ 0›
  have : step (n + d) ≃ 0 := calc
    _ ≃ step (n + d) := Eqv.refl
    _ ≃ step n + d   := Eqv.symm AdditionBase.step_add
    _ ≃ 0            := ‹step n + d ≃ 0›
  exact absurd ‹step (n + d) ≃ 0› Axioms.step_neq_zero

theorem le_from_eqv
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ} : n ≃ m → n ≤ m := by
  intro (_ : n ≃ m)
  show n ≤ m
  have : n ≤ n := Eqv.refl
  exact AA.substR (rβ := (· → ·)) ‹n ≃ m› ‹n ≤ n›

theorem le_from_lt
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ} : n < m → n ≤ m := by
  intro (_ : n < m)
  show n ≤ m
  have ⟨(_ : n ≤ m), _⟩ := OrderBase.lt_defn.mp ‹n < m›
  exact ‹n ≤ m›

theorem le_split
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ} : n ≤ m → n < m ∨ n ≃ m := by
  intro (_ : n ≤ m)
  show n < m ∨ n ≃ m
  have ⟨d, (h : n + d ≃ m)⟩ := OrderBase.le_defn.mp ‹n ≤ m›
  revert h
  apply casesOn (motive := λ d => n + d ≃ m → n < m ∨ n ≃ m) d
  case zero =>
    intro (_ : n + 0 ≃ m)
    apply Or.inr
    show n ≃ m
    calc
      _ ≃ n     := Eqv.refl
      _ ≃ n + 0 := Eqv.symm add_zero
      _ ≃ m     := ‹n + 0 ≃ m›
  case step =>
    intro d (_ : n + step d ≃ m)
    apply Or.inl
    show n < m
    apply lt_step_le.mpr
    show step n ≤ m
    apply OrderBase.le_defn.mpr
    exists d
    show step n + d ≃ m
    calc
      _ ≃ step n + d   := Eqv.refl
      _ ≃ step (n + d) := AdditionBase.step_add
      _ ≃ n + step d   := Eqv.symm add_step
      _ ≃ m            := ‹n + step d ≃ m›

theorem lt_split
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ} : n < step m → n < m ∨ n ≃ m := by
  intro (_ : n < step m)
  show n < m ∨ n ≃ m
  have : step n ≤ step m := lt_step_le.mp ‹n < step m›
  have : n ≤ m := AA.inject ‹step n ≤ step m›
  exact le_split ‹n ≤ m›

theorem lt_trans
    [AdditionBase ℕ] [OrderBase ℕ] {n m k : ℕ} : n < m → m < k → n < k := by
  intro (_ : n < m) (_ : m < k)
  show n < k
  apply lt_step_le.mpr
  show step n ≤ k
  calc
    _ ≤ step n := Eqv.refl
    _ ≤ m      := lt_step_le.mp ‹n < m›
    _ ≤ step m := le_from_lt lt_step
    _ ≤ k      := lt_step_le.mp ‹m < k›

instance [AdditionBase ℕ] [OrderBase ℕ]: Relation.Trans (α := ℕ) (· < ·) where
  trans := lt_trans

theorem trichotomy
    [AdditionBase ℕ] [OrderBase ℕ] {n m : ℕ}
    : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m) := by
  constructor
  case atLeastOne =>
    apply recOn (motive := λ n => AA.OneOfThree (n < m) (n ≃ m) (n > m)) n
    case zero =>
      show AA.OneOfThree (0 < m) (0 ≃ m) (0 > m)
      apply casesOn
        (motive := λ m : ℕ => AA.OneOfThree (0 < m) (0 ≃ m) (0 > m)) m
      case zero =>
        apply AA.OneOfThree.second
        show 0 ≃ 0
        exact Eqv.refl
      case step =>
        intro m
        apply AA.OneOfThree.first
        show 0 < step m
        apply OrderBase.lt_defn.mpr
        apply And.intro
        · show 0 ≤ step m
          apply OrderBase.le_defn.mpr
          exists step m
          exact AdditionBase.zero_add
        · show 0 ≄ step m
          exact Eqv.symm Axioms.step_neq_zero
    case step =>
      intro n (ih : AA.OneOfThree (n < m) (n ≃ m) (n > m))
      show AA.OneOfThree (step n < m) (step n ≃ m) (step n > m)
      match ih with
      | AA.OneOfThree.first (_ : n < m) =>
        have : step n ≤ m := lt_step_le.mp ‹n < m›
        have : step n < m ∨ step n ≃ m := le_split ‹step n ≤ m›
        match ‹step n < m ∨ step n ≃ m› with
        | Or.inl (_ : step n < m) => exact AA.OneOfThree.first ‹step n < m›
        | Or.inr (_ : step n ≃ m) => exact AA.OneOfThree.second ‹step n ≃ m›
      | AA.OneOfThree.second (_ : n ≃ m) =>
        have : m ≃ n := Eqv.symm ‹n ≃ m›
        have : m ≤ n := le_from_eqv ‹m ≃ n›
        have : step m ≤ step n := AA.subst ‹m ≤ n›
        have : m < step n := lt_step_le.mpr ‹step m ≤ step n›
        apply AA.OneOfThree.third
        exact ‹m < step n›
      | AA.OneOfThree.third (_ : n > m) =>
        apply AA.OneOfThree.third
        show m < step n
        exact Eqv.trans ‹m < n› lt_step
  case atMostOne =>
    show ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m)
    intro
    | AA.TwoOfThree.oneAndTwo (_ : n < m) (_ : n ≃ m) =>
      show False
      have ⟨_, (_ : n ≄ m)⟩ := OrderBase.lt_defn.mp ‹n < m›
      exact absurd ‹n ≃ m› ‹n ≄ m›
    | AA.TwoOfThree.oneAndThree (_ : n < m) (_ : n > m) =>
      show False
      have ⟨(_ : n ≤ m), (_ : n ≄ m)⟩ := OrderBase.lt_defn.mp ‹n < m›
      have ⟨(_ : m ≤ n), _⟩ := OrderBase.lt_defn.mp ‹n > m›
      have : n ≃ m := le_antisymm ‹n ≤ m› ‹m ≤ n›
      exact absurd ‹n ≃ m› ‹n ≄ m›
    | AA.TwoOfThree.twoAndThree (_ : n ≃ m) (_ : n > m) =>
      show False
      have ⟨_, (_ : m ≄ n)⟩ := OrderBase.lt_defn.mp ‹n > m›
      exact absurd ‹n ≃ m› (Eqv.symm ‹m ≄ n›)

instance [AdditionBase ℕ] : OrderProperties ℕ where
  le_subst_step := inferInstance
  le_inject_step := inferInstance
  le_subst_eqv := inferInstance
  le_refl := inferInstance
  le_trans := inferInstance
  le_subst_add := inferInstance
  le_cancel_add := inferInstance
  le_antisymm := le_antisymm
  le_from_eqv := le_from_eqv
  le_from_lt := le_from_lt
  le_split := le_split
  lt_subst_eqv := inferInstance
  lt_trans := inferInstance
  lt_zero := lt_zero
  lt_step := lt_step
  lt_step_le := lt_step_le
  lt_split := lt_split
  trichotomy := trichotomy

end Derived

namespace ImplNat

instance : Constructors Nat where
  zero := Nat.zero
  step := Nat.succ

instance : EqvOp? Nat where
  tildeDash := Eq
  refl := λ {x} => Eq.refl x
  symm := Eq.symm
  trans := Eq.trans
  tildeDashQuestion := Nat.decEq

instance : Equality Nat where
  eqvOp? := inferInstance

instance : AA.Substitutive (step : Nat → Nat) (· ≃ ·) (· ≃ ·) where
  subst := congrArg step

theorem succ_injective {n m : Nat} : Nat.succ n = Nat.succ m → n = m
| Eq.refl _ => Eq.refl _

instance : AA.Injective (step : Nat → Nat) (· ≃ ·) (· ≃ ·) where
  inject := succ_injective

def indImpl
    {motive : Nat → Sort v}
    (mz : motive 0) (ms : {n : Nat} → motive n → motive (Nat.succ n)) (n : Nat)
    : motive n :=
  match n with
  | Nat.zero => mz
  | Nat.succ n => ms (indImpl mz ms n)

instance : Axioms Nat where
  step_substitutive := inferInstance
  step_injective := inferInstance
  step_neq_zero := Nat.noConfusion
  -- 2022-01-11: Using `Nat.rec` directly here, gives the following error:
  -- code generator does not support recursor 'Nat.rec' yet, consider using
  -- 'match ... with' and/or structural recursion
  ind := indImpl

instance : AdditionBase Nat where
  addOp := inferInstance
  zero_add := @Nat.zero_add
  step_add := @Nat.succ_add

instance : Addition Nat := Addition.mk
instance : Decl Nat := Decl.mk

end ImplNat

end Natural

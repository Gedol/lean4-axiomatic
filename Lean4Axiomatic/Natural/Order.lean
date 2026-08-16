import Lean4Axiomatic.Logic
import Lean4Axiomatic.Natural.Sign

/-!
# Natural number ordering
-/

namespace Lean4Axiomatic.Natural

open Logic (Either iff_subst_covar or_mapL)
open Signed (Positive)

/-!
## Axioms
-/

/--
Definition of the _less than or equal to_ and _less than_ relations.

All other properties of ordering on natural numbers can be derived from this.
-/
class Order (ℕ : Type) [Core ℕ] [Addition ℕ] where
  /-- Definition of and syntax for the _less than or equal to_ relation. -/
  leOp : LE ℕ

  /--
  The _less than or equal to_ relation between two natural numbers `n` and `m`
  is equivalent to there being a natural number -- the _difference_ between `n`
  and `m` -- that, when added to `n`, results in `m`.
  -/
  le_defn {n m : ℕ} : n ≤ m ↔ ∃ k : ℕ, n + k ≃ m

  /-- Definition of and syntax for the _less than_ relation. -/
  ltOp : LT ℕ

  /--
  The _less than_ relation between two natural numbers is defined to be the
  same as _less than or equal to_, with the added condition that the numbers
  are not equal.
  -/
  lt_defn {n m : ℕ} : n < m ↔ n ≤ m ∧ n ≄ m

-- Higher priority than the stdlib definitions
attribute [implicit_reducible, instance default+1] Order.leOp
attribute [implicit_reducible, instance default+1] Order.ltOp

export Order (le_defn leOp lt_defn ltOp)

/-!
## Derived properties
-/

variable {ℕ : Type} [Core ℕ] [Addition ℕ] [order_inst : Order ℕ]

/--
The _less than or equal to_ relation is preserved when both sides are
incremented.
-/
@[gcongr]
theorem le_subst_step {n₁ n₂ : ℕ} : n₁ ≤ n₂ → step n₁ ≤ step n₂ := by
  intro (_ : n₁ ≤ n₂)
  show step n₁ ≤ step n₂
  have ⟨d, (_ : n₁ + d ≃ n₂)⟩ := le_defn.mp ‹n₁ ≤ n₂›
  apply le_defn.mpr
  exists d
  show step n₁ + d ≃ step n₂
  calc
    step n₁ + d   ≃ _ := step_add
    step (n₁ + d) ≃ _ := by srw [‹n₁ + d ≃ n₂›]
    step n₂       ≃ _ := Rel.refl

instance le_substitutive_step
    : AA.Substitutive₁ (α := ℕ) step (· ≤ ·) (· ≤ ·)
    := {
  subst₁ := le_subst_step
}

/--
The _less than or equal to_ relation is preserved when both sides are
decremented.
-/
theorem le_inject_step {n₁ n₂ : ℕ} : step n₁ ≤ step n₂ → n₁ ≤ n₂ := by
  intro (_ : step n₁ ≤ step n₂)
  show n₁ ≤ n₂
  have ⟨d, (_ : step n₁ + d ≃ step n₂)⟩ := le_defn.mp ‹step n₁ ≤ step n₂›
  apply le_defn.mpr
  exists d
  show n₁ + d ≃ n₂
  have : step (n₁ + d) ≃ step n₂ := calc
    step (n₁ + d) ≃ _ := Rel.symm step_add
    step n₁ + d   ≃ _ := ‹step n₁ + d ≃ step n₂›
    step n₂       ≃ _ := Rel.refl
  exact AA.inject ‹step (n₁ + d) ≃ step n₂›

instance le_injective_step : AA.Injective (α := ℕ) step (· ≤ ·) (· ≤ ·) := {
  inject := le_inject_step
}

/--
Equal natural numbers can be substituted on the right side of
_less than or equal to_.
-/
@[gcongr]
theorem le_eqv_subst {n m₁ m₂ : ℕ} : m₁ ≃ m₂ → n ≤ m₁ → n ≤ m₂ := by
  intro (_ : m₁ ≃ m₂) (_ : n ≤ m₁)
  show n ≤ m₂
  have ⟨d, (_ : n + d ≃ m₁)⟩ := le_defn.mp ‹n ≤ m₁›
  apply le_defn.mpr
  exists d
  show n + d ≃ m₂
  exact Rel.trans ‹n + d ≃ m₁› ‹m₁ ≃ m₂›

/--
Corollary of `le_eqv_subst` to support transitivity of _less than or equivalent
to_ and equivalence.
-/
theorem trans_le_eqv_le {n m k : ℕ} : n ≤ m → m ≃ k → n ≤ k := by
  intro (_ : n ≤ m) (_ : m ≃ k)
  show n ≤ k
  prw [‹m ≃ k›] ‹n ≤ m›

instance trans_le_eqv_le_inst : Trans (α := ℕ) (· ≤ ·) (· ≃ ·) (· ≤ ·) := {
  trans := trans_le_eqv_le
}

/--
Equivalent natural numbers can be substituted on the right side of _less than_.
-/
@[gcongr]
theorem lt_eqv_subst {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → m < n₁ → m < n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : m < n₁)
  show m < n₂
  have ⟨(_ : m ≤ n₁), (_ : m ≄ n₁)⟩ := lt_defn.mp ‹m < n₁›
  have : m ≤ n₂ := by prw [‹n₁ ≃ n₂›] ‹m ≤ n₁›
  have : m ≄ n₂ := by prw [‹n₁ ≃ n₂›] ‹m ≄ n₁›
  apply lt_defn.mpr
  exact ⟨‹m ≤ n₂›, ‹m ≄ n₂›⟩

/--
Corollary of `lt_eqv_subst` to support transitivity of _less than_ and
equivalence.
-/
theorem trans_lt_eqv_lt {n m k : ℕ} : n < m → m ≃ k → n < k := by
  intro (_ : n < m) (_ : m ≃ k)
  show n < k
  prw [‹m ≃ k›] ‹n < m›

instance trans_lt_eqv_lt_inst : Trans (α := ℕ) (· < ·) (· ≃ ·) (· < ·) := {
  trans := trans_lt_eqv_lt
}

variable [Induction.{0} ℕ]

/--
Equal natural numbers can be substituted on the left side of
_less than or equal to_.
-/
@[gcongr]
theorem le_subst_eqv {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ ≤ m → n₂ ≤ m := by
  intro (_ : n₁ ≃ n₂) (_ : n₁ ≤ m)
  show n₂ ≤ m
  have ⟨d, (_ : n₁ + d ≃ m)⟩ := le_defn.mp ‹n₁ ≤ m›
  apply le_defn.mpr
  exists d
  show n₂ + d ≃ m
  calc
    n₂ + d ≃ _ := by srw [←‹n₁ ≃ n₂›]
    n₁ + d ≃ _ := ‹n₁ + d ≃ m›
    m      ≃ _ := Rel.refl

/--
Corollary of `le_subst_eqv` to support transitivity of equivalence and
_less than or equivalent to_.
-/
theorem trans_eqv_le_le {n m k : ℕ} : n ≃ m → m ≤ k → n ≤ k := by
  intro (_ : n ≃ m) (_ : m ≤ k)
  show n ≤ k
  prw [←‹n ≃ m›] ‹m ≤ k›

instance trans_eqv_le_le_inst : Trans (α := ℕ) (· ≃ ·) (· ≤ ·) (· ≤ ·) := {
  trans := trans_eqv_le_le
}

instance le_substitutive_eqv
    : AA.Substitutive₂ (α := ℕ) (· ≤ ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ _ => le_subst_eqv }
  substitutiveR := { subst₂ := λ _ => le_eqv_subst }
}

/-- All natural numbers are _less than or equal to_ themselves. -/
theorem le_refl {n : ℕ} : n ≤ n := by
  apply le_defn.mpr
  exists (0 : ℕ)
  show n + 0 ≃ n
  exact add_zero

instance le_reflexive : Relation.Reflexive (α := ℕ) (· ≤ ·) := {
  refl := le_refl
}

/--
All natural numbers are _greater than or equivalent to_ zero.

**Property intuition**: Zero is the "starting point" for the natural numbers.

**Proof intuition**: Follows directly from the definition of _less than or
equivalent to_, and zero being the additive identity.
-/
theorem ge_zero {n : ℕ} : n ≥ 0 := by
  have : 0 + n ≃ n := AA.identL
  have : n ≥ 0 := le_defn.mpr (Exists.intro n ‹0 + n ≃ n›)
  exact this

theorem le_step_split {n m : ℕ} : n ≤ step m → n ≤ m ∨ n ≃ step m := by
  intro (_ : n ≤ step m)
  show n ≤ m ∨ n ≃ step m
  have ⟨d, (_ : n + d ≃ step m)⟩ := le_defn.mp ‹n ≤ step m›
  let motive := λ x => d ≃ x → n ≤ m ∨ n ≃ step m
  apply (cases_on (motive := motive) d · · Rel.refl)
  · intro (_ : d ≃ 0)
    apply Or.inr
    show n ≃ step m
    calc
      n      ≃ _ := Rel.symm add_zero
      n + 0  ≃ _ := by srw [←‹d ≃ 0›]
      n + d  ≃ _ := ‹n + d ≃ step m›
      step m ≃ _ := Rel.refl
  · intro e (_ : d ≃ step e)
    apply Or.inl
    show n ≤ m
    apply le_defn.mpr
    exists e
    show n + e ≃ m
    apply AA.inject (f := step) (rβ := (· ≃ ·))
    show step (n + e) ≃ step m
    calc
      step (n + e) ≃ _ := Rel.symm add_step
      n + step e   ≃ _ := by srw [←‹d ≃ step e›]
      n + d        ≃ _ := ‹n + d ≃ step m›
      step m       ≃ _ := Rel.refl

theorem le_step {n m : ℕ} : n ≤ m → n ≤ step m := by
  intro (_ : n ≤ m)
  show n ≤ step m
  have ⟨d, (_ : n + d ≃ m)⟩ := le_defn.mp ‹n ≤ m›
  apply le_defn.mpr
  exists step d
  show n + step d ≃ step m
  calc
    n + step d   ≃ _ := add_step
    step (n + d) ≃ _ := by srw [‹n + d ≃ m›]
    step m       ≃ _ := Rel.refl

/--
The _less than or equal to_ relation can be extended through intermediate
values.
-/
theorem le_trans {n m k : ℕ} : n ≤ m → m ≤ k → n ≤ k := by
  intro (_ : n ≤ m)
  have ⟨d, (_ : n + d ≃ m)⟩ := le_defn.mp ‹n ≤ m›
  apply ind_on (motive := λ k => m ≤ k → n ≤ k) k
  case zero =>
    intro (_ : m ≤ 0)
    have ⟨e, (_ : m + e ≃ 0)⟩ := le_defn.mp ‹m ≤ 0›
    show n ≤ 0
    apply le_defn.mpr
    exists d + e
    show n + (d + e) ≃ 0
    calc
      n + (d + e) ≃ _ := Rel.symm AA.assoc
      (n + d) + e ≃ _ := by srw [‹n + d ≃ m›]
      m + e       ≃ _ := ‹m + e ≃ 0›
      0           ≃ _ := Rel.refl
  case step =>
    intro k (ih : m ≤ k → n ≤ k) (_ : m ≤ step k)
    show n ≤ step k
    match le_step_split ‹m ≤ step k› with
    | Or.inl (_ : m ≤ k) =>
      have : n ≤ k := ih ‹m ≤ k›
      have : n ≤ step k := le_step ‹n ≤ k›
      exact this
    | Or.inr (_ : m ≃ step k) =>
      have : n ≤ step k := by prw [‹m ≃ step k›] ‹n ≤ m›
      exact this

instance trans_le_le_le : Trans (α := ℕ) (· ≤ ·) (· ≤ ·) (· ≤ ·) := {
  trans := le_trans
}

/--
The _less than or equal to_ relation is preserved when the same value is
added on the right to both sides.
-/
@[gcongr]
theorem add_substL_le {n₁ n₂ m : ℕ} : n₁ ≤ n₂ → n₁ + m ≤ n₂ + m := by
  intro (_ : n₁ ≤ n₂)
  show n₁ + m ≤ n₂ + m
  have ⟨d, (_ : n₁ + d ≃ n₂)⟩ := le_defn.mp ‹n₁ ≤ n₂›
  apply le_defn.mpr
  exists d
  show (n₁ + m) + d ≃ n₂ + m
  calc
    (n₁ + m) + d ≃ _ := AA.assoc
    n₁ + (m + d) ≃ _ := by srw [AA.comm]
    n₁ + (d + m) ≃ _ := Rel.symm AA.assoc
    (n₁ + d) + m ≃ _ := by srw [‹n₁ + d ≃ n₂›]
    n₂ + m       ≃ _ := Rel.refl

/--
The _less than or equal to_ relation is preserved when the same value is
added on the left to both sides.
-/
@[gcongr]
theorem add_substR_le {n₁ n₂ m : ℕ} : n₁ ≤ n₂ → m + n₁ ≤ m + n₂ := by
  intro (_ : n₁ ≤ n₂)
  show m + n₁ ≤ m + n₂
  calc
    _ = m + n₁ := rfl
    _ ≃ n₁ + m := add_comm
    _ ≤ n₂ + m := by srw [‹n₁ ≤ n₂›]
    _ ≃ m + n₂ := add_comm

instance le_substitutive_add
    : AA.Substitutive₂ (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => add_substL_le }
  substitutiveR := { subst₂ := λ (_ : True) => add_substR_le }
}

/--
The _less than or equal to_ relation is preserved when the same value is
removed from the left side of an addition on both sides of an equivalence.
-/
theorem le_cancel_add {n m₁ m₂ : ℕ} : n + m₁ ≤ n + m₂ → m₁ ≤ m₂ := by
  intro (_ : n + m₁ ≤ n + m₂)
  show m₁ ≤ m₂
  have ⟨d, (_ : (n + m₁) + d ≃ n + m₂)⟩ := le_defn.mp ‹n + m₁ ≤ n + m₂›
  apply le_defn.mpr
  exists d
  show m₁ + d ≃ m₂
  have : n + (m₁ + d) ≃ n + m₂ := calc
    n + (m₁ + d) ≃ _ := Rel.symm AA.assoc
    (n + m₁) + d ≃ _ := ‹(n + m₁) + d ≃ n + m₂›
    n + m₂       ≃ _ := Rel.refl
  exact AA.cancelL ‹n + (m₁ + d) ≃ n + m₂›

@[implicit_reducible]
def le_cancelL_add
    : AA.CancellativeOn Hand.L (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·)
    := {
  cancel := λ (_ : True) => le_cancel_add
}

instance le_cancellative_add
    : AA.Cancellative (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·) := {
  cancellativeL := le_cancelL_add
  cancellativeR := AA.cancelR_from_cancelL le_cancelL_add
}

/-- Two natural numbers `n` and `m` are equal if `n ≤ m` and `m ≤ n`. -/
theorem le_antisymm {n m : ℕ} : n ≤ m → m ≤ n → n ≃ m := by
  intro (_ : n ≤ m) (_ : m ≤ n)
  show n ≃ m
  have (Exists.intro (d₁ : ℕ) (_ : n + d₁ ≃ m)) := le_defn.mp ‹n ≤ m›
  have (Exists.intro (d₂ : ℕ) (_ : m + d₂ ≃ n)) := le_defn.mp ‹m ≤ n›
  have : n + (d₁ + d₂) ≃ n + 0 := calc
    n + (d₁ + d₂) ≃ _ := Rel.symm AA.assoc
    (n + d₁) + d₂ ≃ _ := by srw [‹n + d₁ ≃ m›]
    m + d₂        ≃ _ := ‹m + d₂ ≃ n›
    n             ≃ _ := Rel.symm add_zero
    n + 0         ≃ _ := Rel.refl
  have : d₁ + d₂ ≃ 0 := AA.cancelL ‹n + (d₁ + d₂) ≃ n + 0›
  have (And.intro (_ : d₁ ≃ 0) _) := zero_sum_split.mp ‹d₁ + d₂ ≃ 0›
  calc
    n      ≃ _ := Rel.symm add_zero
    n + 0  ≃ _ := by srw [←‹d₁ ≃ 0›]
    n + d₁ ≃ _ := ‹n + d₁ ≃ m›
    m      ≃ _ := Rel.refl

/--
Equivalent natural numbers can be substituted on the left side of _less than_.
-/
@[gcongr]
theorem lt_subst_eqv {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ < m → n₂ < m := by
  intro (_ : n₁ ≃ n₂) (_ : n₁ < m)
  show n₂ < m
  have ⟨(_ : n₁ ≤ m), (_ : n₁ ≄ m)⟩ := lt_defn.mp ‹n₁ < m›
  have : n₂ ≤ m := by prw [‹n₁ ≃ n₂›] ‹n₁ ≤ m›
  have : n₂ ≄ m := by prw [‹n₁ ≃ n₂›] ‹n₁ ≄ m›
  apply lt_defn.mpr
  exact ⟨‹n₂ ≤ m›, ‹n₂ ≄ m›⟩

/--
Corollary of `lt_subst_eqv` to support transitivity of equivalence and _less
than_.
-/
theorem trans_eqv_lt_lt {n m k : ℕ} : n ≃ m → m < k → n < k := by
  intro (_ : n ≃ m) (_ : m < k)
  show n < k
  prw [←‹n ≃ m›] ‹m < k›

instance trans_eqv_lt_lt_inst : Trans (α := ℕ) (· ≃ ·) (· < ·) (· < ·) := {
  trans := trans_eqv_lt_lt
}

/--
Join a _greater than_ relation and a _equivalent to_ relation that share an
operand into another _greater than_ relation.
-/
theorem trans_gt_eqv_gt {n m k : ℕ} : n > m → m ≃ k → n > k := by
  intro (_ : n > m) (_ : m ≃ k)
  show n > k
  have : k < n := by prw [‹m ≃ k›] ‹m < n›
  exact this

instance trans_gt_eqv_gt_inst : Trans (α := ℕ) (· > ·) (· ≃ ·) (· > ·) := {
  trans := trans_gt_eqv_gt
}

instance lt_substitutive_eqv
    : AA.Substitutive₂ (α := ℕ) (· < ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ _ => lt_subst_eqv }
  substitutiveR := { subst₂ := λ _ => lt_eqv_subst }
}

/-- A natural number is always less than its successor. -/
theorem lt_step {n : ℕ} : n < step n := by
  show n < step n
  apply lt_defn.mpr
  apply And.intro
  · show n ≤ step n
    apply le_defn.mpr
    exists (1 : ℕ)
    show n + 1 ≃ step n
    exact add_one_step
  · show n ≄ step n
    exact Rel.symm step_neqv

/-- The natural number two is greater than one. -/
theorem two_gt_one : (2:ℕ) > 1 := calc
  _ = (1:ℕ)  := rfl
  _ < step 1 := lt_step
  _ ≃ 2      := Rel.symm literal_step

/--
The same number can be added (on the right) to both sides of a _less than_
relation, preserving the ordering of the left operands.

**Property intuition**: Increasing two numbers by the same amount keeps them
the same distance apart.

**Proof intuition**: Split _less than_ into _less than or equivalent to_ and
_not equivalent to_. Show that both of them are preserved under addition. Put
them back together.
-/
@[gcongr]
theorem lt_substL_add {n₁ n₂ m : ℕ} : n₁ < n₂ → n₁ + m < n₂ + m := by
  intro (_ : n₁ < n₂)
  show n₁ + m < n₂ + m
  have (And.intro (_ : n₁ ≤ n₂) (_ : n₁ ≄ n₂)) := lt_defn.mp ‹n₁ < n₂›
  have : n₁ + m ≤ n₂ + m := by srw [‹n₁ ≤ n₂›]
  have : n₁ + m ≄ n₂ + m := mt AA.cancelR ‹n₁ ≄ n₂›
  have : n₁ + m < n₂ + m :=
    lt_defn.mpr (And.intro ‹n₁ + m ≤ n₂ + m› ‹n₁ + m ≄ n₂ + m›)
  exact this

/--
The same number can be added (on the left) to both sides of a _less than_
relation, preserving the ordering of the right operands.

**Property intuition**: Increasing two numbers by the same amount keeps them
the same distance apart.

**Proof intuition**: Use commutativity of addition with the opposite-hand
version of this theorem.
-/
@[gcongr]
theorem lt_substR_add {n₁ n₂ m : ℕ} : n₁ < n₂ → m + n₁ < m + n₂ := by
  intro (_ : n₁ < n₂)
  show m + n₁ < m + n₂
  calc
    _ = m + n₁ := rfl
    _ ≃ n₁ + m := add_comm
    _ < n₂ + m := by srw [‹n₁ < n₂›]
    _ ≃ m + n₂ := add_comm

variable [Sign ℕ]

/--
A useful way to convert between _less than_ and _less than or equal to_ while
keeping the larger number fixed.
-/
theorem lt_step_le {n m : ℕ} : n < m ↔ step n ≤ m := by
  apply Iff.intro
  · intro (_ : n < m)
    show step n ≤ m
    have ⟨(_ : n ≤ m), (_ : n ≄ m)⟩ := lt_defn.mp ‹n < m›
    have ⟨d, (_ : n + d ≃ m)⟩ := le_defn.mp ‹n ≤ m›
    have : d ≄ 0 := by
      intro (_ : d ≃ 0)
      show False
      apply ‹n ≄ m›
      show n ≃ m
      calc
        n     ≃ _ := Rel.symm add_zero
        n + 0 ≃ _ := by srw [←‹d ≃ 0›]
        n + d ≃ _ := ‹n + d ≃ m›
        m     ≃ _ := Rel.refl
    have : Positive d := Signed.positive_defn.mpr ‹d ≄ 0›
    have ⟨d', (_ : step d' ≃ d)⟩ := positive_step ‹Positive d›
    show step n ≤ m
    apply le_defn.mpr
    exists d'
    show step n + d' ≃ m
    calc
      step n + d'   ≃ _ := step_add
      step (n + d') ≃ _ := Rel.symm add_step
      n + step d'   ≃ _ := by srw [‹step d' ≃ d›]
      n + d         ≃ _ := ‹n + d ≃ m›
      m             ≃ _ := Rel.refl
  · intro (_ : step n ≤ m)
    show n < m
    have ⟨d, (_ : step n + d ≃ m)⟩ := le_defn.mp ‹step n ≤ m›
    have : n + step d ≃ m := calc
      n + step d   ≃ _ := add_step
      step (n + d) ≃ _ := Rel.symm step_add
      step n + d   ≃ _ := ‹step n + d ≃ m›
      m            ≃ _ := Rel.refl
    have : ∃ d, n + d ≃ m := ⟨step d, ‹n + step d ≃ m›⟩
    have : n ≤ m := le_defn.mpr ‹∃ d, n + d ≃ m›
    have : n ≄ m := by
      intro (_ : n ≃ m)
      show False
      have : n + step d ≃ n + 0 := calc
        n + step d ≃ _ := ‹n + step d ≃ m›
        m          ≃ _ := Rel.symm ‹n ≃ m›
        n          ≃ _ := Rel.symm add_zero
        n + 0      ≃ _ := Rel.refl
      have : step d ≃ 0 := AA.cancelL ‹n + step d ≃ n + 0›
      exact absurd ‹step d ≃ 0› step_neqv_zero
    show n < m
    apply lt_defn.mpr
    exact ⟨‹n ≤ m›, ‹n ≄ m›⟩

/--
Convert between _less than_ and _less than or equivalent to_ by adding or
removing `step` from the right-hand operand.

**Property intuition**: Even if `n ≃ m`, we must have `n < step m` because
`m < step m`.

**Proof intuition**: Use previous results to convert mechanically between the
expressions.
-/
theorem lt_stepR {n m : ℕ} : n < step m ↔ n ≤ m := calc
  _ ↔ n < step m      := Iff.rfl
  _ ↔ step n ≤ step m := lt_step_le
  _ ↔ n ≤ m           := Iff.intro AA.inject AA.subst₁

/--
The _less than_ relation between two natural numbers `n` and `m` is
equivalent to there being a positive natural number -- the _difference_
between `n` and `m` -- that, when added to `n`, results in `m`.

**Intuition**: This is already quite intuitive, as it's clear that for one
number to be less than another, there must be a nonzero gap between them.
-/
theorem lt_defn_add {n m : ℕ} : n < m ↔ ∃ k, Positive k ∧ m ≃ n + k := by
  apply Iff.intro
  · intro (_ : n < m)
    show ∃ k, Positive k ∧ m ≃ n + k
    have : step n ≤ m := lt_step_le.mp ‹n < m›
    have ⟨k, (_ : step n + k ≃ m)⟩ := le_defn.mp ‹step n ≤ m›
    exists step k
    apply And.intro
    · show Positive (step k)
      have : step k ≄ 0 := step_neqv_zero
      have : Positive (step k) := Signed.positive_defn.mpr ‹step k ≄ 0›
      exact this
    · show m ≃ n + step k
      calc
        m            ≃ _ := Rel.symm ‹step n + k ≃ m›
        step n + k   ≃ _ := step_add
        step (n + k) ≃ _ := Rel.symm add_step
        n + step k   ≃ _ := Rel.refl
  · intro ⟨k, (_ : Positive k), (_ : m ≃ n + k)⟩
    show n < m
    apply lt_step_le.mpr
    show step n ≤ m
    apply le_defn.mpr
    show ∃ k, step n + k ≃ m
    have ⟨k', (_ : step k' ≃ k)⟩ := positive_step ‹Positive k›
    exists k'
    show step n + k' ≃ m
    calc
      step n + k'   ≃ _ := step_add
      step (n + k') ≃ _ := Rel.symm add_step
      n + step k'   ≃ _ := by srw [‹step k' ≃ k›]
      n + k         ≃ _ := Rel.symm ‹m ≃ n + k›
      m             ≃ _ := Rel.refl

/-- No natural number is less than zero. -/
theorem lt_zero {n : ℕ} : n ≮ 0 := by
  intro (_ : n < 0)
  show False
  have : step n ≤ 0 := lt_step_le.mp ‹n < 0›
  have ⟨d, (_ : step n + d ≃ 0)⟩ := le_defn.mp ‹step n ≤ 0›
  have : step (n + d) ≃ 0 := calc
    step (n + d) ≃ _ := Rel.symm step_add
    step n + d   ≃ _ := ‹step n + d ≃ 0›
    0            ≃ _ := Rel.refl
  exact absurd ‹step (n + d) ≃ 0› step_neqv_zero

/--
A natural number is positive iff it's greater than zero.

**Proof intuition**: The _less than_ relation can be defined in terms of a
positive difference between its two arguments. If the left argument is zero,
then the right argument must be positive.
-/
theorem lt_zero_pos {n : ℕ} : Positive n ↔ n > 0 := by
  apply Iff.intro
  · intro (_ : Positive n)
    show 0 < n
    apply lt_defn_add.mpr
    show ∃ k, Positive k ∧ n ≃ 0 + k
    exists n
    apply And.intro
    · show Positive n
      exact ‹Positive n›
    · show n ≃ 0 + n
      exact Rel.symm zero_add
  · intro (_ : 0 < n)
    show Positive n
    have ⟨k, ⟨(_ : Positive k), (_ : n ≃ 0 + k)⟩⟩ := lt_defn_add.mp ‹0 < n›
    have : k ≃ n := Rel.symm (Rel.trans ‹n ≃ 0 + k› zero_add)
    have : Positive n := by prw [‹k ≃ n›] ‹Positive k›
    exact this

/--
The _less than or equivalent to_ relation can be formed from, or split into,
the two relations in its name.

**Proof intuition**: In the forward direction, expand the definition of `n ≤ m`
into `∃ d, n + d ≃ m`. Case split on `d`: if it's zero, then `n ≃ m`; otherwise
it's greater than zero and `n < m`. In the reverse direction, `n < m` includes
`n ≤ m` in its definition, and if `n ≃ m` then `n ≤ n` implies `n ≤ m`.
-/
theorem le_split {n m : ℕ} : n ≤ m ↔ n < m ∨ n ≃ m := by
  apply Iff.intro
  case mp =>
    intro (_ : n ≤ m)
    show n < m ∨ n ≃ m
    have (Exists.intro (d : ℕ) (_ : n + d ≃ m)) := le_defn.mp ‹n ≤ m›
    have : d ≃ 0 ∨ ∃ (d' : ℕ), d ≃ step d' := split_cases d
    match this with
    | Or.inl (_ : d ≃ 0) =>
      have : n ≃ m := calc
        _ = n     := rfl
        _ ≃ n + 0 := Rel.symm add_zero
        _ ≃ n + d := by srw [←‹d ≃ 0›]
        _ ≃ m     := ‹n + d ≃ m›
      exact Or.inr ‹n ≃ m›
    | Or.inr (Exists.intro (d' : ℕ) (_ : d ≃ step d')) =>
      have : step n + d' ≃ m := calc
        _ = step n + d'   := rfl
        _ ≃ n + step d'   := step_add_swap
        _ ≃ n + d         := by srw [←‹d ≃ step d'›]
        _ ≃ m             := ‹n + d ≃ m›
      have : step n ≤ m := le_defn.mpr (Exists.intro d' ‹step n + d' ≃ m›)
      have : n < m := lt_step_le.mpr ‹step n ≤ m›
      exact Or.inl ‹n < m›
  case mpr =>
    intro (_ : n < m ∨ n ≃ m)
    show n ≤ m
    match ‹n < m ∨ n ≃ m› with
    | Or.inl (_ : n < m) =>
      have (And.intro (_ : n ≤ m) _) := lt_defn.mp ‹n < m›
      exact ‹n ≤ m›
    | Or.inr (_ : n ≃ m) =>
      have : n ≤ n := Rel.refl
      have : n ≤ m := by prw [‹n ≃ m›] ‹n ≤ n›
      exact this

/--
Split _greater than or equivalent to_ into the relations implied by its name.

**Proof intuition**: Flip the relation around and use `le_split`.
-/
theorem ge_split {n m : ℕ} : n ≥ m → n > m ∨ n ≃ m := by
  intro (_ : n ≥ m)
  show n > m ∨ n ≃ m
  have : m ≤ n := ‹n ≥ m›
  have : m < n ∨ m ≃ n := le_split.mp this
  match this with
  | Or.inl (_ : m < n) =>
    have : n > m := ‹m < n›
    exact Or.inl this
  | Or.inr (_ : m ≃ n) =>
    have : n ≃ m := Rel.symm ‹m ≃ n›
    exact Or.inr this

/--
Add/remove `step` from the right-hand operand of _less than or equivalent to_.

**Property intuition**: For the conversion to work, we need to account for the
possibility that `n ≃ step m`.

**Proof intuition**: Split `n ≤ step m` into its _less than_ or _equivalent to_
cases, and transform the _less than_ case.
-/
theorem le_stepR {n m : ℕ} : n ≤ step m ↔ n ≤ m ∨ n ≃ step m := calc
  _ ↔ n ≤ step m              := Iff.rfl
  _ ↔ n < step m ∨ n ≃ step m := le_split
  _ ↔ n ≤ m ∨ n ≃ step m      := iff_subst_covar or_mapL lt_stepR

/--
Induction starting from an arbitrary natural number.

**Property intuition**: Induction works fine with non-zero base cases, since
the whole idea is to show that we can reach arbitrarily high by iterating the
inductive step. As long as you don't care about proving the motive for values
below your chosen starting point.

**Proof intuition**: Uses standard induction, proving the origial motive
restricted to inputs _greater than or equivalent to_ the chosen starting point.
For the zero case, show that the starting point must be zero, and thus the
result is given by the `motive m` base case. For the successor case, we have
`step k ≥ m` which we can split into `k ≥ m` and `step k ≃ m`. The first option
follows from the inductive hypothesis; the second option follows from the given
base case `motive m`.
-/
theorem ind_from
    {motive : ℕ → Prop}
    (motive_subst : {k₁ k₂ : ℕ} → k₁ ≃ k₂ → motive k₁ → motive k₂)
    {n m : ℕ} (n_ge_m : n ≥ m)
    (base : motive m) (next : {k : ℕ} → k ≥ m → motive k → motive (step k))
    : motive n
    := by
  let motive' := λ x => x ≥ m → motive x
  have z : motive' 0 := by
    intro (_ : 0 ≥ m)
    show motive 0
    have : m ≥ 0 := ge_zero
    have : m ≃ 0 := le_antisymm ‹m ≤ 0› ‹0 ≤ m›
    have : motive 0 := motive_subst ‹m ≃ 0› ‹motive m›
    exact this
  have s : (k : ℕ) → motive' k → motive' (step k) := by
    intro (k : ℕ) (ih : k ≥ m → motive k) (_ : step k ≥ m)
    show motive (step k)
    have : m ≤ k ∨ m ≃ step k := le_stepR.mp ‹m ≤ step k›
    match ‹m ≤ k ∨ m ≃ step k› with
    | Or.inl (_ : m ≤ k) =>
      have : motive k := ih ‹k ≥ m›
      have : motive (step k) := next ‹k ≥ m› ‹motive k›
      exact this
    | Or.inr (_ : m ≃ step k) =>
      have : motive (step k) := motive_subst ‹m ≃ step k› ‹motive m›
      exact this
  have : n ≥ m → motive n := ind_on n z s
  have : motive n := this ‹n ≥ m›
  exact this

/--
Useful result when needing to decrement the larger number in a _less than_
relation.
-/
theorem lt_split {n m : ℕ} : n < step m → n < m ∨ n ≃ m := by
  intro (_ : n < step m)
  show n < m ∨ n ≃ m
  have : n ≤ m := lt_stepR.mp ‹n < step m›
  exact le_split.mp ‹n ≤ m›

/--
Useful result when needing to decrement the larger number in a _greater than_
relation.
-/
theorem gt_split {n m : ℕ} : step m > n → m ≃ n ∨ m > n := by
  intro (_ : step m > n)
  show m ≃ n ∨ m > n
  have : n < m ∨ n ≃ m := lt_split ‹n < step m›
  match this with
  | Or.inl (_ : n < m) =>
    have : m ≃ n ∨ m > n := Or.inr ‹m > n›
    exact this
  | Or.inr (_ : n ≃ m) =>
    have : m ≃ n ∨ m > n := Or.inl (Rel.symm ‹n ≃ m›)
    exact this

/-- The _less than_ relation can be extended through intermediate values. -/
theorem lt_trans {n m k : ℕ} : n < m → m < k → n < k := by
  intro (_ : n < m) (_ : m < k)
  show n < k
  apply lt_step_le.mpr
  show step n ≤ k
  calc
    step n ≤ _ := lt_step_le.mp ‹n < m›
    m      ≤ _ := le_split.mpr (Or.inl lt_step)
    step m ≤ _ := lt_step_le.mp ‹m < k›
    k      ≤ _ := Rel.refl

instance trans_lt_lt_lt : Trans (α := ℕ) (· < ·) (· < ·) (· < ·) := {
  trans := lt_trans
}

/--
Join a _less than_ relation and a _less than or equivalent_ relation that share
an operand into another _less than_ relation.

**Property intuition**: The hypotheses say that `n` and `m` are separated by
some amount, and that `m` and `k` are separated by another. Thus `n` and `k`
must be separated by some amount as well, and it must be a nonzero amount
because `n` and `m` are separated by a nonzero amount.

**Proof intuition**: Split _less than or equivalent_ into cases and use an
existing transitivity property for each case.
-/
theorem trans_lt_le_lt {n m k : ℕ} : n < m → m ≤ k → n < k := by
  intro (_ : n < m) (_ : m ≤ k)
  show n < k
  have : m < k ∨ m ≃ k := le_split.mp ‹m ≤ k›
  match this with
  | Or.inl (_ : m < k) =>
    have : n < k := lt_trans ‹n < m› ‹m < k›
    exact this
  | Or.inr (_ : m ≃ k) =>
    have : n < k := trans_lt_eqv_lt ‹n < m› ‹m ≃ k›
    exact this

instance trans_lt_le_lt_inst : Trans (α := ℕ) (· < ·) (· ≤ ·) (· < ·) := {
  trans := trans_lt_le_lt
}

/--
Join a _less than or equivalent_ relation and a _less than_ relation that share
an operand into another _less than_ relation.

**Property intuition**: The hypotheses say that `n` and `m` are separated by
some amount, and that `m` and `k` are separated by another. Thus `n` and `k`
must be separated by some amount as well, and it must be a nonzero amount
because `m` and `k` are separated by a nonzero amount.

**Proof intuition**: Split _less than or equivalent_ into cases and use an
existing transitivity property for each case.
-/
theorem trans_le_lt_lt {n m k : ℕ} : n ≤ m → m < k → n < k := by
  intro (_ : n ≤ m) (_ : m < k)
  show n < k
  have : n < m ∨ n ≃ m := le_split.mp ‹n ≤ m›
  match this with
  | Or.inl (_ : n < m) =>
    have : n < k := lt_trans ‹n < m› ‹m < k›
    exact this
  | Or.inr (_ : n ≃ m) =>
    have : n < k := trans_eqv_lt_lt ‹n ≃ m› ‹m < k›
    exact this

instance trans_le_lt_lt_inst : Trans (α := ℕ) (· ≤ ·) (· < ·) (· < ·) := {
  trans := trans_le_lt_lt
}

/--
Join a _greater than_ relation and a _greater than or equivalent to_ relation
that share an operand into another _greater than_ relation.
-/
theorem trans_gt_ge_gt {n m k : ℕ} : n > m → m ≥ k → n > k := by
  intro (_ : n > m) (_ : m ≥ k)
  show n > k
  have : k < n := trans ‹k ≤ m› ‹m < n›
  exact ‹n > k›

instance trans_gt_ge_gt_inst : Trans (α := ℕ) (· > ·) (· ≥ ·) (· > ·) := {
  trans := trans_gt_ge_gt
}

/-- Positive natural numbers are nonzero. -/
theorem neqv_zero_from_gt_zero {n : ℕ} : n > 0 → n ≄ 0 := by
  intro (_ : n > 0)
  have : Positive n := Natural.lt_zero_pos.mpr ‹n > 0›
  have : n ≄ 0 := Signed.positive_defn.mp ‹Positive n›
  exact this

/--
Positive natural numbers are exactly those that are greater than or equivalent
to one.

**Property and proof intuition**: Follows directly from `lt_zero_pos` (positive
naturals are greater than zero) and ordering properties.
-/
theorem positive_ge {n : ℕ} : Positive n ↔ n ≥ 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : Positive n)
    show n ≥ 1
    have : n > 0 := lt_zero_pos.mp ‹Positive n›
    calc
      _ = (1:ℕ)  := rfl
      _ ≃ step 0 := literal_step
      _ ≤ n      := lt_step_le.mp ‹n > 0›
  case mpr =>
    intro (_ : n ≥ 1)
    show Positive n
    have : n > 0 := calc
      _ = (0:ℕ) := rfl
      _ < step 0 := lt_step
      _ ≃ 1      := Rel.symm literal_step
      _ ≤ n      := ‹n ≥ 1›
    have : Positive n := lt_zero_pos.mpr this
    exact this

/--
Integers greater than zero are exactly those that are greater than or
equivalent to one.

**Property intuition**: There's no integer between zero and one.

**Proof intuition**: Follows from `lt_zero_pos` and `positive_ge`.
-/
theorem gt_zero_iff_ge_one {n : ℕ} : n > 0 ↔ n ≥ 1 := calc
  _ ↔ n > 0      := Iff.rfl
  _ ↔ Positive n := lt_zero_pos.symm
  _ ↔ n ≥ 1      := positive_ge

/--
Very general property about ordering which often simplifies proofs that would
otherwise have had to use induction.
-/
theorem trichotomy (n m : ℕ)
    : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m) := by
  constructor
  case atLeastOne =>
    let motive := λ n => AA.OneOfThree (n < m) (n ≃ m) (n > m)
    apply ind_on (motive := motive) n
    case zero =>
      show AA.OneOfThree (0 < m) (0 ≃ m) (0 > m)
      let motive := λ m : ℕ => AA.OneOfThree (0 < m) (0 ≃ m) (0 > m)
      apply cases_on (motive := motive) m
      case zero =>
        apply AA.OneOfThree.second
        show 0 ≃ 0
        exact Rel.refl
      case step =>
        intro m
        apply AA.OneOfThree.first
        show 0 < step m
        apply lt_defn.mpr
        apply And.intro
        · show 0 ≤ step m
          apply le_defn.mpr
          exists step m
          exact zero_add
        · show 0 ≄ step m
          exact Rel.symm step_neqv_zero
    case step =>
      intro n (ih : AA.OneOfThree (n < m) (n ≃ m) (n > m))
      show AA.OneOfThree (step n < m) (step n ≃ m) (step n > m)
      match ih with
      | AA.OneOfThree.first (_ : n < m) =>
        have : step n ≤ m := lt_step_le.mp ‹n < m›
        have : step n < m ∨ step n ≃ m := le_split.mp ‹step n ≤ m›
        match ‹step n < m ∨ step n ≃ m› with
        | Or.inl (_ : step n < m) => exact AA.OneOfThree.first ‹step n < m›
        | Or.inr (_ : step n ≃ m) => exact AA.OneOfThree.second ‹step n ≃ m›
      | AA.OneOfThree.second (_ : n ≃ m) =>
        have : m ≃ n := Rel.symm ‹n ≃ m›
        have : m ≤ n := le_split.mpr (Or.inr ‹m ≃ n›)
        have : step m ≤ step n := by srw [‹m ≤ n›]
        have : m < step n := lt_step_le.mpr ‹step m ≤ step n›
        apply AA.OneOfThree.third
        exact ‹m < step n›
      | AA.OneOfThree.third (_ : n > m) =>
        apply AA.OneOfThree.third
        show m < step n
        exact lt_trans ‹m < n› lt_step
  case atMostOne =>
    show ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m)
    intro
    | AA.TwoOfThree.oneAndTwo (_ : n < m) (_ : n ≃ m) =>
      show False
      have ⟨_, (_ : n ≄ m)⟩ := lt_defn.mp ‹n < m›
      exact absurd ‹n ≃ m› ‹n ≄ m›
    | AA.TwoOfThree.oneAndThree (_ : n < m) (_ : n > m) =>
      show False
      have ⟨(_ : n ≤ m), (_ : n ≄ m)⟩ := lt_defn.mp ‹n < m›
      have ⟨(_ : m ≤ n), _⟩ := lt_defn.mp ‹n > m›
      have : n ≃ m := le_antisymm ‹n ≤ m› ‹m ≤ n›
      exact absurd ‹n ≃ m› ‹n ≄ m›
    | AA.TwoOfThree.twoAndThree (_ : n ≃ m) (_ : n > m) =>
      show False
      have ⟨_, (_ : m ≄ n)⟩ := lt_defn.mp ‹n > m›
      exact absurd ‹n ≃ m› (Rel.symm ‹m ≄ n›)

/--
Two natural numbers cannot be both _less than or equivalent to_ and
_greater than_ each other.
-/
theorem le_gt_false {n m : ℕ} : n ≤ m → n > m → False := by
  intro (_ : n ≤ m) (_ : n > m)
  show False

  let twoOfThree := AA.TwoOfThree (n < m) (n ≃ m) (n > m)
  have : twoOfThree := match show n < m ∨ n ≃ m from le_split.mp ‹n ≤ m› with
  | .inl (_ : n < m) => .oneAndThree ‹n < m› ‹n > m›
  | .inr (_ : n ≃ m) => .twoAndThree ‹n ≃ m› ‹n > m›
  have : ¬twoOfThree := (trichotomy n m).atMostOne
  exact absurd ‹twoOfThree› ‹¬twoOfThree›

/--
Defines `compare`, a comparison function on natural numbers, that determines
the ordering between any two of them: whether one is less than, equivalent to,
or greater than the other.
-/
class Compare (ℕ : Type) [Core ℕ] [Addition ℕ] [Order ℕ] extends Ord ℕ where
  /--
  Replacing `compare`'s left operand with an equivalent natural number gives an
  identical result.
  -/
  compare_substL {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → compare n₁ m = compare n₂ m

  /--
  Replacing `compare`'s right operand with an equivalent natural number gives
  an identical result.
  -/
  compare_substR {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → compare m n₁ = compare m n₂

  /--
  If `compare` returns `Ordering.lt`, its first argument is less than its
  second argument.
  -/
  compare_lt {n m : ℕ} : compare n m = Ordering.lt ↔ n < m

  /-- If `compare` returns `Ordering.eq`, its arguments are equivalent. -/
  compare_eq {n m : ℕ} : compare n m = Ordering.eq ↔ n ≃ m

  /--
  If `compare` returns `Ordering.gt`, its first argument is greater than its
  second argument.
  -/
  compare_gt {n m : ℕ} : compare n m = Ordering.gt ↔ n > m

export Compare (compare_eq compare_gt compare_lt compare_substL compare_substR)

variable [Compare ℕ]

/--
Increasing `compare`'s operands by the same amount gives an identical result.

**Property intuition**: The distance between the operands doesn't change.

**Proof intuition**: There are three possible relations between `compare`'s
operands, by trichotomy. Show via substitution and transitivity that each one
is unchanged under addition.
-/
theorem compare_add {n m k : ℕ} : compare n m = compare (n + k) (m + k) := by
  have tri : AA.OneOfThree (n < m) (n ≃ m) (n > m) :=
    (trichotomy n m).atLeastOne
  match tri with
  | AA.OneOfThree.first (_ : n < m) =>
    have : compare n m = Ordering.lt := compare_lt.mpr ‹n < m›
    have : n + k < m + k := by srw [‹n < m›]
    have : compare (n + k) (m + k) = Ordering.lt := compare_lt.mpr this
    calc
      compare n m
        = _ := ‹compare n m = Ordering.lt›
      Ordering.lt
        = _ := by rw [‹compare (n + k) (m + k) = Ordering.lt›]
      compare (n + k) (m + k)
        = _ := rfl
  | AA.OneOfThree.second (_ : n ≃ m) =>
    have : compare n m = Ordering.eq := compare_eq.mpr ‹n ≃ m›
    have : n + k ≃ m + k := by srw [‹n ≃ m›]
    have : compare (n + k) (m + k) = Ordering.eq :=
      compare_eq.mpr ‹n + k ≃ m + k›
    calc
      compare n m
        = _ := ‹compare n m = Ordering.eq›
      Ordering.eq
        = _ := Eq.symm ‹compare (n + k) (m + k) = Ordering.eq›
      compare (n + k) (m + k)
        = _ := rfl
  | AA.OneOfThree.third (_ : n > m) =>
    have : compare n m = Ordering.gt := compare_gt.mpr ‹n > m›
    have : n + k > m + k := by srw [‹n > m›]
    have : compare (n + k) (m + k) = Ordering.gt :=
      compare_gt.mpr ‹n + k > m + k›
    calc
      compare n m
        = _ := ‹compare n m = Ordering.gt›
      Ordering.gt
        = _ := Eq.symm ‹compare (n + k) (m + k) = Ordering.gt›
      compare (n + k) (m + k)
        = _ := rfl

/--
If two pairs of natural numbers have the same ordering, their component-wise
sum will as well.

**Property intuition**: Adding the components of the pairs will just increase
(or in the case of equality, maintain) the degree of difference. For example,
if the pairs compare as `Ordering.lt`, their first elements are both less than
their second elements. The first element of the sum will be less than the
second element by the combined difference of the input pairs.

**Proof intuition**: For each `Ordering` value, convert the statements about
`compare` into the equivalent statements about ordering relations. Use
addition substitution properties of those relations to obtain the result.
-/
theorem add_preserves_compare
    {ord : Ordering} {n m k j : ℕ}
    : compare n m = ord → compare k j = ord → compare (n + k) (m + j) = ord
    := by
  match ord with
  | Ordering.lt =>
    intro (_ : compare n m = Ordering.lt) (_ : compare k j = Ordering.lt)
    show compare (n + k) (m + j) = Ordering.lt
    have : n < m := compare_lt.mp ‹compare n m = Ordering.lt›
    have : k < j := compare_lt.mp ‹compare k j = Ordering.lt›
    have : n + k < m + j := by srw [‹n < m›, ‹k < j›]
    have : compare (n + k) (m + j) = Ordering.lt := compare_lt.mpr this
    exact this
  | Ordering.eq =>
    intro (_ : compare n m = Ordering.eq) (_ : compare k j = Ordering.eq)
    show compare (n + k) (m + j) = Ordering.eq
    have : n ≃ m := compare_eq.mp ‹compare n m = Ordering.eq›
    have : k ≃ j := compare_eq.mp ‹compare k j = Ordering.eq›
    have : n + k ≃ m + j := by srw [‹n ≃ m›, ‹k ≃ j›]
    have : compare (n + k) (m + j) = Ordering.eq := compare_eq.mpr this
    exact this
  | Ordering.gt =>
    intro (_ : compare n m = Ordering.gt) (_ : compare k j = Ordering.gt)
    show compare (n + k) (m + j) = Ordering.gt
    have : n > m := compare_gt.mp ‹compare n m = Ordering.gt›
    have : k > j := compare_gt.mp ‹compare k j = Ordering.gt›
    have : m + j < n + k := by srw [‹j < k›, ‹m < n›]
    have : compare (n + k) (m + j) = Ordering.gt := compare_gt.mpr this
    exact this

/--
For two natural numbers obeying the _less than or equivalent to_ relation,
compute which more precise relation they obey: _less than_ or
_equivalent to_.
-/
def le_split_either {n m : ℕ} : n ≤ m → Either (n < m) (n ≃ m) := by
  intro (_ : n ≤ m)
  show Either (n < m) (n ≃ m)

  match res : compare n m with
  | .lt =>
    have : compare n m = Ordering.lt := res
    have : n < m := compare_lt.mp ‹compare n m = Ordering.lt›
    exact show Either (n < m) (n ≃ m) from .inl ‹n < m›
  | .eq =>
    have : compare n m = Ordering.eq := res
    have : n ≃ m := compare_eq.mp ‹compare n m = Ordering.eq›
    exact show Either (n < m) (n ≃ m) from .inr ‹n ≃ m›
  | .gt =>
    have : compare n m = Ordering.gt := res
    have : n > m := compare_gt.mp ‹compare n m = Ordering.gt›
    exact show Either (n < m) (n ≃ m) from (le_gt_false ‹n ≤ m› ‹n > m›).elim

variable [Induction.{1} ℕ]

/--
Compute the difference between natural numbers in a
_less than or equivalent to_ relation.
-/
def le_diff {n m : ℕ} : n ≤ m → { d : ℕ // n + d ≃ m } := by
  let motive (x : ℕ) : Type := n ≤ x → { d : ℕ // n + d ≃ x }
  apply ind_on m
  case zero =>
    intro (_ : n ≤ 0)
    show { d : ℕ // n + d ≃ 0 }

    have : n + 0 ≃ 0 := calc
      _ = n + 0 := rfl
      _ ≃ n     := AA.identR
      _ ≃ 0     := le_antisymm ‹n ≤ 0› ge_zero
    have : { d : ℕ // n + d ≃ 0 } := Subtype.mk 0 ‹n + 0 ≃ 0›
    exact this
  case step =>
    intro (m' : ℕ) (ih : n ≤ m' → { d : ℕ // n + d ≃ m' }) (_ : n ≤ step m')
    show { d : ℕ // n + d ≃ step m' }

    have : Either (n < step m') (n ≃ step m') := le_split_either ‹n ≤ step m'›
    match this with
    | .inl (_ : n < step m') =>
      have : n ≤ m' := lt_stepR.mp ‹n < step m'›
      have (Subtype.mk (d : ℕ) (_ : n + d ≃ m')) := ih ‹n ≤ m'›
      have : n + step d ≃ step m' := calc
        _ = n + step d   := rfl
        _ ≃ step (n + d) := add_step
        _ ≃ step m'      := by srw [‹n + d ≃ m'›]
      have : { d : ℕ // n + d ≃ step m' } :=
        Subtype.mk (step d) ‹n + step d ≃ step m'›
      exact this
    | .inr (_ : n ≃ step m') =>
      have : n + 0 ≃ step m' := calc
        _ = n + 0   := rfl
        _ ≃ n       := AA.identR
        _ ≃ step m' := ‹n ≃ step m'›
      have : { d : ℕ // n + d ≃ step m' } := Subtype.mk 0 ‹n + 0 ≃ step m'›
      exact this

end Lean4Axiomatic.Natural

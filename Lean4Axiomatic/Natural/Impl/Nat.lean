import Lean4Axiomatic.Natural
import Lean4Axiomatic.Natural.Impl.Generic

/-!
# Full implementation of `Natural` for Lean's prelude `Nat`
-/

namespace Lean4Axiomatic.Natural.Impl.Nat

open Relation.Equivalence (EqvOp)

local instance constructor_ops : Constructor.Ops Nat := {
  zero := Nat.zero
  step := Nat.succ
}

local instance eqvOp? : Relation.Equivalence.EqvOp? Nat := {
  tildeDash := Eq
  refl := λ {x} => Eq.refl x
  symm := Eq.symm
  trans := Eq.trans
  tildeDashQuestion := Nat.decEq
}

local instance equality : Equality Nat := {
  eqvOp? := eqvOp?
}

local instance literals : Literals Nat := {
  literal := @instOfNatNat
  literal_zero := Rel.refl
  literal_step := Rel.refl
}

@[implicit_reducible]
def step_substitutive
    : AA.Substitutive₁ (step : Nat → Nat) (· ≃ ·) (· ≃ ·)
    := {
  subst₁ := congrArg step
}

theorem succ_injective {n m : Nat} : Nat.succ n = Nat.succ m → n = m
| Eq.refl _ => Eq.refl _

@[implicit_reducible]
def step_injective : AA.Injective (step : Nat → Nat) (· ≃ ·) (· ≃ ·) := {
  inject := succ_injective
}

local instance constructor_props : Constructor.Props Nat := {
  step_neqv_zero := Nat.noConfusion
  step_substitutive := step_substitutive
  step_injective := step_injective
}

local instance core : Core Nat := {}

local instance induction : Induction Nat := {
  ind := Nat.rec
  ind_zero := Rel.refl
  ind_step := Rel.refl
}

local instance addition : Addition Nat := {
  addOp := _root_.instAddNat
  zero_add := @Nat.zero_add
  step_add := @Nat.succ_add
}

local instance multiplication : Multiplication Nat := {
  mulOp := _root_.instMulNat
  zero_mul := @Nat.zero_mul
  step_mul := @Nat.succ_mul
}

local instance sign : Sign Nat := Generic.sign

@[implicit_reducible]
def order : Order Nat := {
  leOp := Generic.le_ex_add
  le_defn := Iff.intro id id

  ltOp := Generic.lt_le_neqv
  lt_defn := Iff.intro id id
}

open Generic (le lt)

def compare : Nat → Nat → Ordering := instOrdNat.compare

/--
Replacing `compare`'s left operand with an equivalent natural number gives an
identical result.

**Property intuition**: This must be true for `compare` to be a valid function.

**Proof intuition**: Equivalence of `Nat`s is just equality, so all functions
are trivially substitutive.
-/
theorem compare_substL
    {n₁ n₂ m : Nat} : n₁ ≃ n₂ → compare n₁ m = compare n₂ m
    := by
  intro (_ : n₁ ≃ n₂)
  show compare n₁ m = compare n₂ m
  rw [‹n₁ ≃ n₂›]

/--
Replacing `compare`'s right operand with an equivalent natural number gives an
identical result.

**Property intuition**: This must be true for `compare` to be a valid function.

**Proof intuition**: Equivalence of `Nat`s is just equality, so all functions
are trivially substitutive.
-/
theorem compare_substR
    {n₁ n₂ m : Nat} : n₁ ≃ n₂ → compare m n₁ = compare m n₂
    := by
  intro (_ : n₁ ≃ n₂)
  show compare m n₁ = compare m n₂
  rw [‹n₁ ≃ n₂›]

/--
Converts the Prelude's _less than or equal to_ relation on `Nat` to ours.

**Proof intuition**: Induction on the structure of `n ≤ m`.
-/
theorem impl_le_from_prelude_le {n m : Nat} : n ≤ m → le n m
| Nat.le.refl => by
  show le n n
  show ∃ k, n + k ≃ n
  have : n + 0 ≃ n := AA.identR
  exact Exists.intro 0 ‹n + 0 ≃ n›
| @Nat.le.step _ m' (_ : n ≤ m') => by
  show le n (step m')
  have : le n m' := impl_le_from_prelude_le ‹n ≤ m'›
  have (Exists.intro k (_ : n + k ≃ m')) := ‹le n m'›
  have : n + step k ≃ step m' := calc
    n + step k   ≃ _ := add_step
    step (n + k) ≃ _ := by srw [‹n + k ≃ m'›]
    step m'      ≃ _ := Rel.refl
  have : ∃ k, n + k ≃ step m' := Exists.intro (step k) ‹n + step k ≃ step m'›
  have : le n (step m') := ‹∃ k, n + k ≃ step m'›
  exact this

/--
Converts our _less than or equivalent to_ relation on `Nat` to the Prelude's
version.

**Proof intuition**: Induction on `m`, with a case split on the the value `k`
from `le`'s definition in the inductive step.
-/
theorem prelude_le_from_impl_le {n : Nat} : {m : Nat} → le n m → n ≤ m
| 0, Exists.intro k (_ : n + k ≃ 0) => by
  show n ≤ 0
  have (And.intro (_ : n ≃ 0) (_ : k ≃ 0)) := zero_sum_split.mp ‹n + k ≃ 0›
  have : n = 0 := ‹n ≃ 0›
  match ‹n = 0› with
  | rfl => exact Nat.le.refl
| Nat.succ m', Exists.intro 0 (_ : n + 0 ≃ step m') => by
  show n ≤ step m'
  have : n ≃ step m' := Rel.trans (Rel.symm AA.identR) ‹n + 0 ≃ step m'›
  have : n = step m' := ‹n ≃ step m'›
  match ‹n = step m'› with
  | rfl => exact Nat.le.refl
| Nat.succ m', Exists.intro (Nat.succ k') (_ : n + step k' ≃ step m') => by
  show n ≤ step m'
  have : step (n + k') ≃ step m' := calc
    step (n + k') ≃ _ := Rel.symm add_step
    n + step k'   ≃ _ := ‹n + step k' ≃ step m'›
    step m'       ≃ _ := Rel.refl
  have : n + k' ≃ m' := AA.inject ‹step (n + k') ≃ step m'›
  have : ∃ k', n + k' ≃ m' := Exists.intro k' ‹n + k' ≃ m'›
  have : le n m' := ‹∃ k', n + k' ≃ m'›
  have : n ≤ m' := prelude_le_from_impl_le ‹le n m'›
  have : n ≤ step m' := Nat.le.step ‹n ≤ m'›
  exact this

/--
Our _less then or equivalent to_ relation on `Nat` is equivalent to the
Prelude's.
-/
theorem prelude_le_iff_impl_le {n m : Nat} : n ≤ m ↔ le n m :=
  Iff.intro impl_le_from_prelude_le prelude_le_from_impl_le

/--
Our _less than_ relation on `Nat` is equivalent to the Prelude's.

**Proof intuition**: For the Prelude-to-ours direction, derive `n ≤ m` from
`n < m`, then convert to `le n m`. Derive `n ≄ m` by contradiction with
`n ≤ m`. Combine them to obtain `lt n m`. For the ours-to-Prelude direction,
split `lt n m` into `le n m` and `n ≄ m`. Convert `le n m` to `n ≤ m` and split
it into `n = m ∨ n < m`. Eliminate the first case by contradiction with
`n ≃ m`, leaving the second case as the result.
-/
theorem prelude_lt_iff_impl_lt {n m : Nat} : n < m ↔ lt n m := by
  apply Iff.intro
  case mp =>
    intro (_ : n < m)
    show lt n m
    have : step n ≤ m := ‹n < m›
    have : step n ≤ step m := Nat.le_succ_of_le ‹step n ≤ m›
    have : n ≤ m := Nat.le_of_succ_le_succ ‹step n ≤ step m›
    have : le n m := prelude_le_iff_impl_le.mp ‹n ≤ m›
    have : n ≄ m := by
      intro (_ : n ≃ m)
      show False
      have : n = m := ‹n ≃ m›
      rw [‹n = m›] at ‹step n ≤ m›
      have : ¬(step m ≤ m) := Nat.not_succ_le_self m
      exact absurd ‹step m ≤ m› ‹¬(step m ≤ m)›
    have : lt n m := And.intro ‹le n m› ‹n ≄ m›
    exact this
  case mpr =>
    intro (_ : lt n m)
    show n < m
    have (And.intro (_ : le n m) (_ : n ≄ m)) := ‹lt n m›
    have : n ≤ m := prelude_le_iff_impl_le.mpr ‹le n m›
    have : n = m ∨ n < m := Nat.eq_or_lt_of_le ‹n ≤ m›
    match ‹n = m ∨ n < m› with
    | Or.inl (_ : n = m) =>
      have : n ≠ m := ‹n ≄ m›
      exact absurd ‹n = m› ‹n ≠ m›
    | Or.inr (_ : n < m) =>
      exact ‹n < m›

/--
If `compare` returns `Ordering.lt`, its first argument is less than its second
argument.

**Proof intuition**: Split the definition of `compare` into cases and eliminate
the incorrect ones by contradiction.
-/
theorem compare_lt {n m : Nat} : compare n m = Ordering.lt ↔ lt n m := by
  apply Iff.intro
  case mp =>
    intro (h : compare n m = Ordering.lt)
    show lt n m
    simp only [compare, Ord.compare, compareOfLessAndEq] at h
    split at h
    case isTrue =>
      have : lt n m := prelude_lt_iff_impl_lt.mp ‹n < m›
      exact this
    case isFalse =>
      split at h <;> contradiction
  case mpr =>
    intro (_ : lt n m)
    show compare n m = Ordering.lt
    simp only [compare, Ord.compare, compareOfLessAndEq]
    split
    case isTrue =>
      show Ordering.lt = Ordering.lt
      rfl
    case isFalse =>
      have : ¬(n < m) := by assumption
      have : n < m := prelude_lt_iff_impl_lt.mpr ‹lt n m›
      exact absurd ‹n < m› ‹¬(n < m)›

/--
If `compare` returns `Ordering.eq`, its arguments are equivalent.

**Proof intuition**: Split the definition of `compare` into cases and eliminate
the incorrect ones by contradiction.
-/
theorem compare_eq {n m : Nat} : compare n m = Ordering.eq ↔ n ≃ m := by
  apply Iff.intro
  case mp =>
    intro (h : compare n m = Ordering.eq)
    show n ≃ m
    simp [compare, Ord.compare, compareOfLessAndEq] at h
    split at h
    case isTrue =>
      have : n < m := by assumption
      contradiction
    case isFalse =>
      split at h
      case isTrue =>
        have : n = m := by assumption
        have : n ≃ m := ‹n = m›
        exact this
      case isFalse =>
        have : n ≠ m := by assumption
        contradiction
  case mpr =>
    intro (_ : n ≃ m)
    show compare n m = Ordering.eq
    simp [compare, Ord.compare, compareOfLessAndEq]
    split
    case isTrue =>
      have : n < m := by assumption
      have : n = m := ‹n ≃ m›
      rw [‹n = m›] at ‹n < m›
      have : ¬(m < m) := Nat.lt_irrefl m
      exact absurd ‹m < m› ‹¬(m < m)›
    case isFalse =>
      split
      case isTrue =>
        show Ordering.eq = Ordering.eq
        rfl
      case isFalse =>
        have : n ≠ m := by assumption
        have : n = m := ‹n ≃ m›
        exact absurd ‹n = m› ‹n ≠ m›

/--
If `compare` returns `Ordering.gt`, its first argument is greater than its
second argument.

**Proof intuition**: Split the definition of `compare` into cases and eliminate
the incorrect ones by contradiction and trichotomy.
-/
theorem compare_gt {n m : Nat} : compare n m = Ordering.gt ↔ lt m n := by
  apply Iff.intro
  case mp =>
    intro (h : compare n m = Ordering.gt)
    show lt m n
    simp [compare, Ord.compare, compareOfLessAndEq] at h
    split at h
    case isTrue =>
      have : n < m := by assumption
      contradiction
    case isFalse =>
      split at h
      case isTrue =>
        have : n = m := by assumption
        contradiction
      case isFalse =>
        have : ¬(n < m) := by assumption
        have : ¬(n = m) := by assumption
        have : n > m ∨ n ≤ m := Nat.lt_or_ge m n
        match ‹n > m ∨ n ≤ m› with
        | Or.inl (_ : n > m) =>
          have : m < n := ‹n > m›
          have : lt m n := prelude_lt_iff_impl_lt.mp ‹m < n›
          exact this
        | Or.inr (_ : n ≤ m) =>
          have : n = m ∨ n < m := Nat.eq_or_lt_of_le ‹n ≤ m›
          match ‹n = m ∨ n < m› with
          | Or.inl (_ : n = m) =>
            exact absurd ‹n = m› ‹¬(n = m)›
          | Or.inr (_ : n < m) =>
            exact absurd ‹n < m› ‹¬(n < m)›
  case mpr =>
    intro (_ : lt m n)
    show compare n m = Ordering.gt
    have notTwo : ¬ AA.TwoOfThree (lt n m) (n ≃ m) (lt m n) :=
      (trichotomy (order_inst := order) n m).atMostOne
    simp [compare, Ord.compare, compareOfLessAndEq]
    split
    case isTrue =>
      have : n < m := by assumption
      apply False.elim
      show False
      have : lt n m := prelude_lt_iff_impl_lt.mp ‹n < m›
      have two : AA.TwoOfThree (lt n m) (n ≃ m) (lt m n) :=
        AA.TwoOfThree.oneAndThree ‹lt n m› ‹lt m n›
      exact absurd two notTwo
    case isFalse =>
      split
      case isTrue =>
        have : n = m := by assumption
        apply False.elim
        show False
        have : n ≃ m := ‹n = m›
        have two : AA.TwoOfThree (lt n m) (n ≃ m) (lt m n) :=
          AA.TwoOfThree.twoAndThree ‹n ≃ m› ‹lt m n›
        exact absurd two notTwo
      case isFalse =>
        show Ordering.gt = Ordering.gt
        rfl

-- Needed for `compare_inst`, but delayed so its ordering operators don't
-- conflict with the Prelude ones used in the proofs above.
attribute [local instance] order

local instance compare_inst : Compare Nat := {
  compare := compare
  compare_substL := compare_substL
  compare_substR := compare_substR
  compare_lt := compare_lt
  compare_eq := compare_eq
  compare_gt := compare_gt
}

instance : Natural Nat := {
  toCore := core
  toInduction₀ := induction
  toInduction₁ := induction
  toAddition := addition
  toSign := sign
  toOrder := order
  toCompare := compare_inst
  toMultiplication := multiplication
  toExponentiation := Generic.exponentiation
  toDivision := Generic.division
}

end Lean4Axiomatic.Natural.Impl.Nat

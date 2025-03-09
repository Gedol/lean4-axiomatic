import Lean4Axiomatic.AbstractAlgebra

/-!
# Fundamental definitions and properties of natural numbers

Closely follows the [Peano axioms](https://en.wikipedia.org/wiki/Peano_axioms).
-/

namespace Lean4Axiomatic.Natural

open Relation.Equivalence (EqvOp)

/-!
## Axioms
-/

/-- Defines the primitive building blocks of all natural numbers. -/
class Constructor.Ops (ℕ : outParam Type) where
  /--
  **Peano axiom 1**: `zero` is a natural number.

  We start at zero instead of one because it gives nicer algebraic properties;
  zero being the identity element for addition, for example.
  -/
  zero : ℕ

  /--
  **Peano axiom 2**: `step n` is a natural number for every natural number `n`.

  The intuition is that `step zero` represents the number one,
  `step (step zero)` represents two, `step (step (step zero))` is three, and in
  general `step n` is the next number after `n` when counting up.

  Other sources call this the _successor_ function, often abbreviated `S`,
  `suc`, or `succ`. Using `step` is just as short, and conveys a similar
  meaning, while not sounding like a word with negative connotations.
  -/
  step : ℕ → ℕ

export Constructor.Ops (zero step)

/-- Definitions pertaining to equality of natural number values. -/
class Equality (ℕ : Type) where
  /-- Natural numbers have a decidable equality relation. -/
  eqvOp? : Relation.Equivalence.EqvOp? ℕ

attribute [instance] Equality.eqvOp?

export Equality (eqvOp?)

/-- Definitions pertaining to numeric literal support for natural numbers. -/
class Literals (ℕ : outParam Type) [Constructor.Ops ℕ] [Equality ℕ] where
  /--
  Enables representation of natural numbers by numeric literals.

  Lean uses this instance to automatically replace literal values `n : Nat`
  with `OfNat.ofNat ℕ n` in expressions where `ℕ` is expected. For example, the
  raw literal `2` is represented as `succ (succ zero) : Nat`. In a context
  where `2` is expected to have type `ℕ`, Lean would use this instance to
  replace it with the term `OfNat.ofNat ℕ (succ (succ zero))`.

  The interpretation of this representation must be equivalent to the
  corresponding `Nat` values. The `literal_zero` and `literal_step` properties
  enforce this requirement.
  -/
  literal {n : Nat} : OfNat ℕ n

  /-- The numeric literal `0` represents the natural number `zero`. -/
  literal_zero : OfNat.ofNat (α := ℕ) Nat.zero ≃ zero

  /--
  If the numeric literal `ℓ : Nat` represents the natural number `k`, then the
  literal `Nat.succ ℓ` represents the natural number `step k`.
  -/
  literal_step {n : Nat}
    : OfNat.ofNat (α := ℕ) (Nat.succ n) ≃ step (OfNat.ofNat n)


attribute [instance] Literals.literal

/-
Ensure that natural number literals without an inferred type default to this
instance. The priority should be higher than the default instance for `Nat`.
-/
attribute [default_instance low+1] Literals.literal

export Literals (literal literal_step literal_zero)

/-- Properties that the natural number constructors must satisfy. -/
class Constructor.Props
    (ℕ : outParam Type) [Ops ℕ] [Equality ℕ] [Literals ℕ]
    where
  /-- **Peano axiom 3**: zero is not the successor of any natural number. -/
  step_neqv_zero {n : ℕ} : step n ≄ 0

  /--
  The `step` function preserves equality of natural numbers; if two natural
  numbers are equal, they are still equal after `step` is applied to both.
   -/
  step_substitutive : AA.Substitutive₁ (α := ℕ) step (· ≃ ·) (· ≃ ·)

  /--
  **Peano axiom 4**: two natural numbers are equal if their successors are.
  -/
  step_injective : AA.Injective (α := ℕ) step (· ≃ ·) (· ≃ ·)

attribute [instance] Constructor.Props.step_injective
attribute [instance] Constructor.Props.step_substitutive

export Constructor.Props (step_injective step_neqv_zero step_substitutive)

/--
Packages together the basic properties of natural numbers, to reduce the amount
of class references needed for more advanced properties.
-/
class Core (ℕ : semiOutParam Type)
  extends Constructor.Ops ℕ, Equality ℕ, Literals ℕ, Constructor.Props ℕ

/--
Provides the induction axiom on natural numbers.

This axiom gets its own class because of a technical type theory issue. Most of
the time, we want the `motive` for induction to be a predicate, `ℕ → Prop`,
because we're proving a proposition. But sometimes we want to define a
recursive function, and so we need the `motive` to be `ℕ → Type` so we can
generate data types. This can be accomplished by having two instances of this
class, at universe levels `0` and `1` -- but if both of those instances are
included in the overall `Core` class instance, Lean has trouble determining
which one to use.

The solution is to include only the level-`0` instance in `Natural` by default,
since it's used very frequently. Code that needs the level-`1` instance for
recursion must specificially request it.
-/
class Induction (ℕ : outParam Type) [Core ℕ] where
  /--
  **Peano axiom 5**: the principle of mathematical induction.

  This axiom is parameterized over universe levels. At universe level `0`, it
  provides the familiar axiom from mathematics: given a predicate on natural
  numbers (here named `motive`), assert that it holds of all natural numbers if
  the following criteria are met:
  1. (base case) `motive 0` holds;
  1. (inductive case) `motive (step n)` holds whenever `motive n` holds, for
     all `n : ℕ`.

  At higher universe levels, `motive` generates an indexed family of types, and
  this axiom can then be used to produce data recursively.
  -/
  ind {motive : ℕ → Sort u}
    : motive 0 → ((m : ℕ) → motive m → motive (step m)) → (n : ℕ) → motive n

  /-- The witness for `motive 0` comes from the base case argument. -/
  ind_zero
    {motive : ℕ → Sort u}
    {z : motive 0} {s : (m : ℕ) → motive m → motive (step m)} : ind z s 0 = z

  /--
  The witness for `motive (step n)` comes from applying the inductive case
  argument to the `motive n` result obtained from a recursive call to `ind`.
  -/
  ind_step
    {motive : ℕ → Sort u}
    {z : motive 0} {s : (m : ℕ) → motive m → motive (step m)}
    {n : ℕ} : ind z s (step n) = s n (ind z s n)

export Induction (ind ind_step ind_zero)

/-!
## Derived properties
-/

variable {ℕ : Type} [Core ℕ]

/--
Non-typeclass version of `step_substitutive.subst₁`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
@[gcongr]
theorem step_subst {n₁ n₂ : ℕ} : n₁ ≃ n₂ → step n₁ ≃ step n₂ := AA.subst₁

/--
Alternative form of `step_neqv_zero` that's useful for showing natural number
literals are nonzero.
-/
theorem eqv_step_neqv_zero {n m : ℕ} : n ≃ step m → n ≄ 0 := by
  intro (_ : n ≃ step m)
  show n ≄ 0
  have : step m ≃ n := Rel.symm ‹n ≃ step m›
  have : step m ≄ 0 := step_neqv_zero
  have : n ≄ 0 := AA.substLFn (f := (· ≄ ·)) ‹step m ≃ n› ‹step m ≄ 0›
  exact this

/-- The natural number 1 is nonzero. -/
theorem one_neqv_zero : (1:ℕ) ≄ 0 :=
  have : (1:ℕ) ≃ step 0 := literal_step
  eqv_step_neqv_zero ‹(1:ℕ) ≃ step 0›

/-- The natural number 2 is nonzero. -/
theorem two_neqv_zero : (2:ℕ) ≄ 0 :=
  have : (2:ℕ) ≃ step 1 := literal_step
  eqv_step_neqv_zero ‹(2:ℕ) ≃ step 1›

section universe_polymorphic_induction
variable [Induction ℕ]

/--
Equivalent to `ind` but with a more convenient argument order when using the
`apply` tactic.
-/
def ind_on
    {motive : ℕ → Sort u} (n : ℕ)
    (zero : motive 0) (step : (m : ℕ) → motive m → motive (step m)) : motive n
    :=
  ind zero step n

/--
Similar to `ind_on`, but doesn't provide an inductive hypothesis. Useful for
proofs that need a case split but not the full power of induction.
-/
def cases_on
    {motive : ℕ → Sort u} (n : ℕ)
    (zero : motive 0) (step : (m : ℕ) → motive (step m)) : motive n
    :=
  ind_on n zero (λ n _ => step n)

/--
Similar to `ind_on`, but with a constant function as the `motive`, producing a
single `Sort` instead of an indexed family of `Sort`s. Useful for defining
recursive functions on data.
-/
def rec_on {α : Sort u} (n : ℕ) (zero : α) (step : α → α) : α :=
  ind_on n zero (λ _ => step)

/--
Evaluate `rec_on` at zero.

**Property and proof intuition**: Zero is the base case for induction and
recursion, so we'd expect `rec_on` to return the corresponding value.
-/
theorem rec_on_zero {α : Sort u} {z : α} {s : α → α} : rec_on 0 z s = z := calc
  _ = rec_on 0 z s          := rfl
  _ = ind_on 0 z (λ _ => s) := rfl
  _ = ind z (λ _ => s) 0    := rfl
  _ = z                     := ind_zero

/--
Evaluate `rec_on` at `step n` for some natural number `n`.

**Property and proof intuition**: This is the inductive/recursive case, so we'd
expect to perform some computation on the result of the recursive call for `n`.
-/
theorem rec_on_step
    {α : Sort u} {n : ℕ} {z : α} {s : α → α}
    : rec_on (step n) z s = s (rec_on n z s)
    := calc
  _ = rec_on (step n) z s               := rfl
  _ = ind_on (step n) z (λ _ => s)      := rfl
  _ = ind z (λ _ => s) (step n)         := rfl
  _ = (λ _ => s) n (ind z (λ _ => s) n) := ind_step
  _ = s (ind z (λ _ => s) n)            := rfl
  _ = s (ind_on n z (λ _ => s))         := rfl
  _ = s (rec_on n z s)                  := rfl

end universe_polymorphic_induction

/--
A natural number is either zero, or the successor of another natural number.

This can sometimes be easier to use than `cases_on`.

**Property intuition**: Zero and successor are the only ways to construct
natural numbers.

**Proof intuition**: Follows directly from `cases_on`.
-/
theorem split_cases
    [Induction.{0} ℕ] (n : ℕ) : n ≃ 0 ∨ ∃ (m : ℕ), n ≃ step m := by
  apply cases_on n
  case zero =>
    show 0 ≃ 0 ∨ ∃ m, 0 ≃ step m
    exact Or.inl Rel.refl
  case step =>
    intro (k : ℕ)
    show step k ≃ 0 ∨ ∃ m, step k ≃ step m
    exact Or.inr (Exists.intro k Rel.refl)

/-- A natural number is never equal to its successor. -/
theorem step_neqv [Induction.{0} ℕ] {n : ℕ} : step n ≄ n := by
  apply ind_on (motive := λ n => step n ≄ n) n
  case zero =>
    show step 0 ≄ 0
    exact step_neqv_zero
  case step =>
    intro n (ih : step n ≄ n)
    show step (step n) ≄ step n
    intro (_ : step (step n) ≃ step n)
    show False
    apply ih
    show step n ≃ n
    exact AA.inject ‹step (step n) ≃ step n›

end Lean4Axiomatic.Natural

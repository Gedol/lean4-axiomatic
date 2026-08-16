import Mathlib.Tactic.GCongr

namespace Lean4Axiomatic.Logic

/--
Apply a covariant mapping to both sides of a logical equivalence.

**Property and proof intuition**: Because the mapping is covariant, each
direction of the equivalence can be rewritten "in place".
-/
theorem iff_subst_covar
    {f : Prop → Prop} (f_subst : {a₁ a₂ : Prop} → (a₁ → a₂) → f a₁ → f a₂)
    {p₁ p₂ : Prop} : (p₁ ↔ p₂) → (f p₁ ↔ f p₂)
    := by
  intro (Iff.intro (_ : p₁ → p₂) (_ : p₂ → p₁))
  show f p₁ ↔ f p₂
  have : f p₁ → f p₂ := f_subst ‹p₁ → p₂›
  have : f p₂ → f p₁ := f_subst ‹p₂ → p₁›
  exact Iff.intro ‹f p₁ → f p₂› ‹f p₂ → f p₁›

/--
Apply a contravariant mapping to both sides of a logical equivalence.

**Property and proof intuition**: Because the mapping is contravariant, the
directions of the equivalence need to be swapped after being rewritten.
-/
theorem iff_subst_contra
    {f : Prop → Prop} (f_subst : {a₁ a₂ : Prop} → (a₁ → a₂) → f a₂ → f a₁)
    {p₁ p₂ : Prop} : (p₁ ↔ p₂) → (f p₁ ↔ f p₂)
    := by
  intro (Iff.intro (_ : p₁ → p₂) (_ : p₂ → p₁))
  show f p₁ ↔ f p₂
  have : f p₂ → f p₁ := f_subst ‹p₁ → p₂›
  have : f p₁ → f p₂ := f_subst ‹p₂ → p₁›
  exact Iff.intro ‹f p₁ → f p₂› ‹f p₂ → f p₁›

/--
Rewrite the left argument of logical _and_ with the provided mapping function.
-/
theorem and_mapL {p₁ p₂ q : Prop} (f : p₁ → p₂) : p₁ ∧ q → p₂ ∧ q := by
  intro (And.intro (_ : p₁) (_ : q))
  show p₂ ∧ q
  have : p₂ := f ‹p₁›
  exact And.intro ‹p₂› ‹q›

/--
Rewrite the right argument of logical _and_ with the provided mapping function.
-/
theorem and_mapR {p₁ p₂ q : Prop} (f : p₁ → p₂) : q ∧ p₁ → q ∧ p₂ := by
  intro (And.intro (_ : q) (_ : p₁))
  show q ∧ p₂
  have : p₂ := f ‹p₁›
  exact And.intro ‹q› ‹p₂›

/--
Rewrite the left side of logical _or_ using the provided mapping function.

**Property and proof intuition**: If we have the left side of the _or_, we can
rewrite it; otherwise we leave it alone.
-/
theorem or_mapL {p₁ p₂ q : Prop} (f : p₁ → p₂) : p₁ ∨ q → p₂ ∨ q := by
  intro (_ : p₁ ∨ q)
  show p₂ ∨ q
  exact match ‹p₁ ∨ q› with
  | Or.inl (_ : p₁) => have : p₂ := f ‹p₁›; Or.inl ‹p₂›
  | Or.inr (_ : q) => Or.inr ‹q›

/--
Rewrite the right side of logical _or_ using the provided mapping function.

**Property intuition**: If we have the right side of the _or_, we can
rewrite it; otherwise we leave it alone.

**Proof intuition**: Reduces the problem to the left-handed version using the
symmetry of logical _or_.
-/
theorem or_mapR {p₁ p₂ q : Prop} (f : p₁ → p₂) : q ∨ p₁ → q ∨ p₂ := by
  intro (_ : q ∨ p₁)
  show q ∨ p₂
  have : p₂ ∨ q := or_mapL f ‹q ∨ p₁›.symm
  exact ‹p₂ ∨ q›.symm

/--
Falsehood is the left identity for disjunction: it can be freely added or
removed as the left operand.
-/
theorem or_identL {p : Prop} : False ∨ p ↔ p := by
  apply Iff.intro
  case mp =>
    intro (_ : False ∨ p)
    show p
    exact ‹False ∨ p›.elim False.elim id
  case mpr =>
    intro (_ : p)
    show False ∨ p
    exact Or.inr ‹p›

/--
Falsehood is the right identity for disjunction: it can be freely added or
removed as the right operand.
-/
theorem or_identR {p : Prop} : p ∨ False ↔ p := calc
  _ ↔ p ∨ False := Iff.rfl
  _ ↔ False ∨ p := Or.comm
  _ ↔ p         := or_identL

/-- A conjuction with both sides identical can be removed. -/
theorem and_merge {p : Prop} : p ∧ p ↔ p :=
  Iff.intro And.left (λ x => And.intro x x)

/-- A disjunction with both sides identical can be removed. -/
theorem or_merge {p : Prop} : p ∨ p ↔ p := Iff.intro (Or.elim · id id) Or.inl

/--
Disjunction distributes over conjunction.

**Intuition**: In the forward direction, if we have `p`, then we can provide it
for both disjunctions in the result. If we instead have `q ∧ r`, then we can
provide `q` in the left disjunction and `r` in the right. In the reverse
direction, there are seemingly more possibilities. But if either of the two
disjunctions turns out to be `p`, then that's what we must have in the result.
Only when the left disjunction is `q` and the right disjunction is `r` can we
provide `q ∧ r`.
-/
theorem or_distribL_and {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  case mp =>
    intro (_ : p ∨ (q ∧ r))
    show (p ∨ q) ∧ (p ∨ r)
    match ‹p ∨ (q ∧ r)› with
    | Or.inl (_ : p) =>
      have : p ∨ q := Or.inl ‹p›
      have : p ∨ r := Or.inl ‹p›
      exact And.intro ‹p ∨ q› ‹p ∨ r›
    | Or.inr (And.intro (_ : q) (_ : r)) =>
      have : p ∨ q := Or.inr ‹q›
      have : p ∨ r := Or.inr ‹r›
      exact And.intro ‹p ∨ q› ‹p ∨ r›
  case mpr =>
    intro (And.intro (_ : p ∨ q) (_ : p ∨ r))
    show p ∨ (q ∧ r)
    match ‹p ∨ q› with
    | Or.inl (_ : p) =>
      exact Or.inl ‹p›
    | Or.inr (_ : q) =>
      match ‹p ∨ r› with
      | Or.inl (_ : p) =>
        exact Or.inl ‹p›
      | Or.inr (_ : r) =>
        have : q ∧ r := And.intro ‹q› ‹r›
        exact Or.inr ‹q ∧ r›

/--
Negation of disjunction, one of
[De Morgan's laws](https://en.wikipedia.org/wiki/De_Morgan%27s_laws).
-/
theorem not_or_iff_and_not {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  case mp =>
    intro (_ : ¬(p ∨ q))
    show ¬p ∧ ¬q
    have : ¬p := by
      intro (_ : p)
      show False
      have : p ∨ q := Or.inl ‹p›
      exact absurd ‹p ∨ q› ‹¬(p ∨ q)›
    have : ¬q := by
      intro (_ : q)
      show False
      have : p ∨ q := Or.inr ‹q›
      exact absurd ‹p ∨ q› ‹¬(p ∨ q)›
    exact And.intro ‹¬p› ‹¬q›
  case mpr =>
    intro (And.intro (_ : ¬p) (_ : ¬q)) (_ : p ∨ q)
    show False
    match ‹p ∨ q› with
    | Or.inl (_ : p) => exact absurd ‹p› ‹¬p›
    | Or.inr (_ : q) => exact absurd ‹q› ‹¬q›

/--
Similar to `Or` but where the knowledge of which constructor was selected is
computationally relevant.

Isomorphic to the type `{ b : Bool // if b then α else β }`.
-/
inductive Either (α : Prop) (β : Prop) : Type where
| /-- Left injection. -/ inl (p : α) : Either α β
| /-- Right injection. -/ inr (p : β) : Either α β

/-- Exchange Either's parameters. -/
def Either.swap {α β : Prop} : Either α β → Either β α
| .inl (x : α) => .inr x
| .inr (y : β) => .inl y

/--
Class that enables arbitrary expressions in `Prop` to be used as instance
arguments.

This is mainly helpful for definitions of operators, e.g. division, which have
restrictions on their argument values that aren't normally made explicit in
standard mathematical notation.

It can also greatly reduce clutter in proofs, or allow automatic derivation of
simple facts that would otherwise be tedious to write by hand.

The name `AP` was chosen to be short, and to stand for "automatic `Prop`" or
"arbitrary `Prop`".

#### Parameters
1. `p`: The expression to turn into an instance.
-/
class AP (p : Prop) : Prop where
  /-- Evidence that `p` is true. -/
  ev : p

/-- Apply `f`, a conversion from one proposition to another, inside `AP`. -/
@[implicit_reducible]
def AP.map {p q : Prop} (ap : AP p) (f : p → q) : AP q := AP.mk (f ap.ev)

/-- Lift an implication into `AP`. -/
@[implicit_reducible, gcongr]
def AP.subst {p q : Prop} : (p → q) → AP p → AP q := λ f ap => ap.map f

end Lean4Axiomatic.Logic

import Lean4Axiomatic.Hand
import Lean4Axiomatic.Operators
import Lean4Axiomatic.Relation.Equivalence.Core
import Mathlib.Tactic.GCongr

namespace Lean4Axiomatic.Relation.Equivalence.Impl

/-! # Implementations of equivalence relations -/

namespace DepFn

/-! ## For dependent functions -/

variable {α : Sort u}
variable {β : α → Sort v}
variable [indexed_eqvOp : {x : α} → EqvOp (β x)]

/--
The "pointwise" equivalence relation for dependent functions.

Two dependent functions are considered to be equivalent if their outputs are
equivalent for every inhabitant of their domain.

**Named parameters**
- `α`: The domain of the dependent functions.
- `β`: The codomain family of the dependent functions.
- `indexed_eqvOp`: Evidence that all codomains have an equivalence relation.
- `f₁`, `f₂`: The dependent functions to evaluate for equivalence.
-/
def eqv (f₁ f₂ : (x : α) → β x) : Prop := ∀ (x : α), f₁ x ≃ f₂ x

local instance eqv_tildeDash_inst : Operators.TildeDash ((x : α) → β x) := {
  tildeDash := eqv
}

/--
The reflexive property of pointwise equivalence for dependent functions.

**Intuition**: We need to show that `f x ≃ f x` for every `x : α`. But this
follows immediately (by `refl`) from the `EqvOp (β x)` instance obtained from
`indexed_eqvOp` for each `x`.

**Named parameters**
- `α`: The domain of the dependent functions.
- `β`: The codomain family of the dependent functions.
- `indexed_eqvOp`: Evidence that all codomains have an equivalence relation.
- `f`: The function to evaluate for equivalence to itself.
-/
theorem refl {f : (x : α) → β x} : f ≃ f := by
  show ∀ (x : α), f x ≃ f x
  intro x
  exact indexed_eqvOp.refl

/--
The symmetric property of pointwise equivalence for dependent functions.

**Intuition**: We need to show that `f x ≃ g x → g x ≃ f x` for every `x : α`.
But this follows immediately (by `symm`) from the `EqvOp (β x)` instance
obtained from `indexed_eqvOp` for each `x`.

**Named parameters**
- `α`: The domain of the dependent functions.
- `β`: The codomain family of the dependent functions.
- `indexed_eqvOp`: Evidence that all codomains have an equivalence relation.
- `f`, `g`: The dependent functions that are arguments to the relation.
-/
theorem symm {f g : (x : α) → β x} : f ≃ g → g ≃ f := by
  intro (_ : ∀ (x : α), f x ≃ g x)
  show ∀ (x : α), g x ≃ f x
  intro x
  have : f x ≃ g x := ‹∀ (x : α), f x ≃ g x› x
  exact indexed_eqvOp.symm ‹f x ≃ g x›

/--
The transitive property of pointwise equivalence for dependent functions.

**Intuition**: We need to show that `f x ≃ g x → g x ≃ h x → f x ≃ h x` for
every `x : α`. But this follows immediately (by `trans`) from the `EqvOp (β x)`
instance obtained from `indexed_eqvOp` for each `x`.

**Named parameters**
- `α`: The domain of the dependent functions.
- `β`: The codomain family of the dependent functions.
- `indexed_eqvOp`: Evidence that all codomains have an equivalence relation.
- `f`, `g`, `h`: The dependent functions that are arguments to the relation.
-/
theorem trans {f g h : (x : α) → β x} : f ≃ g → g ≃ h → f ≃ h := by
  intro (_ : ∀ (x : α), f x ≃ g x) (_ : ∀ (x : α), g x ≃ h x)
  show ∀ (x : α), f x ≃ h x
  intro x
  have : f x ≃ g x := ‹∀ (x : α), f x ≃ g x› x
  have : g x ≃ h x := ‹∀ (x : α), g x ≃ h x› x
  exact indexed_eqvOp.trans ‹f x ≃ g x› ‹g x ≃ h x›

/--
Generates a "pointwise" equivalence relation (with its essential properties)
for dependent functions, from evidence that every codomain in the functions'
indexed family of output `Sort`s has an equivalence relation.

More intuitively, a dependent function can be viewed as a generalization of a
tuple. Each inhabitant `x : α` of the function's domain is an index to a unique
tuple element. Just as in an ordinary tuple, the `Sort` of each element can be
different; here it is given by `β x`. Comparing tuples for equivalence requires
that each element be comparable in turn: the first elements must be equivalent,
and the second elements, and the third, etc. This is what is meant by the term
"pointwise". The `indexed_eqvOp` parameter provides the necessary equivalence
relations for every tuple element.

Thus, due to the `indexed_eqvOp` parameter, this definition is not directly
useful as an `instance` of `EqvOp`. Instead, every caller of this function is
expected to declare the result as an instance, specific to a particular use
case.

**Named parameters**
- `α`: The domain of the dependent functions.
- `β`: The codomain family of the dependent functions.
- `indexed_eqvOp`: Evidence that all codomains have an equivalence relation.
-/
instance eqvOp : EqvOp ((x : α) → β x) := {
  tildeDash := eqv
  refl := refl
  symm := symm
  trans := trans
}

end DepFn

namespace Mapped

/-! ## For types that convert into types having equivalence -/

/--
Extends an equivalence relation via a mapping between types.

More concretely, given a sort `β` that has an equivalence relation, and a
function `f` from a sort `α` into `β`, this definition generates an equivalence
relation for `α`. It can save quite a lot of effort if writing the mapping
between `α` and `β` is simple.

Since the behavior of the equivalence relation depends completely upon the
explicit parameter `f`, this definition is not directly useful as an `instance`
of `EqvOp`. Instead, every caller of this function is expected to declare the
result as an instance, specific to a particular use case.

**Named parameters**
- `α`: The `Sort` to generate an equivalence relation for.
- `β`: The `Sort` that already has an equivalence relation.
- `f`: The mapping from `α` to `β`.

**Class parameters**
- `EqvOp β`: The equivalence relation on `β`.
-/
@[implicit_reducible]
def eqvOp
    {α : Sort u} {β : Sort v} (f : α → β) [β_eqvOp : EqvOp β] : EqvOp α
    := {
  tildeDash := λ x y => f x ≃ f y
  refl := β_eqvOp.refl
  symm := β_eqvOp.symm
  trans := β_eqvOp.trans
}

end Mapped

namespace Prod

/-! ## For product types (i.e. ordered pairs) -/

variable {α β : Type}
variable [EqvOp α]
variable [EqvOp β]

/--
Converts an ordered pair into its dependent function representation.

This function is a supporting definition for `Prod.eqvOp`, and is likely not
very useful on its own.

**Intuition**: The `Hand` parameter of the dependent function selects the
associated component of the ordered pair to return. Since there are exactly two
values of `Hand`, there are exactly two result types of the dependent
function, and thus it fully reproduces the state of the pair.

**Named parameters**
- `α`: The `Type` of the pair's left element.
- `β`: The `Type` of the pair's right element.
-/
def depFn_from_prod : α × β → ((hand : Hand) → hand.pick α β)
| (a, _), Hand.L => a
| (_, b), Hand.R => b

/--
Evidence that all codomains in the dependent function representation of ordered
pairs have equivalence relations.

This function is a supporting definition for `Prod.eqvOp`, and is likely not
very useful on its own.

**Intuition**: As the `indexed_eqvOp` argument to `DepFn.eqvOp`, this function
provides evidence that there is an equivalence relation for every component of
an ordered pair. Since there are only two components, this can easily be done
by explicitly listing all associations.

**Named parameters**
- `α`: The `Type` of the codomain for `Hand.L`.
- `β`: The `Type` of the codomain for `Hand.R`.

**Class parameters**
- `EqvOp α`: Evidence that `α` has an equivalence relation.
- `EqvOp β`: Evidence that `β` has an equivalence relation.
-/
instance indexed_eqvOp : {hand : Hand} → EqvOp (hand.pick α β)
| Hand.L => ‹EqvOp α›
| Hand.R => ‹EqvOp β›

/--
The standard ("pointwise") equivalence relation on ordered pairs whose left-
and right-handed component types both have their own equivalence relations.

**Implementation intuition**: Uses `Prod.indexed_eqvOp` and
`Prod.depFn_from_prod` to produce an equivalence relation on the dependent
function representation of ordered pairs, and extend it back to the original
type `α × β`.

**Named parameters**
- `α`: The left-hand component type.
- `β`: The right-hand component type.

**Class parameters**
- `EqvOp α`: Evidence that `α` has an equivalence relation.
- `EqvOp β`: Evidence that `β` has an equivalence relation.
-/
instance eqvOp : EqvOp (α × β) := Mapped.eqvOp depFn_from_prod

/--
Characterizes the equivalence relation on ordered pairs in terms of the pairs'
elements.

**Proof intuition**: Fully expanding the definition of the equivalence relation
on ordered pairs reveals it to be a dependent function with domain `Hand`. The
codomain of the function simplifies greatly when specialized to a specific
`Hand` value; doing that for both `Hand.L` and `Hand.R` gives the two
equivalences between elements on the conjunction side of this theorem's type.

**Named parameters**
- `α`: The type of the pairs' left elements.
- `β`: The type of the pairs' right elements.
- `a₁`: The first pair's left element.
- `a₂`: The second pair's left element.
- `b₁`: The first pair's right element.
- `b₂`: The second pair's right element.

**Class parameters**
- `EqvOp α`: Evidence that `α` has an equivalence relation.
- `EqvOp β`: Evidence that `β` has an equivalence relation.
-/
theorem eqv_defn
    {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≃ (a₂, b₂) ↔ a₁ ≃ a₂ ∧ b₁ ≃ b₂
    := by
  let dffp := @depFn_from_prod
  let expanded_eqv := (hand : Hand) → dffp (a₁, b₁) hand ≃ dffp (a₂, b₂) hand
  apply Iff.intro
  case mp =>
    intro (_ : (a₁, b₁) ≃ (a₂, b₂))
    show a₁ ≃ a₂ ∧ b₁ ≃ b₂
    have elem_eqv : expanded_eqv := ‹(a₁, b₁) ≃ (a₂, b₂)›
    have : a₁ ≃ a₂ := elem_eqv Hand.L
    have : b₁ ≃ b₂ := elem_eqv Hand.R
    exact And.intro ‹a₁ ≃ a₂› ‹b₁ ≃ b₂›
  case mpr =>
    intro (And.intro (_ : a₁ ≃ a₂) (_ : b₁ ≃ b₂))
    show (a₁, b₁) ≃ (a₂, b₂)
    show expanded_eqv
    intro hand
    cases hand
    case L => exact ‹a₁ ≃ a₂›
    case R => exact ‹b₁ ≃ b₂›

end Prod

namespace Subtype

/-- Equivalence for subtypes. -/
scoped instance subtype_eqvop_inst
    {α : Type} [EqvOp α] {P : α → Prop} : EqvOp (Subtype P)
    := {
  tildeDash := λ s₁ s₂ => s₁.val ≃ s₂.val
  refl := Rel.refl
  symm := Rel.symm
  trans := Rel.trans
}

/-- Value projection respects subtype equivalence. -/
@[gcongr]
theorem subtype_val_subst
    {α : Type} [EqvOp α] {P : α → Prop} {s₁ s₂ : Subtype P}
    : s₁ ≃ s₂ → s₁.val ≃ s₂.val
    :=
  id

end Subtype

end Lean4Axiomatic.Relation.Equivalence.Impl

import Lean4Axiomatic.Relation.Equivalence.Core
import Mathlib.Tactic.GCongr

/-! # Indexed families of types -/

namespace Lean4Axiomatic.Function

open Relation.Equivalence (EqvOp)

/--
Indicates that the provided function is an index into a collection of related
Sorts that respects equivalence on both the indexing type and each indexed
Sort.

The equivalence aspect is important when proving properties about the indexed
family, as it allows the use of substitution. For example, indexed families
can be viewed as predicates on the indexing type, which makes them commonly
used for induction proofs.
-/
class IndexedFamily {α : Type} [EqvOp α] (fam : α → Sort u) where
  /-- Each Sort in the indexed family obeys its own equivalence relation. -/
  fam_eqv {x : α} : EqvOp (fam x)

  /--
  Equivalence of the indexing type in an indexed family is respected.

  In more detail: if we have a value of Sort `fam x₁`, and `x₁` is equivalent
  to `x₂`, then we also have a value of Sort `fam x₂`.

  **Intuition**: This must be the case for equivalence on the indexing type to
  be meaningful.
  -/
  fsubst {x₁ x₂ : α} : x₁ ≃ x₂ → fam x₁ → fam x₂

  /--
  Substituting an indexed family's index with itself does nothing.

  Useful when there's a need to add or remove an `fsubst` in an expression.

  **Intuition**: The `fsubst` function should be implementable for all types.
  The only consistent thing it can do when the index value is the same is leave
  the input term unchanged.
  -/
  fsubst_refl {x : α} {fx : fam x} : fsubst Rel.refl fx ≃ fx

  /--
  Composing two indexed family substitutions is the same as a single
  substitution from the first to the last index value.

  An alternative version, `fsubst_trans`, is defined below; it's easier to use
  in proofs. This version is easier for implementations to define.

  **Intutition**: The `fsubst` function does not change the underlying terms
  (elements of the family) in a significant way. Substitution is purely an
  operation on types.
  -/
  _fsubst_trans
    {x y z : α} {fx : fam x} (xy : x ≃ y) (yz : y ≃ z)
    : fsubst ‹y ≃ z› (fsubst ‹x ≃ y› fx) ≃
      fsubst (Rel.trans ‹x ≃ y› ‹y ≃ z›) fx

  /--
  The `fsubst` function supports substitution of its right-hand argument (with
  respect to equivalence).

  An alternative version, `fsubst_substR`, is defined below; it's easier to use
  in proofs. This version is easier for implementations to define.

  **Intuition**: We want `fsubst` to behave like a function with respect to
  equivalence: it should map equivalent inputs to equivalent outputs.
  -/
  _fsubst_substR
    {x y : α} {fx₁ fx₂ : fam x} (xy : x ≃ y)
    : fx₁ ≃ fx₂ → fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂

  /--
  The `fsubst` function is injective in its right-hand argument (with respect
  to equivalence).

  An alternative version, `fsubst_injectR`, is defined below; it's easier to
  use in proofs. This version is easier for implementations to define.

  **Intuition**: We want `fsubst` to "preserve distinctions" with respect to
  equivalence: outputs can only be equivalent if they came from equivalent
  inputs. This is because `fsubst` is merely converting the type of an
  expression to an equivalent form; it's not changing the expression's value.
  -/
  _fsubst_injectR
    {x y : α} {fx₁ fx₂ : fam x} (xy : x ≃ y)
    : fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂ → fx₁ ≃ fx₂

attribute [implicit_reducible, instance] IndexedFamily.fam_eqv

export IndexedFamily (fsubst fsubst_refl)

/--
Composing two indexed family substitutions is the same as a single substitution
from the first to the last index value.

Useful when wanting to remove a nested `fsubst` in an expression.
-/
abbrev fsubst_trans
    {α : Type} [EqvOp α] {fam : α → Sort u} [IndexedFamily fam]
    {x y z : α} {fx : fam x} {xy : x ≃ y} {yz : y ≃ z}
    : fsubst ‹y ≃ z› (fsubst ‹x ≃ y› fx) ≃
      fsubst (Rel.trans ‹x ≃ y› ‹y ≃ z›) fx
    :=
  IndexedFamily._fsubst_trans xy yz

/--
The `fsubst` function supports substitution of its right-hand argument (with
respect to equivalence).

Useful when proving properties of expressions wrapped by `fsubst`.
-/
@[gcongr]
abbrev fsubst_substR
    {α : Type} [EqvOp α] {fam : α → Sort u} [IndexedFamily fam]
    {x y : α} {fx₁ fx₂ : fam x} {xy : x ≃ y}
    : fx₁ ≃ fx₂ → fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂
    :=
  IndexedFamily._fsubst_substR xy

/--
The `fsubst` function is injective in its right-hand argument (with respect to
equivalence).
-/
abbrev fsubst_injectR
    {α : Type} [EqvOp α] {fam : α → Sort u} [IndexedFamily fam]
    {x y : α} {fx₁ fx₂ : fam x} {xy : x ≃ y}
    : fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂ → fx₁ ≃ fx₂
    :=
  IndexedFamily._fsubst_injectR xy

/--
All constant functions (with domain and range supporting equivalence) are
(trivially) indexed families.

Useful when defining simple recursive functions, which usually return a single
type. For example, addition on the natural numbers returns values in `ℕ` for
all arguments.

**Intuition**: There is nothing for `fsubst` to do, because the output of the
indexing function is the same for all indices, not just the equivalent ones.
-/
instance idx_fam_const
    {α : Type} [EqvOp α] {X : Sort u} [EqvOp X]
    : IndexedFamily (λ (_ : α) => X)
    := {
  fam_eqv := λ {_} => ‹EqvOp X›
  fsubst := λ _ => id
  fsubst_refl := Rel.refl
  _fsubst_trans := λ _ _ => Rel.refl
  _fsubst_substR := λ _ => id
  _fsubst_injectR := λ _ => id
}

/--
All predicates (functions into `Prop`, with domains supporting equivalence)
obeying the `fsubst` property are indexed families.

Useful when proving properties by induction: the `motive` predicate just needs
to support substitution.

**Intuition**: All elements of `fam x` are equal (thus equivalent) for every
`x`, because `fam x : Prop`.
-/
@[implicit_reducible]
def idx_fam_prop
    {α : Type} [EqvOp α] {fam : α → Prop}
    (fsubst : {x₁ x₂ : α} → x₁ ≃ x₂ → fam x₁ → fam x₂)
    : IndexedFamily fam
    := {
  fam_eqv := Relation.Equivalence.eqvOp_prop_term
  fsubst := fsubst
  fsubst_refl := rfl
  _fsubst_trans := λ _ _ => rfl
  _fsubst_substR := λ _ _ => rfl
  _fsubst_injectR := λ _ _ => rfl
}

end Lean4Axiomatic.Function

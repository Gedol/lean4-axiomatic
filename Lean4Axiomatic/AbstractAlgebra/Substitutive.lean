import Lean4Axiomatic.AbstractAlgebra.Commutative
import Lean4Axiomatic.AbstractAlgebra.Core
import Lean4Axiomatic.Tactic.Rewrite

namespace Lean4Axiomatic.AA

open Relation.Equivalence (EqvOp)

/-!
# (Generalized) substitution and related properties

Generalized substitution allows the equalities of the ordinary substitution
property to be replaced by arbitrary binary relations.

## Substitution

### Definitions
-/

/--
Class for types and operations that satisfy the unary generalized substitution
property.

For more information see `Substitutive₁.subst₁`.

**Named parameters**
- `α`: the argument type of the unary operation `f`.
- `β`: the result type of the unary operation `f`.
- `f`: the unary operation that obeys the generalized substitution property.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class Substitutive₁
    {α : Sort u} {β : Sort v} (f : semiOutParam (α → β))
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop)
    where
  /--
  The generalized substitution property of an unary operation `f`.

  An `f` that satisfies this property must map values of type `α` that are
  related by `rα` to values of type `β` that are related by `rβ`.

  Often `α` and `β` will be the same type, and `rα` and `rβ` will be the same
  relation. The canonical example is the ordinary
  [substitution property of equality](https://w.wiki/4vEu): if we have `x = y`
  for any values `x` and `y`, then we know `f x = f y`.

  **Named parameters**
  - see `Substitutive₁` for the class parameters.
  - `x₁` and `x₂`: the arguments to `f`, related by `rα`.
  -/
  subst₁ {x₁ x₂ : α} : rα x₁ x₂ → rβ (f x₁) (f x₂)

export Substitutive₁ (subst₁)

/--
Convenience function for the unary generalized substitution property, for a
predicate `f`.

Type inference for `subst₁` gets stuck when the output relation is `(· → ·)`;
this helper works around that issue by hardcoding the argument.

See `subst₁` for further documentation.

**Named parameters**
- `α`: The `Sort` of `f`'s input parameter.
- `f`: The unary predicate that obeys the generalized substitution property.
- `rα`: A binary relation on `f`'s input values.
- See `subst₁` for documentation on the remaining parameters.
-/
abbrev substFn {α : Sort u} {f : α → Prop} {rα : α → α → Prop} :=
  @subst₁ α (β := Prop) f rα (rβ := (· → ·))

/--
Class for types and operations that satisfy the unary generalized injective
property.

For more information see `Injective.inject`.

**Named parameters**
- `α`: the argument type of the unary operation `f`.
- `β`: the result type of the unary operation `f`.
- `f`: the unary operation that obeys the generalized injective property.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class Injective
    {α : Sort u} {β : Sort v} (f : semiOutParam (α → β))
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop)
    where
  /--
  The generalized injective property of an unary operation `f`.

  Operations `f` that have this property can be traced backward in some sense.
  It is the converse of the substitution property. In other words, if we know
  that the results of two operations, `f x₁` and `f x₂`, are related by `rβ`,
  then we can conclude that the inputs `x₁` and `x₂` are related by `rα`.

  Often `α` and `β` will be the same type, and `rα` and `rβ` will be the same
  relation. The canonical example is the ordinary
  [injective property of functions](https://w.wiki/4vTb): if we have
  `f x = f y` for any values `x` and `y`, then we know `x = y`.

  **Named parameters**
  - see `Injective` for the class parameters.
  - `x₁` and `x₂`: the arguments to `f`.
  -/
  inject {x₁ x₂ : α} : rβ (f x₁) (f x₂) → rα x₁ x₂

export Injective (inject)

section neqv

variable {α : Sort u} {β : Sort v} [EqvOp α] [EqvOp β] {f : α → β}

/--
A function is substitutive over non-equivalence if it's injective over
equivalence.

**Property and proof intuition**: It's the contrapositive of the injective
property.
-/
theorem subst_neqv
    {x₁ x₂ : α} [Injective f (· ≃ ·) (· ≃ ·)] : x₁ ≄ x₂ → f x₁ ≄ f x₂
    := by
  intro (_ : x₁ ≃ x₂ → False) (_ : f x₁ ≃ f x₂)
  show False
  apply ‹x₁ ≃ x₂ → False›
  show x₁ ≃ x₂
  exact inject ‹f x₁ ≃ f x₂›

instance substitutive_neqv_from_injective_eqv
    [Injective f (· ≃ ·) (· ≃ ·)] : Substitutive₁ f (· ≄ ·) (· ≄ ·)
    := {
  subst₁ := subst_neqv
}

/--
A function is injective over non-equivalence if it's substitutive over
equivalence.

**Property and proof intuition**: It's the contrapositive of the substitutive
property.
-/
theorem inject_neqv
    {x₁ x₂ : α} [Substitutive₁ f (· ≃ ·) (· ≃ ·)] : f x₁ ≄ f x₂ → x₁ ≄ x₂
    := by
  intro (_ : f x₁ ≃ f x₂ → False) (_ : x₁ ≃ x₂)
  show False
  apply ‹f x₁ ≃ f x₂ → False›
  show f x₁ ≃ f x₂
  exact subst₁ ‹x₁ ≃ x₂›

instance injective_neqv_from_substitutive_eqv
    [Substitutive₁ f (· ≃ ·) (· ≃ ·)] : Injective f (· ≄ ·) (· ≄ ·)
    := {
  inject := inject_neqv
}

end neqv

/--
Class for types and operations that satisfy either the left- or right-handed
heterogeneous binary generalized substitution property.

For more information see `SubstitutiveOn.subst₂`.

**Named parameters**
- `hand`:
    Indicates whether the property is left- or right-handed.
- `α`:
    The `Sort` of `f`'s left-hand parameter.
- `β`:
    The `Sort` of `f`'s right-hand parameter.
- `γ`:
    The `Sort` of `f`'s result.
- `f`:
    The heterogeneous binary operation that obeys the generalized substitution
    property.
- `C`:
    A constraint that the non-`hand` argument to `f` must meet.
- `inputRel`:
    A binary relation on values of `α` or `β`, whichever is selected by `hand`.
- `outputRel`:
    A binary relation on values of `γ`.
-/
class SubstitutiveOn
    (hand : Hand) {α β : Sort u} {γ : Sort v} (f : α → β → γ)
    (C : outParam (hand.pick β α → Prop))
    (inputRel : outParam (hand.pick α β → hand.pick α β → Prop))
    (outputRel : γ → γ → Prop)
    where
  /--
  The left- or right-handed generalized substitution property of a
  heterogeneous binary operation `f`.

  An `f` that satisfies this property must map values of one of its input sorts
  (either `α` or `β`) that are related by `inputRel` to values of sort `γ` that
  are related by `outputRel`. If `hand` is `Hand.L`, then the input sort is `α`
  because that's the one for `f`'s left-hand parameter. Similarly, `Hand.R`
  picks `β` for the input sort.

  Often `α`, `β`, and `γ` will be the same sort, and `inputRel` and `outputRel`
  will be the same relation. A simple example is addition on natural numbers:
  if we know `n₁ ≃ n₂`, then we can conclude that `n₁ + m ≃ n₂ + m`, or that
  `m + n₁ ≃ m + n₂`.

  More advanced applications may require a nontrivial constraint `C` on `y`; an
  example is that `x₁ < x₂` implies `x₁ * y < x₂ * y` only for positive `y`.

  **Named parameters**
  - See `SubstitutiveOn` for the class parameters.
  - `x₁` and `x₂`:
      The arguments to `f`, related by `inputRel`; the `hand` parameter
      indicates which side of `f` they are given on.
  - `y`:
      The other argument to `f`; goes on the side opposite `hand`.
  - `cy`:
      Evidence that the constraint on `y` is satisfied.
  -/
  subst₂
    {x₁ x₂ : hand.pick α β} {y : hand.pick β α} (cy : C y)
    : inputRel x₁ x₂ → outputRel (hand.hAlign f x₁ y) (hand.hAlign f x₂ y)

export SubstitutiveOn (subst₂)

/--
Convenience function for the left-handed binary generalized substitution
property, for a homogeneous `f` without a constraint on `y`.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.

**Named parameters**
- `α`:
    The `Sort` of `f`'s input parameters.
- `β`:
    The `Sort` of `f`'s result.
- `f`:
    The homogeneous binary operation that obeys the left-handed generalized
    substitution property.
- `rα`:
    A binary relation on `f`'s input values.
- `rβ`:
    A binary relation on `f`'s output values.
- `x₁`, `x₂`:
    The left-hand arguments to `f`, related by `rα`.
- `y`:
    The right-hand argument to `f`.
-/
abbrev substL
    {α : Sort u} {β : Sort v} {f : α → α → β} {rα : α → α → Prop}
    {rβ : β → β → Prop} [self : SubstitutiveOn Hand.L f tc rα rβ] {x₁ x₂ y : α}
    :=
  @subst₂ Hand.L α α β f tc rα rβ self x₁ x₂ y True.intro

/--
Convenience function for the right-handed binary generalized substitution
property, for a homogeneous `f` without a constraint on `y`.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.

**Named parameters**
- `α`:
    The `Sort` of `f`'s input parameters.
- `β`:
    The `Sort` of `f`'s result.
- `f`:
    The homogeneous binary operation that obeys the right-handed generalized
    substitution property.
- `rα`:
    A binary relation on `f`'s input values.
- `rβ`:
    A binary relation on `f`'s output values.
- `x₁`, `x₂`:
    The right-hand arguments to `f`, related by `rα`.
- `y`:
    The left-hand argument to `f`.
-/
abbrev substR
    {α : Sort u} {β : Sort v} {f : α → α → β} {rα : α → α → Prop}
    {rβ : β → β → Prop} [self : SubstitutiveOn Hand.R f tc rα rβ] {x₁ x₂ y : α}
    :=
  @subst₂ Hand.R α α β f tc rα rβ self x₁ x₂ y True.intro

/--
Convenience function for the left-handed binary generalized substitution
property, for a homogeneous predicate `f` without a constraint on `y`.

Type inference for `substL` gets stuck when the output relation is `(· → ·)`;
this helper works around that issue by hardcoding the argument.

See `substL` for further documentation.

**Named parameters**
- `α`:
    The `Sort` of `f`'s input parameters.
- `f`:
    The homogeneous binary predicate that obeys the left-handed generalized
    substitution property.
- `rα`:
    A binary relation on `f`'s input values.
- See `substL` for documentation on the remaining parameters.
-/
abbrev substLFn {α : Sort u} {f : α → α → Prop} {rα : α → α → Prop} :=
  @substL α (β := Prop) f rα (rβ := (· → ·))

/--
Convenience function for the right-handed binary generalized substitution
property, for a homogeneous predicate `f` without a constraint on `y`.

Type inference for `substR` gets stuck when the output relation is `(· → ·)`;
this helper works around that issue by hardcoding the argument.

See `substR` for further documentation.

**Named parameters**
- `α`:
    The `Sort` of `f`'s input parameters.
- `f`:
    The homogeneous binary predicate that obeys the right-handed generalized
    substitution property.
- `rα`:
    A binary relation on `f`'s input values.
- See `substR` for documentation on the remaining parameters.
-/
abbrev substRFn {α : Sort u} {f : α → α → Prop} {rα : α → α → Prop} :=
  @substR α (β := Prop) f rα (rβ := (· → ·))

/--
Convenience function for the left-handed binary generalized substitution
property, with an explicit argument for the constraint on `y`.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.
-/
abbrev substLC := @subst₂ Hand.L

/--
Convenience function for the right-handed binary generalized substitution
property, with an explicit argument for the constraint on `y`.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.
-/
abbrev substRC := @subst₂ Hand.R

/--
Convenience class for types and heterogeneous operations that satisfy the full
(left- **and** right-handed) binary generalized substitution property.

See `SubstitutiveOn` for detailed documentation.

**Named parameters**
- `α`:
    The `Sort` of `f`'s left-hand parameter.
- `β`:
    The `Sort` of `f`'s right-hand parameter.
- `γ`:
    The `Sort` of `f`'s result.
- `f`:
    The heterogeneous binary operation that obeys the left- and right-handed
    generalized substitution property.
- `CL`:
    A constraint that the right-hand argument to `f` must meet for left-handed
    substitution.
- `CR`:
    A constraint that the left-hand argument to `f` must meet for right-handed
    substitution.
- `inputRelL`:
    A binary relation on input values of sort `α`, used for left-handed
    substitution.
- `inputRelR`:
    A binary relation on input values of sort `β`, used for right-handed
    substitution.
- `outputRel`:
    A binary relation on values of `γ`.
-/
class HSubstitutive₂
    {α β : Sort u} {γ : Sort v} (f : α → β → γ)
    (CL : outParam (β → Prop)) (CR : outParam (α → Prop))
    (inputRelL : outParam (α → α → Prop)) (inputRelR : outParam (β → β → Prop))
    (outputRel : γ → γ → Prop)
    where
  substitutiveL : SubstitutiveOn Hand.L f CL inputRelL outputRel
  substitutiveR : SubstitutiveOn Hand.R f CR inputRelR outputRel

attribute [instance] HSubstitutive₂.substitutiveL
attribute [instance] HSubstitutive₂.substitutiveR

/--
Simplified type constructor for the very common case of _homogeneous_
operations that satisfy the full (left- **and** right-handed) binary
generalized substitution property.

See `HSubstitutive₂` for the more general type constructor that supports
heterogeneous operations.

**Named parameters**
- `α`:
    The `Sort` of `f`'s input parameters.
- `β`:
    The `Sort` of `f`'s result.
- `f`:
    The homogeneous binary operation that obeys the left- and right-handed
    generalized substitution property.
- `C`:
    A constraint that the argument to `f` (on the side opposite the substituted
    argument) must meet.
- `inputRel`:
    A binary relation on the input values to `f` that are being substituted.
-/
abbrev Substitutive₂
    {α : Sort u} {β : Sort v}
    (f : α → α → β) (C : α → Prop) (inputRel : α → α → Prop)
    :=
  @HSubstitutive₂ α α β f C C inputRel inputRel

/-! ### Properties -/

/--
If two properties are logically equivalent, one can be substituted for the
other as the assumption (i.e. antecedent) of an implication.

**Proof intuition**: assume one of the properties, then convert it to the other
using the equivalence, and obtain the implication's conclusion.

**Named parameters**:
- `p₁`: one of the two equivalent properties.
- `p₂`: the other equivalent property.
- `q`: the conclusion of the implication.
-/
def iff_substL {p₁ p₂ q : Prop} : (p₁ ↔ p₂) → (p₁ → q) → (p₂ → q) := by
  intro ⟨(_ : p₁ → p₂), (_ : p₂ → p₁)⟩ (_ : p₁ → q) (_ : p₂)
  show q
  have : p₁ := ‹p₂ → p₁› ‹p₂›
  have : q := ‹p₁ → q› ‹p₁›
  exact ‹q›

/--
If two properties are logically equivalent, one can be substituted for the
other as the conclusion (i.e. consequent) of an implication.

**Proof intuition**: obtain one of the properties from the given implication
and common assumption, then convert it to the other using the equivalence.

**Named parameters**:
- `p₁`: one of the two equivalent properties.
- `p₂`: the other equivalent property.
- `q`: the assumption of the implication.
-/
def iff_substR {p₁ p₂ q : Prop} : (p₁ ↔ p₂) → (q → p₁) → (q → p₂) := by
  intro ⟨(_ : p₁ → p₂), (_ : p₂ → p₁)⟩ (_ : q → p₁) (_ : q)
  show p₂
  have : p₁ := ‹q → p₁› ‹q›
  have : p₂ := ‹p₁ → p₂› ‹p₁›
  exact ‹p₂›

/--
Logically equivalent properties can be substituted on both sides of an
implication.
-/
instance iff_substitutive : Substitutive₂ (· → ·) tc (· ↔ ·) (· → ·) where
  substitutiveL := SubstitutiveOn.mk λ (_ : True) => iff_substL
  substitutiveR := SubstitutiveOn.mk λ (_ : True) => iff_substR

/--
Convenience definition that converts instances of `Commutative` into instances
of `Swappable`.

The `Swappable` class is a generalization of the commutative and symmetric
properties, and is used in very abstract, general definitions. This instance
makes it easy for those definitions to apply to commutative functions.

**Named parameters**
- `α`: the argument type of the commutative function `f`.
- `β`: the result type of the commutative function `f`.
- `f`: the commutative function to produce a `Swappable` instance for.
- `R`: the binary relation that connects the two sides of the `swap` operation.

**Class parameters**
- `EqvOp β`:
    required by `Commutative f`.
- `Commutative f`:
    the property to translate into a `Swappable` instance.
- `Relation.Reflexive R`:
    provides a starting point for substitution.
- `SubstitutitveOn Hand.R R tc (· ≃ ·) (· → ·)`:
    necessary for transfering commutativity from `EqvOp β` to `R`.
-/
instance swappable_from_commutative
    {α : Type u} {β : Type v} {f : α → α → β} {R : β → β → Prop}
    [EqvOp β] [inst : SubstitutiveOn Hand.R R tc (· ≃ ·) (· → ·)]
    [Relation.Reflexive R] [Commutative f] : Fn.Swappable f R
    := {
  swap := by
    intro x y
    show R (f x y) (f y x)
    have : R (f x y) (f x y) := Rel.refl
    exact substR (self := inst) comm ‹R (f x y) (f x y)›
}

/--
Derives the right-handed binary generalized substitution property from its
left-handed counterpart, provided that the arguments to the operation `f` can
be swapped in an appropriate way.

There are many binary operations that have a symmetry between their left- and
right-handed arguments. This convenience function is a general-purpose way to
leverage that symmetry to avoid having to write a redundant proof of
right-handed substitution.

**Proof intuition**: apply left-handed substitution, then swap the arguments to
both invocations of `f`.

**Named parameters**
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized substitution property.
- `C`: a constraint that the opposite-handed argument to `f` must meet.
- `rα`: how the substitutable arguments to `f` are related.
- `rβ`: how the invocations of `f` pre- and post-substitution are related.
- `rS`: how an invocation of `f` is related to its swapped-argument version.

**Class parameters**
- `Fn.Swappable f rS`:
    The arguments of `f` need to be swappable to go from left-handed to right-
    handed substitution.
- `Substitutive₂ rβ tc rS (· → ·)`:
    Allows the result of left-handed substitution, which is an instance of the
    relation `rβ`, to be converted into the right-handed result. Both the left
    and right sides of `rβ` are invocations of `f`, and can be replaced by
    their swapped-argument versions due to how `rS` is used here and in
    `Fn.Swappable f rS`.
-/
@[implicit_reducible]
def substR_from_substL_swap
    {α : Sort u} {β : Sort v}
    {f : α → α → β} {C : α → Prop} {rα : α → α → Prop} {rβ rS : β → β → Prop}
    [Fn.Swappable f rS] [Substitutive₂ rβ tc rS (· → ·)]
    : SubstitutiveOn Hand.L f C rα rβ → SubstitutiveOn Hand.R f C rα rβ := by
  intro _ -- Make left-substitution available for instance search
  apply SubstitutiveOn.mk
  intro x₁ x₂ y (_ : C y) (_ : rα x₁ x₂)
  show rβ (f y x₁) (f y x₂)
  have : rβ (f x₁ y) (f x₂ y) := AA.substLC ‹C y› ‹rα x₁ x₂›
  have : rβ (f y x₁) (f x₂ y) := AA.substLFn Fn.swap this
  have : rβ (f y x₁) (f y x₂) := AA.substRFn Fn.swap this
  exact this

/--
The left-hand side of an equivalence can be replaced by an equivalent value.

**Intuition**: This is a somewhat trivial case of binary substitution,
essentially just transivity expressed in a slightly different way.
-/
theorem eqv_substL
    {α : Sort u} [EqvOp α] {x₁ x₂ y : α} : x₁ ≃ x₂ → x₁ ≃ y → x₂ ≃ y
    := by
  intro (_ : x₁ ≃ x₂) (_ : x₁ ≃ y)
  show x₂ ≃ y
  exact Rel.trans (Rel.symm ‹x₁ ≃ x₂›) ‹x₁ ≃ y›

/--
The left-hand side of an equivalence can be replaced by an equivalent value,
bidirectionally.

**Intuition**: Given `eqv_substL`, symmetry of equivalence means it works in
the other direction too.
-/
@[gcongr]
theorem eqv_substL_iff
    {α : Sort u} [EqvOp α] {x₁ x₂ y : α} : x₁ ≃ x₂ → (x₁ ≃ y ↔ x₂ ≃ y)
    := by
  intro (_ : x₁ ≃ x₂)
  exact Iff.intro (eqv_substL ‹x₁ ≃ x₂›) (eqv_substL (Rel.symm ‹x₁ ≃ x₂›))

/--
The right-hand side of an equivalence can be replaced by an equivalent value.

**Intuition**: This is a somewhat trivial case of binary substitution,
essentially just transivity expressed in a slightly different way.
-/
theorem eqv_substR
    {α : Sort u} [EqvOp α] {x y₁ y₂ : α} : y₁ ≃ y₂ → x ≃ y₁ → x ≃ y₂
    := by
  intro (_ : y₁ ≃ y₂) (_ : x ≃ y₁)
  show x ≃ y₂
  exact Rel.trans ‹x ≃ y₁› ‹y₁ ≃ y₂›

/--
The right-hand side of an equivalence can be replaced by an equivalent value,
bidirectionally.

**Intuition**: Given `eqv_substR`, symmetry of equivalence means it works in
the other direction too.
-/
@[gcongr]
theorem eqv_substR_iff
    {α : Sort u} [EqvOp α] {x y₁ y₂ : α} : y₁ ≃ y₂ → (x ≃ y₁ ↔ x ≃ y₂)
    := by
  intro (_ : y₁ ≃ y₂)
  exact Iff.intro (eqv_substR ‹y₁ ≃ y₂›) (eqv_substR (Rel.symm ‹y₁ ≃ y₂›))

instance eqv_substitutive
    {α : Sort u} [EqvOp α]
    : Substitutive₂ (α := α) (· ≃ ·) tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => eqv_substL }
  substitutiveR := { subst₂ := λ (_ : True) => eqv_substR }
}

/--
The left-hand side of a negated equivalence can be replaced by an equivalent
value.

**Intuition**: if we know two terms are unequal, and replace the left-hand one
with an equivalent term, the right-hand term should still be unequal to the new
term.
-/
@[gcongr]
theorem neqv_substL
    {α : Sort u} [EqvOp α] {x₁ x₂ y : α} : x₁ ≃ x₂ → x₁ ≄ y → x₂ ≄ y
    := by
  intro (_ : x₁ ≃ x₂) (_ : x₁ ≄ y) (_ : x₂ ≃ y)
  show False
  have : x₁ ≃ y := Rel.trans ‹x₁ ≃ x₂› ‹x₂ ≃ y›
  exact absurd ‹x₁ ≃ y› ‹x₁ ≄ y›

/--
The right-hand side of a negated equivalence can be replaced by an equivalent
value.

**Intuition**: if we know two terms are unequal, and replace the right-hand one
with an equivalent term, the left-hand term should still be unequal to the new
term.
-/
@[gcongr]
theorem neqv_substR
    {α : Sort u} [EqvOp α] {x₁ x₂ y : α} : x₁ ≃ x₂ → y ≄ x₁ → y ≄ x₂
    := by
  intro (_ : x₁ ≃ x₂) (_ : y ≄ x₁) (_ : y ≃ x₂)
  show False
  have : y ≃ x₁ := Rel.trans ‹y ≃ x₂› (Rel.symm ‹x₁ ≃ x₂›)
  exact absurd ‹y ≃ x₁› ‹y ≄ x₁›

instance neqv_substitutive
    {α : Sort u} [EqvOp α]
    : Substitutive₂ (α := α) (· ≄ ·) tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => neqv_substL }
  substitutiveR := { subst₂ := λ (_ : True) => neqv_substR }
}

/-- Negated equivalence is transitive with equivalence on the right. -/
theorem trans_neqv_eqv
    {α : Sort u} [EqvOp α] {x y z : α} : x ≄ y → y ≃ z → x ≄ z
    := by
  intro (_ : x ≄ y) (_ : y ≃ z)
  show x ≄ z
  prw [‹y ≃ z›] ‹x ≄ y›

/-- Enables negated equivalence usage in `calc` tactics. -/
instance trans_neqv_eqv_inst
    {α : Sort u} [EqvOp α] : Trans (β := α) (· ≄ ·) (· ≃ ·) (· ≄ ·) := {
  trans := trans_neqv_eqv
}

/-- Negated equivalence is transitive with equivalence on the left. -/
theorem trans_eqv_neqv
    {α : Sort u} [EqvOp α] {x y z : α} : x ≃ y → y ≄ z → x ≄ z
    := by
  intro (_ : x ≃ y) (_ : y ≄ z)
  show x ≄ z
  prw [←‹x ≃ y›] ‹y ≄ z›

/-- Enables negated equivalence usage in `calc` tactics. -/
instance trans_eqv_neqv_inst
    {α : Sort u} [EqvOp α] : Trans (β := α) (· ≃ ·) (· ≄ ·) (· ≄ ·) := {
  trans := trans_eqv_neqv
}

/--
The left-hand side of a negated equivalence can be replaced by an equivalent
value, bidirectionally.

**Intuition**: Given `neqv_substL`, symmetry of equivalence means it works in
the other direction too.
-/
@[gcongr]
theorem neqv_substL_iff
    {α : Sort u} [EqvOp α] {x₁ x₂ y : α} : x₁ ≃ x₂ → (x₁ ≄ y ↔ x₂ ≄ y)
    := by
  intro (_ : x₁ ≃ x₂)
  show x₁ ≄ y ↔ x₂ ≄ y
  exact Iff.intro (neqv_substL ‹x₁ ≃ x₂›) (neqv_substL (Rel.symm ‹x₁ ≃ x₂›))

/--
The right-hand side of a negated equivalence can be replaced by an equivalent
value, bidirectionally.

**Intuition**: Given `neqv_substR`, symmetry of equivalence means it works in
the other direction too.
-/
@[gcongr]
theorem neqv_substR_iff
    {α : Sort u} [EqvOp α] {x₁ x₂ y : α} : x₁ ≃ x₂ → (y ≄ x₁ ↔ y ≄ x₂)
    := by
  intro (_ : x₁ ≃ x₂)
  show y ≄ x₁ ↔ y ≄ x₂
  exact Iff.intro (neqv_substR ‹x₁ ≃ x₂›) (neqv_substR (Rel.symm ‹x₁ ≃ x₂›))

namespace Prod

/-! ### Products (i.e. ordered pairs) -/

open Relation.Equivalence.Impl.Prod (eqv_defn)

variable {α β : Type}
variable [EqvOp α]
variable [EqvOp β]

/--
Substitution of equivalent values in the left component of ordered pairs.

**Intuition**: This follows directly from the definition of equivalence for
ordered pairs. The left components must be equivalent for the pairs to be
equivalent.

**Named parameters**
- `α`: The type of the pairs' left components.
- `β`: The type of the pairs' right components.
- `x₁`, `x₂`: The equivalent left component values to substitute.
- `y`: The right component value.

**Class parameters**
- `EqvOp α`, `EqvOp β`: Needed for equivalence between pairs.
-/
@[gcongr]
theorem substL {x₁ x₂ : α} {y : β} : x₁ ≃ x₂ → (x₁, y) ≃ (x₂, y) := by
  intro (_ : x₁ ≃ x₂)
  apply eqv_defn.mpr
  show x₁ ≃ x₂ ∧ y ≃ y
  exact And.intro ‹x₁ ≃ x₂› Rel.refl

@[implicit_reducible]
def substitutiveL
    : SubstitutiveOn Hand.L (α := α) (β := β) (·,·) tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => substL
}

/--
Substitution of equivalent values in the right component of ordered pairs.

**Intuition**: This follows directly from the definition of equivalence for
ordered pairs. The right components must be equivalent for the pairs to be
equivalent.

**Named parameters**
- `α`: The type of the pairs' left components.
- `β`: The type of the pairs' right components.
- `x₁`, `x₂`: The equivalent right component values to substitute.
- `y`: The left component value.

**Class parameters**
- `EqvOp α`, `EqvOp β`: Needed for equivalence between pairs.
-/
@[gcongr]
theorem substR {x₁ x₂ : β} {y : α} : x₁ ≃ x₂ → (y, x₁) ≃ (y, x₂) := by
  intro (_ : x₁ ≃ x₂)
  apply eqv_defn.mpr
  show y ≃ y ∧ x₁ ≃ x₂
  exact And.intro Rel.refl ‹x₁ ≃ x₂›

@[implicit_reducible]
def substitutiveR
    : SubstitutiveOn Hand.R (α := α) (β := β) (·,·) tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => substR
}

instance substitutive
    : HSubstitutive₂ (α := α) (β := β) (·,·) tc tc (· ≃ ·) (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := substitutiveL
  substitutiveR := substitutiveR
}

/-- Equivalent pairs have equivalent first projections. -/
@[gcongr]
theorem fst_subst {p₁ p₂ : α × β} : p₁ ≃ p₂ → p₁.fst ≃ p₂.fst := by
  revert p₁; intro (x₁, y₁); let p₁ := (x₁, y₁)
  revert p₂; intro (x₂, y₂); let p₂ := (x₂, y₂)
  intro (_ : p₁ ≃ p₂)
  show p₁.fst ≃ p₂.fst

  have (And.intro (_ : x₁ ≃ x₂) _) := eqv_defn.mp ‹(x₁, y₁) ≃ (x₂, y₂)›
  calc
    _ = p₁.fst       := rfl
    _ = (x₁, y₁).fst := rfl
    _ = x₁           := rfl
    _ ≃ x₂           := ‹x₁ ≃ x₂›
    _ = (x₂, y₂).fst := rfl
    _ = p₂.fst       := rfl

/-- Equivalent pairs have equivalent second projections. -/
@[gcongr]
theorem snd_subst {p₁ p₂ : α × β} : p₁ ≃ p₂ → p₁.snd ≃ p₂.snd := by
  revert p₁; intro (x₁, y₁); let p₁ := (x₁, y₁)
  revert p₂; intro (x₂, y₂); let p₂ := (x₂, y₂)
  intro (_ : p₁ ≃ p₂)
  show p₁.snd ≃ p₂.snd

  have (And.intro _ (_ : y₁ ≃ y₂)) := eqv_defn.mp ‹(x₁, y₁) ≃ (x₂, y₂)›
  calc
    _ = p₁.snd       := rfl
    _ = (x₁, y₁).snd := rfl
    _ = y₁           := rfl
    _ ≃ y₂           := ‹y₁ ≃ y₂›
    _ = (x₂, y₂).snd := rfl
    _ = p₂.snd       := rfl

end Prod

/-!
## Cancellation

### Definitions
-/

/--
Class for types and operations that satisfy either the left- or right-handed
generalized cancellation property.

For more information see `CancellativeOn.cancel`.

**Named parameters**
- `hand`: indicates whether the property is left- or right-handed.
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized cancellation property.
- `C`: a constraint that the argument on the `hand` side of `f` must meet.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class CancellativeOn
    (hand : Hand) {α : Sort u} {β : Sort v}
    (f : α → α → β) (C : outParam (α → Prop))
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop)
    where
  /--
  The left- or right-handed generalized cancellation property of a binary
  operation `f`.

  This property is in some sense the converse of the generalized substitution
  property; see `SubstitutiveOn.subst₂`. It says: knowing that the results of
  two invocations of `f` satisfy the relation `rβ` tells us that the two left-
  or right-handed arguments to `f` satisfy the relation `rα`.

  Often `α` and `β` will be the same type, and `rα` and `rβ` will be the same
  relation. A simple example is of addition on natural numbers: if we know that
  `n₁ + m ≃ n₂ + m`, or that `m + n₁ ≃ m + n₂`, then we can conclude that
  `n₁ ≃ n₂`.

  More advanced applications may require a nontrivial constraint `C` on `x`; an
  example is that `x * y₁ ≃ x * y₂` implies `y₁ ≃ y₂` only for nonzero `x`.

  **Named parameters**
  - see `CancellativeOn` for the class parameters.
  - `x`: the "cancelled" argument to `f`; the `hand` parameter
    indicates which side of `f` it appears on.
  - `y₁` and `y₂`: the other arguments to `f`; appearing on the side opposite
    `hand`. They are related by `rα` in the result.
  - `cx`: evidence that the constraint on `x` is satisfied.
  -/
  cancel
    {x y₁ y₂ : α} (cx : C x)
    : rβ (hand.align f x y₁) (hand.align f x y₂) → rα y₁ y₂

export CancellativeOn (cancel)

/--
Convenience function for the left-handed generalized cancellation property,
without a constraint on `x`.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelL
    {α : Sort u} {β : Sort v} {f : α → α → β} {rα : α → α → Prop}
    {rβ : β → β → Prop} [self : CancellativeOn Hand.L f tc rα rβ]
    {x y₁ y₂ : α} :=
  @cancel Hand.L α β f tc rα rβ self x y₁ y₂ True.intro

/--
Convenience function for the right-handed generalized cancellation property,
without a constraint on `x`.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelR
    {α : Sort u} {β : Sort v} {f : α → α → β} {rα : α → α → Prop}
    {rβ : β → β → Prop} [self : CancellativeOn Hand.R f tc rα rβ]
    {x y₁ y₂ : α} :=
  @cancel Hand.R α β f tc rα rβ self x y₁ y₂ True.intro

/--
Convenience function for the left-handed generalized cancellation property,
with an explicit argument for the constraint on `x`.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelLC := @cancel Hand.L

/--
Convenience function for the right-handed generalized cancellation property,
with an explicit argument for the constraint on `x`.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelRC := @cancel Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) generalized cancellation property.

See `CancellativeOn` for detailed documentation.
-/
class Cancellative
    {α : Sort u} {β : Sort v} (f : α → α → β) (C : outParam (α → Prop))
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop)
    where
  cancellativeL : CancellativeOn Hand.L f C rα rβ
  cancellativeR : CancellativeOn Hand.R f C rα rβ

attribute [instance] Cancellative.cancellativeL
attribute [instance] Cancellative.cancellativeR

/-! ### Properties -/

/--
Derives the right-handed generalized cancellation property from its left-handed
counterpart, provided that the types and operations involved obey some
restrictions.

**Intuition**: if `f` is commutative and `rβ` supports substitution, then the
arguments to `f` can be swapped so that left-handed cancellation can be used.

**Named parameters**
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized cancellation property.
- `C`: a constraint that the argument on the cancellation-hand side of `f` must
  meet.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.

**Class parameters**
- `EqvOp β`: needed for both the `Commutative` and `Substitutive₂` parameters
- `Commutative f`: needed for swapping the arguments to `f`.
- `Substitutive₂ rβ (· ≃ ·) (· → ·)`: needed to update the right-handed
  hypothesis involving `rβ` to a left-handed hypothesis.
-/
@[implicit_reducible]
def cancelR_from_cancelL
    {α : Sort u} {β : Sort v}
    {f : α → α → β} {C : α → Prop} {rα : α → α → Prop} {rβ : β → β → Prop}
    [EqvOp β] [Commutative f] [Substitutive₂ rβ tc (· ≃ ·) (· → ·)]
    : CancellativeOn Hand.L f C rα rβ → CancellativeOn Hand.R f C rα rβ := by
  intro
  constructor
  intro x y₁ y₂ (_ : C x) (_ : rβ (f y₁ x) (f y₂ x))
  show rα y₁ y₂
  have : rβ (f x y₁) (f y₂ x) := AA.substLFn AA.comm ‹rβ (f y₁ x) (f y₂ x)›
  have : rβ (f x y₁) (f x y₂) := AA.substRFn AA.comm ‹rβ (f x y₁) (f y₂ x)›
  exact AA.cancelLC ‹C x› ‹rβ (f x y₁) (f x y₂)›

end Lean4Axiomatic.AA

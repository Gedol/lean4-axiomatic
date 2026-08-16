import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.Logic

namespace Lean4Axiomatic.AA

open Logic (Either)
open Relation.Equivalence (EqvOp)

/--
Class for types and operations that satisfy the associative property.

For more information see `Associative.assoc` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Associative_property).

**Named parameters**
- `α`: the type that the binary operation `f` is defined over.
- `f`: the binary operation that obeys the associative property.

**Class parameters**
- `EqvOp α`: necessary because the property expresses an equality on `α`.
-/
class Associative {α : Sort u} [EqvOp α] (f : α → α → α) where
  /--
  The associative property of a binary operation `f` defined over a type `α`.

  Some well-known examples from arithmetic are that addition and multiplication
  are associative; we have `(a + b) + c ≃ a + (b + c)` and
  `(a * b) * c ≃ a * (b * c)` for all natural numbers `a`, `b`, and `c`.

  **Named parameters**
  - see `Associative` for the class parameters.
  - `x`: the first operand (when reading from left to right).
  - `y`: the second operand.
  - `z`: the third operand.
  -/
  assoc {x y z : α} : f (f x y) z ≃ f x (f y z)

export Associative (assoc)

/--
Class for types and operations that have either a left or right absorbing
element.

For more information see `AbsorbingOn.absorb` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Absorbing_element).

**Named parameters**
- `hand`:
  Indicates whether the absorbing element is the left or right argument to the
  binary operation `f`.
- `α`:
  The `Sort` of the absorbing element and the parameters of the operation `f`.
- `z`:
  The absorbing element, named `z` to suggest zero (the canonical example).
- `f`:
  The binary operation that has `z` as absorbing element.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equivalence on `α`.
-/
class AbsorbingOn
    (hand : Hand) {α : Sort u} [EqvOp α] (z : α) (f : α → α → α)
    where
  /--
  The left- or right-handed absorption property of a distinguished element `z`
  and a binary operation `f` defined over a sort `α`.

  The most well-known example of an absorbing element is zero, when paired with
  multiplication. In all standard number systems, `0 * x ≃ 0 ≃ x * 0` for all
  numbers `x`.

  **Named parameters**
  - See `AbsorbingOn` for the class parameters.
  - `x`:
    The argument to `f` that is not the absorbing element; it will be in the
    position that is the opposite of `hand`.
  -/
  absorb {x : α} : hand.align f z x ≃ z

export AbsorbingOn (absorb)

/--
Convenience function for the left-handed absorption property.

Can often resolve cases where type inference gets stuck when using the more
general `AbsorbingOn.absorb` function; see its documentation for details.
-/
abbrev absorbL := @absorb Hand.L

/--
Convenience function for the right-handed absorption property.

Can often resolve cases where type inference gets stuck when using the more
general `AbsorbingOn.absorb` function; see its documentation for details.
-/
abbrev absorbR := @absorb Hand.R

/--
Convenience class for types and operations that have left **and** right
absorbing element.

See `AbsorbingOn` for detailed documentation.
-/
class Absorbing {α : Sort u} [EqvOp α] (z : α) (f : α → α → α) where
  absorbingL : AbsorbingOn Hand.L z f
  absorbingR : AbsorbingOn Hand.R z f

attribute [instance] Absorbing.absorbingL
attribute [instance] Absorbing.absorbingR

/--
Derive right-handed absorption from left-handed absorption for operations `f`
meeting certain conditions.

**Intuition**: Both left and right absorbing elements produce the same result
(themselves) from their associated binary operation. Thus, if the arguments to
`f` can be swapped, one hand can be shown to imply the other.

**Named parameters**
- `α`: The `Sort` of the absorbing element `z`, and `f`'s parameters.
- `z`: The absorbing element.
- `f`: The binary operation that has `z` as absorbing element.

**Class parameters**
- `EqvOp α`: Necessary because `AbsorbingOn.absorb` requires it.
- `Commutative f`: Restriction on `f` that's required for the derivation.
-/
@[implicit_reducible]
def absorbingR_from_absorbingL
    {α : Sort u} {z : α} {f : α → α → α} [EqvOp α] [Commutative f]
    : AbsorbingOn Hand.L z f → AbsorbingOn Hand.R z f
    := by
  intro _ -- Make left absorbing available to instance search
  apply AbsorbingOn.mk
  intro (x : α)
  show f x z ≃ z
  exact Rel.trans AA.comm AA.absorbL

/--
Class for types, values, and operations that satisfy either the left- or
right-handed identity property.

For more information see `IdentityOn.ident` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Identity_element).

**Named parameters**
- `hand`:
  Indicates whether the property is left- or right-handed.
- `α`:
  The `Sort` of the identity element and the parameters of the operation.
- `e`:
  The identity element. It's labeled as an `outParam` because it's useful to
  have it be inferred in some contexts; see `InverseOn` for an example.
- `f`:
  The binary operation that obeys the identity property with `e`.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equality on `α`.
-/
class IdentityOn
    (hand : Hand) {α : Sort u} [EqvOp α] (e : outParam α) (f : α → α → α)
    where
  /--
  The left- or right-handed identity property of a distinguished element `e`
  and a binary operation `f` defined over a sort `α`.

  The most well-known examples are the additive and multiplicative identities
  from arithmetic. Zero is the identity element for addition (because
  `0 + n ≃ n + 0 ≃ n` for all `n`), while one is the identity for
  multiplication (because `1 * m ≃ m * 1 ≃ m` for all `m`).

  **Named parameters**
  - See `IdentityOn` for the class parameters.
  - `x`:
    The argument to `f` that is not the identity element; it will be in the
    position that is the opposite of `hand`.
  -/
  ident {x : α} : hand.align f e x ≃ x

export IdentityOn (ident)

/--
Convenience function for the left-handed identity property.

Can often resolve cases where type inference gets stuck when using the more
general `ident` function.

See `IdentityOn.ident` for detailed documentation.
-/
abbrev identL := @ident Hand.L

/--
Convenience function for the right-handed identity property.

Can often resolve cases where type inference gets stuck when using the more
general `ident` function.

See `IdentityOn.ident` for detailed documentation.
-/
abbrev identR := @ident Hand.R

/--
Convenience class for types, values, and operations that satisfy the full
(left- **and** right-handed) identity property.

See `IdentityOn` for detailed documentation.
-/
class Identity {α : Sort u} [EqvOp α] (e : outParam α) (f : α → α → α) where
  identityL : IdentityOn Hand.L e f
  identityR : IdentityOn Hand.R e f

attribute [instance] Identity.identityL
attribute [instance] Identity.identityR

/--
Derive the right-identity property from left-identity for operations `f`
meeting certain conditions.

**Intuition**: Both the left-handed and right-handed versions of the property
equate an application of `f` to the same value. Thus if `f` is commutative, one
version implies the other.

**Named parameters**
- `α`: The `Sort` of the identity element and the parameters of the operation.
- `e`: The identity element.
- `f`: The binary operation that obeys the identity property with `e`.

**Class parameters**
- `EqvOp α`: Necessary because `IdentityOn.ident` expresses an equality on `α`.
- `Commutative f`: Restriction on `f` that's required for the derivation.
-/
@[implicit_reducible]
def identityR_from_identityL
    {α : Sort u} [EqvOp α] {e : α} {f : α → α → α} [Commutative f]
    : IdentityOn Hand.L e f → IdentityOn Hand.R e f
    := by
  intro _ -- Make left identity available to instance search
  apply IdentityOn.mk
  intro (x : α)
  show f x e ≃ x
  exact Rel.trans AA.comm AA.identL

/--
Class for types and operations that satisfy either the left- or right-handed
inverse property.

For more information see `InverseOn.inverse` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Inverse_element).

**Named parameters**
- `hand`: Indicates whether the property is left- or right-handed.
- `α`: The `Sort` of the operations' parameters.
- `e`: An identity element under the operation `f`.
- `inv`: An operation that turns any `α` value into its inverse.
- `f`: The binary operation that, with `inv`, obeys the inverse property.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equality on `α`.
- `IdentityOn hand e f`: Evidence that `e` is an identity element.
-/
class InverseOn
    (hand : Hand) {α : Sort u} {e : α} (inv : outParam (α → α)) (f : α → α → α)
    [EqvOp α] [IdentityOn hand e f]
    where
  /--
  The left- or right-handed inverse property of an inverse operation `inv` and
  a binary operation `f` defined over a sort `α`.

  The most well-known examples are additive and multiplicative inverses from
  arithmetic. Integers are the simplest numbers to have additive inverses, via
  negation; `a + (-a) ≃ (-a) + a ≃ 0` for all `a`. Similarly, rational numbers
  are the simplest ones with multiplicative inverses, via reciprocation;
  `q * q⁻¹ ≃ q⁻¹ * q ≃ 1` for all nonzero `q`.

  **Named parameters**
  - See `InverseOn` for the class parameters.
  - `x`: The value that is combined (via `f`) with its own inverse.
  -/
  inverse {x : α} : hand.align f (inv x) x ≃ e

export InverseOn (inverse)

/--
Convenience function for the left-handed inverse property.

Can often resolve cases where type inference gets stuck when using the more
general `inverse` function.

See `InverseOn.inverse` for detailed documentation.
-/
abbrev inverseL := @inverse Hand.L

/--
Convenience function for the right-handed inverse property.

Can often resolve cases where type inference gets stuck when using the more
general `inverse` function.

See `InverseOn.inverse` for detailed documentation.
-/
abbrev inverseR := @inverse Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) inverse property.

See `InverseOn` for detailed documentation.
-/
class Inverse
    {α : Sort u} {e : α} (inv : outParam (α → α)) (f : α → α → α)
    [EqvOp α] [Identity e f]
    where
  inverseL : InverseOn Hand.L inv f
  inverseR : InverseOn Hand.R inv f

attribute [instance] Inverse.inverseL
attribute [instance] Inverse.inverseR

/--
Derive the right-inverse property from left-inverse for operations `f`
meeting certain conditions.

**Intuition**: Both the left-handed and right-handed versions of the property
equate an application of `f` to the same value. Thus if `f` is commutative, one
version implies the other.

**Named parameters**
- `α`: The `Sort` of the operations' parameters.
- `e`: An identity element under the operation `f`.
- `inv`: An operation that turns any `α` value into its inverse.
- `f`: The binary operation that, with `inv`, obeys the inverse property.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equality on `α`.
- `IdentityOn hand e f`: Evidence that `e` is an identity element.
- `Commutative f`: Restriction on `f` that's required for the derivation.
-/
@[implicit_reducible]
def inverseR_from_inverseL
    {α : Sort u} {e : α} {inv : α → α} {f : α → α → α}
    [EqvOp α] [Identity e f] [Commutative f]
    : InverseOn Hand.L inv f → InverseOn Hand.R inv f
    := by
  intro _ -- Make left inverse available to instance search
  apply InverseOn.mk
  intro (x : α)
  show f x (inv x) ≃ e
  exact Rel.trans AA.comm AA.inverseL

/--
Class for types and operations that satisfy either the left- or right-handed
semicompatibility property.

This property doesn't seem to have a standard name. For more information see
`SemicompatibleOn.scompat`

**Named parameters**
- `hand`: Indicates whether the property is left- or right-handed.
- `α`: The `Sort` that the operations `f` and `g` are defined over.
- `f`: An unary operation on `α`.
- `g`: A binary operation on `α`.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equivalence on `α`.
-/
class SemicompatibleOn
    (hand : Hand) {α : Sort u} [EqvOp α] (f : α → α) (g : α → α → α)
    where
  /--
  The left- or right-handed semicompatibility property of two operations `f`
  and `g` defined over a sort `α`.

  The property is called _semi_-compatible because when `f` is exchanged with
  `g`, it only operates on one of `g`'s arguments, rather than both. An example
  of operations that are semicompatible are _successor_ (i.e., `step`) and
  _addition_ on natural numbers: `step n + m ≃ step (n + m) ≃ n + step m`.
  Another example is negation and multiplication on integers:
  `(-a) * b ≃ -(a * b) ≃ a * (-b)`.

  **Named parameters**
  - See `SemicompatibleOn` for the class parameters.
  - `x`: The left-hand argument to `g`.
  - `y`: The right-hand argument to `g`.
  -/
  scompat {x y : α} : f (g x y) ≃ hand.pick (g (f x) y) (g x (f y))

export SemicompatibleOn (scompat)

/--
Convenience function for the left-handed semicompatibility property.

Can often resolve cases where type inference gets stuck when using the more
general `scompat` function.

See `SemicompatibleOn.scompat` for detailed documentation.
-/
abbrev scompatL := @scompat Hand.L

/--
Convenience function for the right-handed semicompatibility property.

Can often resolve cases where type inference gets stuck when using the more
general `scompat` function.

See `SemicompatibleOn.scompat` for detailed documentation.
-/
abbrev scompatR := @scompat Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) semicompatibility property.

See `SemicompatibleOn` for detailed documentation.
-/
class Semicompatible {α : Sort u} [EqvOp α] (f : α → α) (g : α → α → α) where
  semicompatibleL : SemicompatibleOn Hand.L f g
  semicompatibleR : SemicompatibleOn Hand.R f g

attribute [instance] Semicompatible.semicompatibleL
attribute [instance] Semicompatible.semicompatibleR

/--
Derive the right-semicompatibility property from left-semicompatibility for
operations `f` and `g` meeting certain conditions.

**Intuition**: Both the left-handed and right-handed versions of the property
have one side of their equivalences in common. Thus if `g` is commutative, one
version implies the other.

**Named parameters**
- `α`: The `Sort` of the operations' parameters.
- `f`: An unary operation on `α`.
- `g`: A binary operation on `α`.

**Class parameters**
- `EqvOp α`:
    Necessary because the property expresses an equivalence on `α`.
- `Substitutive₁ f (· ≃ ·) (· ≃ ·)`:
    Needed to transform an expression passed to `f`. Nearly every useful `f`
    will satisfy this property.
- `Commutative g`:
    Restriction on `g` that's required for the derivation.
-/
@[implicit_reducible]
def semicompatibleR_from_semicompatibleL
    {α : Sort u} {f : α → α} {g : α → α → α}
    [EqvOp α] [Substitutive₁ f (· ≃ ·) (· ≃ ·)] [Commutative g]
    : SemicompatibleOn Hand.L f g → SemicompatibleOn Hand.R f g
    := by
  intro _ -- Make the left-hand property available to instance search
  apply SemicompatibleOn.mk
  intro x y
  show f (g x y) ≃ g x (f y)
  calc
    f (g x y) ≃ _ := AA.subst₁ AA.comm
    f (g y x) ≃ _ := AA.scompatL
    g (f y) x ≃ _ := AA.comm
    g x (f y) ≃ _ := Rel.refl

/--
Class for types and operations that satisfy the binary compatibility property.

This property does not have a standard name in abstract algebra. However, it is
a key part of what it means to have a
[homomorphism](https://en.wikipedia.org/wiki/Homomorphism) between algebraic
structures.

**Named parameters**
- `α`:
    The `Sort` that is the input of `f` and that the operation `g` is defined
    over.
- `β`:
    The `Sort` that is the output of `f` and that the operation `h` is defined
    over.
- `f`:
    An unary operation mapping `α` to `β`, that is "compatible" with operations
    `g` and `h`.
- `g`:
    A binary operation on `α`.
- `h`:
    A binary operation on `β`.

**Class parameters**
- `EqvOp β`: Necessary because the property expresses an equivalence on `β`.
-/
class Compatible₂
    {α β : Sort u} [EqvOp β]
    (f : α → β) (g : α → α → α) (h : outParam (β → β → β))
    where
  /--
  The compatibility property of an unary operation `f` with two binary
  operations `g` and `h` that are defined over sorts `α` and `β`, respectively.

  Typically, `g` and `h` represent a similar operation on each of their sorts,
  and we say that `f` _is compatible with_ that operation, or that `f`
  _preserves_ the operation. In particular, `α` and `β` are often the same
  sort, and `g` and `h` are often the same operation.

  An example instance of the property is that negation is compatible with
  addition on the integers: `-(a + b) ≃ (-a) + (-b)` for all integers `a` and
  `b`.

  **Named parameters**
  - See `Compatible` for the class parameters.
  - `x`: The left-hand argument to `g`.
  - `y`: The right-hand argument to `g`.
  -/
  compat₂ {x y : α} : f (g x y) ≃ h (f x) (f y)

export Compatible₂ (compat₂)

/--
Class for types and operations that satisfy either the left- or right-handed
distributive property.

For more information see `DistributiveOn.distrib` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Distributive_property).

**Named parameters**
- `hand`: indicates whether the property is left- or right-handed.
- `α`: the type that the binary operations `f` and `g` are defined over.
- `f`: the binary operation that distributes over `g`.
- `g`: the binary operation that `f` distributes over.

**Class parameters**
- `EqvOp α`: necessary because the property expresses an equality on `α`.
-/
class DistributiveOn
    (hand : Hand) {α : Sort u} [EqvOp α] (f g : α → α → α) where
  /--
  The left- or right-handed distributive property of two binary operations `f`
  and `g` defined over a type `α`.

  If this property is satisfied, one says that `f` _distributes_ over `g`. A
  well-known example from arithmetic is that multiplication distributes over
  addition; `a * (b + c) ≃ a * b + a * c` for the left-handed case and
  `(b + c) * a ≃ b * a + c * a` for the right-handed case.

  **Named parameters**
  - see `DistributiveOn` for the class parameters.
  - `x`: the argument to `f` that gets distributed; the `hand` parameter
    indicates which side of `f` it is on.
  - `y`: the left argument to `g`.
  - `z`: the right argument to `g`.
  -/
  distrib {x y z : α} :
    hand.align f x (g y z) ≃ g (hand.align f x y) (hand.align f x z)

export DistributiveOn (distrib)

/--
Convenience function for the left-handed distributive property.

Can often resolve cases where type inference gets stuck when using the more
general `distrib` function.

See `DistributiveOn.distrib` for detailed documentation.
-/
abbrev distribL := @distrib Hand.L

/--
Convenience function for the right-handed distributive property.

Can often resolve cases where type inference gets stuck when using the more
general `distrib` function.

See `DistributiveOn.distrib` for detailed documentation.
-/
abbrev distribR := @distrib Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) distributive property.

See `DistributiveOn` for detailed documentation.
-/
class Distributive {α : Sort u} [EqvOp α] (f g : α → α → α) where
  distributiveL : DistributiveOn Hand.L f g
  distributiveR : DistributiveOn Hand.R f g

attribute [instance] Distributive.distributiveL
attribute [instance] Distributive.distributiveR

/--
Derive right-distributivity from left-distributivity for operations `f` and `g`
meeting certain conditions.
-/
@[implicit_reducible]
def distributiveR_from_distributiveL
    {α : Sort u} {f g : α → α → α}
    [EqvOp α] [Commutative f] [Substitutive₂ g AA.tc (· ≃ ·) (· ≃ ·)]
    : DistributiveOn Hand.L f g → DistributiveOn Hand.R f g := by
  intro
  constructor
  intro x y z
  show f (g y z) x ≃ g (f y x) (f z x)
  calc
    f (g y z) x       ≃ _ := AA.comm
    f x (g y z)       ≃ _ := AA.distribL
    g (f x y) (f x z) ≃ _ := AA.substL AA.comm
    g (f y x) (f x z) ≃ _ := AA.substR AA.comm
    g (f y x) (f z x) ≃ _ := Rel.refl

/-- Expresses that one of two propositions is true, but not both. -/
def ExactlyOneOfTwo (α β : Prop) : Prop := (α ∨ β) ∧ ¬ (α ∧ β)

/--
Provides a value of one of the two given propositions, and a proof that the
other proposition cannot be inhabited.
-/
structure ExactlyOneOfTwo₁ (α β : Prop) : Type where
  /-- A value of one of the two propositions. -/
  atLeastOne : Either α β

  /-- Both propositions cannot be inhabited. -/
  atMostOne : ¬(α ∧ β)

/--
Inhabited when at least one of its three propositions is true; a three-way
logical OR.
-/
inductive OneOfThree (α β γ : Prop) : Prop
| first  (a : α)
| second (b : β)
| third  (c : γ)

/--
Inhabited when at least one of its three propositions is true; a three-way
logical OR.

It's in `Type` rather than `Prop` so it can be used for branching in program
logic.
-/
inductive OneOfThree₁ (α β γ : Prop) : Type
| first  (a : α)
| second (b : β)
| third  (c : γ)

/--
Converts each proposition in `OneOfThree` to a different one while preserving
which one is inhabited.

Intended to be used in contexts where the mapping functions are previously
defined, to keep the code compact.
-/
def OneOfThree.map
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Prop}
    : OneOfThree α₁ β₁ γ₁ → (α₁ → α₂) → (β₁ → β₂) → (γ₁ → γ₂)
    → OneOfThree α₂ β₂ γ₂
| first a, f, _, _ => first (f a)
| second b, _, g, _ => second (g b)
| third c, _, _, h => third (h c)

/--
"Rotates" `OneOfThree`'s propositions one place to the left: the leftmost one
becomes the rightmost.

This merely changes how the type is written; the value is preserved. Useful
in conjunction with `OneOfThree.map` to translate between arbitrary
`OneOfThree` types.
-/
def OneOfThree.rotL {α β γ : Prop} : OneOfThree α β γ → OneOfThree β γ α
| first a => third a
| second b => first b
| third c => second c

/--
"Rotates" `OneOfThree`'s propositions one place to the right: the rightmost one
becomes the leftmost.

This merely changes how the type is written; the value is preserved. Useful
in conjunction with `OneOfThree.map` to translate between arbitrary
`OneOfThree` types.
-/
def OneOfThree.rotR {α β γ : Prop} : OneOfThree α β γ → OneOfThree γ α β
| first a => second a
| second b => third b
| third c => first c

/-- Inhabited when at least two of its three propositions are true. -/
inductive TwoOfThree (α β γ : Prop) : Prop
| oneAndTwo   (a : α) (b : β)
| oneAndThree (a : α) (c : γ)
| twoAndThree (b : β) (c : γ)

/--
Converts each proposition in `TwoOfThree` to a different one while preserving
which ones are inhabited.

Intended to be used in contexts where the mapping functions are previously
defined, to keep the code compact.
-/
def TwoOfThree.map
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Prop} (f : α₁ → α₂) (g : β₁ → β₂) (h : γ₁ → γ₂)
    : TwoOfThree α₁ β₁ γ₁ → TwoOfThree α₂ β₂ γ₂
| oneAndTwo a b => oneAndTwo (f a) (g b)
| oneAndThree a c => oneAndThree (f a) (h c)
| twoAndThree b c => twoAndThree (g b) (h c)

/--
"Rotates" `TwoOfThree`'s propositions one place to the left: the leftmost one
becomes the rightmost.

This merely changes how the type is written; the value is preserved. Useful
in conjunction with `TwoOfThree.map` to translate between arbitrary
`TwoOfThree` types.
-/
def TwoOfThree.rotL {α β γ : Prop} : TwoOfThree α β γ → TwoOfThree β γ α
| oneAndTwo a b => oneAndThree b a
| oneAndThree a c => twoAndThree c a
| twoAndThree b c => oneAndTwo b c

/--
"Rotates" `TwoOfThree`'s propositions one place to the right: the rightmost one
becomes the leftmost.

This merely changes how the type is written; the value is preserved. Useful
in conjunction with `TwoOfThree.map` to translate between arbitrary
`TwoOfThree` types.
-/
def TwoOfThree.rotR {α β γ : Prop} : TwoOfThree α β γ → TwoOfThree γ α β
| oneAndTwo a b => twoAndThree a b
| oneAndThree a c => oneAndTwo c a
| twoAndThree b c => oneAndThree c b

/--
Inhabited when exactly one of its three propositions is true.

Can be used to express the various "trichotomy" properties in algebra.
-/
structure ExactlyOneOfThree (α β γ : Prop) : Prop where
  atLeastOne :   OneOfThree α β γ
  atMostOne  : ¬ TwoOfThree α β γ

/--
Converts all propositions in `ExactlyOneOfThree` to equivalents while
preserving the one that's inhabited.

Intended to be used in contexts where the mapping functions are previously
defined, to keep the code compact.
-/
def ExactlyOneOfThree.map
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Prop}
    : ExactlyOneOfThree α₁ β₁ γ₁ → (α₁ ↔ α₂) → (β₁ ↔ β₂) → (γ₁ ↔ γ₂)
    → ExactlyOneOfThree α₂ β₂ γ₂
    := by
  intro (x : ExactlyOneOfThree α₁ β₁ γ₁)
  intro (f : α₁ ↔ α₂) (g : β₁ ↔ β₂) (h : γ₁ ↔ γ₂)
  have atLeastOne : OneOfThree α₂ β₂ γ₂ := x.atLeastOne.map f.mp g.mp h.mp
  have atMostOne : ¬TwoOfThree α₂ β₂ γ₂ :=
    mt (TwoOfThree.map f.mpr g.mpr h.mpr) x.atMostOne
  exact ExactlyOneOfThree.mk atLeastOne atMostOne

/--
"Rotates" `ExactlyOneOfThree`'s propositions one place to the left: the
leftmost one becomes the rightmost.

This merely changes how the type is written; the value is preserved. Useful
in conjunction with `ExactlyOneOfThree.map` to translate between arbitrary
`ExactlyOneOfThree` types.
-/
def ExactlyOneOfThree.rotL
    {α β γ : Prop} : ExactlyOneOfThree α β γ → ExactlyOneOfThree β γ α
    := by
  intro (x : ExactlyOneOfThree α β γ)
  have atLeastOne : OneOfThree β γ α := x.atLeastOne.rotL
  have atMostOne : ¬TwoOfThree β γ α := mt TwoOfThree.rotR x.atMostOne
  exact ExactlyOneOfThree.mk atLeastOne atMostOne

/--
"Rotates" `ExactlyOneOfThree`'s propositions one place to the right: the
rightmost one becomes the leftmost.

This merely changes how the type is written; the value is preserved. Useful
in conjunction with `ExactlyOneOfThree.map` to translate between arbitrary
`ExactlyOneOfThree` types.
-/
def ExactlyOneOfThree.rotR
    {α β γ : Prop} : ExactlyOneOfThree α β γ → ExactlyOneOfThree γ α β
    := by
  intro (x : ExactlyOneOfThree α β γ)
  have atLeastOne : OneOfThree γ α β := x.atLeastOne.rotR
  have atMostOne : ¬TwoOfThree γ α β := mt TwoOfThree.rotL x.atMostOne
  exact ExactlyOneOfThree.mk atLeastOne atMostOne

/--
Class for types and operations that satisfy the
[zero-product property](https://en.wikipedia.org/wiki/Zero-product_property).

**Named parameters**
- `α`: the type of values in the product.
- `f`: the product operation.

**Class parameters**
- `EqvOp α`: necessary because the property expresses an equivalence on `α`.
- `OfNat α 0`: necessary because the property requires `α` to contain zero.
-/
class ZeroProduct {α : Type u} [EqvOp α] [OfNat α 0] (f : α → α → α) where
  /--
  The zero-product property of a product operation `f` defined over a type `α`.

  The canonical example of this is from arithmetic:
  `a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0`, and it holds in all of the familiar number
  systems, from the natural numbers `ℕ` through the complex numbers `ℂ`.

  **Named parameters**
  - `x`: the left argument to `f`.
  - `y`: the right argument to `f`.
  -/
  zero_prod {x y : α} : f x y ≃ 0 → x ≃ 0 ∨ y ≃ 0

export ZeroProduct (zero_prod)

/--
Swaps the middle two elements of a balanced four-element expression involving a
single binary operation.

The sort `α` and its binary operation `f` must form a commutative semigroup.

**Named parameters**
- `α`: the sort over which `f` operates.
- `f`: the binary operation used in the expression.
- `a`, `b`, `c`, `d`: the operands to `f` in the expression.

**Class parameters**
- `EqvOp α`: needed to express the identity between expressions.
- `Associative f`, `Commutative f`: needed to rearrange the operands freely.
- `Substitutive₂ f tc (· ≃ ·) (· ≃ ·)`: needed to rearrange subexpressions.
-/
theorem expr_xxfxxff_lr_swap_rl
    {α : Sort u} {f : α → α → α} {a b c d : α} [EqvOp α]
    [Associative f] [Commutative f] [Substitutive₂ f tc (· ≃ ·) (· ≃ ·)]
    : f (f a b) (f c d) ≃ f (f a c) (f b d)
    := calc
  f (f a b) (f c d) ≃ _ := AA.assoc
  f a (f b (f c d)) ≃ _ := AA.substR (Rel.symm AA.assoc)
  f a (f (f b c) d) ≃ _ := AA.substR (AA.substL AA.comm)
  f a (f (f c b) d) ≃ _ := AA.substR AA.assoc
  f a (f c (f b d)) ≃ _ := Rel.symm AA.assoc
  f (f a c) (f b d) ≃ _ := Rel.refl

/--
Swaps the second and fourth elements of a balanced four-element expression
involving a single binary operation.

The sort `α` and its binary operation `f` must form a commutative semigroup.

**Named parameters**
- `α`: the sort over which `f` operates.
- `f`: the binary operation used in the expression.
- `a`, `b`, `c`, `d`: the operands to `f` in the expression.

**Class parameters**
- `EqvOp α`: needed to express the identity between expressions.
- `Associative f`, `Commutative f`: needed to rearrange the operands freely.
- `Substitutive₂ f tc (· ≃ ·) (· ≃ ·)`: needed to rearrange subexpressions.
-/
theorem expr_xxfxxff_lr_swap_rr
    {α : Sort u} {f : α → α → α} {a b c d : α} [EqvOp α]
    [Associative f] [Commutative f] [Substitutive₂ f tc (· ≃ ·) (· ≃ ·)]
    : f (f a b) (f c d) ≃ f (f a d) (f c b)
    := calc
  f (f a b) (f c d) ≃ _ := AA.substR AA.comm
  f (f a b) (f d c) ≃ _ := expr_xxfxxff_lr_swap_rl
  f (f a d) (f b c) ≃ _ := AA.substR AA.comm
  f (f a d) (f c b) ≃ _ := Rel.refl

end Lean4Axiomatic.AA

import Lean4Axiomatic.Integer.Multiplication
import Lean4Axiomatic.ClassicalAlgebra.Group

/-!
# Integer negation
-/

namespace Lean4Axiomatic.Integer

/-!
## Axioms
-/

/--
Definition of negation, and properties that it must satisfy.

All other properties of negation can be derived from these.
-/
class Negation
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ]
    :=
  /-- Definition of and syntax for negation. -/
  negOp : Neg ℤ

  /--
  Negation preserves equality of integers; two equal integers are still equal
  after both are negated.
  -/
  neg_substitutive : AA.Substitutive₁ (α := ℤ) (-·) (· ≃ ·) (· ≃ ·)

  /-- An integer added to its negation is always zero. -/
  neg_inverse : AA.Inverse (α := ℤ) (-·) (· + ·)

attribute [instance] Negation.negOp
attribute [instance] Negation.neg_inverse
attribute [instance] Negation.neg_substitutive

export Negation (negOp)

/-!
## Derived properties
-/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core (ℕ := ℕ) ℤ]
variable [Addition ℤ] [Multiplication ℤ] [Negation ℤ]

open Coe (coe)
open Natural (step)
open Signed (Positive)

/--
The integer negative one (`-1`) is not equivalent to zero.

**Proof intuition**: Assume that it is; add one to both sides, obtaining
`0 ≃ 1`. Contradict with `0 ≄ 1` to prove the negation.
-/
theorem neg_one_neqv_zero : -1 ≄ (0:ℤ) := by
  intro (_ : -1 ≃ (0:ℤ))
  show False
  have : 1 ≃ (0:ℤ) := calc
    1      ≃ _ := Rel.symm AA.identR
    1 + 0  ≃ _ := AA.substR (Rel.symm ‹-1 ≃ (0:ℤ)›)
    1 + -1 ≃ _ := AA.inverseR
    0      ≃ _ := Rel.refl
  have : (1:ℤ) ≄ 0 := one_neqv_zero
  exact absurd ‹1 ≃ (0:ℤ)› ‹1 ≄ (0:ℤ)›

/--
The integer negative one (`-1`) is not equivalent to one.

**Proof intuition**: Assume that it is; add one to both sides, obtaining
`0 ≃ 2`. Convert into natural numbers, `coe 0 ≃ coe 2`, then contradict with
the axiom `step n ≄ 0` to prove the negation.
-/
theorem neg_one_neqv_one : -1 ≄ (1 : ℤ) := by
  intro (_ : -1 ≃ (1 : ℤ))
  show False
  have : step 0 ≃ 1 := Rel.symm Natural.literal_step
  have : (step 1 : ℤ) ≃ (0 : ℤ) := calc
    (step 1 : ℤ)           ≃ _ := AA.subst₁ (AA.subst₁ (Rel.symm AA.identR))
    (step (1 + 0) : ℤ)     ≃ _ := AA.subst₁ AA.scompatR
    ((1 + step 0 : ℕ) : ℤ) ≃ _ := AA.subst₁ (AA.substR ‹step 0 ≃ 1›)
    ((1 + 1 : ℕ) : ℤ)      ≃ _ := AA.compat₂
    (1 : ℤ) + (1 : ℤ)      ≃ _ := AA.substR (Rel.symm ‹-1 ≃ (1 : ℤ)›)
    1 + -1                 ≃ _ := AA.inverseR
    0                      ≃ _ := Rel.refl
  have : step 1 ≃ 0 := AA.inject ‹((step 1 : ℕ) : ℤ) ≃ ((0 : ℕ) : ℤ)›
  have : step 1 ≄ 0 := Natural.step_neqv_zero
  exact absurd ‹step 1 ≃ 0› ‹step 1 ≄ 0›

/--
None of the three sign values `0`, `1`, and `-1` are equivalent to each other.

This extremely obvious property is useful as a lemma when proving trichotomy of
the `sgn` function or of the ordering relations.
-/
theorem signs_distinct {a : ℤ} : ¬ AA.TwoOfThree (a ≃ 0) (a ≃ 1) (a ≃ -1) := by
  intro (two : AA.TwoOfThree (a ≃ 0) (a ≃ 1) (a ≃ -1))
  show False
  match two with
  | AA.TwoOfThree.oneAndTwo (_ : a ≃ 0) (_ : a ≃ 1) =>
    exact Rel.trans_failR ‹a ≃ 1› one_neqv_zero ‹a ≃ 0›
  | AA.TwoOfThree.oneAndThree (_ : a ≃ 0) (_ : a ≃ -1) =>
    exact Rel.trans_failR ‹a ≃ -1› neg_one_neqv_zero ‹a ≃ 0›
  | AA.TwoOfThree.twoAndThree (_ : a ≃ 1) (_ : a ≃ -1) =>
    exact Rel.trans_failR ‹a ≃ -1› neg_one_neqv_one ‹a ≃ 1›

/--
Non-typeclass version of `neg_inverse.inverseL`.

Eventually, this should become the axiom and the typeclass should be derived.
-/
theorem neg_invL {a : ℤ} : -a + a ≃ 0 := AA.inverseL

/--
Zero is a left absorbing element for multiplication.

**Property intuition**: A sum of zero terms should produce the empty sum, i.e.
the additive identity, which is zero.

**Proof intuition**: The only way to produce zero by itself, given the
properties of integer addition and multiplication, is by adding a value to its
negation. So we somehow need to obtain `0 * a + -(0 * a)` from `0 * a`. We can
easily get `0 * a + (0 * a + -(0 * a))` from the additive identity and inverse
properties. The key is then using associativity, distributivity, and again
additive identity to merge the two instances of `0 * a` into one.
-/
def mul_absorbL {a : ℤ} : 0 * a ≃ 0 := calc
  0 * a                      ≃ _ := Rel.symm AA.identR
  0 * a + 0                  ≃ _ := AA.substR (Rel.symm AA.inverseR)
  0 * a + (0 * a + -(0 * a)) ≃ _ := Rel.symm AA.assoc
  (0 * a + 0 * a) + -(0 * a) ≃ _ := AA.substL (Rel.symm AA.distribR)
  (0 + 0) * a + -(0 * a)     ≃ _ := AA.substL (AA.substL AA.identL)
  0 * a + -(0 * a)           ≃ _ := AA.inverseR
  (0 : ℤ)                    ≃ _ := Rel.refl

def mul_absorbingL : AA.AbsorbingOn Hand.L (α := ℤ) 0 (· * ·) := {
  absorb := mul_absorbL
}

instance mul_absorbing : AA.Absorbing (α := ℤ) 0 (· * ·) := {
  absorbingL := mul_absorbingL
  absorbingR := AA.absorbingR_from_absorbingL mul_absorbingL
}

/--
Negation is left-semicompatible with multiplication.

**Property intuition**: Negating the sum of `b` copies of `a` should be the
same as the sum of `b` copies of `-a`.

**Proof intuition**: We're showing how negation and multiplication interact, so
there's no preexisting property that tells us how to manipulate `-(a * b)`. The
next best thing is to try to introduce some new terms, one of which is our
desired result `(-a) * b`, but the other is `a * b` to cancel out `-(a * b)`.
And it turns out those new terms have a factor of `b` in common, so we can
produce them using distributivity and the additive inverse property.
-/
theorem neg_scompatL_mul {a b : ℤ} : -(a * b) ≃ (-a) * b := calc
  -(a * b)
    ≃ _ := Rel.symm AA.identL
  0 + -(a * b)
    ≃ _ := AA.substL (Rel.symm AA.absorbL)
  0 * b + -(a * b)
    ≃ _ := AA.substL (AA.substL (Rel.symm AA.inverseL))
  (-a + a) * b + -(a * b)
    ≃ _ := AA.substL AA.distribR
  (-a * b + a * b) + -(a * b)
    ≃ _ := AA.assoc
  (-a) * b + (a * b + -(a * b))
    ≃ _ := AA.substR AA.inverseR
  (-a) * b + 0
    ≃ _ := AA.identR
  (-a) * b
    ≃ _ := Rel.refl

def neg_semicompatibleL_mul
    : AA.SemicompatibleOn Hand.L (α := ℤ) (-·) (· * ·)
    := {
  scompat := neg_scompatL_mul
}

instance neg_semicompatible_mul
    : AA.Semicompatible (α := ℤ) (-·) (· * ·)
    := {
  semicompatibleL :=
    neg_semicompatibleL_mul
  semicompatibleR :=
    AA.semicompatibleR_from_semicompatibleL neg_semicompatibleL_mul
}

/--
Multiplication by negative one is equivalent to negation.

**Property and proof intuition**: Separating `-1` into its sign and its
magnitude, multiplying by the magnitude (`1`) leaves the result unchanged, and
multiplying with the sign (`-`) means the result is negated.
-/
theorem mul_neg_one {a : ℤ} : -1 * a ≃ -a := calc
  -1 * a     ≃ _ := Rel.symm AA.scompatL
  (-(1 * a)) ≃ _ := AA.subst₁ AA.identL
  (-a)       ≃ _ := Rel.refl

/--
Negation is an involution: applying it twice is equivalent to not applying it
at all.

**Property intuition**: Negation transforms an integer into its "mirror image"
reflection across zero. Reflecting twice gives back the original integer.

**Proof intuition**: The value `-a` is the additive inverse of `-(-a)` and also
`a`. Thus, it can be used as an intermediate to replace one with the other.
-/
theorem neg_involutive {a : ℤ} : -(-a) ≃ a := calc
  -(-a)            ≃ _ := Rel.symm AA.identL
  0 + -(-a)        ≃ _ := AA.substL (Rel.symm AA.inverseR)
  (a + -a) + -(-a) ≃ _ := AA.assoc
  a + (-a + -(-a)) ≃ _ := AA.substR AA.inverseR
  a + 0            ≃ _ := AA.identR
  a                ≃ _ := Rel.refl

/--
Negation is an injection: it sends distinct inputs to distinct outputs.

**Property intuition**: We expect this to be true because negation doesn't
change the magnitude of an integer, just its sign.

**Proof intuition**: Invoke involution to rewrite the integers in a form that
allows the assumption `-a₁ ≃ -a₂` to be used.
-/
theorem neg_inject {a₁ a₂ : ℤ} : -a₁ ≃ -a₂ → a₁ ≃ a₂ := by
  intro (_ : -a₁ ≃ -a₂)
  show a₁ ≃ a₂
  calc
    a₁       ≃ _ := Rel.symm neg_involutive
    (-(-a₁)) ≃ _ := AA.subst₁ ‹-a₁ ≃ -a₂›
    (-(-a₂)) ≃ _ := neg_involutive
    a₂       ≃ _ := Rel.refl

instance neg_injective : AA.Injective (α := ℤ) (-·) (· ≃ ·) (· ≃ ·) := {
  inject := neg_inject
}

/--
Negation is compatible with addition; i.e., it distributes over addition.

**Property intuition**: Visualizing integers as vectors, the theorem says that
adding vectors and then reflecting the result across zero is the same as
reflecting the vectors before adding them.

**Proof intuition**: Negation is the same as multiplication by -1. The result
follows from the distributive property.
-/
theorem neg_compat_add {a b : ℤ} : -(a + b) ≃ -a + -b := calc
  -(a + b)            ≃ _ := Rel.symm mul_neg_one
  (-1) * (a + b)      ≃ _ := AA.distribL
  (-1) * a + (-1) * b ≃ _ := AA.substL mul_neg_one
  (-a) + (-1) * b     ≃ _ := AA.substR mul_neg_one
  (-a) + -b           ≃ _ := Rel.refl

/--
Remove a common left operand of addition from both sides of an equivalence.

**Property and proof intuition**: Add the operand's additive inverse to both
sides, and simplify.
-/
theorem add_cancelL {a b₁ b₂ : ℤ} : a + b₁ ≃ a + b₂ → b₁ ≃ b₂ := by
  intro (_ : a + b₁ ≃ a + b₂)
  show b₁ ≃ b₂
  have reduce {x y : ℤ} : -x + (x + y) ≃ y := calc
    _ = -x + (x + y) := rfl
    _ ≃ (-x + x) + y := Rel.symm AA.assoc
    _ ≃ 0 + y        := AA.substL AA.inverseL
    _ ≃ y            := AA.identL
  calc
    _ = b₁            := rfl
    _ ≃ -a + (a + b₁) := Rel.symm reduce
    _ ≃ -a + (a + b₂) := AA.substR ‹a + b₁ ≃ a + b₂›
    _ ≃ b₂            := reduce

/--
Remove a common right operand of addition from both sides of an equivalence.

**Property and proof intuition**: Follows from left cancellation due to
addition's commutativity.
-/
theorem add_cancelR {a₁ a₂ b : ℤ} : a₁ + b ≃ a₂ + b → a₁ ≃ a₂ := by
  intro (_ : a₁ + b ≃ a₂ + b)
  show a₁ ≃ a₂
  have : b + a₁ ≃ b + a₂ := calc
    _ = b + a₁ := rfl
    _ ≃ a₁ + b := AA.comm
    _ ≃ a₂ + b := ‹a₁ + b ≃ a₂ + b›
    _ ≃ b + a₂ := AA.comm
  have : a₁ ≃ a₂ := add_cancelL ‹b + a₁ ≃ b + a₂›
  exact this

/--
Add or remove a left operand to addition on both sides of an equivalence.

Useful when working with chains of `· ↔ ·` relations.

**Property and proof intuition**: Combines left substitution and left
cancellation of addition.
-/
theorem add_bijectL {a b₁ b₂ : ℤ} : b₁ ≃ b₂ ↔ a + b₁ ≃ a + b₂ :=
  Iff.intro AA.substR add_cancelL

/--
Add or remove a right operand to addition on both sides of an equivalence.

Useful when working with chains of `· ↔ ·` relations.

**Property and proof intuition**: Combines right substitution and right
cancellation of addition.
-/
theorem add_bijectR {a₁ a₂ b : ℤ} : a₁ ≃ a₂ ↔ a₁ + b ≃ a₂ + b :=
  Iff.intro AA.substL add_cancelR

/-
Example showing that integers with addition form a Group.
-/
local instance add_group_ops : CA.Group.Ops ℤ := {
  --inverse := (-·)
  inverse := λ x => -x
}

def add_group_props : CA.Group.Props (α := ℤ)
  (binop := (· + ·)) (ident := 0) :=
{
  substL := AA.substL
  substR := AA.substR
  assoc := AA.assoc
  identL := AA.identL
  identR := AA.identR
  inverseL := λ _ => AA.inverseL
  inverseR := λ _ => AA.inverseR
}

end Lean4Axiomatic.Integer

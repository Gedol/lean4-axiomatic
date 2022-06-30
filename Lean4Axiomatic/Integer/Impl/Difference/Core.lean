import Lean4Axiomatic.Integer
import Lean4Axiomatic.Natural

namespace Lean4Axiomatic.Integer.Impl

/-! ## Implementation of fundamental definitions and properties of integers -/

/-! ### Formal difference representation of integers -/

/--
The formal (as in "having the form of") difference between two values of the
same type.

The field names suggest an interpretation for this structure of a starting
value (`init`) that has a quantity (`take`) removed from it. The structure then
denotes the value of the result.

Equivalently, this structure can be viewed as measuring the "directed gap"
between the two values. Specifically, it denotes the value that, when combined
with `take`, gives the result `init`.

Given a type of natural numbers `ℕ`, integers can be defined as values of
`Difference ℕ` under an equivalence relation that considers two differences to
be equal when they denote the same value according to an interpretation above.
-/
structure Difference (α : Type) : Type :=
  init : α
  take : α

infixl:90 "——" => Difference.mk

namespace Difference

/--
Create a `Difference` from an ordered pair of values.

**Named parameters**
- `α`: The type of both elements of the ordered pair.
-/
def from_prod {α : Type} : α × α → Difference α
| (x, y) => x——y

variable {ℕ : Type}
variable [Natural ℕ]

/-! ### Equivalence -/

/--
The equivalence relation that separates all `Difference ℕ` values into buckets
denoting integers.

In other words, given two differences `d₁` and `d₂`, they represent the same
integer if and only if `eqv d₁ d₂` holds.

**Definition intuition**: Equating two differences means that they represent
the same quantity after subtraction; i.e., after their `take` values have been
removed from their `init` values. The subtracted values can be removed from the
equation without changing its correctness by adding each of them to both sides.
Doing that produces the expression that is the definition of this relation.
-/
def eqv : Difference ℕ → Difference ℕ → Prop
| a——b, c——d => a + d ≃ c + b

-- This is an instance so the operator can be used in the rest of the file
instance tildeDash : Operators.TildeDash (Difference ℕ) := {
  tildeDash := eqv
}

/--
The equivalence relation on differences is reflexive.

**Proof intuition**: The underlying equality in the equivalence relation is
symmetric in terms of the two differences; when both differences are the same,
the equality is trivial.
-/
theorem refl {a : Difference ℕ} : a ≃ a := by
  revert a; intro (a₁——a₂)
  show a₁ + a₂ ≃ a₁ + a₂
  exact Rel.refl

/--
The equivalence relation on differences is symmetric.

**Proof intuition**: The underlying equality in the equivalence relation is
already symmetric in terms of the two differences.
-/
theorem symm {a b : Difference ℕ} : a ≃ b → b ≃ a := by
  revert a; intro (a₁——a₂); revert b; intro (b₁——b₂)
  intro (_ : a₁ + b₂ ≃ b₁ + a₂)
  show b₁ + a₂ ≃ a₁ + b₂
  exact Rel.symm ‹a₁ + b₂ ≃ b₁ + a₂›

/--
The equivalence relation on differences is transitive.

**Proof intuition**: Add the underlying equalities of the two hypotheses; this
nearly produces the goal equality, but both sides have an extra `b₂ + b₁`. Use
the cancellation property of natural number addition to remove it.

The bulk of the proof is just the algebra needed to prepare for cancellation.
-/
theorem trans {a b c : Difference ℕ} : a ≃ b → b ≃ c → a ≃ c := by
  revert a; intro (a₁——a₂); revert b; intro (b₁——b₂); revert c; intro (c₁——c₂)
  intro (_ : a₁ + b₂ ≃ b₁ + a₂) (_ : b₁ + c₂ ≃ c₁ + b₂)
  show a₁ + c₂ ≃ c₁ + a₂
  have : (a₁ + c₂) + (b₂ + b₁) ≃ (c₁ + a₂) + (b₂ + b₁) := calc
    (a₁ + c₂) + (b₂ + b₁) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (a₁ + b₂) + (c₂ + b₁) ≃ _ := AA.substL ‹a₁ + b₂ ≃ b₁ + a₂›
    (b₁ + a₂) + (c₂ + b₁) ≃ _ := AA.substL AA.comm
    (a₂ + b₁) + (c₂ + b₁) ≃ _ := AA.substR AA.comm
    (a₂ + b₁) + (b₁ + c₂) ≃ _ := AA.substR ‹b₁ + c₂ ≃ c₁ + b₂›
    (a₂ + b₁) + (c₁ + b₂) ≃ _ := AA.comm
    (c₁ + b₂) + (a₂ + b₁) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (c₁ + a₂) + (b₂ + b₁) ≃ _ := Rel.refl
  exact AA.cancelR ‹(a₁ + c₂) + (b₂ + b₁) ≃ (c₁ + a₂) + (b₂ + b₁)›

instance eqvOp : Relation.Equivalence.EqvOp (Difference ℕ) := {
  toTildeDash := tildeDash
  refl := refl
  symm := symm
  trans := trans
}

/--
Conversion of ordered pairs into `Difference`s preserves equivalence.

**Proof intuition**: Equivalence of ordered pairs is stricter than equivalence
of differences. For ordered pairs, both the left and right elements must be
equivalent; for differences, any values representing the same gap are
equivalent. Thus one only needs to show that the former is strong enough to
imply the latter.
-/
instance from_prod_substitutive
    : AA.Substitutive₁ (α := ℕ × ℕ) from_prod (· ≃ ·) (· ≃ ·)
    := by
  apply AA.Substitutive₁.mk
  intro p q; revert p; intro ((n, m)); revert q; intro ((k, j))
  intro (_ : (n, m) ≃ (k, j))
  show from_prod (n, m) ≃ from_prod (k, j)
  show n——m ≃ k——j
  show n + j ≃ k + m
  have (And.intro (_ : n ≃ k) (_ : m ≃ j)) :=
    Relation.Equivalence.Impl.Prod.eqv_defn.mp ‹(n, m) ≃ (k, j)›
  calc
    n + j ≃ _ := AA.substL ‹n ≃ k›
    k + j ≃ _ := AA.substR (Rel.symm ‹m ≃ j›)
    k + m ≃ _ := Rel.refl

instance equality : Equality (Difference ℕ) := {
  eqvOp := eqvOp
}

/-! ### Conversion -/

/--
Every natural number can be represented as a difference.

Frequently used to convert natural number literals into differences, so it's
defined as an `abbrev` so the typechecker will always expand it.

**Definition intuition**: Taking nothing away from a natural number preserves
its value.
-/
abbrev from_natural : Coe ℕ (Difference ℕ) := {
  coe := (·——0)
}

instance conversion : Conversion ℕ (Difference ℕ) := {
  from_natural := from_natural
}

end Difference

end Lean4Axiomatic.Integer.Impl
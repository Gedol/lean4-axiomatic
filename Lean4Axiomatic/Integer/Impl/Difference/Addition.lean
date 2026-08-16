import Lean4Axiomatic.Integer.Impl.Difference.Core

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Addition of formal differences -/

variable {ℕ : Type} [Natural ℕ]

/--
Addition of differences.

**Definition intuition**: the sum of two differences should be the net effect
of applying both of them.
-/
def add : Difference ℕ → Difference ℕ → Difference ℕ
| a——b, c——d => (a + c)——(b + d)

instance addOp : Add (Difference ℕ) := {
  add := add
}

/--
Addition of natural number differences is commutative.

**Proof intuition**: Expand definitions to see that we need to show the
equivalence of two differences of natural number sums. The left and right
elements of the differences are directly equivalent via commutativity of
natural number addition, so convert the differences into ordered pairs and use
commutativity element-wise.
-/
theorem add_comm {a b : Difference ℕ} : a + b ≃ b + a := by
  revert a; intro (n——m); let a := n——m; revert b; intro (k——j); let b := k——j
  show a + b ≃ b + a
  calc
    _ = a + b            := rfl
    _ = n——m + k——j      := rfl
    _ = (n + k)——(m + j) := rfl
    _ ≃ (k + n)——(j + m) := by srw [Natural.add_comm, Natural.add_comm]
    _ = k——j + n——m      := rfl
    _ = b + a            := rfl

instance add_commutative : AA.Commutative (α := Difference ℕ) (· + ·) := {
  comm := add_comm
}

/--
Adding the same difference on the right of two equivalent differences preserves
their equivalence.

**Proof intuition**: The property is already intuitively true; imagine
extending two line segments of the same length by the same amount. So the proof
just expands all definitions into equalities of sums of natural numbers, and
performs algebra to obtain the desired result.
-/
@[gcongr]
theorem add_substL {a₁ a₂ b : Difference ℕ} : a₁ ≃ a₂ → a₁ + b ≃ a₂ + b := by
  revert a₁; intro (n——m); let a₁ := n——m
  revert a₂; intro (k——j); let a₂ := k——j
  revert b; intro (p——q); let b := p——q
  intro (_ : a₁ ≃ a₂)
  show a₁ + b ≃ a₂ + b

  have : n——m ≃ k——j   := ‹a₁ ≃ a₂›
  have : n + j ≃ k + m := this
  have : (n + p) + (j + q) ≃ (k + p) + (m + q) := calc
    _ = (n + p) + (j + q) := rfl
    _ ≃ (n + j) + (p + q) := AA.expr_xxfxxff_lr_swap_rl (f := (· + ·))
    _ ≃ (k + m) + (p + q) := by srw [‹n + j ≃ k + m›]
    _ ≃ (k + p) + (m + q) := AA.expr_xxfxxff_lr_swap_rl (f := (· + ·))

  have diff_eqv : (n + p)——(m + q) ≃ (k + p)——(j + q) :=
    ‹(n + p) + (j + q) ≃ (k + p) + (m + q)›
  calc
    _ = a₁ + b           := rfl
    _ = n——m + p——q      := rfl
    _ = (n + p)——(m + q) := rfl
    _ ≃ (k + p)——(j + q) := diff_eqv
    _ = k——j + p——q      := rfl
    _ = a₂ + b           := rfl

/--
Adding the same difference on the left of two equivalent differences preserves
their equivalence.

**Proof intuition**: Use commutativity to substitute on the other side.
-/
@[gcongr]
theorem add_substR {a₁ a₂ b : Difference ℕ} : a₁ ≃ a₂ → b + a₁ ≃ b + a₂ := by
  intro (_ : a₁ ≃ a₂)
  show b + a₁ ≃ b + a₂
  calc
    _ = b + a₁ := rfl
    _ ≃ a₁ + b := add_comm
    _ ≃ a₂ + b := by srw [‹a₁ ≃ a₂›]
    _ ≃ b + a₂ := add_comm

instance add_substitutive
    : AA.Substitutive₂ (α := Difference ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => add_substL }
  substitutiveR := { subst₂ := λ (_ : True) => add_substR }
}

/--
Addition of natural number differences is associative.

**Proof intuition**: Expand definitions to see that we need to show the
equivalence of two differences of natural number sums. The left and right
elements of the differences are directly equivalent via associativity of
natural number addition.
-/
def add_assoc {a b c : Difference ℕ} : (a + b) + c ≃ a + (b + c) := by
  revert a; intro (n——m); let a := n——m
  revert b; intro (k——j); let b := k——j
  revert c; intro (p——q); let c := p——q
  show (a + b) + c ≃ a + (b + c)
  calc
    _ = (a + b) + c                  := rfl
    _ = (n——m + k——j) + p——q         := rfl
    _ = (n + k)——(m + j) + p——q      := rfl
    _ = ((n + k) + p)——((m + j) + q) := rfl
    _ ≃ (n + (k + p))——((m + j) + q) := by srw [Natural.add_assoc]
    _ ≃ (n + (k + p))——(m + (j + q)) := by srw [Natural.add_assoc]
    _ = n——m + (k + p)——(j + q)      := rfl
    _ = n——m + (k——j + p——q)         := rfl
    _ = a + (b + c)                  := rfl

@[implicit_reducible]
def add_associative : AA.Associative (α := Difference ℕ) (· + ·) := {
  assoc := add_assoc
}

/--
The natural number difference `0` is a left additive identity element.

**Property intuition**: Adding nothing to a value should leave it unchanged.

**Proof intuition**: Both components of the literal `0` are also `0`, so we can
use the additive identity property on natural numbers elementwise.
-/
theorem add_identL {a : Difference ℕ} : 0 + a ≃ a := by
  revert a; intro (n——m); let a := n——m
  show 0 + a ≃ a
  calc
    _ = 0 + a            := rfl
    _ = 0——0 + n——m      := rfl
    _ = (0 + n)——(0 + m) := rfl
    _ ≃ n——m             := by srw [Natural.zero_add, Natural.zero_add]
    _ = a                := rfl

@[implicit_reducible]
def add_identityL : AA.IdentityOn Hand.L (α := Difference ℕ) 0 (· + ·) := {
  ident := add_identL
}

instance add_identity : AA.Identity (α := Difference ℕ) 0 (· + ·) := {
  identityL := add_identityL
  identityR := AA.identityR_from_identityL add_identityL
}

/--
Conversion from `ℕ` to `Difference ℕ` is compatible with addition.

**Proprty intuition**: One would hope this is true, otherwise we could not say
that the set of differences (integers) is a superset of the natural numbers.

**Proof intuition**: Expanding definitions is enough to get us nearly there --
just need to clean up an extra zero.
-/
theorem add_compat_natural
    {n m : ℕ} : ((n + m : ℕ):Difference ℕ) ≃ (n:Difference ℕ) + (m:Difference ℕ)
    := by
  calc
    _ = ((n + m : ℕ): Difference ℕ)         := rfl
    _ = (n + m)——0                          := rfl
    _ ≃ (n + m)——(0 + 0)                    := by srw [←Natural.add_zero]
    _ = n——0 + m——0                         := rfl
    _ = (n:Difference ℕ) + (m:Difference ℕ) := rfl

@[implicit_reducible]
def add_compatible_from_natural
    : AA.Compatible₂ (α := ℕ) (β := Difference ℕ) (↑·) (· + ·) (· + ·)
    := {
  compat₂ := add_compat_natural
}

instance addition : Addition (ℕ := ℕ) (Difference ℕ) := {
  addOp := addOp
  add_substitutive := add_substitutive
  add_commutative := add_commutative
  add_associative := add_associative
  add_identity := add_identity
  add_compatible_from_natural := add_compatible_from_natural
}

end Lean4Axiomatic.Integer.Impl.Difference

import Lean4Axiomatic.Integer

/-! # Rational numbers: fundamental definitions and properties -/

namespace Lean4Axiomatic.Rational

open Logic (AP)

/-- Operations pertaining to rational number equivalence. -/
class Equivalence.Ops (ℚ : Type) where
  /-- Equivalence relation; holds if the inputs have the same numeric value. -/
  eqv : ℚ → ℚ → Prop

export Equivalence.Ops (eqv)

/-- Enables the use of the `· ≃ ·` operator for equivalence. -/
instance eqv_tilde_dash_inst
    {ℚ : Type} [Equivalence.Ops ℚ] : Operators.TildeDash ℚ
    := {
  tildeDash := eqv
}

/-- Properties of rational number equivalence. -/
class Equivalence.Props (ℚ : Type) [Ops ℚ] where
  /-- Equivalence is reflexive. -/
  eqv_refl {p : ℚ} : p ≃ p

  /-- Equivalence is symmetric. -/
  eqv_symm {p q : ℚ} : p ≃ q → q ≃ p

  /-- Equivalence is transitive. -/
  eqv_trans {p q r : ℚ} : p ≃ q → q ≃ r → p ≃ r

export Equivalence.Props (eqv_refl eqv_symm eqv_trans)

/-- All rational number equivalence axioms. -/
class Equivalence (ℚ : Type) extends Equivalence.Ops ℚ, Equivalence.Props ℚ

/--
Rational number equivalence is an equivalence relation.

This enables it to be used in generic contexts; for example, as a relation in
`calc` expressions.
-/
instance eqv_op_inst
    {ℚ : Type} [Equivalence ℚ] : Relation.Equivalence.EqvOp ℚ
    := {
  refl := eqv_refl
  symm := eqv_symm
  trans := eqv_trans
}

/--
Operations pertaining to the conversion of rational numbers into and out of
other types.
-/
class Conversion.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] (ℚ : Type)
    where
  /-- Converts an integer into its equivalent rational number value. -/
  from_integer : ℤ → ℚ

export Conversion.Ops (from_integer)

/-- Enables the use of implicit coercions from integers to rationals. -/
instance coe_from_integer_inst
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Conversion.Ops (ℤ := ℤ) ℚ] : Coe ℤ ℚ
    := {
  coe := from_integer
}

/-- Natural number literals can be converted into rational numbers. -/
instance of_nat_inst
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Conversion.Ops (ℤ := ℤ) ℚ] {n : Nat} : OfNat ℚ n
    := {
  ofNat := ((OfNat.ofNat n : ℤ) : ℚ)
}

/-- Properties of rational number conversion. -/
class Conversion.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Equivalence.Ops ℚ] [Ops (ℤ := ℤ) ℚ]
    where
  /-- Equivalent integers are converted to equivalent rationals. -/
  from_integer_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → (a₁ : ℚ) ≃ (a₂ : ℚ)

  /-- Equivalent converted rationals came from the same integer. -/
  from_integer_inject {a₁ a₂ : ℤ} : (a₁ : ℚ) ≃ (a₂ : ℚ) → a₁ ≃ a₂

attribute [gcongr] Conversion.Props.from_integer_subst

export Conversion.Props (from_integer_inject from_integer_subst)

/-- All rational number conversion axioms. -/
class Conversion
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Equivalence.Ops ℚ]
    where
  toOps : Conversion.Ops (ℤ := ℤ) ℚ
  toProps : Conversion.Props ℚ

attribute [implicit_reducible, instance] Conversion.toOps
attribute [instance] Conversion.toProps

/-- All fundamental rational number axioms. -/
class Core
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] (ℚ : Type)
    where
  toEquivalence : Equivalence ℚ
  toConversion : Conversion (ℤ := ℤ) ℚ

attribute [implicit_reducible, instance] Core.toConversion
attribute [implicit_reducible, instance] Core.toEquivalence

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type} [Core (ℤ := ℤ) ℚ]

/--
Allows the integer-to-rational conversion syntax `((·:ℤ):ℚ)` to be used in
places that require a nonzero value, such as under a division operator, as long
as the underlying integer value is also nonzero.
-/
instance from_integer_preserves_neqv_zero_inst
    {a : ℤ} [AP (a ≄ 0)] : AP ((a:ℚ) ≄ 0)
    :=
  ‹AP (a ≄ 0)›.map (mt from_integer_inject)

/--
If `Integer.Nonzero` holds for an integer, then `· ≄ 0` holds for its rational
equivalent.
-/
theorem from_integer_preserves_nonzero
    {a : ℤ} : Integer.Nonzero a → (a:ℚ) ≄ 0
    := by
  intro (_ : Integer.Nonzero a)
  show (a:ℚ) ≄ 0
  have : a ≄ 0 := Integer.nonzero_iff_neqv_zero.mp ‹Integer.Nonzero a›
  have : (a:ℚ) ≄ 0 := mt from_integer_inject ‹a ≄ 0›
  exact this

/-- Make `from_integer_preserves_nonzero` available for instance search. -/
instance from_integer_preserves_nonzero_inst
    {a : ℤ} [Integer.Nonzero a] : AP ((a:ℚ) ≄ 0)
    :=
  AP.mk (from_integer_preserves_nonzero ‹Integer.Nonzero a›)

/-- One and zero are distinct rational numbers. -/
theorem nonzero_one : (1:ℚ) ≄ 0 :=
  mt from_integer_inject Integer.one_neqv_zero

/-- Two and zero are distinct rational numbers. -/
theorem nonzero_two : (2:ℚ) ≄ 0 :=
  mt from_integer_inject Integer.two_neqv_zero

/-!
### Instances for `OfNat` literals

Lean's instance search appears to distinguish between `OfNat` expressions with
literal values (e.g. `(3:ℚ)`) and `OfNat` expressions with variables (e.g.
`(n:ℚ)`, where `n : Nat`). This makes it impossible to write an instance
parameterized over some `n : Nat` that works for expressions like `(3:ℚ)`.

I haven't uncovered the root cause for this, but I suspect it has something to
do with how the syntax for `Nat` literals interacts with the `OfNat` syntax.
Assuming the expression `(n:ℚ)` is expanded to `(OfNat.ofNat n : ℚ)`, then the
expression `(3:ℚ)` should be expanded to `(OfNat.ofNat 3 : ℚ)` as well. But
that has a bare literal value, which is likely expanded again to
`(OfNat.ofNat (nat_lit 3) : Nat)`. And because `nat_lit` is a macro, it only
accepts syntax representing literals, so there's no way to write a theorem with
a variable `n : Nat` that has a subexpression `nat_lit n`.

The workaround is to declare an instance for each literal natural number that
we need one for. Even a macro-based solution would amount to the same thing,
just with less boilerplate.
-/

instance nonzero_one_inst : AP ((1:ℚ) ≄ 0) := AP.mk nonzero_one
instance nonzero_two_inst : AP ((2:ℚ) ≄ 0) := AP.mk nonzero_two

end Lean4Axiomatic.Rational

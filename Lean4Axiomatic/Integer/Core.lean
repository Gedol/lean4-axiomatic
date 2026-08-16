import Lean4Axiomatic.Natural
import Lean4Axiomatic.Relation.Equivalence

/-! # Fundamental definitions and properties of integers -/

namespace Lean4Axiomatic.Integer

open Coe (coe)
open Logic (AP)

/-! ## Axioms -/

/--
Definitions pertaining to equivalence of integer values.

**Named parameters**
- `ℤ`: The integers.
-/
class Equivalence (ℤ : Type) where
  /--
  The standard equivalence relation on integers, expressed with the syntax
  `a ≃ b`.
  -/
  eqvOp : Relation.Equivalence.EqvOp ℤ

attribute [implicit_reducible, instance] Equivalence.eqvOp

export Equivalence (eqvOp)

/--
Definitions pertaining to conversion of other types into or out of integers.

**Named parameters**
- `ℕ`: The natural numbers.
- `ℤ`: The integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
- All other class parameters provide the subset of integer properties necessary
  to define the fields of this class.
-/
class Conversion {ℕ : Type} [Natural ℕ] (ℤ : Type) [Equivalence ℤ] where
  /-- Every natural number has an integer representation. -/
  from_natural : Coe ℕ ℤ

  /-- Every natural number maps to a unique integer. -/
  from_natural_subst {n₁ n₂ : ℕ} : n₁ ≃ n₂ → (n₁:ℤ) ≃ (n₂:ℤ)

  /-- Every integer representation comes from a unique natural number. -/
  from_natural_injective : AA.Injective (α := ℕ) (β := ℤ) coe (· ≃ ·) (· ≃ ·)

export Conversion (from_natural_subst)

attribute [gcongr] from_natural_subst
attribute [implicit_reducible, instance] Conversion.from_natural
attribute [instance] Conversion.from_natural_injective

instance from_natural_substitutive
    {ℕ ℤ : Type} [Natural ℕ] [Equivalence ℤ] [Conversion (ℕ := ℕ) ℤ]
    : AA.Substitutive₁ (α := ℕ) (β := ℤ) coe (· ≃ ·) (· ≃ ·)
    := {
  subst₁ := from_natural_subst
}

/--
Bundles all core integer classes into one, to reduce the number of core
dependencies needed by other integer classes.

**Named parameters**
- `ℕ`: The natural numbers.
- `ℤ`: The integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
-/
class Core {ℕ : outParam Type} [Natural ℕ] (ℤ : Type)
  extends Equivalence ℤ, Conversion (ℕ := ℕ) ℤ

/-! ## Derived properties -/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core (ℕ := ℕ) ℤ]

/--
Provides a single definition of integer literals, for convenience.

To resolve situations with ambiguous literals, it's a default instance with a
higher priority than `Natural`'s default `OfNat` instance.
-/
@[default_instance low+2]
instance literal {n : Nat} : OfNat ℤ n := {
  ofNat := coe (OfNat.ofNat n : ℕ)
}

/-- The integer one is not the same as the integer zero. -/
theorem one_neqv_zero : (1 : ℤ) ≄ 0 :=
  mt Conversion.from_natural_injective.inject Natural.one_neqv_zero

instance one_neqv_zero_inst : AP ((1:ℤ) ≄ 0) := AP.mk one_neqv_zero

/-- The integer two is not the same as the integer zero. -/
theorem two_neqv_zero : (2:ℤ) ≄ 0 :=
  mt Conversion.from_natural_injective.inject Natural.two_neqv_zero

instance two_neqv_zero_inst : AP ((2:ℤ) ≄ 0) := AP.mk two_neqv_zero

end Lean4Axiomatic.Integer

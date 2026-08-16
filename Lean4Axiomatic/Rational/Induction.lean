import Lean4Axiomatic.Function
import Lean4Axiomatic.Rational.Reciprocation

/-!
# Rational induction

See `Lean4Axiomatic.Integer.Induction` for a detailed explanation of the
concepts.
-/

namespace Lean4Axiomatic.Rational

open Function (IndexedFamily fsubst)
open Logic (AP)
open Relation.Equivalence (EqvOp)

/-! ## Axioms -/

/--
Provides "handler" functions for the structures traversed during induction.
-/
class Induction.Context
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] (motive : ℚ → Sort u) [IndexedFamily motive]
    where
  /-- Handler for a ratio of integers (this is the only one for rationals). -/
  on_ratio (a b : ℤ) [AP (b ≄ 0)] : motive (a / b)

  /-- The `on_ratio` handler respects equivalence of ratios. -/
  on_ratio_subst
    {a₁ b₁ a₂ b₂ : ℤ} [AP (b₁ ≄ 0)] [AP (b₂ ≄ 0)]
    (ratio_eqv : (a₁:ℚ) / b₁ ≃ a₂ / b₂)
    : fsubst ratio_eqv (on_ratio a₁ b₁) ≃ on_ratio a₂ b₂

/-- The fundamental induction operations on rational numbers. -/
@[univ_out_params]
class Induction.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ]
    where

  /--
  Induction principle for rational numbers: if a property holds for all ratios
  of two integers, then it holds for all rational numbers.
  -/
  ind_ratio
    {motive : ℚ → Sort u} [IndexedFamily motive] (ctx : Context motive) (p : ℚ)
    : motive p

/--
Convenience function that enables using `ctx.ind_ratio` instead of
`ind_ratio ctx`.
-/
def Induction.Context.ind_ratio
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Ops ℚ]
    {motive : ℚ → Sort u} [IndexedFamily motive]
    : (ctx : Context motive) → (p : ℚ) → motive p
    :=
  Ops.ind_ratio

/-- Properties of rational induction operations. -/
class Induction.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Ops ℚ]
    where
  /-- The computational behavior of rational number induction. -/
  ind_ratio_eval
    {motive : ℚ → Sort u} [IndexedFamily motive] (ctx : Context motive)
    {a b : ℤ} [AP (b ≄ 0)] : ctx.ind_ratio (a / b) ≃ ctx.on_ratio a b

  /-- Rational number induction respects equivalence. -/
  ind_ratio_subst
    {motive : ℚ → Sort u} [IndexedFamily motive] {ctx : Context motive}
    {p₁ p₂ : ℚ} {p_eqv : p₁ ≃ p₂}
    : fsubst ‹p₁ ≃ p₂› (ctx.ind_ratio p₁) ≃ ctx.ind_ratio p₂

/-- All rational number induction axioms. -/
class Induction.{u}
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ]
    where
  toOps : Induction.Ops.{u} ℚ
  toProps : Induction.Props ℚ

attribute [implicit_reducible, instance] Induction.toOps
attribute [instance] Induction.toProps

/-! ## Derived properties -/

variable
  {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Reciprocation ℚ] [Division ℚ] [Induction ℚ]

/-- Create a rational induction context for a `ℚ → Prop` motive. -/
@[implicit_reducible]
def ind_ctx_prop
    {motive : ℚ → Prop} [IndexedFamily motive]
    (on_ratio : (a b : ℤ) → [AP (b ≄ 0)] → motive (a / b))
    : Induction.Context motive
    := {
  on_ratio := on_ratio
  on_ratio_subst := λ _ => Rel.refl
}

/--
Create a rational induction context for a "constant" motive; i.e. a motive of
the form `ℚ → X` where `X` is a specific type (not a type family).
-/
@[implicit_reducible]
def ind_ctx_const
    {X : Sort u} [EqvOp X] {on_ratio : (a b : ℤ) → [AP (b ≄ 0)] → X}
    (on_ratio_subst :
      {a₁ b₁ a₂ b₂ : ℤ} → [AP (b₁ ≄ 0)] → [AP (b₂ ≄ 0)] →
      (a₁:ℚ) / b₁ ≃ a₂ / b₂ → on_ratio a₁ b₁ ≃ on_ratio a₂ b₂)
    : Induction.Context (λ (_ : ℚ) => X)
    := {
  on_ratio := on_ratio
  on_ratio_subst := on_ratio_subst
}

/--
Syntax sugar; enables `ctx.ind_ratio_eval` to be used instead of
`Rational.ind_ratio_eval ctx`.
-/
theorem Induction.Context.ind_ratio_eval
    {motive : ℚ → Sort u} [IndexedFamily motive]
    : (ctx : Context motive) → {a b : ℤ} → [AP (b ≄ 0)] →
      ctx.ind_ratio (a / b) ≃ ctx.on_ratio a b
    :=
  Induction.Props.ind_ratio_eval

/--
Syntax sugar; enables `ctx.ind_ratio_subst` to be used instead of
`Rational.ind_ratio_const ctx`.
-/
theorem Induction.Context.ind_ratio_subst
    {motive : ℚ → Sort u} [IndexedFamily motive] (ctx : Context motive)
    {p₁ p₂ : ℚ} (p_eqv : p₁ ≃ p₂)
    : fsubst ‹p₁ ≃ p₂› (ctx.ind_ratio p₁) ≃ ctx.ind_ratio p₂
    :=
  Induction.Props.ind_ratio_subst

/-- Recursion principle for rationals. -/
def Induction.Context.rec_ratio
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℚ) => X)) : ℚ → X
    :=
  ctx.ind_ratio

/-- The computational behavior of rational number recursion. -/
theorem Induction.Context.rec_ratio_eval
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℚ) => X))
    : {a b : ℤ} → [AP (b ≄ 0)] → ctx.rec_ratio (a / b) ≃ ctx.on_ratio a b
    :=
  ctx.ind_ratio_eval

/-- Rational number recursion respects equivalence. -/
theorem Induction.Context.rec_ratio_subst
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℚ) => X))
    : {p₁ p₂ : ℚ} → (p_eqv : p₁ ≃ p₂) → ctx.rec_ratio p₁ ≃ ctx.rec_ratio p₂
    :=
  ctx.ind_ratio_subst

/-- Express a rational number as a ratio of integers. -/
structure AsRatio (p : ℚ) where
  a : ℤ
  b : ℤ
  b_nonzero : AP (b ≄ 0)
  p_eqv : p ≃ a / b

/-- Given a rational number, generate the integer ratio it's equivalent to. -/
def as_ratio (p : ℚ) : AsRatio p := by
  let fam_eqv {x : ℚ} : EqvOp (AsRatio x) :=
    Relation.Equivalence.Impl.Mapped.eqvOp (λ _ => x)

  let fsubst {x₁ x₂ : ℚ} : x₁ ≃ x₂ → AsRatio x₁ → AsRatio x₂ := by
    intro (_ : x₁ ≃ x₂) (_ : AsRatio x₁)
    show AsRatio x₂
    have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) x₁_eqv) := ‹AsRatio x₁›
    have : x₁ ≃ a / b := x₁_eqv
    have : x₂ ≃ a / b := eqv_trans (eqv_symm ‹x₁ ≃ x₂›) ‹x₁ ≃ a / b›
    have : AsRatio x₂ := AsRatio.mk a b ‹AP (b ≄ 0)› ‹x₂ ≃ a / b›
    exact this

  have fsubst_refl {x : ℚ} {fx : AsRatio x} : fsubst Rel.refl fx ≃ fx :=
    Rel.refl

  have fsubst_trans
      {x y z : ℚ} {fx : AsRatio x} (xy : x ≃ y) (yz : y ≃ z)
      : fsubst ‹y ≃ z› (fsubst ‹x ≃ y› fx) ≃
        fsubst (Rel.trans ‹x ≃ y› ‹y ≃ z›) fx
      :=
    Rel.refl

  have fsubst_addrem
      {x y : ℚ} {fx₁ fx₂ : AsRatio x} (xy : x ≃ y)
      : fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂ ↔ fx₁ ≃ fx₂
      := by
    have : y ≃ y ↔ x ≃ x := Iff.intro (λ _ => Rel.refl) (λ _ => Rel.refl)
    calc
      _ ↔ fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂ := Iff.rfl
      _ ↔ y ≃ y                                   := Iff.rfl
      _ ↔ x ≃ x                                   := ‹y ≃ y ↔ x ≃ x›
      _ ↔ fx₁ ≃ fx₂                               := Iff.rfl
  have fsubst_substR
      {x y : ℚ} {fx₁ fx₂ : AsRatio x} (xy : x ≃ y)
      : fx₁ ≃ fx₂ → fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂
      :=
    (fsubst_addrem ‹x ≃ y›).mpr
  have fsubst_injectR
      {x y : ℚ} {fx₁ fx₂ : AsRatio x} (xy : x ≃ y)
      : fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂ → fx₁ ≃ fx₂
      :=
    (fsubst_addrem ‹x ≃ y›).mp

  let idx_fam : IndexedFamily AsRatio := {
    fam_eqv := fam_eqv
    fsubst := fsubst
    fsubst_refl := fsubst_refl
    _fsubst_trans := fsubst_trans
    _fsubst_substR := fsubst_substR
    _fsubst_injectR := fsubst_injectR
  }

  let on_ratio (a b : ℤ) [AP (b ≄ 0)] : AsRatio ((a:ℚ) / b) := {
    a := a
    b := b
    b_nonzero := ‹AP (b ≄ 0)›
    p_eqv := eqv_refl
  }
  have on_ratio_subst
      {a₁ b₁ a₂ b₂ : ℤ} [AP (b₁ ≄ 0)] [AP (b₂ ≄ 0)]
      (ratio_eqv : (a₁:ℚ) / b₁ ≃ a₂ / b₂)
      : fsubst ratio_eqv (on_ratio a₁ b₁) ≃ on_ratio a₂ b₂
      := by
    have : (a₂:ℚ) / b₂ ≃ (a₂:ℚ) / b₂ := Rel.refl
    have : fsubst ratio_eqv (on_ratio a₁ b₁) ≃ on_ratio a₂ b₂ := this
    exact this
  let ctx : Induction.Context AsRatio := {
    on_ratio := on_ratio
    on_ratio_subst := on_ratio_subst
  }

  have : AsRatio p := ctx.ind_ratio p
  exact this

end Lean4Axiomatic.Rational

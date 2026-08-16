import Lean4Axiomatic.Integer.Impl.Difference.Negation
import Lean4Axiomatic.Integer.Impl.Generic.Subtraction

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Induction/eliminators on formal differences -/

open scoped Integer.Impl.Generic
open Function (IndexedFamily fsubst fsubst_refl fsubst_substR fsubst_trans)
open Relation.Equivalence (EqvOp)

variable {ℕ : Type} [Natural ℕ]

/--
Subtraction and formal differences are equivalent.

**Property intuition**: Formal differences are a representation of subtraction,
so we should expect this to be true.

**Proof intuition**: Expand definitions and simplify.
-/
theorem sub_eqv_diff
    {n m : ℕ} : (n:Difference ℕ) - m ≃ n——m
    := calc
  _ = (n:Difference ℕ) - m := rfl
  _ = (n——0) - (m——0)      := rfl
  _ ≃ (n——0) + -(m——0)     := sub_defn
  _ = (n——0) + (0——m)      := rfl
  _ = (n + 0)——(0 + m)     := rfl
  _ ≃ n——m                 := by srw [Natural.add_zero, Natural.zero_add]

/--
Implementation of integer "difference" induction for formal differences.

**Property intuition**: The only way to obtain values of `motive a`, where `a`
is a formal difference, is via the `on_diff` function provided by the induction
context. And `on_diff` takes two natural number arguments, which can be gotten
directly from the value of the formal difference. In other words, implementing
a function that says "every formal difference can be represented as a
difference of two natural numbers" is trivial.

**Proof intuition**: As described in **Property intuition**, we can easily
obtain a value of `motive (n - m)` via the `on_diff` function. The trick is
showing that's the same as `motive (n——m)`: all we need is for `motive` to
obey a substitution property and for `n - m` to be equivalent to `n——m`.
-/
def ind_diff
    {motive : Difference ℕ → Sort u} [IndexedFamily motive]
    (ctx : Induction.Context motive)
    : (a : Difference ℕ) → motive a
    := by
  intro (n——m)
  show motive (n——m)
  have : motive (n - m) := ctx.on_diff n m
  have : motive (n——m) := fsubst sub_eqv_diff this
  exact this

/--
Formal differences support integer induction operations.

Defined as a local instance so it can be used in later definitions, but only in
this file. We don't want it to conflict with the `Induction.Ops` instance for
generic integers.
-/
local instance ind_ops : Induction.Ops (Difference ℕ) := {
  ind_diff := ind_diff
}

/--
Integer "difference" induction on formal differences respects equivalence of
its argument.

**Property intuition**: We know `ind_diff` calls `on_diff` with the two natural
numbers in the difference argument. And we know that `on_diff` obeys
substitution because the context provides that proof, so we expect `ind_diff`
does as well.

**Proof intuition**: We have two terms that we want to show are equivalent, but
they have different types: `motive a₁` and `motive a₂`. Replacing the `a₁` term
step-by-step with equivalent values eventually produces the `a₂` term,
completing the proof.

A complication is that the `a₁` term is wrapped inside a call to `fsubst`, to
make the types of the equivalence work. One way to look at the purpose of
`fsubst` is that it's acting as a bridge across the "gap" between the types
`motive a₁` and `motive a₂`. At each replacement of the term on the `a₁` side,
the type of that term gets "closer" to `motive a₂`, and so we also need to
adjust the bridge to get "shorter".

Let's look at the first replacement in the proof as an example. We start with
the term `ctx.ind_diff a₁`, having type `motive a₁`. We're trying to show it's
equivalent to `ctx.ind_diff a₂: motive a₂`, so we have to wrap it in a call to
`fsubst ‹a₁ ≃ a₂›` to give it the type `motive a₂`. Now, expand the definition
of `ctx.ind_diff`, replacing it with `fsubst ‹d₁ ≃ a₁› od₁`. We now have one
`fsubst` call nested inside another, adjusting the type of `od₁` first from
`motive d₁` to `motive a₁`, and then from `motive a₁` to `motive a₂`.

Now we can "shorten the bridge": apply `fsubst_trans` to flatten the nested
calls, producing a single `fsubst` whose equivalence argument is the arguments
of the previous calls, joined by transitivity: `Rel.trans ‹d₁ ≃ a₁› ‹a₁ ≃ a₂›`.
You can see how this is equivalent to the nested arrangement: `d₁` is converted
to `a₁` and then to `a₂`. Because equivalence lives in `Prop`, all proofs of a
specific proposition are equal, so we can replace the `Rel.trans` expression
with a `‹d₁ ≃ a₂›` proof that we derived earlier.

The remaining steps in the proof perform the final "bridge shortening" in the
same way. They also use the key property that this proof requires:
`ctx.on_diff_subst`, expressing that `ctx.on_diff` respects equivalence.
-/
theorem ind_diff_subst
    {motive : Difference ℕ → Sort u} [IndexedFamily motive]
    {ctx : Induction.Context motive} {a₁ a₂ : Difference ℕ} {a_eqv : a₁ ≃ a₂}
    : fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂
    := by
  revert a₁ a₂; intro (n₁——m₁) (n₂——m₂)
  let a₁ := n₁——m₁; let a₂ := n₂——m₂
  intro (_ : a₁ ≃ a₂)
  show fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂

  let d₁ := (n₁:Difference ℕ) - m₁; let d₂ := (n₂:Difference ℕ) - m₂
  have : d₁ ≃ a₁ := sub_eqv_diff
  have : d₂ ≃ a₂ := sub_eqv_diff
  have : d₁ ≃ a₂ := Rel.trans ‹d₁ ≃ a₁› ‹a₁ ≃ a₂›
  have : d₂ ≃ d₁ := Rel.trans ‹d₂ ≃ a₂› (Rel.symm ‹d₁ ≃ a₂›)

  let od₁ := ctx.on_diff n₁ m₁; let od₂ := ctx.on_diff n₂ m₂
  have od_subst : od₁ ≃ fsubst ‹d₂ ≃ d₁› od₂ := Rel.symm ctx.on_diff_subst
  calc
    _ = fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁)         := rfl
    _ = fsubst ‹a₁ ≃ a₂› (fsubst ‹d₁ ≃ a₁› od₁)    := rfl
    _ ≃ fsubst (Rel.trans ‹d₁ ≃ a₁› ‹a₁ ≃ a₂›) od₁ := fsubst_trans
    _ = fsubst ‹d₁ ≃ a₂› od₁                       := rfl
    _ ≃ fsubst ‹d₁ ≃ a₂› (fsubst ‹d₂ ≃ d₁› od₂)    := fsubst_substR od_subst
    _ ≃ fsubst (Rel.trans ‹d₂ ≃ d₁› ‹d₁ ≃ a₂›) od₂ := fsubst_trans
    _ = fsubst ‹d₂ ≃ a₂› od₂                       := rfl
    _ = ctx.ind_diff a₂                            := rfl

/--
Evaluation of integer "difference" induction for formal differences.

**Property intuition** (copied from `Integer.Induction`): Integer induction can
somehow treat any integer as a difference of natural numbers, so if it's given
an integer that's _already in that form_, then it must be the case that it uses
`on_diff` to process the natural numbers directly. This is the intended
_meaning_ of `ind_diff` and `on_diff`.

**Proof intuition**: Similar strategy to `ind_diff_subst` (see its comment for
a detailed explanation): expand definitions and perform simplications of
`fsubst` expressions until the result is obtained. In this case, expanding the
definition of `ind_diff` and then using substitution introduces two
equivalences that are "mirror images": they cancel, leaving a trivial
reflexivity which disappears.
-/
theorem ind_diff_eval
    {motive : Difference ℕ → Sort u} [IndexedFamily motive]
    (ctx : Induction.Context motive) {n m : ℕ}
    : ctx.ind_diff (n - m) ≃ ctx.on_diff n m
    := by
  have sed : (n:Difference ℕ) - m ≃ n——m := sub_eqv_diff
  have des : n——m ≃ n - m := Rel.symm sed
  calc
    _ = ctx.ind_diff (n - m)                         := rfl
    _ ≃ fsubst des (ctx.ind_diff (n——m))             := Rel.symm ind_diff_subst
    _ = fsubst des (fsubst sed (ctx.on_diff n m))    := rfl
    _ ≃ fsubst (Rel.trans sed des) (ctx.on_diff n m) := fsubst_trans
    _ = fsubst Rel.refl (ctx.on_diff n m)            := rfl
    _ ≃ ctx.on_diff n m                              := fsubst_refl

/--
Formal differences obey all expected properties of integer induction.

Not an instance to prevent clashes with the `Induction` instances in `Integer`.
-/
@[implicit_reducible]
def ind_props : Induction.Props (Difference ℕ) := {
  ind_diff_subst := ind_diff_subst
  ind_diff_eval := ind_diff_eval
}

/--
Formal differences fully implement integer "difference" induction.

Not an instance to prevent clashes with the `Induction` instances in `Integer`.
-/
@[implicit_reducible]
def induction : Induction (Difference ℕ) := {
  toOps := ind_ops
  toProps := ind_props
}

end Lean4Axiomatic.Integer.Impl.Difference

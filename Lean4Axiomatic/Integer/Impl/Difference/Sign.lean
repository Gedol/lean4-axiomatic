import Lean4Axiomatic.Integer.Impl.Generic.Sign
import Lean4Axiomatic.Integer.Impl.Difference.Multiplication
import Lean4Axiomatic.Integer.Impl.Difference.Negation

namespace Lean4Axiomatic.Integer.Impl.Difference

variable {ℕ : Type} [Natural ℕ]

open Coe (coe)
open Signed (Negative Positive)

/--
A `Difference` of natural numbers is zero exactly when the numbers are
equivalent.

**Property intuition**: Subtracting a value from itself always gives zero.

**Proof intuition**: Expand the definition of `Difference` equivalence and add
or remove zeros.
-/
theorem zero_diff_eqv {n m : ℕ} : n——m ≃ 0 ↔ n ≃ m := by
  apply Iff.intro
  case mp =>
    intro (_ : n——m ≃ 0)
    show n ≃ m
    have : n——m ≃ 0——0 := ‹n——m ≃ 0›
    have : n + 0 ≃ 0 + m := ‹n——m ≃ 0——0›
    exact Natural.add_swapped_zeros_eqv.mp ‹n + 0 ≃ 0 + m›
  case mpr =>
    intro (_ : n ≃ m)
    show n——m ≃ 0
    show n——m ≃ 0——0
    show n + 0 ≃ 0 + m
    exact Natural.add_swapped_zeros_eqv.mpr ‹n ≃ m›

/--
A `Difference` of natural numbers is negative exactly when the first component
is less than the second.

**Property intuition**: Subtracting a larger value from a smaller will give a
negative result.

**Proof intuition**: There's no simple trick for this proof. Just expand the
definitions of `Negative` and `(· < ·)` and show that the equivalence for one
implies the other.
-/
theorem neg_diff_lt {n m : ℕ} : Negative (n——m) ↔ n < m := by
  have neg_diff {k : ℕ} : 0——k ≃ -1 * coe k := by
    apply Rel.symm
    calc
      (-1) * coe k ≃ _ := Rel.refl
      (-1) * k——0  ≃ _ := mul_neg_one
      (-(k——0))    ≃ _ := Rel.refl
      0——k         ≃ _ := Rel.refl
  apply Iff.intro
  case mp =>
    intro (_ : Negative (n——m))
    show n < m
    apply Natural.lt_defn_add.mpr
    show ∃ (k : ℕ), Positive k ∧ m ≃ n + k
    have
      (NonzeroWithSign.intro (k : ℕ) (_ : Positive k) (_ : n——m ≃ -1 * coe k))
        := Generic.negative_iff_sign_neg1.mp ‹Negative (n——m)›
    have : n——m ≃ 0——k := Rel.trans ‹n——m ≃ -1 * coe k› (Rel.symm neg_diff)
    have : n + k ≃ 0 + m := ‹n——m ≃ 0——k›
    have : m ≃ n + k := calc
      m     ≃ _ := Rel.symm Natural.zero_add
      0 + m ≃ _ := Rel.symm ‹n + k ≃ 0 + m›
      n + k ≃ _ := Rel.refl
    exact Exists.intro k (And.intro ‹Positive k› ‹m ≃ n + k›)
  case mpr =>
    intro (_ : n < m)
    show Negative (n——m)
    apply Generic.negative_iff_sign_neg1.mpr
    show NonzeroWithSign (n——m) (-1)
    have (Exists.intro k (And.intro (_ : Positive k) (_ : m ≃ n + k))) :=
      Natural.lt_defn_add.mp ‹n < m›
    apply NonzeroWithSign.intro k ‹Positive k›
    show n——m ≃ -1 * coe k
    have : 0——k ≃ -1 * coe k := neg_diff
    apply (Rel.trans · ‹0——k ≃ -1 * coe k›)
    show n——m ≃ 0——k
    show n + k ≃ 0 + m
    calc
      n + k ≃ _ := Rel.symm ‹m ≃ n + k›
      m     ≃ _ := Rel.symm Natural.zero_add
      0 + m ≃ _ := Rel.refl

/--
A `Difference` of natural numbers is positive exactly when the first component
is greater than the second.

**Property intuition**: Subtracting a smaller value from a larger will give a
positive result.

**Proof intuition**: By definition, `n > m` is the same as `m < n`. And we
already know (from `neg_diff_lt`) that `m < n` is equivalent to
`Negative (m——n)`. So if we can show that `Positive (n——m)` iff
`Negative (m——n)`, then that will prove the result.
-/
theorem pos_diff_gt {n m : ℕ} : Positive (n——m) ↔ n > m := by
  apply Iff.intro
  case mp =>
    intro (_ : Positive (n——m))
    have
      (NonzeroWithSign.intro (k : ℕ) (_ : Positive k) (_ : n——m ≃ 1 * coe k))
        := Generic.positive_iff_sign_pos1.mp ‹Positive (n——m)›
    show m < n
    apply neg_diff_lt.mp
    show Negative (m——n)
    apply Generic.negative_iff_sign_neg1.mpr
    show NonzeroWithSign (m——n) (-1)
    apply NonzeroWithSign.intro k ‹Positive k›
    show m——n ≃ -1 * coe k
    calc
      m——n           ≃ _ := Rel.symm neg_involutive
      (-(-(m——n)))   ≃ _ := Rel.refl
      (-(n——m))      ≃ _ := by srw [‹n——m ≃ 1 * coe k›]
      (-(1 * coe k)) ≃ _ := AA.scompatL
      (-1) * coe k   ≃ _ := Rel.refl
  case mpr =>
    intro (_ : m < n)
    show Positive (n——m)
    apply Generic.positive_iff_sign_pos1.mpr
    show NonzeroWithSign (n——m) 1
    have : Negative (m——n) := neg_diff_lt.mpr ‹m < n›
    have
      (NonzeroWithSign.intro (k : ℕ) (_ : Positive k) (_ : m——n ≃ -1 * coe k))
        := Generic.negative_iff_sign_neg1.mp ‹Negative (m——n)›
    apply NonzeroWithSign.intro k ‹Positive k›
    show n——m ≃ 1 * coe k
    calc
      n——m              ≃ _ := Rel.symm neg_involutive
      (-(-(n——m)))      ≃ _ := Rel.refl
      (-(m——n))         ≃ _ := by srw [‹m——n ≃ -1 * coe k›]
      (-(-1 * coe k))   ≃ _ := by srw [←AA.scompatL]
      (-(-(1 * coe k))) ≃ _ := neg_involutive
      1 * coe k         ≃ _ := Rel.refl

/--
Every natural number difference is equivalent to exactly one of the following:
* zero;
* a positive natural number;
* the negation of a positive natural number.

**Proof intuition**: This property is equivalent to the trichotomy of order on
the natural number components of differences. Given a difference `n——m`, it is
equal to
* zero when `n ≃ m`;
* a positive natural number when `n > m`;
* the negation of a positive natural number when `n < m`.

The whole proof is just translating from one form of trichotomy into the other.
-/
theorem sign_trichotomy
    (a : Difference ℕ) : AA.ExactlyOneOfThree (a ≃ 0) (Positive a) (Negative a)
    := by
  revert a; intro (n——m)
  show AA.ExactlyOneOfThree (n——m ≃ 0) (Positive (n——m)) (Negative (n——m))
  have natOrderTri : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m) :=
    Natural.trichotomy n m
  apply AA.ExactlyOneOfThree.mk
  case atLeastOne =>
    show AA.OneOfThree (n——m ≃ 0) (Positive (n——m)) (Negative (n——m))
    match natOrderTri.atLeastOne with
    | AA.OneOfThree.first (_ : n < m) =>
      have : Negative (n——m) := neg_diff_lt.mpr ‹n < m›
      exact AA.OneOfThree.third ‹Negative (n——m)›
    | AA.OneOfThree.second (_ : n ≃ m) =>
      have : n——m ≃ 0 := zero_diff_eqv.mpr ‹n ≃ m›
      exact AA.OneOfThree.first ‹n——m ≃ 0›
    | AA.OneOfThree.third (_ : n > m) =>
      have : Positive (n——m) := pos_diff_gt.mpr ‹n > m›
      exact AA.OneOfThree.second ‹Positive (n——m)›
  case atMostOne =>
    intro (h : AA.TwoOfThree (n——m ≃ 0) (Positive (n——m)) (Negative (n——m)))
    have twoOfThree : AA.TwoOfThree (n < m) (n ≃ m) (n > m) := match h with
    | AA.TwoOfThree.oneAndTwo (_ : n——m ≃ 0) (_ : Positive (n——m)) =>
      have : n ≃ m := zero_diff_eqv.mp ‹n——m ≃ 0›
      have : n > m := pos_diff_gt.mp ‹Positive (n——m)›
      AA.TwoOfThree.twoAndThree ‹n ≃ m› ‹n > m›
    | AA.TwoOfThree.oneAndThree (_ : n——m ≃ 0) (_ : Negative (n——m)) =>
      have : n < m := neg_diff_lt.mp ‹Negative (n——m)›
      have : n ≃ m := zero_diff_eqv.mp ‹n——m ≃ 0›
      AA.TwoOfThree.oneAndTwo ‹n < m› ‹n ≃ m›
    | AA.TwoOfThree.twoAndThree (_ : Positive (n——m)) (_ : Negative (n——m)) =>
      have : n < m := neg_diff_lt.mp ‹Negative (n——m)›
      have : n > m := pos_diff_gt.mp ‹Positive (n——m)›
      AA.TwoOfThree.oneAndThree ‹n < m› ‹n > m›
    show False
    have notTwoOfThree : ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m) :=
      natOrderTri.atMostOne
    exact absurd twoOfThree notTwoOfThree

/--
Implementation of the
[signum function](https://en.wikipedia.org/wiki/Sign_function) for differences.

**Definition intuition**: For a difference `n——m`, gives the correct sign value
according to the ordering of `n` and `m`.
-/
def sgn : Difference ℕ → Difference ℕ
| n——m => ord_sgn (compare n m)

/--
There are only three possible result values of the `sgn` function.

Defined as a `def` that returns a `Type` so that it can be used for branching
logic in computable functions.

**Property intuition**: The `sgn` function computes a representation of a
number's sign; thus it must return dinstinct values for zero, positive, and
negative; and return _only_ those values.

**Proof intuition**: Case split on the result of `compare`; each case
corresponds to one of the three values.
-/
def sgn_trichotomy
    (a : Difference ℕ) : AA.OneOfThree₁ (sgn a ≃ 0) (sgn a ≃ 1) (sgn a ≃ -1)
    := by
  revert a; intro (n——m)
  show AA.OneOfThree₁ (sgn (n——m) ≃ 0) (sgn (n——m) ≃ 1) (sgn (n——m) ≃ -1)
  show AA.OneOfThree₁
    (ord_sgn (compare n m) ≃ 0)
    (ord_sgn (compare n m) ≃ 1)
    (ord_sgn (compare n m) ≃ -1)
  match compare n m with
  | Ordering.lt =>
    apply AA.OneOfThree₁.third
    show ord_sgn Ordering.lt ≃ -1
    show -1 ≃ -1
    exact Rel.refl
  | Ordering.eq =>
    apply AA.OneOfThree₁.first
    show ord_sgn Ordering.eq ≃ 0
    show 0 ≃ 0
    exact Rel.refl
  | Ordering.gt =>
    apply AA.OneOfThree₁.second
    show ord_sgn Ordering.gt ≃ 1
    show 1 ≃ 1
    exact Rel.refl

/--
Zero is the only difference with sign value zero.

**Property intuition**: Zero is neither positive nor negative, so it gets its
own sign value.

**Proof intuition**: All differences with value zero have components that are
equivalent. The `sgn` function evaluates to zero in that case.
-/
theorem sgn_zero {a : Difference ℕ} : sgn a ≃ 0 ↔ a ≃ 0 := by
  revert a; intro (n——m)
  apply Iff.intro
  case mp =>
    intro (_ : sgn (n——m) ≃ 0)
    show n——m ≃ 0
    have : ord_sgn (compare n m) ≃ (0:Difference ℕ) := ‹sgn (n——m) ≃ 0›
    have : ord_sgn (compare n m) ≃ ord_sgn Ordering.eq := this
    have : compare n m = Ordering.eq := ord_sgn_inject this
    have : n ≃ m := Natural.compare_eq.mp this
    have : n——m ≃ 0 := zero_diff_eqv.mpr this
    exact this
  case mpr =>
    intro (_ : n——m ≃ 0)
    show sgn (n——m) ≃ 0
    have : n ≃ m := zero_diff_eqv.mp ‹n——m ≃ 0›
    have : compare n m = Ordering.eq := Natural.compare_eq.mpr this
    have : ord_sgn (ℤ := Difference ℕ) (compare n m) ≃ ord_sgn Ordering.eq :=
      by srw [‹compare n m = Ordering.eq›]
    have : ord_sgn (compare n m) ≃ (0:Difference ℕ) := this
    have : sgn (n——m) ≃ 0 := this
    exact this

/--
Only positive differences have sign value one.

**Property intuition**: The definition of the `sgn` function is for all, and
only, positive integers to have sign value one.

**Proof intuition**: All positive differences have a first component that's
greater than their second component. The `sgn` function evaluates to one in
that case.
-/
theorem sgn_positive {a : Difference ℕ} : Positive a ↔ sgn a ≃ 1 := by
  revert a; intro (n——m)
  apply Iff.intro
  case mp =>
    intro (_ : Positive (n——m))
    show sgn (n——m) ≃ 1
    have : n > m := pos_diff_gt.mp ‹Positive (n——m)›
    have : compare n m = Ordering.gt := Natural.compare_gt.mpr this
    have : ord_sgn (ℤ := Difference ℕ) (compare n m) ≃ ord_sgn Ordering.gt :=
      by srw [‹compare n m = Ordering.gt›]
    have : ord_sgn (compare n m) ≃ (1:Difference ℕ) := this
    have : sgn (n——m) ≃ 1 := this
    exact this
  case mpr =>
    intro (_ : sgn (n——m) ≃ 1)
    show Positive (n——m)
    have : ord_sgn (compare n m) ≃ (1:Difference ℕ) := ‹sgn (n——m) ≃ 1›
    have : ord_sgn (compare n m) ≃ ord_sgn Ordering.gt := this
    have : compare n m = Ordering.gt := ord_sgn_inject this
    have : n > m := Natural.compare_gt.mp this
    have : Positive (n——m) := pos_diff_gt.mpr this
    exact this

/--
Only negative differences have sign value negative one.

**Property intuition**: The definition of the `sgn` function is for all, and
only, negative integers to have sign value negative one.

**Proof intuition**: All negative differences have a first component that's
less than their second component. The `sgn` function evaluates to negative one
in that case.
-/
theorem sgn_negative {a : Difference ℕ} : Negative a ↔ sgn a ≃ -1 := by
  revert a; intro (n——m)
  apply Iff.intro
  case mp =>
    intro (_ : Negative (n——m))
    show sgn (n——m) ≃ -1
    have : n < m := neg_diff_lt.mp ‹Negative (n——m)›
    have : compare n m = Ordering.lt := Natural.compare_lt.mpr this
    have : ord_sgn (ℤ := Difference ℕ) (compare n m) ≃ ord_sgn Ordering.lt :=
      by srw [‹compare n m = Ordering.lt›]
    have : ord_sgn (compare n m) ≃ (-1:Difference ℕ) := this
    have : sgn (n——m) ≃ -1 := this
    exact this
  case mpr =>
    intro (_ : sgn (n——m) ≃ -1)
    show Negative (n——m)
    have : ord_sgn (compare n m) ≃ (-1:Difference ℕ) := ‹sgn (n——m) ≃ -1›
    have : ord_sgn (compare n m) ≃ ord_sgn Ordering.lt := this
    have : compare n m = Ordering.lt := ord_sgn_inject this
    have : n < m := Natural.compare_lt.mp this
    have : Negative (n——m) := neg_diff_lt.mpr this
    exact this

/--
If two differences have the same sign value, their sum will as well.

**Property intuition**: If we visualize differences as arrows on a number line,
an arrow's length is its magnitude and its direction is its sign. Two positive
or two negative numbers will have their arrows pointing in the same direction;
adding them produces a longer arrow, again pointing in the same direction.

**Proof intuition**: Convert statements about signs of differences into
comparisons of their underlying natural numbers. Use the property that adding
pairs of natural numbers that are ordered in the same way produces a pair with
the same ordering.
-/
theorem add_preserves_sign
    {s a b : Difference ℕ} : sgn a ≃ s → sgn b ≃ s → sgn (a + b) ≃ s
    := by
  revert a; intro (n——m); revert b; intro (k——j)
  intro (_ : sgn (n——m) ≃ s) (_ : sgn (k——j) ≃ s)
  show sgn (n——m + k——j) ≃ s
  have : ord_sgn (compare n m) ≃ s := ‹sgn (n——m) ≃ s›
  have : ord_sgn (compare k j) ≃ s := ‹sgn (k——j) ≃ s›
  have : ord_sgn (compare n m) ≃ ord_sgn (compare k j) :=
    Rel.trans ‹ord_sgn (compare n m) ≃ s› (Rel.symm this)
  have : compare n m = compare k j := ord_sgn_inject this
  have : compare (n + k) (m + j) = compare k j :=
    Natural.add_preserves_compare this rfl
  have : sgn (n——m + k——j) ≃ s := calc
    sgn (n——m + k——j)                 ≃ _ := Rel.refl
    sgn ((n + k)——(m + j))            ≃ _ := Rel.refl
    ord_sgn (compare (n + k) (m + j)) ≃ _ := by srw [this]
    ord_sgn (compare k j)             ≃ _ := ‹ord_sgn (compare k j) ≃ s›
    s                                 ≃ _ := Rel.refl
  exact this

instance sign_props : Sign.Props (Difference ℕ) := {
  positive_iff_sign_pos1 := Generic.positive_iff_sign_pos1
  negative_iff_sign_neg1 := Generic.negative_iff_sign_neg1
  nonzero_iff_nonzero_impl := Generic.nonzero_iff_nonzero_impl
  sign_trichotomy := sign_trichotomy
}

instance sgn_ops : Sgn.Ops (ℤ := Difference ℕ) (Difference ℕ) := {
  sgn := sgn
}

instance sgn_props : Sgn.Props (Difference ℕ) := {
  sgn_zero := sgn_zero
  sgn_positive := sgn_positive
  sgn_negative := sgn_negative
  add_preserves_sign := add_preserves_sign
  sgn_trichotomy := sgn_trichotomy
}

instance sign : Sign (Difference ℕ) := {
  toSignedOps := Generic.signed_ops
  toSignProps := sign_props
  toSgnOps := sgn_ops
  toSgnProps := sgn_props
}

end Lean4Axiomatic.Integer.Impl.Difference

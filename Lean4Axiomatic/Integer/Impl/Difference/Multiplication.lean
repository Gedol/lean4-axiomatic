import Lean4Axiomatic.Integer.Impl.Difference.Addition

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Multiplication of formal differences -/

variable {ℕ : Type} [Natural ℕ]

/--
Multiplication of differences.

**Definition intuition**: Geometry might be the best way to understand this
definition. Let's interpret each difference as the sum of a _positive_ value
(on the left) and a _negative_ value (on the right). Visualize this as a line
segment divided into two subsegments, colored black and red, with lengths
proportional to the positive and negative parts of the difference,
respectively.

The multiplication of two differences is then represented by a rectangle, where
each difference gets a dimension. The rectangle is divided into four smaller
rectangles, one for each combination of subsegments. The four regions are
colored according to the rules for multiplication of signs: if both sides of a
region are the same color, the region is colored black; if they are different
colors, the region is colored red. The difference in area between the black and
red regions is the result of the multiplication.
-/
def mul : Difference ℕ → Difference ℕ → Difference ℕ
| a——b, c——d => (a * c + b * d)——(a * d + b * c)

instance mulOp : Mul (Difference ℕ) := {
  mul := mul
}

/--
Multiplication of natural number differences is commutative.

**Proof intuition**: Expand definitions to see that we need to show the
equivalence of two differences of natural number sums of products. The left and
right elements of the differences are directly equivalent via commutativity of
natural number addition and multiplication.
-/
theorem mul_comm {a b : Difference ℕ} : a * b ≃ b * a := by
  revert a; intro (n——m); let a := n——m; revert b; intro (k——j); let b := k——j
  show a * b ≃ b * a
  calc
    _ = a * b                            := rfl
    _ = n——m * k——j                      := rfl
    _ = (n * k + m * j)——(n * j + m * k) := rfl
    _ ≃ (k * n + m * j)——(n * j + m * k) := by srw [Natural.mul_comm]
    _ ≃ (k * n + j * m)——(n * j + m * k) := by srw [Natural.mul_comm]
    _ ≃ (k * n + j * m)——(j * n + m * k) := by srw [Natural.mul_comm]
    _ ≃ (k * n + j * m)——(j * n + k * m) := by srw [Natural.mul_comm]
    _ ≃ (k * n + j * m)——(k * m + j * n) := by srw [Natural.add_comm]
    _ = k——j * n——m                      := rfl
    _ = b * a                            := rfl

instance mul_commutative : AA.Commutative (α := Difference ℕ) (· * ·) := {
  comm := mul_comm
}

/--
Multiplying the same difference on the right of two equivalent differences
preserves their equivalence.

**Proof intuition**: The property is already intuitively true; imagine
stretching two line segments of the same length by the same amount. So the
proof just expands all definitions into equalities of sums of products of
natural numbers, and performs algebra to obtain the desired result.
-/
@[gcongr]
theorem mul_substL {a₁ a₂ b : Difference ℕ} : a₁ ≃ a₂ → a₁ * b ≃ a₂ * b := by
  revert a₁; intro (n——m); let a₁ := n——m
  revert a₂; intro (k——j); let a₂ := k——j
  revert b; intro (p——q); let b := p——q
  intro (_ : a₁ ≃ a₂)
  show a₁ * b ≃ a₂ * b

  have lr_swap_rr {p q r s : ℕ} : (p + q) + (r + s) ≃ (p + s) + (r + q) :=
    AA.expr_xxfxxff_lr_swap_rr (f := (· + ·))
  have expand_swap
      {u v w x y z : ℕ}
      : (w + x) * u + (y + z) * v ≃ (w * u + z * v) + (y * v + x * u)
      := calc
    (w + x) * u     + (y + z) * v     ≃ _ := by srw [Natural.mul_distribR_add]
    (w * u + x * u) + (y + z) * v     ≃ _ := by srw [Natural.mul_distribR_add]
    (w * u + x * u) + (y * v + z * v) ≃ _ := lr_swap_rr
    (w * u + z * v) + (y * v + x * u) ≃ _ := Rel.refl

  have : n——m ≃ k——j   := ‹a₁ ≃ a₂›
  have : n + j ≃ k + m := this
  have : (n * p + m * q) + (k * q + j * p) ≃ (k * p + j * q) + (n * q + m * p)
       := calc
    (n * p + m * q) + (k * q + j * p) ≃ _ := Rel.symm expand_swap
    (n + j) * p     + (k + m) * q     ≃ _ := by srw [‹n + j ≃ k + m›]
    (k + m) * p     + (k + m) * q     ≃ _ := by srw [←‹n + j ≃ k + m›]
    (k + m) * p     + (n + j) * q     ≃ _ := expand_swap
    (k * p + j * q) + (n * q + m * p) ≃ _ := Rel.refl

  have diff_eqv
      : (n * p + m * q)——(n * q + m * p) ≃ (k * p + j * q)——(k * q + j * p)
      := ‹(n * p + m * q) + (k * q + j * p) ≃ (k * p + j * q) + (n * q + m * p)›
  calc
    _ = a₁ * b                           := rfl
    _ = n——m * p——q                      := rfl
    _ = (n * p + m * q)——(n * q + m * p) := rfl
    _ ≃ (k * p + j * q)——(k * q + j * p) := diff_eqv
    _ = k——j * p——q                      := rfl
    _ = a₂ * b                           := rfl

/--
Multiplying the same difference on the left of two equivalent differences
preserves their equivalence.
-/
@[gcongr]
theorem mul_substR {a₁ a₂ b : Difference ℕ} : a₁ ≃ a₂ → b * a₁ ≃ b * a₂ := by
  intro (_ : a₁ ≃ a₂)
  show b * a₁ ≃ b * a₂
  calc
    _ = b * a₁ := rfl
    _ ≃ a₁ * b := mul_comm
    _ ≃ a₂ * b := by srw [‹a₁ ≃ a₂›]
    _ ≃ b * a₂ := mul_comm

@[implicit_reducible]
def mul_substitutive
    : AA.Substitutive₂ (α := Difference ℕ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  substitutiveL := { subst₂ := λ (_ : True) => mul_substL }
  substitutiveR := { subst₂ := λ (_ : True) => mul_substR }
}

/--
Multiplication of natural number differences is associative.

**Intuition**: It's not really clear why the property is true, or if there's a
clear principle behind the proof; brute force definition expansion and algebra
get the job done anyway.
-/
theorem mul_assoc {a b c : Difference ℕ} : (a * b) * c ≃ a * (b * c) := by
  revert a; intro (q——p); let a := q——p
  revert b; intro (n——m); let b := n——m
  revert c; intro (k——j); let c := k——j
  show (a * b) * c ≃ a * (b * c)

  have nat_distribL {x y z : ℕ} : z * (x + y) ≃ z * x + z * y :=
    Natural.mul_distribL_add
  have nat_distribR {x y z : ℕ} : (x + y) * z ≃ x * z + y * z :=
    Natural.mul_distribR_add
  have swap_middle {w x y z : ℕ} : (w + x) + (y + z) ≃ (w + y) + (x + z) :=
    AA.expr_xxfxxff_lr_swap_rl (f := (· + ·))

  let qn := q * n; let qm := q * m; let pn := p * n; let pm := p * m
  have redistr (x y : ℕ)
      : let mx := m * x; let my := m * y; let nx := n * x; let ny := n * y
        (qn + pm) * x + (qm + pn) * y ≃ q * (nx + my) + p * (ny + mx)
      := by
    intro mx my nx ny
    calc
      _ = (qn + pm) * x + (qm + pn) * y         := rfl
      _ ≃ (qn * x + pm * x) + (qm + pn) * y     := by srw [nat_distribR]
      _ ≃ (qn * x + pm * x) + (qm * y + pn * y) := by srw [nat_distribR]
      _ ≃ (qn * x + qm * y) + (pm * x + pn * y) := swap_middle
      _ ≃ (qn * x + qm * y) + (pn * y + pm * x) := by srw [Natural.add_comm]
      _ ≃ (q * nx + qm * y) + (pn * y + pm * x) := by srw [Natural.mul_assoc]
      _ ≃ (q * nx + q * my) + (pn * y + pm * x) := by srw [Natural.mul_assoc]
      _ ≃ (q * nx + q * my) + (p * ny + pm * x) := by srw [Natural.mul_assoc]
      _ ≃ (q * nx + q * my) + (p * ny + p * mx) := by srw [Natural.mul_assoc]
      _ ≃ q * (nx + my) + (p * ny + p * mx)     := by srw [←nat_distribL]
      _ ≃ q * (nx + my) + p * (ny + mx)         := by srw [←nat_distribL]

  let nk := n * k; let nj := n * j; let mk := m * k; let mj := m * j
  calc
    _ = (a * b) * c                                      := rfl
    _ = (q——p * n——m) * k——j                             := rfl
    _ = (qn+pm)——(qm+pn) * k——j                          := rfl
    _ = ((qn+pm)*k + (qm+pn)*j)——((qn+pm)*j + (qm+pn)*k) := rfl
    _ ≃ (q*(nk+mj) + p*(nj+mk))——((qn+pm)*j + (qm+pn)*k) := by srw [redistr k j]
    _ ≃ (q*(nk+mj) + p*(nj+mk))——(q*(nj+mk) + p*(nk+mj)) := by srw [redistr j k]
    _ = q——p * (nk+mj)——(nj+mk)                          := rfl
    _ = q——p * (n——m * k——j)                             := rfl
    _ = a * (b * c)                                      := rfl

@[implicit_reducible]
def mul_associative : AA.Associative (α := Difference ℕ) (· * ·) := {
  assoc := mul_assoc
}

/--
The natural number difference `1` is a left multiplicative identity element.

**Property intuition**: A sum of a single value produces that same value.

**Proof intuition**: Not sure there's any deep insight here, the proof is the
standard formula of (1) expand definitions and (2) algebra.
-/
theorem mul_identL {a : Difference ℕ} : 1 * a ≃ a := by
  revert a; intro (n——m); let a := n——m
  show 1 * a ≃ a

  calc
    _ = 1 * a                            := rfl
    _ = 1——0 * n——m                      := rfl
    _ = (1 * n + 0 * m)——(1 * m + 0 * n) := rfl
    _ ≃ (n + 0 * m)——(1 * m + 0 * n)     := by srw [Natural.mul_identL]
    _ ≃ (n + 0 * m)——(m + 0 * n)         := by srw [Natural.mul_identL]
    _ ≃ (n + 0)——(m + 0 * n)             := by srw [Natural.zero_mul]
    _ ≃ (n + 0)——(m + 0)                 := by srw [Natural.zero_mul]
    _ ≃ n——(m + 0)                       := by srw [Natural.add_zero]
    _ ≃ n——m                             := by srw [Natural.add_zero]
    _ = a                                := rfl

/--
The natural number difference `1` is a right multiplicative identity element.

**Property intuition**: A sum of a single value produces that same value.

**Proof intuition**: Use commutativity of multiplication and the left identity.
-/
theorem mul_identR {a : Difference ℕ} : a * 1 ≃ a := calc
  _ = a * 1 := rfl
  _ ≃ 1 * a := mul_comm
  _ ≃ a     := mul_identL

@[implicit_reducible]
def mul_identity : AA.Identity (α := Difference ℕ) 1 (· * ·) := {
  identityL := { ident := mul_identL }
  identityR := { ident := mul_identR }
}

/--
Multiplication on the left distributes over addition.

**Property intuition**

If we think of natural number differences as 1-dimensional vectors representing
the distance and direction to get from their first component to their second
component, then addition of differences is just the sum of vectors (magnitudes
and directions combine and some cancellation may occur) and multiplication of
differences is scaling, with a change in direction if the signs are opposite.

With that interpretation, this property then says that adding (combining) two
differences and multiplying (scaling with direction) the result is the same as
multiplying each difference before adding them. Geometrically this seems
plausible.

**Proof intuition**

After all definitions are expanded, the resulting equivalence of differences
turns out to follow from the "pointwise" equivalence of their components. Both
of these can be shown to hold with algebraic identities on natural numbers.
-/
theorem mul_distribL {a b c : Difference ℕ} : a * (b + c) ≃ a * b + a * c := by
  revert a; intro (q——p); let a := q——p
  revert b; intro (n——m); let b := n——m
  revert c; intro (k——j); let c := k——j
  show a * (b + c) ≃ a * b + a * c

  have swap_middle {w x y z : ℕ} : (w + x) + (y + z) ≃ (w + y) + (x + z) :=
    AA.expr_xxfxxff_lr_swap_rl (f := (· + ·))
  have distr_swap
      {w x y z : ℕ}
      : q * (w + y) + p * (x + z) ≃ (q * w + p * x) + (q * y + p * z)
      := by
    calc
      _ = q * (w + y) + p * (x + z)         := rfl
      _ ≃ (q * w + q * y) + p * (x + z)     := by srw [Natural.mul_distribL_add]
      _ ≃ (q * w + q * y) + (p * x + p * z) := by srw [Natural.mul_distribL_add]
      _ ≃ (q * w + p * x) + (q * y + p * z) := swap_middle

  let qn := q * n; let qm := q * m; let qk := q * k; let qj := q * j
  let pn := p * n; let pm := p * m; let pk := p * k; let pj := p * j
  calc
    _ = a * (b + c)                                      := rfl
    _ = q——p * (n——m + k——j)                             := rfl
    _ = q——p * (n+k)——(m+j)                              := rfl
    _ = (q * (n+k) + p * (m+j))——(q * (m+j) + p * (n+k)) := rfl
    _ ≃ ((qn + pm) + (qk + pj))——(q * (m+j) + p * (n+k)) := by srw [distr_swap]
    _ ≃ ((qn + pm) + (qk + pj))——((qm + pn) + (qj + pk)) := by srw [distr_swap]
    _ = (qn + pm)——(qm + pn) + (qk + pj)——(qj + pk)      := rfl
    _ = q——p * n——m + q——p * k——j                        := rfl
    _ = a * b + a * c                                    := rfl

/-- Multiplication on the right distributes over addition. -/
theorem mul_distribR
    {a b c : Difference ℕ} : (b + c) * a ≃ b * a + c * a
    := calc
  _ = (b + c) * a   := rfl
  _ ≃ a * (b + c)   := mul_comm
  _ ≃ a * b + a * c := mul_distribL
  _ ≃ b * a + c * a := by srw [mul_comm, mul_comm]

@[implicit_reducible]
def mul_distributive : AA.Distributive (α := Difference ℕ) (· * ·) (· + ·) := {
  distributiveL := { distrib := mul_distribL }
  distributiveR := { distrib := mul_distribR }
}

/--
Conversion from `ℕ` to `Difference ℕ` is compatible with multiplication.

**Proprty intuition**: One would hope this is true, otherwise we could not say
that the set of differences (integers) is a superset of the natural numbers.

**Proof intuition**: Expand definitions to see that we only need to prove
equivalence of differences element-wise. And then it's just a matter of
reducing terms to zero and removing them.
-/
theorem mul_compat_natural
    {n m : ℕ} : ((n * m : ℕ):Difference ℕ) ≃ (n:Difference ℕ) * (m:Difference ℕ)
    :=
  Rel.symm $ calc
    _ = (n:Difference ℕ) * (m:Difference ℕ) := rfl
    _ = (n * m + 0 * 0)——(n * 0 + 0 * m)    := rfl
    _ ≃ (n * m + 0)——(n * 0 + 0 * m)        := by srw [Natural.zero_mul]
    _ ≃ (n * m + 0)——(0 + 0 * m)            := by srw [Natural.mul_zero]
    _ ≃ (n * m + 0)——(0 + 0)                := by srw [Natural.zero_mul]
    _ ≃ (n * m)——(0 + 0)                    := by srw [Natural.add_zero]
    _ ≃ (n * m)——0                          := by srw [Natural.zero_add]
    _ = ((n * m : ℕ):Difference ℕ)          := rfl

@[implicit_reducible]
def mul_compatible_from_natural
    : AA.Compatible₂ (α := ℕ) (β := Difference ℕ) (↑·) (· * ·) (· * ·)
    := {
  compat₂ := mul_compat_natural
}

instance multiplication : Multiplication (ℕ := ℕ) (Difference ℕ) := {
  mulOp := mulOp
  mul_commutative := mul_commutative
  mul_substitutive := mul_substitutive
  mul_associative := mul_associative
  mul_identity := mul_identity
  mul_distributive := mul_distributive
  mul_compatible_from_natural := mul_compatible_from_natural
}

end Lean4Axiomatic.Integer.Impl.Difference

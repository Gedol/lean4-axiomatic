import Lean4Axiomatic.Rational.Metric

/-! # Generic implementation of rational metric functions and properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Lean4Axiomatic.Metric (abs dist)
open Lean4Axiomatic.Signed (sgn)

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Order ℚ]

/-- Definition of absolute value that matches the axioms. -/
def _abs (p : ℚ) : ℚ := p * sgn p

/-- Definition of distance that matches the axioms. -/
def _dist (p q : ℚ) : ℚ := _abs (p - q)

/-- Definition of ε-closeness that matches the axioms. -/
def _close (ε p q : ℚ) : Prop := _dist p q ≤ ε

/-- Definition of betweenness that matches the axioms. -/
def _between (p q r : ℚ) : Prop := p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p

local instance metric_ops : Metric.Ops ℚ := {
  _abs := _abs
  _dist := _dist
  _close := _close
  _between := _between
}

@[implicit_reducible]
def metric_props : Metric.Props ℚ := {
  abs_sgn := eqv_refl
  dist_abs := eqv_refl
  close_dist := Iff.intro id id
  between_order := Iff.intro id id
}

@[implicit_reducible]
def metric : Metric ℚ := {
  toOps := metric_ops
  toProps := metric_props
}

end Lean4Axiomatic.Rational.Impl.Generic

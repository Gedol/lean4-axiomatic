import Lean4Axiomatic.Integer.Metric

/-! # Generic implementation of integer metric functions and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

open Lean4Axiomatic.Metric (abs dist)

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
    [Subtraction ℤ]

/-- Definition of absolute value that matches the axioms. -/
def _abs (a : ℤ) : ℤ := a * sgn a

/-- Definition of distance that matches the axioms. -/
def _dist (a b : ℤ) : ℤ := _abs (a - b)

local instance metric_ops : Metric.Ops ℤ := {
  _abs := _abs
  _dist := _dist
}

@[implicit_reducible]
def metric_props : Metric.Props ℤ := {
  abs_sgn := Rel.refl
}

@[implicit_reducible]
def metric : Metric ℤ := {
  toOps := metric_ops
  toProps := metric_props
}

end Lean4Axiomatic.Integer.Impl.Generic

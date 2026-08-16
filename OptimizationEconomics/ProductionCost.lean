import OptimizationEconomics.Basic
import OptimizationEconomics.Monotonicity
import Mathlib.Tactic

/-!
# Production and cost

Simple algebraic relations. No institutional or empirical claims are made.
-/

namespace OptimizationEconomics

/-!
## Case P01 — Linear production is strictly monotone in labor when `α > 0`

MATHEMATICAL / ECONOMIC INTENT:
  `q = α * ℓ` rises strictly with `ℓ` if productivity is positive.
VARIABLE DOMAINS: `α ℓ : ℝ`.
ASSUMPTIONS: `0 < α`.
FORMAL LEAN STATEMENT: `StrictMono (linearProduction α)`.
PROOF ARCHITECTURE: reuse `M01`.
KEY LEAN/MATHLIB MECHANISM: `StrictMono`.
EDGE CASE: `α = 0` yields zero output for every input.
SEMANTIC FAITHFULNESS AUDIT:
  `α` is a real coefficient. Calling it productivity is interpretation.
-/
theorem P01_linear_production_strictMono {α : ℝ} (hα : 0 < α) :
    StrictMono (linearProduction α) :=
  M01_pos_scale_strictMono hα

/-!
## Case P02 — Output stays nonnegative on a nonnegative domain

MATHEMATICAL / ECONOMIC INTENT:
  If `0 ≤ α` and `0 ≤ ℓ` then `0 ≤ α * ℓ`.
VARIABLE DOMAINS: `α ℓ : ℝ`.
ASSUMPTIONS: both nonnegative.
FORMAL LEAN STATEMENT: `0 ≤ linearProduction α ℓ`.
PROOF ARCHITECTURE: `mul_nonneg`.
KEY LEAN/MATHLIB MECHANISM: ordered ring.
EDGE CASE: a negative input with negative `α` also gives positive output;
  that is excluded by the domain assumptions, not by algebra alone.
SEMANTIC FAITHFULNESS AUDIT:
  Nonnegativity of output is an implication of the stated sign restrictions.
-/
theorem P02_output_nonneg {α ℓ : ℝ} (hα : 0 ≤ α) (hℓ : 0 ≤ ℓ) :
    0 ≤ linearProduction α ℓ :=
  mul_nonneg hα hℓ

/-!
## Case P03 — Linear cost is well-defined after a nonzero productivity assumption

MATHEMATICAL / ECONOMIC INTENT:
  `linearCost w α q = w * q / α` requires `α ≠ 0`.
VARIABLE DOMAINS: `w α q : ℝ`.
ASSUMPTIONS: `α ≠ 0`.
FORMAL LEAN STATEMENT: `α * linearCost w α q = w * q`.
PROOF ARCHITECTURE: `mul_div_cancel₀`.
KEY LEAN/MATHLIB MECHANISM: field cancellation.
EDGE CASE: `α = 0` makes the defining expression illegal in this model.
SEMANTIC FAITHFULNESS AUDIT:
  The theorem does not define cost at zero productivity.
-/
theorem P03_linear_cost_cancel {w α q : ℝ} (hα : α ≠ 0) :
    α * linearCost w α q = w * q :=
  mul_div_cancel₀ (w * q) hα

/-!
## Case P04 — Average cost of the linear model is `w / α` when `q ≠ 0`

MATHEMATICAL / ECONOMIC INTENT:
  For `q ≠ 0` and `α ≠ 0`, `averageCost (linearCost w α q) q = w / α`.
VARIABLE DOMAINS: `w α q : ℝ`.
ASSUMPTIONS: `α ≠ 0`, `q ≠ 0`.
FORMAL LEAN STATEMENT: the identity above.
PROOF ARCHITECTURE: `field_simp`.
KEY LEAN/MATHLIB MECHANISM: `field_simp`.
EDGE CASE: average cost is not defined at `q = 0` in this development.
SEMANTIC FAITHFULNESS AUDIT:
  The identity is algebraic. It is not a statement about firms or markets.
-/
theorem P04_average_cost_linear {w α q : ℝ} (hα : α ≠ 0) (hq : q ≠ 0) :
    averageCost (linearCost w α q) q = w / α := by
  unfold averageCost linearCost
  field_simp

/-!
## Case P05 — Difference quotient of linear cost equals `w / α`

MATHEMATICAL / ECONOMIC INTENT:
  The increment `(c(q+h) - c(q)) / h` equals `w / α` whenever `h ≠ 0` and
  `α ≠ 0`.
VARIABLE DOMAINS: `w α q h : ℝ`.
ASSUMPTIONS: `α ≠ 0`, `h ≠ 0`.
FORMAL LEAN STATEMENT: the difference-quotient identity.
PROOF ARCHITECTURE: `field_simp` and `ring`.
KEY LEAN/MATHLIB MECHANISM: field algebra.
EDGE CASE: `h = 0` would divide by zero; the statement excludes it.
SEMANTIC FAITHFULNESS AUDIT:
  This is an algebraic marginal-cost identity for an affine cost, not a
  derivative theorem in the topological sense (though it implies one).
-/
theorem P05_linear_cost_difference_quotient {w α q h : ℝ}
    (hα : α ≠ 0) (hh : h ≠ 0) :
    (linearCost w α (q + h) - linearCost w α q) / h = w / α := by
  unfold linearCost
  field_simp
  ring

/-!
## Case P06 — Linear cost is monotone in output when `w / α` is nonnegative

MATHEMATICAL / ECONOMIC INTENT:
  If `0 ≤ w` and `0 < α` then cost is a monotone function of output.
VARIABLE DOMAINS: `w α : ℝ`.
ASSUMPTIONS: `0 ≤ w`, `0 < α`.
FORMAL LEAN STATEMENT: `Monotone (linearCost w α)`.
PROOF ARCHITECTURE: nonnegative slope `w / α`.
KEY LEAN/MATHLIB MECHANISM: `div_nonneg`, affine monotonicity.
EDGE CASE: if `w < 0` the cost would decrease in output.
SEMANTIC FAITHFULNESS AUDIT:
  Monotone cost is not “increasing returns” or “decreasing returns”. Those
  phrases are not used as theorems here.
-/
theorem P06_linear_cost_monotone {w α : ℝ} (hw : 0 ≤ w) (hα : 0 < α) :
    Monotone (linearCost w α) := by
  intro q q' hqq
  unfold linearCost
  have hwa : 0 ≤ w / α := div_nonneg hw hα.le
  have hmul : (w / α) * q ≤ (w / α) * q' :=
    mul_le_mul_of_nonneg_left hqq hwa
  have h₁ : w * q / α = (w / α) * q := by ring
  have h₂ : w * q' / α = (w / α) * q' := by ring
  exact h₁ ▸ h₂ ▸ hmul

end OptimizationEconomics

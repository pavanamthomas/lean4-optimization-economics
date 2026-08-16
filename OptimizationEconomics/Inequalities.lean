import OptimizationEconomics.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Linear inequalities used as constraints

These lemmas isolate the algebraic facts that later budget and comparative-static
arguments rely on. They are not consumer theory.
-/

namespace OptimizationEconomics

/-!
## Case I01 — Transitivity of a linear expenditure bound

MATHEMATICAL / ECONOMIC INTENT:
  If expenditure is at most `m` and `m ≤ m'`, the same bundle meets `m'`.
VARIABLE DOMAINS: all real.
ASSUMPTIONS: `p * x ≤ m` and `m ≤ m'`.
FORMAL LEAN STATEMENT: `p * x ≤ m'`.
PROOF ARCHITECTURE: `le_trans`.
KEY LEAN/MATHLIB MECHANISM: ordered semiring transitivity.
EDGE CASE: the lemma does not require `0 ≤ x` or `0 < p`.
SEMANTIC FAITHFULNESS AUDIT:
  This is only transitivity. It does not say income “relaxes the consumer”.
-/
theorem I01_expenditure_le_trans {p x m m' : ℝ}
    (h : p * x ≤ m) (hmm : m ≤ m') : p * x ≤ m' :=
  le_trans h hmm

/-!
## Case I02 — Nonnegative scaling preserves an inequality

MATHEMATICAL / ECONOMIC INTENT:
  Multiplying a weak inequality by a nonnegative scalar preserves direction.
VARIABLE DOMAINS: `a b c : ℝ`.
ASSUMPTIONS: `a ≤ b`, `0 ≤ c`.
FORMAL LEAN STATEMENT: `c * a ≤ c * b`.
PROOF ARCHITECTURE: `mul_le_mul_of_nonneg_left`.
KEY LEAN/MATHLIB MECHANISM: ordered ring.
EDGE CASE: if `c < 0` the inequality reverses. That is Case I03.
SEMANTIC FAITHFULNESS AUDIT:
  Direction of an inequality is part of the mathematics, not decoration.
-/
theorem I02_nonneg_mul_le {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h hc

/-!
## Case I03 — Negative scaling reverses an inequality

MATHEMATICAL / ECONOMIC INTENT:
  A negative multiplier flips `≤` to `≥`.
VARIABLE DOMAINS: `a b c : ℝ`.
ASSUMPTIONS: `a ≤ b`, `c < 0`.
FORMAL LEAN STATEMENT: `c * b ≤ c * a`.
PROOF ARCHITECTURE: `mul_le_mul_of_nonpos_left`.
KEY LEAN/MATHLIB MECHANISM: `nonpos` left multiplication.
EDGE CASE: this is why a negative price turns “more quantity” into “less
  expenditure”.
SEMANTIC FAITHFULNESS AUDIT:
  Using the same inequality direction for negative prices is a formal error.
-/
theorem I03_neg_mul_le {a b c : ℝ} (h : a ≤ b) (hc : c < 0) :
    c * b ≤ c * a :=
  mul_le_mul_of_nonpos_left h hc.le

/-!
## Case I04 — Weak versus strict product inequalities

MATHEMATICAL / ECONOMIC INTENT:
  Strict increase of a positive factor times a positive quantity is strict.
VARIABLE DOMAINS: `p p' x : ℝ`.
ASSUMPTIONS: `0 < x`, `p < p'`.
FORMAL LEAN STATEMENT: `p * x < p' * x`.
PROOF ARCHITECTURE: `mul_lt_mul_of_pos_right`.
KEY LEAN/MATHLIB MECHANISM: strict ordered ring.
EDGE CASE: if `x = 0` then `p * x = p' * x = 0` even when `p < p'`.
SEMANTIC FAITHFULNESS AUDIT:
  A strict price change does not strictly change expenditure of the zero bundle.
-/
theorem I04_strict_mul_right {p p' x : ℝ} (hx : 0 < x) (hpp : p < p') :
    p * x < p' * x :=
  mul_lt_mul_of_pos_right hpp hx

theorem I04_zero_quantity_cancels_price {p p' : ℝ} :
    p * (0 : ℝ) = p' * 0 := by
  simp

/-!
## Case I05 — Sum of two linear inequalities

MATHEMATICAL / ECONOMIC INTENT:
  Adding two expenditure bounds yields a bound on the sum.
VARIABLE DOMAINS: reals.
ASSUMPTIONS: `a ≤ a'`, `b ≤ b'`.
FORMAL LEAN STATEMENT: `a + b ≤ a' + b'`.
PROOF ARCHITECTURE: `add_le_add`.
KEY LEAN/MATHLIB MECHANISM: ordered monoid.
EDGE CASE: one coordinate can increase if the other decreases enough; the
  summed lemma does not prevent that.
SEMANTIC FAITHFULNESS AUDIT:
  This is algebra of bounds, not a substitution effect.
-/
theorem I05_add_le_add {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    a + b ≤ a' + b' :=
  add_le_add ha hb

/-!
## Case I06 — Positive denominator and division direction

MATHEMATICAL / ECONOMIC INTENT:
  For `0 < p`, `p * x ≤ m` is equivalent to `x ≤ m / p`.
VARIABLE DOMAINS: `p m x : ℝ`.
ASSUMPTIONS: `0 < p`.
FORMAL LEAN STATEMENT: `p * x ≤ m ↔ x ≤ m / p`.
PROOF ARCHITECTURE: `le_div_iff₀` / `div_le_iff₀` family.
KEY LEAN/MATHLIB MECHANISM: `le_div_iff₀`.
EDGE CASE: the equivalence is false for `p = 0` or `p < 0`.
SEMANTIC FAITHFULNESS AUDIT:
  Converting a budget into a quantity bound requires a positive price. The
  conversion is not valid as a background convention.
-/
theorem I06_budget_iff_div {p m x : ℝ} (hp : 0 < p) :
    p * x ≤ m ↔ x ≤ m / p := by
  rw [mul_comm p x]
  exact (le_div_iff₀ hp).symm

end OptimizationEconomics

import OptimizationEconomics.Basic
import OptimizationEconomics.BudgetConstraints
import OptimizationEconomics.Feasibility
import OptimizationEconomics.Objectives
import Mathlib.Tactic

/-!
# Comparative statics

Each statement is an implication from explicit parameter changes. No
equilibrium selection or empirical response is claimed.
-/

namespace OptimizationEconomics
open Set

/-!
## Case C01 — Raising an upper resource bound expands the interval

MATHEMATICAL / ECONOMIC INTENT:
  If `m ≤ m'` then `Icc 0 m ⊆ Icc 0 m'`.
VARIABLE DOMAINS: `m m' : ℝ`.
ASSUMPTIONS: `m ≤ m'`.
FORMAL LEAN STATEMENT: the inclusion above.
PROOF ARCHITECTURE: `Icc_subset_Icc`.
KEY LEAN/MATHLIB MECHANISM: interval subset lemmas.
EDGE CASE: the inclusion is weak. If `m < 0` and `m' < 0` both sets may be
  empty, hence equal.
SEMANTIC FAITHFULNESS AUDIT:
  Expansion of a feasible set is not an increase in a chosen action.
-/
theorem C01_resource_bound_expands {m m' : ℝ} (hmm : m ≤ m') :
    Icc (0 : ℝ) m ⊆ Icc (0 : ℝ) m' :=
  Icc_subset_Icc le_rfl hmm

/-!
## Case C02 — Income weakly expands the two-good budget set

MATHEMATICAL / ECONOMIC INTENT:
  Same mathematics as B03, recorded as a comparative-static implication.
VARIABLE DOMAINS: prices and incomes in `ℝ`.
ASSUMPTIONS: `m ≤ m'`.
FORMAL LEAN STATEMENT: `budgetSet p₁ p₂ m ⊆ budgetSet p₁ p₂ m'`.
PROOF ARCHITECTURE: reuse B03.
KEY LEAN/MATHLIB MECHANISM: set inclusion.
EDGE CASE: zero prices and already-nonnegative income give equality, not
  strict expansion. See ReviewerCases.
SEMANTIC FAITHFULNESS AUDIT:
  “Can weakly expand” is the correct strength. “Must strictly expand” is not.
-/
theorem C02_income_weakly_expands {p₁ p₂ m m' : ℝ} (hmm : m ≤ m') :
    budgetSet p₁ p₂ m ⊆ budgetSet p₁ p₂ m' :=
  B03_income_expands hmm

/-!
## Case C03 — A strictly larger income and a positive price add a new 1D bundle

MATHEMATICAL / ECONOMIC INTENT:
  If `0 < p` and `m < m'` then `m' / p` is feasible at `m'` and not at `m`
  (provided we do not require anything else).
VARIABLE DOMAINS: `p m m' : ℝ`.
ASSUMPTIONS: `0 < p`, `m < m'`, and `0 ≤ m'` so the new point is nonnegative.
FORMAL LEAN STATEMENT:
  `m' / p ∈ budget1D p m'` and `m' / p ∉ budget1D p m`.
PROOF ARCHITECTURE: expenditure equals `m'` at the new point.
KEY LEAN/MATHLIB MECHANISM: `mul_div_cancel₀`.
EDGE CASE: if `m' < 0` the candidate `m'/p` is negative, hence excluded by
  `x ≥ 0`.
SEMANTIC FAITHFULNESS AUDIT:
  This is a sufficient condition for *strict* expansion in one dimension.
  It is not the same as C02.
-/
theorem C03_strict_1D_income_expansion {p m m' : ℝ}
    (hp : 0 < p) (hmm : m < m') (hm' : 0 ≤ m') :
    m' / p ∈ budget1D p m' ∧ m' / p ∉ budget1D p m := by
  have hfeas : m' / p ∈ budget1D p m' := by
    refine ⟨div_nonneg hm' hp.le, ?_⟩
    simp [mul_div_cancel₀ m' hp.ne']
  refine ⟨hfeas, ?_⟩
  intro h
  have : p * (m' / p) ≤ m := h.2
  have : m' ≤ m := by simpa [mul_div_cancel₀ m' hp.ne'] using this
  exact not_le.mpr hmm this

/-!
## Case C04 — Increasing a positive price can destroy affordability of a fixed bundle

MATHEMATICAL / ECONOMIC INTENT:
  If `0 < x` and `p < p'` then expenditure strictly rises, so a bundle that
  sat exactly on the budget at `p` is unaffordable at `p'`.
VARIABLE DOMAINS: `p p' x m : ℝ`.
ASSUMPTIONS: `0 < x`, `p < p'`, `p * x = m`.
FORMAL LEAN STATEMENT: `¬ p' * x ≤ m`.
PROOF ARCHITECTURE: `p * x < p' * x`.
KEY LEAN/MATHLIB MECHANISM: `mul_lt_mul_of_pos_right`.
EDGE CASE: if `x = 0` the price change is invisible.
SEMANTIC FAITHFULNESS AUDIT:
  The bundle is held fixed. This is not a demand response.
-/
theorem C04_price_breaks_exact_budget {p p' x m : ℝ}
    (hx : 0 < x) (hpp : p < p') (heq : p * x = m) :
    ¬ p' * x ≤ m := by
  have : p * x < p' * x := mul_lt_mul_of_pos_right hpp hx
  exact not_le.mpr (by simpa [heq] using this)

/-!
## Case C05 — A larger slope raises an affine objective at a positive point

MATHEMATICAL / ECONOMIC INTENT:
  If `0 < x` and `a < a'` then `affineObj a b x < affineObj a' b x`.
VARIABLE DOMAINS: `a a' b x : ℝ`.
ASSUMPTIONS: `0 < x`, `a < a'`.
FORMAL LEAN STATEMENT: the strict comparison above.
PROOF ARCHITECTURE: factor `x`.
KEY LEAN/MATHLIB MECHANISM: `mul_lt_mul_of_pos_right`.
EDGE CASE: at `x = 0` the slope is invisible.
SEMANTIC FAITHFULNESS AUDIT:
  Parameter monotonicity of an objective is not a revealed-preference claim.
-/
theorem C05_affine_slope_increases_value {a a' b x : ℝ}
    (hx : 0 < x) (haa : a < a') :
    affineObj a b x < affineObj a' b x := by
  unfold affineObj
  linarith [mul_lt_mul_of_pos_right haa hx]

/-!
## Case C06 — Monotone parameter effect on a feasible interval family

MATHEMATICAL / ECONOMIC INTENT:
  The family `m ↦ Icc 0 m` is monotone with respect to inclusion.
VARIABLE DOMAINS: `m₁ m₂ : ℝ`.
ASSUMPTIONS: `m₁ ≤ m₂`.
FORMAL LEAN STATEMENT: `resourceInterval m₁ ⊆ resourceInterval m₂`.
PROOF ARCHITECTURE: C01.
KEY LEAN/MATHLIB MECHANISM: `Icc_subset_Icc`.
EDGE CASE: same as C01.
SEMANTIC FAITHFULNESS AUDIT:
  Monotone correspondence of feasible sets ≠ monotone selection.
-/
theorem C06_resource_family_monotone {m₁ m₂ : ℝ} (h : m₁ ≤ m₂) :
    resourceInterval m₁ ⊆ resourceInterval m₂ :=
  C01_resource_bound_expands h

/-!
## Case C07 — Raising both prices weakly shrinks the budget set

MATHEMATICAL / ECONOMIC INTENT:
  If prices rise coordinatewise and goods are constrained to be nonnegative,
  the budget set shrinks.
VARIABLE DOMAINS: prices and income in `ℝ`.
ASSUMPTIONS: `p₁ ≤ p₁'`, `p₂ ≤ p₂'`.
FORMAL LEAN STATEMENT: `budgetSet p₁' p₂' m ⊆ budgetSet p₁ p₂ m`.
PROOF ARCHITECTURE: expenditure at lower prices is smaller for nonnegative
  bundles.
KEY LEAN/MATHLIB MECHANISM: `mul_le_mul_of_nonneg_right`.
EDGE CASE: if a coordinate is zero, that price can change freely without
  affecting that bundle. The set inclusion still holds.
SEMANTIC FAITHFULNESS AUDIT:
  Shrinkage is weak. Equality can hold, for example if `m < 0` and prices stay
  nonnegative, both sets empty.
-/
theorem C07_higher_prices_shrink {p₁ p₁' p₂ p₂' m : ℝ}
    (hp₁ : p₁ ≤ p₁') (hp₂ : p₂ ≤ p₂') :
    budgetSet p₁' p₂' m ⊆ budgetSet p₁ p₂ m := by
  intro xy h
  refine ⟨h.1, h.2.1, ?_⟩
  have h1 : p₁ * xy.1 ≤ p₁' * xy.1 := mul_le_mul_of_nonneg_right hp₁ h.1
  have h2 : p₂ * xy.2 ≤ p₂' * xy.2 := mul_le_mul_of_nonneg_right hp₂ h.2.1
  linarith [h.2.2]

end OptimizationEconomics

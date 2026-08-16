import OptimizationEconomics.Basic
import OptimizationEconomics.BudgetConstraints
import OptimizationEconomics.Monotonicity
import OptimizationEconomics.Optimization
import Mathlib.Tactic

/-!
# Utility-style models

MATHEMATICAL THEOREM versus ECONOMIC INTERPRETATION:
  A utility is a function `u : domain → ℝ`. Theorems below are about that
  function on an explicit set. They do not assert that `u` represents
  preference, that a consumer exists, or that observed choices maximize `u`.
-/

namespace OptimizationEconomics
open Set

/-!
## Case U01 — `u(x) = x` is strictly monotone

MATHEMATICAL THEOREM: `StrictMono (fun x : ℝ => x)`.
ECONOMIC INTERPRETATION (not a theorem): “more of the single good is better”.
VARIABLE DOMAINS: `ℝ`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: identity.
KEY LEAN/MATHLIB MECHANISM: `strictMono_id`.
EDGE CASE: none on `ℝ`.
SEMANTIC FAITHFULNESS AUDIT:
  The interpretation uses words the theorem does not contain.
-/
theorem U01_id_utility_strictMono : StrictMono (fun x : ℝ => x) :=
  fun _ _ h => h

/-!
## Case U02 — `u(x,y) = x + y` is monotone in each coordinate

MATHEMATICAL THEOREM: increasing one coordinate, holding the other fixed,
  weakly increases the sum.
ECONOMIC INTERPRETATION (not a theorem): “more of either good is better”.
VARIABLE DOMAINS: `x x' y y' : ℝ`.
ASSUMPTIONS: `x ≤ x'`, `y ≤ y'`.
FORMAL LEAN STATEMENT: `x + y ≤ x' + y'`.
PROOF ARCHITECTURE: `add_le_add`.
KEY LEAN/MATHLIB MECHANISM: ordered monoid.
EDGE CASE: the map is not strictly monotone on `ℝ × ℝ` in the product order
  unless both coordinates increase and at least one strictly; we do not claim
  `StrictMono` on the product.
SEMANTIC FAITHFULNESS AUDIT:
  Coordinatewise monotonicity ≠ unique demand.
-/
theorem U02_sum_mono {x x' y y' : ℝ} (hx : x ≤ x') (hy : y ≤ y') :
    x + y ≤ x' + y' :=
  add_le_add hx hy

theorem U02_sum_mono_left (y : ℝ) : Monotone (fun x : ℝ => x + y) :=
  monotone_id.add_const y

theorem U02_sum_mono_right (x : ℝ) : Monotone (fun y : ℝ => x + y) :=
  monotone_const.add monotone_id

/-!
## Case U03 — Weighted linear utility is monotone when weights are nonnegative

MATHEMATICAL THEOREM: if `0 ≤ w₁` and `0 ≤ w₂` then
  `x ≤ x'` and `y ≤ y'` imply `w₁ x + w₂ y ≤ w₁ x' + w₂ y'`.
ECONOMIC INTERPRETATION (not a theorem): nonnegative marginal utilities.
VARIABLE DOMAINS: weights and quantities in `ℝ`.
ASSUMPTIONS: nonnegative weights and coordinatewise increase.
PROOF ARCHITECTURE: two nonnegative scalings plus addition.
KEY LEAN/MATHLIB MECHANISM: `mul_le_mul_of_nonneg_left`.
EDGE CASE: a negative weight reverses that coordinate.
SEMANTIC FAITHFULNESS AUDIT:
  The theorem is silent about how weights are estimated or whether they are
  utilities at all.
-/
theorem U03_weighted_mono {w₁ w₂ x x' y y' : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hx : x ≤ x') (hy : y ≤ y') :
    weightedUtility w₁ w₂ x y ≤ weightedUtility w₁ w₂ x' y' := by
  unfold weightedUtility
  exact add_le_add (mul_le_mul_of_nonneg_left hx hw₁)
    (mul_le_mul_of_nonneg_left hy hw₂)

/-!
## Case U04 — Unique maximizer of `u(x) = x` on `[0, m]`

MATHEMATICAL THEOREM: if `0 ≤ m` then `m` is the unique maximizer of `id`
  on `Icc 0 m`.
ECONOMIC INTERPRETATION (not a theorem): the consumer spends the entire
  resource on the single good.
VARIABLE DOMAINS: `m x : ℝ`.
ASSUMPTIONS: `0 ≤ m`.
PROOF ARCHITECTURE: specialize Z01 with slope `1`.
KEY LEAN/MATHLIB MECHANISM: `IsMaxOn`, uniqueness via strict monotonicity.
EDGE CASE: if `m < 0` the feasible set is empty and existence fails.
SEMANTIC FAITHFULNESS AUDIT:
  Uniqueness uses strict monotonicity of `id`. A flat utility would not be
  unique.
-/
theorem U04_id_max_on_interval {m : ℝ} (hm : 0 ≤ m) :
    (m ∈ Icc (0 : ℝ) m) ∧ IsMaxOn (fun x : ℝ => x) (Icc 0 m) m := by
  refine ⟨right_mem_Icc.mpr hm, ?_⟩
  intro x hx
  exact hx.2

theorem U04_id_max_unique {m x : ℝ} (hm : 0 ≤ m)
    (hx : x ∈ Icc (0 : ℝ) m) (hmax : IsMaxOn (fun y : ℝ => y) (Icc 0 m) x) :
    x = m := by
  have hle : x ≤ m := hx.2
  have hge : m ≤ x := hmax (right_mem_Icc.mpr hm)
  exact le_antisymm hle hge

/-!
## Case U05 — Nonunique maximizers of `u(x,y) = x + y` on the unit simplex

MATHEMATICAL THEOREM: if `p₁ = p₂ = 1` and `m = 1`, every bundle
  `(t, 1 - t)` for `t ∈ [0, 1]` is feasible and attains utility `1`, which is
  maximal on the budget set.
ECONOMIC INTERPRETATION (not a theorem): perfect substitutes with equal prices
  have a whole segment of demand.
VARIABLE DOMAINS: `t : ℝ`.
ASSUMPTIONS: `t ∈ Icc 0 1`.
PROOF ARCHITECTURE:
  feasibility of the segment; any feasible bundle has `x + y ≤ 1`; so utility
  `1` is maximal; distinct `t` give distinct bundles.
KEY LEAN/MATHLIB MECHANISM: `IsMaxOn`, explicit parametrization.
EDGE CASE: uniqueness fails as soon as two distinct `t` are allowed.
SEMANTIC FAITHFULNESS AUDIT:
  Existence of a maximizer is true; uniqueness is false. An economic sentence
  that says “the consumer buys a unique bundle” is stronger than the math.
-/
theorem U05_simplex_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t, 1 - t) ∈ budgetSet 1 1 1 := by
  refine ⟨ht.1, sub_nonneg.mpr ht.2, ?_⟩
  simp

theorem U05_sum_le_one_on_budget {xy : ℝ × ℝ}
    (h : xy ∈ budgetSet 1 1 1) : xy.1 + xy.2 ≤ 1 := by
  have := h.2.2
  simpa using this

theorem U05_segment_is_max {t : ℝ} (_ht : t ∈ Icc (0 : ℝ) 1) :
    IsMaxOn (fun xy : ℝ × ℝ => xy.1 + xy.2) (budgetSet 1 1 1) (t, 1 - t) := by
  intro xy hxy
  have : xy.1 + xy.2 ≤ 1 := U05_sum_le_one_on_budget hxy
  simpa using this

theorem U05_two_distinct_maxima :
    let u := fun xy : ℝ × ℝ => xy.1 + xy.2
    (0, 1) ∈ budgetSet 1 1 1 ∧ (1, 0) ∈ budgetSet 1 1 1 ∧
      (0 : ℝ) ≠ 1 ∧
      IsMaxOn u (budgetSet 1 1 1) (0, 1) ∧
      IsMaxOn u (budgetSet 1 1 1) (1, 0) := by
  refine ⟨?_, ?_, one_ne_zero.symm, ?_, ?_⟩
  · simp
  · simp
  · simpa using U05_segment_is_max (left_mem_Icc.mpr zero_le_one)
  · simpa using U05_segment_is_max (right_mem_Icc.mpr zero_le_one)

/-!
## Case U06 — Corner maximizer when only the first good is valued

MATHEMATICAL THEOREM: if `0 < p₁`, `0 < p₂`, `0 ≤ m`, then
  `(m / p₁, 0)` maximizes `(x,y) ↦ x` on `budgetSet p₁ p₂ m`.
ECONOMIC INTERPRETATION (not a theorem): the consumer spends everything on
  the only valued good.
VARIABLE DOMAINS: prices, income, bundles in `ℝ`.
ASSUMPTIONS: positive prices, nonnegative income.
PROOF ARCHITECTURE:
  feasibility of the corner; any feasible `(x,y)` satisfies `p₁ x ≤ m`.
KEY LEAN/MATHLIB MECHANISM: `IsMaxOn`, `le_div_iff₀`.
EDGE CASE: if the second weight is also positive, this need not be unique
  (see U05).
SEMANTIC FAITHFULNESS AUDIT:
  The objective ignores `y`. That is a mathematical choice, not a claim that
  the second good is worthless in the world.
-/
theorem U06_corner_feasible {p₁ p₂ m : ℝ} (hp₁ : 0 < p₁) (hm : 0 ≤ m) :
    (m / p₁, (0 : ℝ)) ∈ budgetSet p₁ p₂ m := by
  refine ⟨div_nonneg hm hp₁.le, le_rfl, ?_⟩
  have : p₁ * (m / p₁) = m := mul_div_cancel₀ m hp₁.ne'
  simp [this]

theorem U06_corner_is_max {p₁ p₂ m : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (_hm : 0 ≤ m) :
    IsMaxOn (fun xy : ℝ × ℝ => xy.1) (budgetSet p₁ p₂ m) (m / p₁, 0) := by
  intro xy hxy
  have hexp := hxy.2.2
  have hy : 0 ≤ p₂ * xy.2 := mul_nonneg hp₂.le hxy.2.1
  have : p₁ * xy.1 ≤ m := le_trans (le_add_of_nonneg_right hy) hexp
  exact (le_div_iff₀ hp₁).mpr (by simpa [mul_comm] using this)

theorem U06_corner_unique {p₁ p₂ m : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hm : 0 ≤ m) {xy : ℝ × ℝ}
    (hxy : xy ∈ budgetSet p₁ p₂ m)
    (hmax : IsMaxOn (fun z : ℝ × ℝ => z.1) (budgetSet p₁ p₂ m) xy) :
    xy = (m / p₁, 0) := by
  have hxle : xy.1 ≤ m / p₁ := U06_corner_is_max hp₁ hp₂ hm hxy
  have hxge : m / p₁ ≤ xy.1 := hmax (U06_corner_feasible hp₁ hm)
  have hx : xy.1 = m / p₁ := le_antisymm hxle hxge
  have hexp := hxy.2.2
  have : p₁ * xy.1 + p₂ * xy.2 ≤ m := hexp
  have : p₁ * (m / p₁) + p₂ * xy.2 ≤ m := by simpa [hx] using this
  have : m + p₂ * xy.2 ≤ m := by
    simpa [mul_div_cancel₀ m hp₁.ne'] using this
  have hy0 : p₂ * xy.2 ≤ 0 := by linarith
  have hynn : 0 ≤ p₂ * xy.2 := mul_nonneg hp₂.le hxy.2.1
  have : p₂ * xy.2 = 0 := le_antisymm hy0 hynn
  have hy : xy.2 = 0 :=
    (mul_eq_zero.mp this).resolve_left hp₂.ne'
  ext
  · exact hx
  · exact hy

end OptimizationEconomics

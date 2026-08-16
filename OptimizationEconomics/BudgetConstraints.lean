import OptimizationEconomics.Basic
import OptimizationEconomics.Feasibility
import OptimizationEconomics.Inequalities
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-!
# Budget-constraint models

Model: `p₁ * x + p₂ * y ≤ m` with explicit sign assumptions. Theorems below
are implications of those inequalities. They are not empirical demand facts.
-/

namespace OptimizationEconomics
open Set

/-!
## Case B01 — Nonemptiness when income is nonnegative

MATHEMATICAL / ECONOMIC INTENT:
  The zero bundle is feasible whenever `0 ≤ m`, for any prices.
VARIABLE DOMAINS: `p₁ p₂ m : ℝ`.
ASSUMPTIONS: `0 ≤ m`.
FORMAL LEAN STATEMENT: `(0, 0) ∈ budgetSet p₁ p₂ m`.
PROOF ARCHITECTURE: `0 + 0 ≤ m`.
KEY LEAN/MATHLIB MECHANISM: `budgetSet`.
EDGE CASE: if both goods are required to be strictly positive, this witness
  fails.
SEMANTIC FAITHFULNESS AUDIT:
  Nonemptiness is existence of some feasible bundle, not existence of an
  interior bundle or of a utility maximizer.
-/
theorem B01_zero_bundle {p₁ p₂ m : ℝ} (hm : 0 ≤ m) :
    (0, 0) ∈ budgetSet p₁ p₂ m := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  simpa using hm

theorem B01_nonempty {p₁ p₂ m : ℝ} (hm : 0 ≤ m) :
    (budgetSet p₁ p₂ m).Nonempty :=
  ⟨(0, 0), B01_zero_bundle hm⟩

/-!
## Case B02 — Emptiness when income is negative and prices are nonnegative

MATHEMATICAL / ECONOMIC INTENT:
  Nonnegative goods and nonnegative prices cannot meet `m < 0`.
VARIABLE DOMAINS: `p₁ p₂ m : ℝ`.
ASSUMPTIONS: `0 ≤ p₁`, `0 ≤ p₂`, `m < 0`.
FORMAL LEAN STATEMENT: `budgetSet p₁ p₂ m = ∅`.
PROOF ARCHITECTURE: expenditure is nonnegative, hence cannot be `< 0`.
KEY LEAN/MATHLIB MECHANISM: `add_nonneg`, `mul_nonneg`.
EDGE CASE: a negative price restores nonemptiness by making some positive
  bundles cheap. See B06.
SEMANTIC FAITHFULNESS AUDIT:
  Emptiness uses both nonnegativity of goods and of prices. Drop either and
  the set may become nonempty.
-/
theorem B02_empty_neg_income {p₁ p₂ m : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hm : m < 0) :
    budgetSet p₁ p₂ m = ∅ := by
  ext xy
  constructor
  · intro h
    have hexp : 0 ≤ p₁ * xy.1 + p₂ * xy.2 :=
      add_nonneg (mul_nonneg hp₁ h.1) (mul_nonneg hp₂ h.2.1)
    exact (not_le.mpr (lt_of_lt_of_le hm hexp)).elim h.2.2
  · intro h
    exact h.elim

/-!
## Case B03 — Weak expansion of the budget set in income

MATHEMATICAL / ECONOMIC INTENT:
  Raising income from `m` to `m'` with `m ≤ m'` cannot remove a feasible bundle.
VARIABLE DOMAINS: `p₁ p₂ m m' : ℝ`.
ASSUMPTIONS: `m ≤ m'`.
FORMAL LEAN STATEMENT: `budgetSet p₁ p₂ m ⊆ budgetSet p₁ p₂ m'`.
PROOF ARCHITECTURE: transitivity of `≤` on the expenditure inequality.
KEY LEAN/MATHLIB MECHANISM: `Set.subset_def`.
EDGE CASE: the inclusion is weak. It can be equality, e.g. if both sets are
  empty or if both prices are zero and `0 ≤ m`.
SEMANTIC FAITHFULNESS AUDIT:
  This is not a strict expansion and not a demand change. It is a set inclusion.
-/
theorem B03_income_expands {p₁ p₂ m m' : ℝ} (hmm : m ≤ m') :
    budgetSet p₁ p₂ m ⊆ budgetSet p₁ p₂ m' := by
  intro xy h
  exact ⟨h.1, h.2.1, le_trans h.2.2 hmm⟩

/-!
## Case B04 — Higher prices make a fixed bundle harder to afford

MATHEMATICAL / ECONOMIC INTENT:
  For a nonnegative bundle, raising a price cannot make an unaffordable
  inequality become true; equivalently, affordability at the higher price
  implies affordability at the lower price.
VARIABLE DOMAINS: `p₁ p₁' p₂ m x y : ℝ`.
ASSUMPTIONS: `0 ≤ x`, `0 ≤ y`, `p₁ ≤ p₁'`, and the higher-price budget holds.
FORMAL LEAN STATEMENT: `Affordable p₁ p₂ m x y`.
PROOF ARCHITECTURE: `p₁ * x ≤ p₁' * x` by nonnegative right multiplication.
KEY LEAN/MATHLIB MECHANISM: `mul_le_mul_of_nonneg_right`.
EDGE CASE: if `x = 0`, the first price is irrelevant.
SEMANTIC FAITHFULNESS AUDIT:
  The theorem is about one fixed bundle. It is not a substitution-effect
  statement and does not mention choice.
-/
theorem B04_higher_price_still_affordable {p₁ p₁' p₂ m x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : p₁ ≤ p₁')
    (h : Affordable p₁' p₂ m x y) :
    Affordable p₁ p₂ m x y := by
  refine ⟨hx, hy, ?_⟩
  have : p₁ * x ≤ p₁' * x := mul_le_mul_of_nonneg_right hp hx
  linarith [h.2.2]

/-!
## Case B05 — Zero income and positive prices force the origin

MATHEMATICAL / ECONOMIC INTENT:
  If `m = 0` and both prices are positive, the only feasible bundle is `(0,0)`.
VARIABLE DOMAINS: `p₁ p₂ : ℝ`.
ASSUMPTIONS: `0 < p₁`, `0 < p₂`.
FORMAL LEAN STATEMENT: `budgetSet p₁ p₂ 0 = {(0, 0)}`.
PROOF ARCHITECTURE: nonnegative sum of nonnegative terms vanishes iff each
  term vanishes; positive prices force both coordinates to zero.
KEY LEAN/MATHLIB MECHANISM: `add_eq_zero_iff_of_nonneg`, `mul_eq_zero`.
EDGE CASE: a zero price on one good would allow any quantity of that good.
SEMANTIC FAITHFULNESS AUDIT:
  Uniqueness of the feasible bundle is not uniqueness of a utility maximizer;
  the feasible set is a singleton, so every objective is uniquely maximized.
-/
theorem B05_zero_income_singleton {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) :
    budgetSet p₁ p₂ 0 = {(0, 0)} := by
  ext xy
  constructor
  · intro h
    have hexp0 : p₁ * xy.1 + p₂ * xy.2 = 0 := by
      have hnn : 0 ≤ p₁ * xy.1 + p₂ * xy.2 :=
        add_nonneg (mul_nonneg hp₁.le h.1) (mul_nonneg hp₂.le h.2.1)
      exact le_antisymm h.2.2 hnn
    have h1 : p₁ * xy.1 = 0 :=
      (add_eq_zero_iff_of_nonneg
        (mul_nonneg hp₁.le h.1) (mul_nonneg hp₂.le h.2.1)).mp hexp0 |>.1
    have h2 : p₂ * xy.2 = 0 :=
      (add_eq_zero_iff_of_nonneg
        (mul_nonneg hp₁.le h.1) (mul_nonneg hp₂.le h.2.1)).mp hexp0 |>.2
    have hx : xy.1 = 0 := by
      have := mul_eq_zero.mp h1
      exact this.resolve_left hp₁.ne'
    have hy : xy.2 = 0 := by
      have := mul_eq_zero.mp h2
      exact this.resolve_left hp₂.ne'
    exact Prod.ext hx hy
  · rintro ⟨rfl⟩
    exact B01_zero_bundle le_rfl

/-!
## Case B06 — A negative price makes the budget unbounded in that good

MATHEMATICAL / ECONOMIC INTENT:
  If `p₁ < 0`, arbitrarily large nonnegative `x` remains affordable (take `y = 0`).
VARIABLE DOMAINS: `p₁ p₂ m : ℝ`.
ASSUMPTIONS: `p₁ < 0`.
FORMAL LEAN STATEMENT: for every `K` there is `x ≥ K` with `(x, 0)` feasible.
PROOF ARCHITECTURE: choose `x` at least `K`, at least `0`, and at least `m / p₁`,
  then use that dividing by a negative number flips the inequality.
KEY LEAN/MATHLIB MECHANISM: `div_le_iff_of_neg`.
EDGE CASE: this is why “price” in the economic reading is taken positive. The
  mathematics of a negative coefficient is a different feasible set.
SEMANTIC FAITHFULNESS AUDIT:
  The theorem does not say negative prices are impossible. It says they make
  this particular budget set unbounded above in the first coordinate.
-/
theorem B06_neg_price_unbounded {p₁ p₂ m : ℝ} (hp₁ : p₁ < 0) :
    ∀ K : ℝ, ∃ x : ℝ, K ≤ x ∧ (x, 0) ∈ budgetSet p₁ p₂ m := by
  intro K
  let x := max (max K 0) (m / p₁)
  refine ⟨x, le_trans (le_max_left K 0) (le_max_left _ _), ?_⟩
  refine ⟨le_trans (le_max_right K 0) (le_max_left _ _), le_rfl, ?_⟩
  have hx : m / p₁ ≤ x := le_max_right _ _
  have : p₁ * x ≤ m := by
    rw [mul_comm]
    exact (div_le_iff_of_neg hp₁).mp hx
  simpa using this

/-!
## Case B07 — Convexity of the two-good budget set

MATHEMATICAL / ECONOMIC INTENT:
  A budget set defined by linear inequalities is convex.
VARIABLE DOMAINS: `p₁ p₂ m : ℝ`.
ASSUMPTIONS: none. Convexity does not need positive prices.
FORMAL LEAN STATEMENT: `Convex ℝ (budgetSet p₁ p₂ m)`.
PROOF ARCHITECTURE: convex combination preserves nonnegativity and the linear
  inequality.
KEY LEAN/MATHLIB MECHANISM: `Convex`, scalar multiplication on `ℝ × ℝ`.
EDGE CASE: convexity is not compactness and does not give existence of maxima.
SEMANTIC FAITHFULNESS AUDIT:
  Convexity of the constraint set is not quasiconcavity of a utility.
-/
theorem B07_convex_budget (p₁ p₂ m : ℝ) : Convex ℝ (budgetSet p₁ p₂ m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · have : 0 ≤ a * x.1 + b * y.1 :=
      add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
    simpa [smul_eq_mul] using this
  · have : 0 ≤ a * x.2 + b * y.2 :=
      add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
    simpa [smul_eq_mul] using this
  · have hxexp := hx.2.2
    have hyexp := hy.2.2
    have : p₁ * (a * x.1 + b * y.1) + p₂ * (a * x.2 + b * y.2) ≤ m := by
      have hlin :
          p₁ * (a * x.1 + b * y.1) + p₂ * (a * x.2 + b * y.2) =
            a * (p₁ * x.1 + p₂ * x.2) + b * (p₁ * y.1 + p₂ * y.2) := by
        ring
      have hbound :
          a * (p₁ * x.1 + p₂ * x.2) + b * (p₁ * y.1 + p₂ * y.2) ≤ a * m + b * m :=
        add_le_add (mul_le_mul_of_nonneg_left hxexp ha)
          (mul_le_mul_of_nonneg_left hyexp hb)
      have habm : a * m + b * m = m := by
        calc
          a * m + b * m = (a + b) * m := by ring
          _ = 1 * m := by rw [hab]
          _ = m := one_mul m
      exact hlin ▸ habm ▸ hbound
    simpa [smul_eq_mul] using this

end OptimizationEconomics

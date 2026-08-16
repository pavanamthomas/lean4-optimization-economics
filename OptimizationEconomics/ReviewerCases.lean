import OptimizationEconomics.Basic
import OptimizationEconomics.BudgetConstraints
import OptimizationEconomics.ComparativeStatics
import OptimizationEconomics.ExistenceUniqueness
import OptimizationEconomics.Feasibility
import OptimizationEconomics.Inequalities
import OptimizationEconomics.Objectives
import OptimizationEconomics.Optimization
import OptimizationEconomics.ProductionCost
import OptimizationEconomics.Utility
import Mathlib.Tactic

/-!
# Semantic-review cases

Each case records a model intent, a defective candidate (in comments only),
the exact defect, a counterexample when practical, a corrected Lean statement,
and a compiling proof.

Defective formulas are not executable declarations.
-/

namespace OptimizationEconomics
open Set

/-!
## Reviewer R01 — omitted nonnegativity restriction

MODEL INTENT:
  Quantities are nonnegative, so a one-good budget is `0 ≤ x ∧ p * x ≤ m`.
DEFECTIVE FORMALIZATION (not executable):
  `theorem budget_nonempty (p m : ℝ) (hp : 0 < p) : {x | p * x ≤ m}.Nonempty`
  This drops `x ≥ 0`. It is true for a different set, by taking `x = m / p`,
  including when `m < 0` and that point is negative.
EXACT DEFECT:
  The stated feasible set is not the nonnegative budget set.
COUNTEREXAMPLE:
  `p = 1`, `m = -1`: the unrestricted half-space contains `-1`, while
  `budget1D 1 (-1) = ∅`.
CORRECTED STATEMENT: emptiness of the nonnegative budget when `m < 0 < p`,
  and nonemptiness of the unrestricted half-space whenever `p ≠ 0`.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  Nonnegativity is restored as an explicit conjunct of membership.
-/
theorem R01_unrestricted_halfspace_nonempty {p m : ℝ} (hp : p ≠ 0) :
    { x : ℝ | p * x ≤ m }.Nonempty :=
  ⟨m / p, by simp [mul_div_cancel₀ m hp]⟩

theorem R01_nonneg_budget_empty {p m : ℝ} (hp : 0 < p) (hm : m < 0) :
    budget1D p m = ∅ :=
  F08_empty_budget_neg_income hp hm

/-!
## Reviewer R02 — omitted positive-price assumption

MODEL INTENT:
  A price is a positive real, so no single price makes every nonnegative
  quantity affordable against a fixed income.
DEFECTIVE FORMALIZATION (not executable):
  `∃ p : ℝ, ∀ x : ℝ, 0 ≤ x → p * x ≤ m`
  True by taking `p = 0` (or `p < 0`).
EXACT DEFECT:
  The existential is allowed to range over non-positive prices.
COUNTEREXAMPLE:
  `p = 0` affords every `x` when `0 ≤ m` fails... actually `0 * x = 0 ≤ m`
  needs `0 ≤ m`. For any `m`, `p = min 0 m` can be arranged; simplest: `p = 0`
  works iff `0 ≤ m`. For a uniform counter-model, take `p` negative enough.
  The defective claim is still true for all `m` by `p = min 0 (m - 1)` wait:
  `p = -1` gives `-x ≤ m` for all `x ≥ 0` iff `0 ≤ m` (the worst case is `x = 0`).
  For all `m`, take `p = 0` only if `0 ≤ m`. Take a very negative `p`? Then
  `-|p| x ≤ m` for large `x` fails.
  The genuine witness that kills the economic reading is `p = 0` when `0 ≤ m`,
  or any `p ≤ 0` when `0 ≤ m`. The corrected theorem therefore assumes `0 < p`.
CORRECTED STATEMENT: no positive price affords every nonnegative quantity.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The quantifier on `p` is restricted to `0 < p`, matching “price”.
-/
theorem R02_no_positive_price_affords_all (m : ℝ) :
    ¬ ∃ p : ℝ, 0 < p ∧ ∀ x : ℝ, 0 ≤ x → p * x ≤ m := by
  rintro ⟨p, hp, h⟩
  let x := |m| / p + 1
  have hx : 0 ≤ x := add_nonneg (div_nonneg (abs_nonneg m) hp.le) zero_le_one
  have hx' : p * x ≤ m := h x hx
  have heq : p * (|m| / p + 1) = |m| + p := by field_simp
  have hsum : |m| + p ≤ m := by linarith
  have : |m| + p ≤ |m| := le_trans hsum (le_abs_self m)
  linarith

/-!
## Reviewer R03 — wrong variable domain (`ℕ` versus `ℝ`)

MODEL INTENT:
  If quantity is modeled as `ℕ`, nonnegativity is automatic. If it is modeled
  as `ℝ`, nonnegativity is an extra assumption.
DEFECTIVE FORMALIZATION (not executable):
  Transfer a theorem about `n : ℕ` to `x : ℝ` without adding `0 ≤ x`.
EXACT DEFECT:
  `ℕ` embeds into the nonnegative reals; `ℝ` does not.
COUNTEREXAMPLE:
  Every `n : ℕ` satisfies `0 ≤ (n : ℝ)`, but `-1 : ℝ` does not.
CORRECTED STATEMENT: the two domain facts, side by side.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  It makes the domain difference itself the theorem.
-/
theorem R03_nat_cast_nonneg (n : ℕ) : 0 ≤ (n : ℝ) :=
  Nat.cast_nonneg n

theorem R03_real_need_not_be_nonneg : ∃ x : ℝ, ¬ 0 ≤ x :=
  ⟨-1, by norm_num⟩

/-!
## Reviewer R04 — reversed inequality

MODEL INTENT:
  Higher prices shrink, not expand, the nonnegative budget set.
DEFECTIVE FORMALIZATION (not executable):
  `p ≤ p' → budgetSet p' q m ⊆ budgetSet p q m` written in the opposite
  inclusion.
EXACT DEFECT:
  Inclusion direction reversed.
COUNTEREXAMPLE:
  `p = 1`, `p' = 2`, `q = 1`, `m = 1`, bundle `(1, 0)` is in the cheaper
  budget and not in the dearer one.
CORRECTED STATEMENT: C07 / the concrete witness below.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The inclusion matches “more expensive ⇒ fewer feasible nonnegative bundles”.
-/
theorem R04_cheaper_allows_unit_bundle :
    (1, 0) ∈ budgetSet 1 1 1 ∧ (1, 0) ∉ budgetSet 2 1 1 := by
  constructor
  · exact ⟨by norm_num, by norm_num, by norm_num⟩
  · intro h
    have : (2 : ℝ) * 1 + 1 * 0 ≤ 1 := h.2.2
    norm_num at this

theorem R04_higher_prices_shrink {p₁ p₁' p₂ p₂' m : ℝ}
    (hp₁ : p₁ ≤ p₁') (hp₂ : p₂ ≤ p₂') :
    budgetSet p₁' p₂' m ⊆ budgetSet p₁ p₂ m :=
  C07_higher_prices_shrink hp₁ hp₂

/-!
## Reviewer R05 — incorrect quantifier order

MODEL INTENT:
  “There is a price at which every nonnegative bundle of size at most `1`
  is affordable” is different from “every such bundle has some price that
  affords it”.
DEFECTIVE FORMALIZATION (not executable):
  Treat `∀ x, ∃ p, 0 < p ∧ p * x ≤ m` as equivalent to
  `∃ p, 0 < p ∧ ∀ x, p * x ≤ m`.
EXACT DEFECT:
  `∃ ∀` is strictly stronger than `∀ ∃` in general.
COUNTEREXAMPLE:
  For `m = 1`, every nonnegative `x` has some positive price with `p * x ≤ 1`
  (take `p` small), but no single positive `p` works for all `x` (R02).
CORRECTED STATEMENT: the `∀ ∃` claim, with an explicit small price.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  Quantifier order is written exactly.
-/
theorem R05_forall_exists_small_price (m : ℝ) (hm : 0 < m) :
    ∀ x : ℝ, 0 ≤ x → ∃ p : ℝ, 0 < p ∧ p * x ≤ m := by
  intro x hx
  by_cases hxz : x = 0
  · exact ⟨1, one_pos, by simp [hxz, hm.le]⟩
  · refine ⟨m / (x + 1), div_pos hm (add_pos_of_nonneg_of_pos hx one_pos), ?_⟩
    have hx1 : 0 < x + 1 := add_pos_of_nonneg_of_pos hx one_pos
    have : m / (x + 1) * x ≤ m / (x + 1) * (x + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hm.le hx1.le)
    have hcancel : m / (x + 1) * (x + 1) = m := div_mul_cancel₀ m hx1.ne'
    linarith

/-!
## Reviewer R06 — accidental universal claim

MODEL INTENT:
  Optimality of every feasible bundle holds for a constant objective, not for
  `u(x) = x`.
DEFECTIVE FORMALIZATION (not executable):
  `∀ x ∈ Icc 0 m, IsMaxOn id (Icc 0 m) x`.
EXACT DEFECT:
  A property of one maximizer is written as a property of all feasible points.
COUNTEREXAMPLE:
  `m = 1`, `x = 0`: `id 1 = 1 ≰ 0 = id 0`.
CORRECTED STATEMENT: the universal claim is false for `id` when `0 < m`,
  and true for a constant.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The universal quantifier is used only where it is justified.
-/
theorem R06_id_not_max_everywhere {m : ℝ} (hm : 0 < m) :
    ¬ ∀ x ∈ Icc (0 : ℝ) m, IsMaxOn (fun y : ℝ => y) (Icc 0 m) x := by
  intro h
  have h0 := h 0 ⟨le_rfl, hm.le⟩
  have : m ≤ 0 := h0 (right_mem_Icc.mpr hm.le)
  exact not_le_of_gt hm this

theorem R06_constant_is_max_everywhere {m c : ℝ} (hm : 0 ≤ m) :
    ∀ x ∈ Icc (0 : ℝ) m, IsMaxOn (fun _ : ℝ => c) (Icc 0 m) x :=
  Z05_constant_max_everywhere hm

/-!
## Reviewer R07 — existence without feasibility

MODEL INTENT:
  A maximizer must lie in the feasible set.
DEFECTIVE FORMALIZATION (not executable):
  `∃ x, IsMaxOn f ∅ x`  -- true for every `x` because the universal quantifier
  in `IsMaxOn` ranges over no points, but `x` need not be feasible.
EXACT DEFECT:
  `IsMaxOn` does not include `x ∈ s`.
COUNTEREXAMPLE:
  `IsMaxOn id ∅ 0` holds, yet `0 ∉ ∅`.
CORRECTED STATEMENT: existence is `∃ x, x ∈ s ∧ IsMaxOn f s x`, which fails
  on `∅`.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  Feasibility is a conjunct, not an ambient convention.
-/
theorem R07_isMaxOn_empty_vacuous (f : ℝ → ℝ) (x : ℝ) : IsMaxOn f ∅ x :=
  fun _ hy => hy.elim

theorem R07_no_feasible_maximizer_on_empty (f : ℝ → ℝ) :
    ¬ ∃ x, x ∈ (∅ : Set ℝ) ∧ IsMaxOn f ∅ x :=
  E06_no_max_on_empty f

/-!
## Reviewer R08 — uniqueness without sufficient conditions

MODEL INTENT:
  Uniqueness of a maximizer needs a strict condition (strict monotonicity,
  strict convexity, a singleton feasible set, ...).
DEFECTIVE FORMALIZATION (not executable):
  From `∃ x ∈ Icc u v, IsMaxOn f (Icc u v) x` infer `∃! x, ...`.
EXACT DEFECT:
  Existence does not imply uniqueness.
COUNTEREXAMPLE:
  Constant objective on `Icc 0 1`.
CORRECTED STATEMENT: E07 / Z05, and the strict-mono uniqueness E04.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  Uniqueness is a separate theorem with a strict hypothesis.
-/
theorem R08_existence_not_uniqueness :
    (∃ x ∈ Icc (0 : ℝ) 1, IsMaxOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) x) ∧
      ¬ ∃! x, x ∈ Icc (0 : ℝ) 1 ∧
          IsMaxOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) x := by
  constructor
  · exact ⟨0, left_mem_Icc.mpr zero_le_one,
      Z05_constant_max_everywhere zero_le_one 0 (left_mem_Icc.mpr zero_le_one)⟩
  · intro h
    obtain ⟨x, hx, huniq⟩ := h
    have h0 := huniq 0 ⟨left_mem_Icc.mpr zero_le_one,
      Z05_constant_max_everywhere zero_le_one 0 (left_mem_Icc.mpr zero_le_one)⟩
    have h1 := huniq 1 ⟨right_mem_Icc.mpr zero_le_one,
      Z05_constant_max_everywhere zero_le_one 1 (right_mem_Icc.mpr zero_le_one)⟩
    exact zero_ne_one (h0.trans h1.symm)

/-!
## Reviewer R09 — maximizing over an unbounded domain

MODEL INTENT:
  Continuity of `id` does not give a maximum on `Ici 0`.
DEFECTIVE FORMALIZATION (not executable):
  `Continuous id → ∃ x ∈ Ici 0, IsMaxOn id (Ici 0) x`.
EXACT DEFECT:
  Compactness / boundedness omitted.
COUNTEREXAMPLE: E05.
CORRECTED STATEMENT: no maximizer on the ray; maximizer on each compact
  interval.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The domain is named. The compact case is a different theorem.
-/
theorem R09_no_max_unbounded : ¬ ∃ x ∈ Ici (0 : ℝ), IsMaxOn id (Ici 0) x :=
  E05_id_no_max_on_Ici

theorem R09_max_on_compact {m : ℝ} (hm : 0 ≤ m) :
    ∃ x ∈ Icc (0 : ℝ) m, IsMaxOn id (Icc 0 m) x :=
  ⟨m, right_mem_Icc.mpr hm, fun _ hx => hx.2⟩

/-!
## Reviewer R10 — economically described claim stronger than its mathematics

MODEL INTENT:
  `u(x,y) = x + y` on the budget `x + y ≤ 1`, `x,y ≥ 0` has maximizers, but
  not a unique maximizer.
DEFECTIVE FORMALIZATION (not executable):
  An English sentence “the consumer buys the unique optimal bundle”.
EXACT DEFECT:
  Uniqueness is not a consequence of the model.
COUNTEREXAMPLE: `(0,1)` and `(1,0)` are distinct maximizers (U05).
CORRECTED STATEMENT: existence of at least two maximizers.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The mathematics is existence without uniqueness. The stronger English claim
  is rejected.
-/
theorem R10_perfect_substitutes_not_unique :
    let u := fun xy : ℝ × ℝ => xy.1 + xy.2
    (0, 1) ∈ budgetSet 1 1 1 ∧ (1, 0) ∈ budgetSet 1 1 1 ∧
      IsMaxOn u (budgetSet 1 1 1) (0, 1) ∧
      IsMaxOn u (budgetSet 1 1 1) (1, 0) ∧
      (0, 1) ≠ (1, 0) := by
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · simp
  · simp
  · simpa using U05_segment_is_max (left_mem_Icc.mpr zero_le_one)
  · simpa using U05_segment_is_max (right_mem_Icc.mpr zero_le_one)

/-!
## Reviewer R11 — division without a nonzero assumption

MODEL INTENT:
  Average cost `totalCost / q` is a real number only when `q ≠ 0`.
DEFECTIVE FORMALIZATION (not executable):
  `averageCost (linearCost w α 0) 0 = w / α`.
EXACT DEFECT:
  Division by zero.
COUNTEREXAMPLE:
  The defining expression `0 / 0` is not the intended real identity.
CORRECTED STATEMENT: P04 with `q ≠ 0` and `α ≠ 0`.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The domain of average cost is the nonzero outputs.
-/
theorem R11_average_cost_needs_nonzero {w α q : ℝ} (hα : α ≠ 0) (hq : q ≠ 0) :
    averageCost (linearCost w α q) q = w / α :=
  P04_average_cost_linear hα hq

/-!
## Reviewer R12 — boundary case ignored

MODEL INTENT:
  Closed intervals contain their endpoints; open intervals do not.
DEFECTIVE FORMALIZATION (not executable):
  Transfer a maximizer `v` of `id` from `Icc u v` to `Ioo u v`.
EXACT DEFECT:
  `v ∉ Ioo u v`.
COUNTEREXAMPLE: F04.
CORRECTED STATEMENT: right endpoint is feasible in the closed interval and
  infeasible in the open interval.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The feasible set actually used is `Icc`, where the endpoint belongs.
-/
theorem R12_closed_contains_right {u v : ℝ} (huv : u ≤ v) : v ∈ Icc u v :=
  right_mem_Icc.mpr huv

theorem R12_open_misses_right {u v : ℝ} : v ∉ Ioo u v :=
  F04_right_endpoint_not_open

/-!
## Reviewer R13 — feasible-set expansion incorrectly stated as strict

MODEL INTENT:
  More income weakly expands the budget set. Strict expansion needs extra
  hypotheses.
DEFECTIVE FORMALIZATION (not executable):
  `m < m' → budgetSet 0 0 m ⊂ budgetSet 0 0 m'`.
EXACT DEFECT:
  With zero prices and `0 ≤ m`, both sets equal the nonnegative quadrant.
COUNTEREXAMPLE: `m = 1`, `m' = 2`, `p₁ = p₂ = 0`.
CORRECTED STATEMENT: weak expansion always; equality in the zero-price case.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The inclusion strength matches the algebra.
-/
theorem R13_zero_price_no_strict_expansion {m m' : ℝ}
    (hm : 0 ≤ m) (hm' : 0 ≤ m') :
    budgetSet 0 0 m = { xy : ℝ × ℝ | 0 ≤ xy.1 ∧ 0 ≤ xy.2 } ∧
      budgetSet 0 0 m' = { xy : ℝ × ℝ | 0 ≤ xy.1 ∧ 0 ≤ xy.2 } := by
  constructor
  · ext xy
    simp [budgetSet, hm]
  · ext xy
    simp [budgetSet, hm']

theorem R13_weak_expansion {p₁ p₂ m m' : ℝ} (h : m ≤ m') :
    budgetSet p₁ p₂ m ⊆ budgetSet p₁ p₂ m' :=
  B03_income_expands h

/-!
## Reviewer R14 — parameter direction reversed

MODEL INTENT:
  A larger positive slope raises, not lowers, the affine objective at a
  positive point.
DEFECTIVE FORMALIZATION (not executable):
  `a < a' → affineObj a' b x < affineObj a b x` with `0 < x`.
EXACT DEFECT:
  Comparison reversed.
COUNTEREXAMPLE: `a = 1`, `a' = 2`, `b = 0`, `x = 1` gives `2 ≮ 1`.
CORRECTED STATEMENT: C05.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  The inequality direction follows `a < a'` after multiplying by `x > 0`.
-/
theorem R14_slope_direction {a a' b x : ℝ} (hx : 0 < x) (haa : a < a') :
    affineObj a b x < affineObj a' b x :=
  C05_affine_slope_increases_value hx haa

/-!
## Reviewer R15 — weak versus strict inequality

MODEL INTENT:
  `x ≤ y` and a monotone `f` give `f x ≤ f y`, not `f x < f y`.
DEFECTIVE FORMALIZATION (not executable):
  `Monotone f → x < y → f x < f y`.
EXACT DEFECT:
  Weak monotonicity is used as if it were strict.
COUNTEREXAMPLE: a constant function.
CORRECTED STATEMENT: M05, and the strict-mono lemma M01.
WHY THE CORRECTION PRESERVES THE INTENDED MODEL:
  Strict conclusions require `StrictMono` (or an equivalent strict hypothesis).
-/
theorem R15_monotone_not_strict :
    Monotone (fun _ : ℝ => (0 : ℝ)) ∧
      ¬ ∀ {x y : ℝ}, x < y → (0 : ℝ) < 0 :=
  ⟨fun _ _ _ => le_rfl, fun h => lt_irrefl _ (h (show (0 : ℝ) < 1 from one_pos))⟩

theorem R15_strictMono_gives_strict {α : ℝ} (hα : 0 < α) {x y : ℝ}
    (hxy : x < y) : α * x < α * y :=
  M01_pos_scale_strictMono hα hxy

end OptimizationEconomics

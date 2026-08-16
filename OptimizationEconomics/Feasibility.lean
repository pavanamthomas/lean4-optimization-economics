import OptimizationEconomics.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

/-!
# Feasibility and constraint sets

FOUNDATIONAL through INTERMEDIATE cases showing that a feasible set is a
mathematical subset of an explicit domain, not an informal list of “allowed
choices”. Hidden domain assumptions change emptiness, membership, and
optimization statements.
-/

namespace OptimizationEconomics
open Set

/-!
## Case F01 — Nonnegativity membership

MATHEMATICAL / ECONOMIC INTENT:
  A quantity constraint `x ≥ 0` is a set-membership statement on `ℝ`.
VARIABLE DOMAINS: `x : ℝ`.
ASSUMPTIONS: none beyond the real order.
FORMAL LEAN STATEMENT: `x ∈ Ici 0 ↔ 0 ≤ x`.
PROOF ARCHITECTURE: unfolding `Ici`.
KEY LEAN/MATHLIB MECHANISM: `Set.mem_Ici`.
EDGE CASE: `x = 0` is feasible under nonnegativity and infeasible under positivity.
SEMANTIC FAITHFULNESS AUDIT:
  This is only membership. It does not say that nonnegative quantities are
  “goods” or that an agent can obtain them.
-/
@[simp] theorem F01_nonneg_mem (x : ℝ) : x ∈ Ici (0 : ℝ) ↔ 0 ≤ x :=
  mem_Ici

/-!
## Case F02 — Positivity is a strictly smaller constraint

MATHEMATICAL / ECONOMIC INTENT:
  Strict positivity excludes the boundary `0`.
VARIABLE DOMAINS: `x : ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `Ioi 0 ⊂ Ici 0` and `0 ∉ Ioi 0`.
PROOF ARCHITECTURE: subset of closures of the order, plus a concrete witness.
KEY LEAN/MATHLIB MECHANISM: `Set.ssubset_iff_subset_ne`, `mem_Ioi`.
EDGE CASE: the origin is the entire difference between the two sets in this
  one-dimensional model.
SEMANTIC FAITHFULNESS AUDIT:
  Switching `≥ 0` to `> 0` is a different feasible set. Later budget
  nonemptiness proofs that use the zero bundle fail if positivity is required
  of every coordinate.
-/
theorem F02_pos_ssubset_nonneg : Ioi (0 : ℝ) ⊂ Ici (0 : ℝ) := by
  refine ssubset_iff_subset_ne.mpr ⟨Ioi_subset_Ici_self, ?_⟩
  intro h
  have hz : (0 : ℝ) ∈ Ici 0 := by simp
  have : (0 : ℝ) ∈ Ioi 0 := h.symm ▸ hz
  exact lt_irrefl (0 : ℝ) (mem_Ioi.mp this)

theorem F02_zero_not_pos : (0 : ℝ) ∉ Ioi 0 :=
  fun h => lt_irrefl (0 : ℝ) (mem_Ioi.mp h)

/-!
## Case F03 — Closed interval membership

MATHEMATICAL / ECONOMIC INTENT:
  A closed resource bound `[0, m]` is the conjunction of two inequalities.
VARIABLE DOMAINS: `m x : ℝ`.
ASSUMPTIONS: none in the membership lemma; nonemptiness needs `0 ≤ m`.
FORMAL LEAN STATEMENT: `x ∈ Icc 0 m ↔ 0 ≤ x ∧ x ≤ m`.
PROOF ARCHITECTURE: `mem_Icc`.
KEY LEAN/MATHLIB MECHANISM: `Set.Icc`.
EDGE CASE: if `m < 0` the set is empty even though the notation looks like an
  “interval of resources”.
SEMANTIC FAITHFULNESS AUDIT:
  Writing `[0, m]` without `0 ≤ m` silently changes every existence claim.
-/
theorem F03_interval_mem (m x : ℝ) :
    x ∈ Icc (0 : ℝ) m ↔ 0 ≤ x ∧ x ≤ m :=
  mem_Icc

/-!
## Case F04 — Boundary of closed versus open intervals

MATHEMATICAL / ECONOMIC INTENT:
  Endpoints are feasible on a closed interval and infeasible on the open one.
VARIABLE DOMAINS: `a b : ℝ` with `a < b`.
ASSUMPTIONS: `a < b` so both sets are nonempty and the endpoints are distinct.
FORMAL LEAN STATEMENT: `a ∈ Icc a b`, `a ∉ Ioo a b`, and likewise at `b`.
PROOF ARCHITECTURE: unfold interval membership and use `lt_irrefl`.
KEY LEAN/MATHLIB MECHANISM: `left_mem_Icc`, `mem_Ioo`.
EDGE CASE: an “interior optimum” statement cannot place the solution at `a` or
  `b` if the domain is `Ioo a b`.
SEMANTIC FAITHFULNESS AUDIT:
  Closed/open is not stylistic. It decides whether boundary optima exist.
-/
theorem F04_left_endpoint_closed {a b : ℝ} (hab : a ≤ b) : a ∈ Icc a b :=
  left_mem_Icc.mpr hab

theorem F04_left_endpoint_not_open {a b : ℝ} : a ∉ Ioo a b := by
  intro h
  exact lt_irrefl a h.1

theorem F04_right_endpoint_closed {a b : ℝ} (hab : a ≤ b) : b ∈ Icc a b :=
  right_mem_Icc.mpr hab

theorem F04_right_endpoint_not_open {a b : ℝ} : b ∉ Ioo a b := by
  intro h
  exact lt_irrefl b h.2

/-!
## Case F05 — Linear inequality membership

MATHEMATICAL / ECONOMIC INTENT:
  A one-price budget constraint is the half-space `p * x ≤ m` intersected with
  `x ≥ 0`.
VARIABLE DOMAINS: `p m x : ℝ`.
ASSUMPTIONS: none for membership; sign of `p` and `m` control emptiness.
FORMAL LEAN STATEMENT: `x ∈ budget1D p m ↔ 0 ≤ x ∧ p * x ≤ m`.
PROOF ARCHITECTURE: definitional.
KEY LEAN/MATHLIB MECHANISM: custom set `budget1D`.
EDGE CASE: if `p < 0`, large positive `x` becomes cheaper, so the “budget”
  is unbounded. That is a different model.
SEMANTIC FAITHFULNESS AUDIT:
  The predicate does not mention prices being positive. Later theorems add
  `0 < p` when the economic reading requires it.
-/
theorem F05_linear_constraint_mem (p m x : ℝ) :
    x ∈ budget1D p m ↔ 0 ≤ x ∧ p * x ≤ m :=
  mem_budget1D

/-!
## Case F06 — Empty versus nonempty closed intervals

MATHEMATICAL / ECONOMIC INTENT:
  `Icc a b` is nonempty if and only if `a ≤ b`.
VARIABLE DOMAINS: `a b : ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `(Icc a b).Nonempty ↔ a ≤ b`.
PROOF ARCHITECTURE: mathlib interval API.
KEY LEAN/MATHLIB MECHANISM: `Set.nonempty_Icc`.
EDGE CASE: `Icc 1 0 = ∅`, so every “there exists a feasible point” claim is
  false on that set.
SEMANTIC FAITHFULNESS AUDIT:
  Existence of a choice is a theorem about the set, not a default.
-/
theorem F06_Icc_nonempty_iff (a b : ℝ) :
    (Icc a b).Nonempty ↔ a ≤ b :=
  nonempty_Icc

theorem F06_Icc_empty_of_lt {a b : ℝ} (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty (not_le.mpr h)

/-!
## Case F07 — Zero bundle witnesses one-dimensional feasibility

MATHEMATICAL / ECONOMIC INTENT:
  If income is nonnegative and the good is nonnegative, the zero bundle is
  feasible regardless of the price sign.
VARIABLE DOMAINS: `p m : ℝ`.
ASSUMPTIONS: `0 ≤ m`.
FORMAL LEAN STATEMENT: `0 ∈ budget1D p m`.
PROOF ARCHITECTURE: `p * 0 = 0 ≤ m`.
KEY LEAN/MATHLIB MECHANISM: `mul_zero`.
EDGE CASE: if the model required `0 < x`, this witness would disappear.
SEMANTIC FAITHFULNESS AUDIT:
  Nonemptiness here uses the zero bundle. It is not a statement about
  interior demand.
-/
theorem F07_zero_bundle_feasible {p m : ℝ} (hm : 0 ≤ m) :
    (0 : ℝ) ∈ budget1D p m := by
  refine ⟨le_rfl, ?_⟩
  simpa using hm

/-!
## Case F08 — Positive prices and negative income make an empty budget

MATHEMATICAL / ECONOMIC INTENT:
  Nonnegative quantities and a positive price cannot meet a negative income.
VARIABLE DOMAINS: `p m x : ℝ`.
ASSUMPTIONS: `0 < p`, `m < 0`, `0 ≤ x`.
FORMAL LEAN STATEMENT: `budget1D p m = ∅`.
PROOF ARCHITECTURE: `p * x ≥ 0 > m` for `x ≥ 0`.
KEY LEAN/MATHLIB MECHANISM: `mul_nonneg`, `not_le.mpr`.
EDGE CASE: dropping `x ≥ 0` restores nonemptiness by allowing negative `x`.
SEMANTIC FAITHFULNESS AUDIT:
  Emptiness is a joint consequence of the sign assumptions. Remove any one of
  them and the statement can fail.
-/
theorem F08_empty_budget_neg_income {p m : ℝ} (hp : 0 < p) (hm : m < 0) :
    budget1D p m = ∅ := by
  ext x
  constructor
  · intro hx
    have hpx : 0 ≤ p * x := mul_nonneg hp.le hx.1
    exact (not_le.mpr (lt_of_lt_of_le hm hpx)).elim hx.2
  · intro hx
    exact hx.elim

/-!
## Case F09 — Two-good feasible-set membership

MATHEMATICAL / ECONOMIC INTENT:
  A two-good budget is three inequalities, not a single informal “can buy”.
VARIABLE DOMAINS: `p₁ p₂ m x y : ℝ`.
ASSUMPTIONS: none for the membership lemma.
FORMAL LEAN STATEMENT: `Affordable p₁ p₂ m x y ↔ 0 ≤ x ∧ 0 ≤ y ∧ p₁*x+p₂*y ≤ m`.
PROOF ARCHITECTURE: definitional.
KEY LEAN/MATHLIB MECHANISM: `Affordable` / `budgetSet`.
EDGE CASE: omitting either nonnegativity conjunct yields a different set.
SEMANTIC FAITHFULNESS AUDIT:
  Affordability is exactly this predicate. No preference or choice is implied.
-/
theorem F09_two_good_membership (p₁ p₂ m x y : ℝ) :
    Affordable p₁ p₂ m x y ↔ 0 ≤ x ∧ 0 ≤ y ∧ p₁ * x + p₂ * y ≤ m :=
  affordable_iff

end OptimizationEconomics

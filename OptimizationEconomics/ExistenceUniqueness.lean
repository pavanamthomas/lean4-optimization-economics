import OptimizationEconomics.Basic
import OptimizationEconomics.Optimization
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Existence and uniqueness

Separate existence, uniqueness, and existence+uniqueness. Defective candidate
formulations that drop compactness, nonemptiness, or strictness are recorded
only as comments in `ReviewerCases.lean`, not as executable declarations.
-/

namespace OptimizationEconomics
open Set

/-!
## Case E01 — Extreme value theorem on a nonempty compact interval

MATHEMATICAL / ECONOMIC INTENT:
  A continuous real function on `Icc a b` with `a ≤ b` attains a maximum.
VARIABLE DOMAINS: `a b : ℝ`, `f : ℝ → ℝ`.
ASSUMPTIONS: `a ≤ b`, `ContinuousOn f (Icc a b)`.
FORMAL LEAN STATEMENT: `∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x`.
PROOF ARCHITECTURE: `isCompact_Icc.exists_isMaxOn`.
KEY LEAN/MATHLIB MECHANISM: `IsCompact.exists_isMaxOn`, `isCompact_Icc`.
EDGE CASE: if `b < a` the set is empty and existence fails. If `f` is not
  continuous, existence can fail (e.g. a jump omitted from this file).
SEMANTIC FAITHFULNESS AUDIT:
  The theorem gives existence, not uniqueness, and not a formula for the
  maximizer.
-/
theorem E01_exists_max_continuous_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x :=
  isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf

theorem E01_exists_min_continuous_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ∃ x ∈ Icc a b, IsMinOn f (Icc a b) x :=
  isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf

/-!
## Case E02 — Compactness of a closed real interval

MATHEMATICAL / ECONOMIC INTENT:
  `Icc a b` is compact in `ℝ`.
VARIABLE DOMAINS: `a b : ℝ`.
ASSUMPTIONS: none. If `b < a` the set is empty, and the empty set is compact.
FORMAL LEAN STATEMENT: `IsCompact (Icc a b)`.
PROOF ARCHITECTURE: `isCompact_Icc`.
KEY LEAN/MATHLIB MECHANISM: `CompactIccSpace`.
EDGE CASE: compactness of the empty set does not yield a maximizer.
SEMANTIC FAITHFULNESS AUDIT:
  Compactness is a topological hypothesis used by E01. It is not an economic
  regularity condition by itself.
-/
theorem E02_isCompact_Icc (a b : ℝ) : IsCompact (Icc a b) :=
  isCompact_Icc

/-!
## Case E03 — Continuous affine maps attain a maximum on `[a,b]`

MATHEMATICAL / ECONOMIC INTENT:
  Specialize E01 to `affineObj a b`, which is continuous.
VARIABLE DOMAINS: `a b u v : ℝ`.
ASSUMPTIONS: `u ≤ v`.
FORMAL LEAN STATEMENT: existence of a maximizer of `affineObj a b` on `Icc u v`.
PROOF ARCHITECTURE: continuity of addition and multiplication, then E01.
KEY LEAN/MATHLIB MECHANISM: `continuous_add`, `continuous_const.mul`,
  `Continuous.continuousOn`.
EDGE CASE: existence does not name the maximizer; Z01 names it when `0 < a`.
SEMANTIC FAITHFULNESS AUDIT:
  Continuity + compactness + nonemptiness ⇒ existence. Slope sign is not
  required for existence.
-/
theorem E03_affine_continuous (a b : ℝ) : Continuous (affineObj a b) := by
  unfold affineObj
  exact (continuous_const.mul continuous_id).add continuous_const

theorem E03_affine_exists_max {a b u v : ℝ} (huv : u ≤ v) :
    ∃ x ∈ Icc u v, IsMaxOn (affineObj a b) (Icc u v) x :=
  E01_exists_max_continuous_Icc huv (E03_affine_continuous a b).continuousOn

/-!
## Case E04 — Existence plus uniqueness for a strictly increasing continuous map

MATHEMATICAL / ECONOMIC INTENT:
  On `Icc u v`, a strictly monotone objective has a unique maximizer, namely
  `v`.
VARIABLE DOMAINS: `u v : ℝ`, `f : ℝ → ℝ`.
ASSUMPTIONS: `u ≤ v`, `StrictMono f`. Continuity is unused because the
  maximizer is identified directly.
FORMAL LEAN STATEMENT: `∃! x, x ∈ Icc u v ∧ IsMaxOn f (Icc u v) x`.
PROOF ARCHITECTURE: `v` works; injectivity of `f` gives uniqueness.
KEY LEAN/MATHLIB MECHANISM: `ExistsUnique`, `StrictMono.injective`.
EDGE CASE: dropping `StrictMono` to `Monotone` loses uniqueness (constant).
SEMANTIC FAITHFULNESS AUDIT:
  Existence and uniqueness are proved together here because the candidate is
  explicit. E01 alone does not give uniqueness.
-/
theorem E04_unique_max_strictMono {u v : ℝ} (huv : u ≤ v) {f : ℝ → ℝ}
    (hf : StrictMono f) :
    ∃! x, x ∈ Icc u v ∧ IsMaxOn f (Icc u v) x := by
  refine ⟨v, ⟨right_mem_Icc.mpr huv, ?_⟩, ?_⟩
  · intro x hx
    exact hf.monotone hx.2
  · intro x hx
    have hle : f x ≤ f v := hf.monotone hx.1.2
    have hge : f v ≤ f x := hx.2 (right_mem_Icc.mpr huv)
    exact hf.injective (le_antisymm hle hge)

/-!
## Case E05 — No maximizer of `id` on the unbounded ray `[0, ∞)`

MATHEMATICAL / ECONOMIC INTENT:
  Boundedness / compactness is necessary in general: `id` has no maximum on
  `Ici 0`.
VARIABLE DOMAINS: `ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `¬ ∃ x ∈ Ici 0, IsMaxOn id (Ici 0) x`.
PROOF ARCHITECTURE: from any candidate `x`, `x+1` is feasible and larger.
KEY LEAN/MATHLIB MECHANISM: `IsMaxOn`.
EDGE CASE: the same function *does* attain a max on every `Icc 0 m` with
  `0 ≤ m`.
SEMANTIC FAITHFULNESS AUDIT:
  An existence claim for a maximum of an increasing function on an unbounded
  feasible region is not justified by continuity alone.
-/
theorem E05_id_no_max_on_Ici :
    ¬ ∃ x ∈ Ici (0 : ℝ), IsMaxOn (id : ℝ → ℝ) (Ici 0) x := by
  rintro ⟨x, hx, hmax⟩
  have hx0 : 0 ≤ x := hx
  have hx1 : x + 1 ∈ Ici (0 : ℝ) := add_nonneg hx0 zero_le_one
  have : x + 1 ≤ x := hmax hx1
  linarith

/-!
## Case E06 — No maximizer on the empty set

MATHEMATICAL / ECONOMIC INTENT:
  Existence requires a point of the feasible set.
VARIABLE DOMAINS: `f : ℝ → ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `¬ ∃ x, x ∈ (∅ : Set ℝ) ∧ IsMaxOn f ∅ x`.
PROOF ARCHITECTURE: empty membership is false.
KEY LEAN/MATHLIB MECHANISM: `Set.not_mem_empty`.
EDGE CASE: `IsMaxOn f ∅ x` is vacuously true for every `x`, but `x ∈ ∅` is not.
  This is why existence statements must include membership, not only `IsMaxOn`.
SEMANTIC FAITHFULNESS AUDIT:
  Vacuous optimality without feasibility is not existence of a choice.
-/
theorem E06_no_max_on_empty (f : ℝ → ℝ) :
    ¬ ∃ x, x ∈ (∅ : Set ℝ) ∧ IsMaxOn f ∅ x := by
  rintro ⟨x, hx, _⟩
  exact hx

/-!
## Case E07 — Existence without uniqueness: constant on a nondegenerate interval

MATHEMATICAL / ECONOMIC INTENT:
  E01-style existence can hold while uniqueness fails.
VARIABLE DOMAINS: `u v c : ℝ`.
ASSUMPTIONS: `u < v`.
FORMAL LEAN STATEMENT: there exist at least two distinct maximizers.
PROOF ARCHITECTURE: reuse Z05.
KEY LEAN/MATHLIB MECHANISM: `IsMaxOn`.
EDGE CASE: if `u = v` uniqueness is restored because the set is a singleton.
SEMANTIC FAITHFULNESS AUDIT:
  “A maximizer exists” does not imply “the maximizer”.
-/
theorem E07_exists_not_unique {u v c : ℝ} (huv : u < v) :
    ∃ x y, x ∈ Icc u v ∧ y ∈ Icc u v ∧ x ≠ y ∧
      IsMaxOn (fun _ : ℝ => c) (Icc u v) x ∧
      IsMaxOn (fun _ : ℝ => c) (Icc u v) y :=
  Z05_constant_not_unique huv

/-!
## Case E08 — `x^2` is unbounded above on `ℝ`

MATHEMATICAL / ECONOMIC INTENT:
  A continuous function on a noncompact domain need not attain a maximum.
VARIABLE DOMAINS: `ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `¬ ∃ M, ∀ x, x^2 ≤ M`.
PROOF ARCHITECTURE: from any `M` take `x = |M| + 1`.
KEY LEAN/MATHLIB MECHANISM: `sq_abs`, comparison of squares.
EDGE CASE: the same function is bounded below and attains its minimum.
SEMANTIC FAITHFULNESS AUDIT:
  Continuity without a compact feasible set does not give a maximum.
-/
theorem E08_sq_unbounded_above : ¬ ∃ M : ℝ, ∀ x : ℝ, x ^ 2 ≤ M := by
  rintro ⟨M, hM⟩
  have : (M + 1) ^ 2 ≤ M := hM (M + 1)
  nlinarith

end OptimizationEconomics

import OptimizationEconomics.Basic
import OptimizationEconomics.Objectives
import OptimizationEconomics.Monotonicity
import Mathlib.Data.Finset.Max
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

/-!
# Simple optimization

Controlled examples: linear maximization on a closed interval, unique
minimization of a square, comparison of feasible alternatives, boundary
optima, and finite choice. Existence theorems that need compactness live in
`ExistenceUniqueness.lean`.
-/

namespace OptimizationEconomics
open Set

/-!
## Case Z01 — Maximizing an increasing affine map on `[u, v]`

MATHEMATICAL / ECONOMIC INTENT:
  If `0 < a` then `affineObj a b` attains its unique maximum on `Icc u v` at `v`.
VARIABLE DOMAINS: `a b u v : ℝ`.
ASSUMPTIONS: `0 < a`, `u ≤ v`.
FORMAL LEAN STATEMENT:
  `v ∈ Icc u v` and `IsMaxOn (affineObj a b) (Icc u v) v`, and any other
  maximizer equals `v`.
PROOF ARCHITECTURE:
  feasibility of `v`; monotonicity gives the max property; strict monotonicity
  plus injectivity gives uniqueness.
KEY LEAN/MATHLIB MECHANISM: `IsMaxOn`, `StrictMono`.
EDGE CASE: if `a = 0` every point is a maximizer.
SEMANTIC FAITHFULNESS AUDIT:
  The maximizer is the right endpoint because the objective is strictly
  increasing, not because of an economic “corner solution” narrative.
-/
theorem Z01_affine_max_at_right {a b u v : ℝ} (ha : 0 < a) (huv : u ≤ v) :
    v ∈ Icc u v ∧ IsMaxOn (affineObj a b) (Icc u v) v := by
  refine ⟨right_mem_Icc.mpr huv, ?_⟩
  intro x hx
  exact (O02_affine_strictMono_iff a b).mpr ha |>.monotone hx.2

theorem Z01_affine_max_unique {a b u v x : ℝ} (ha : 0 < a) (huv : u ≤ v)
    (hx : x ∈ Icc u v) (hmax : IsMaxOn (affineObj a b) (Icc u v) x) :
    x = v := by
  have hf : StrictMono (affineObj a b) := (O02_affine_strictMono_iff a b).mpr ha
  have hle : affineObj a b x ≤ affineObj a b v := hf.monotone hx.2
  have hge : affineObj a b v ≤ affineObj a b x := hmax (right_mem_Icc.mpr huv)
  exact hf.injective (le_antisymm hle hge)

/-!
## Case Z02 — Unique minimizer of `x^2` on `ℝ`

MATHEMATICAL / ECONOMIC INTENT:
  `x ↦ x^2` has a unique global minimizer at `0`.
VARIABLE DOMAINS: `x : ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT:
  `IsMinOn (fun x : ℝ => x^2) univ 0` and any minimizer equals `0`.
PROOF ARCHITECTURE: `sq_nonneg` and `sq_eq_zero_iff`.
KEY LEAN/MATHLIB MECHANISM: `IsMinOn`.
EDGE CASE: there is no maximizer on `ℝ`. See ExistenceUniqueness.
SEMANTIC FAITHFULNESS AUDIT:
  Global minimization on `univ` is a different claim from minimization on a
  compact interval.
-/
theorem Z02_sq_min_at_zero : IsMinOn (fun x : ℝ => x ^ 2) univ 0 := by
  intro x _
  simpa using sq_nonneg x

theorem Z02_sq_min_unique {x : ℝ} (h : IsMinOn (fun y : ℝ => y ^ 2) univ x) :
    x = 0 := by
  have hx : x ^ 2 ≤ 0 := by
    have := h (mem_univ (0 : ℝ))
    simpa using this
  have : x ^ 2 = 0 := le_antisymm hx (sq_nonneg x)
  exact sq_eq_zero_iff.mp this

/-!
## Case Z03 — Unique minimizer of `(x - c)^2`

MATHEMATICAL / ECONOMIC INTENT:
  Translating the square moves the unique minimizer to `c`.
VARIABLE DOMAINS: `c x : ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: unique global min at `c`.
PROOF ARCHITECTURE: reduce to `sq_nonneg` after translation.
KEY LEAN/MATHLIB MECHANISM: `IsMinOn`, `sq_eq_zero_iff`.
EDGE CASE: uniqueness uses that a square vanishes at exactly one point.
SEMANTIC FAITHFULNESS AUDIT:
  This is a translated quadratic, not a general strictly convex program.
-/
theorem Z03_shifted_sq_min (c : ℝ) :
    IsMinOn (fun x : ℝ => (x - c) ^ 2) univ c := by
  intro x _
  simpa using sq_nonneg (x - c)

theorem Z03_shifted_sq_min_unique {c x : ℝ}
    (h : IsMinOn (fun y : ℝ => (y - c) ^ 2) univ x) : x = c := by
  have hx : (x - c) ^ 2 ≤ 0 := by
    have := h (mem_univ c)
    simpa using this
  have : (x - c) ^ 2 = 0 := le_antisymm hx (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)

/-!
## Case Z04 — Comparison of two named feasible alternatives

MATHEMATICAL / ECONOMIC INTENT:
  If two feasible points are given, optimality of one relative to the other is
  a two-point comparison, not an argmax over the whole set.
VARIABLE DOMAINS: `m x y : ℝ`.
ASSUMPTIONS: both in `resourceInterval m`, compare `id`.
FORMAL LEAN STATEMENT: `x ≤ y ↔ id x ≤ id y`, specialized to feasible points.
PROOF ARCHITECTURE: `id` is the identity.
KEY LEAN/MATHLIB MECHANISM: unfolding `id`.
EDGE CASE: the larger feasible point is better for `id`, but need not be a
  global maximizer unless it is the right endpoint.
SEMANTIC FAITHFULNESS AUDIT:
  Pairwise comparison ≠ identification of an optimum of the feasible set.
-/
theorem Z04_pairwise_id {m x y : ℝ}
    (_hx : x ∈ resourceInterval m) (_hy : y ∈ resourceInterval m) :
    x ≤ y ↔ id x ≤ id y := by
  simp

/-!
## Case Z05 — Constant objective: every feasible point is optimal

MATHEMATICAL / ECONOMIC INTENT:
  A constant objective has many maximizers as soon as the feasible set has
  two points.
VARIABLE DOMAINS: `u v c : ℝ`.
ASSUMPTIONS: `u ≤ v`.
FORMAL LEAN STATEMENT: every point of `Icc u v` is a maximizer of
  `fun _ => c`.
PROOF ARCHITECTURE: `le_rfl` on the constant value.
KEY LEAN/MATHLIB MECHANISM: `IsMaxOn`.
EDGE CASE: uniqueness fails whenever `u < v`.
SEMANTIC FAITHFULNESS AUDIT:
  Existence of a maximizer is true; uniqueness is false. They are different
  claims.
-/
theorem Z05_constant_max_everywhere {u v c : ℝ} (_huv : u ≤ v) :
    ∀ x ∈ Icc u v, IsMaxOn (fun _ : ℝ => c) (Icc u v) x := by
  intro x _hx y _hy
  exact (le_rfl : c ≤ c)

theorem Z05_constant_not_unique {u v c : ℝ} (huv : u < v) :
    ∃ x y, x ∈ Icc u v ∧ y ∈ Icc u v ∧ x ≠ y ∧
      IsMaxOn (fun _ : ℝ => c) (Icc u v) x ∧
      IsMaxOn (fun _ : ℝ => c) (Icc u v) y := by
  refine ⟨u, v, left_mem_Icc.mpr huv.le, right_mem_Icc.mpr huv.le, ne_of_lt huv, ?_, ?_⟩
  · exact Z05_constant_max_everywhere huv.le u (left_mem_Icc.mpr huv.le)
  · exact Z05_constant_max_everywhere huv.le v (right_mem_Icc.mpr huv.le)

/-!
## Case Z06 — Finite feasible set: a maximizer exists

MATHEMATICAL / ECONOMIC INTENT:
  A nonempty finite set of real alternatives has a greatest element.
VARIABLE DOMAINS: `s : Finset ℝ`.
ASSUMPTIONS: `s.Nonempty`.
FORMAL LEAN STATEMENT: `∃ x ∈ s, ∀ y ∈ s, y ≤ x`.
PROOF ARCHITECTURE: `Finset.max'`.
KEY LEAN/MATHLIB MECHANISM: `Finset.max'`, `Finset.le_max'`.
EDGE CASE: emptiness removes existence; infinitude of `ℝ` is irrelevant here
  because the feasible set is finite.
SEMANTIC FAITHFULNESS AUDIT:
  Finite choice is not the extreme value theorem. Compactness is a different
  sufficient condition, used later.
-/
theorem Z06_finite_exists_max (s : Finset ℝ) (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, y ≤ x :=
  ⟨s.max' hs, s.max'_mem hs, fun y hy => s.le_max' y hy⟩

/-!
## Case Z07 — Minimizing an increasing affine map on `[u, v]`

MATHEMATICAL / ECONOMIC INTENT:
  The unique minimizer of a strictly increasing affine map on `Icc u v` is `u`.
VARIABLE DOMAINS: `a b u v : ℝ`.
ASSUMPTIONS: `0 < a`, `u ≤ v`.
FORMAL LEAN STATEMENT: `IsMinOn` at `u`, uniqueness.
PROOF ARCHITECTURE: dual to Z01.
KEY LEAN/MATHLIB MECHANISM: `IsMinOn`, `StrictMono`.
EDGE CASE: a decreasing slope would swap max and min endpoints.
SEMANTIC FAITHFULNESS AUDIT:
  Endpoint optima are consequences of monotonicity plus a closed interval.
-/
theorem Z07_affine_min_at_left {a b u v : ℝ} (ha : 0 < a) (huv : u ≤ v) :
    u ∈ Icc u v ∧ IsMinOn (affineObj a b) (Icc u v) u := by
  refine ⟨left_mem_Icc.mpr huv, ?_⟩
  intro x hx
  exact (O02_affine_strictMono_iff a b).mpr ha |>.monotone hx.1

theorem Z07_affine_min_unique {a b u v x : ℝ} (ha : 0 < a) (huv : u ≤ v)
    (hx : x ∈ Icc u v) (hmin : IsMinOn (affineObj a b) (Icc u v) x) :
    x = u := by
  have hf : StrictMono (affineObj a b) := (O02_affine_strictMono_iff a b).mpr ha
  have hle : affineObj a b u ≤ affineObj a b x := hf.monotone hx.1
  have hge : affineObj a b x ≤ affineObj a b u := hmin (left_mem_Icc.mpr huv)
  exact hf.injective (le_antisymm hge hle)

end OptimizationEconomics

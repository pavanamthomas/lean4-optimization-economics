import OptimizationEconomics.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# Objective functions

Evaluation, comparison, monotonicity, and bounds for affine, quadratic, and
elementary polynomial objectives on explicit real domains.
-/

namespace OptimizationEconomics
open Set

/-!
## Case O01 — Affine evaluation and comparison

MATHEMATICAL / ECONOMIC INTENT:
  An affine objective is determined by slope `a` and intercept `b`.
VARIABLE DOMAINS: `a b x y : ℝ`.
ASSUMPTIONS: `x ≤ y` and `0 ≤ a` for the comparison direction below.
FORMAL LEAN STATEMENT: `affineObj a b x ≤ affineObj a b y`.
PROOF ARCHITECTURE: factor `a * (y - x)` and use nonnegativity.
KEY LEAN/MATHLIB MECHANISM: `mul_nonneg`, unfolding `affineObj`.
EDGE CASE: if `a < 0` the comparison reverses.
SEMANTIC FAITHFULNESS AUDIT:
  Comparison of values is not “preference”. It is an order fact about a map.
-/
theorem O01_affine_eval (a b x : ℝ) : affineObj a b x = a * x + b :=
  rfl

theorem O01_affine_mono_of_nonneg_slope {a b x y : ℝ}
    (ha : 0 ≤ a) (hxy : x ≤ y) :
    affineObj a b x ≤ affineObj a b y := by
  unfold affineObj
  linarith [mul_nonneg ha (sub_nonneg.mpr hxy)]

/-!
## Case O02 — Affine map is strictly monotone iff the slope is positive

MATHEMATICAL / ECONOMIC INTENT:
  Strict comparison of affine values is equivalent to a positive slope.
VARIABLE DOMAINS: `a b : ℝ`.
ASSUMPTIONS: none in the `iff`; each direction uses the slope sign.
FORMAL LEAN STATEMENT: `StrictMono (affineObj a b) ↔ 0 < a`.
PROOF ARCHITECTURE:
  forward: evaluate at `0 < 1`;
  reverse: `mul_lt_mul_of_pos_left`.
KEY LEAN/MATHLIB MECHANISM: `StrictMono`.
EDGE CASE: `a = 0` gives a constant, which is monotone but not strictly monotone.
SEMANTIC FAITHFULNESS AUDIT:
  The intercept `b` is irrelevant to monotonicity. An economic story that
  treats `b` as “baseline welfare” is interpretation, not this theorem.
-/
theorem O02_affine_strictMono_iff (a b : ℝ) :
    StrictMono (affineObj a b) ↔ 0 < a := by
  constructor
  · intro hf
    have h01 : (0 : ℝ) < 1 := one_pos
    have := hf h01
    simpa [affineObj] using this
  · intro ha x y hxy
    simpa [affineObj] using (mul_lt_mul_of_pos_left hxy ha)

theorem O02_constant_affine_not_strictMono (b : ℝ) :
    ¬ StrictMono (affineObj 0 b) := by
  intro h
  have := h (show (0 : ℝ) < 1 from one_pos)
  simp [affineObj] at this

/-!
## Case O03 — Quadratic evaluation and the canonical square

MATHEMATICAL / ECONOMIC INTENT:
  `x^2` is nonnegative and vanishes only at `0`.
VARIABLE DOMAINS: `x : ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `0 ≤ x^2` and `x^2 = 0 ↔ x = 0`.
PROOF ARCHITECTURE: mathlib square lemmas.
KEY LEAN/MATHLIB MECHANISM: `sq_nonneg`, `sq_eq_zero_iff`.
EDGE CASE: on `ℝ` this is a global lower bound, not an upper bound.
SEMANTIC FAITHFULNESS AUDIT:
  Nonnegativity of `x^2` is not a “loss function interpretation” by itself.
-/
theorem O03_sq_nonneg (x : ℝ) : 0 ≤ x ^ 2 :=
  sq_nonneg x

theorem O03_sq_eq_zero_iff (x : ℝ) : x ^ 2 = 0 ↔ x = 0 :=
  sq_eq_zero_iff

theorem O03_quadratic_eval (a b c x : ℝ) :
    quadraticObj a b c x = a * x ^ 2 + b * x + c :=
  rfl

/-!
## Case O04 — Completed square lower bound

MATHEMATICAL / ECONOMIC INTENT:
  `x^2 - 2 c x + c^2 = (x - c)^2 ≥ 0`, so `x^2 + k` is bounded below after
  completing the square in the monic case `quadraticObj 1 (-2*c) (c^2)`.
VARIABLE DOMAINS: `c x : ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `0 ≤ (x - c)^2` and the algebraic identity.
PROOF ARCHITECTURE: `ring` plus `sq_nonneg`.
KEY LEAN/MATHLIB MECHANISM: `ring`, `sq_nonneg`.
EDGE CASE: the lower bound `0` is achieved exactly at `x = c`.
SEMANTIC FAITHFULNESS AUDIT:
  This identifies a unique minimizer of this quadratic. It does not identify a
  maximizer on `ℝ`.
-/
theorem O04_completed_square (c x : ℝ) :
    (x - c) ^ 2 = x ^ 2 - 2 * c * x + c ^ 2 := by
  ring

theorem O04_completed_square_nonneg (c x : ℝ) : 0 ≤ (x - c) ^ 2 :=
  sq_nonneg _

/-!
## Case O05 — Cube is strictly monotone on the nonnegative ray

MATHEMATICAL / ECONOMIC INTENT:
  `x ↦ x^3` is strictly monotone on `Ici 0`.
VARIABLE DOMAINS: `x y : ℝ`.
ASSUMPTIONS: `0 ≤ x`, `x < y`.
FORMAL LEAN STATEMENT: `x^3 < y^3`.
PROOF ARCHITECTURE: factor `y^3 - x^3` and use positivity of the remaining
  quadratic-looking factor on this range.
KEY LEAN/MATHLIB MECHANISM: `pow_lt_pow_left₀` (odd powers are globally
  strictly monotone; we specialize to the nonnegative ray).
EDGE CASE: the same map is still strictly monotone on all of `ℝ` because the
  exponent is odd; we state the ray version to keep the domain explicit.
SEMANTIC FAITHFULNESS AUDIT:
  Restricting the domain is a modeling choice. The global fact is stronger;
  stating only the ray version is still correct, just weaker.
-/
theorem O05_pow_three_strictMonoOn_nonneg :
    StrictMonoOn (fun x : ℝ => x ^ 3) (Ici 0) := by
  have hodd : Odd (3 : ℕ) := ⟨1, rfl⟩
  exact hodd.strictMono_pow.strictMonoOn _

/-!
## Case O06 — Affine bounds on a closed interval

MATHEMATICAL / ECONOMIC INTENT:
  If `0 ≤ a` and `x ∈ Icc u v`, then `affineObj a b x` lies in
  `Icc (affineObj a b u) (affineObj a b v)`.
VARIABLE DOMAINS: `a b u v x : ℝ`.
ASSUMPTIONS: `0 ≤ a`, `u ≤ x`, `x ≤ v`.
FORMAL LEAN STATEMENT: the two-sided bound above.
PROOF ARCHITECTURE: apply Case O01 twice.
KEY LEAN/MATHLIB MECHANISM: monotonicity of an affine map.
EDGE CASE: if `a < 0` the endpoints swap.
SEMANTIC FAITHFULNESS AUDIT:
  The bound uses the closed interval. On `Ioo u v` the image need not include
  the endpoint values.
-/
theorem O06_affine_bounds_Icc {a b u v x : ℝ}
    (ha : 0 ≤ a) (hux : u ≤ x) (hxv : x ≤ v) :
    affineObj a b u ≤ affineObj a b x ∧ affineObj a b x ≤ affineObj a b v :=
  ⟨O01_affine_mono_of_nonneg_slope ha hux,
    O01_affine_mono_of_nonneg_slope ha hxv⟩

/-!
## Case O07 — Linear objective comparison of two feasible points

MATHEMATICAL / ECONOMIC INTENT:
  Given two points in `Icc 0 m` and a nonnegative slope, the larger point has
  the larger objective.
VARIABLE DOMAINS: `a m x y : ℝ`.
ASSUMPTIONS: `0 ≤ a`, both points feasible, `x ≤ y`.
FORMAL LEAN STATEMENT: `affineObj a 0 x ≤ affineObj a 0 y`.
PROOF ARCHITECTURE: reduce to O01.
KEY LEAN/MATHLIB MECHANISM: reuse of affine monotonicity.
EDGE CASE: feasibility is unused in the inequality. It is recorded so the
  statement matches a constrained-comparison model.
SEMANTIC FAITHFULNESS AUDIT:
  Unused assumptions do not become economic conclusions. They only locate the
  comparison inside a feasible set.
-/
theorem O07_compare_feasible_affine {a m x y : ℝ}
    (ha : 0 ≤ a)
    (_hx : x ∈ resourceInterval m) (_hy : y ∈ resourceInterval m)
    (hxy : x ≤ y) :
    affineObj a 0 x ≤ affineObj a 0 y :=
  O01_affine_mono_of_nonneg_slope ha hxy

end OptimizationEconomics

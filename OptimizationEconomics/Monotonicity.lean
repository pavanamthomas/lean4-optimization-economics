import OptimizationEconomics.Basic
import OptimizationEconomics.Objectives
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# Monotonicity

Distinguish algebraic monotonicity from economic interpretation. A monotone map
preserves order. It does not, by itself, describe choice, welfare, or markets.
-/

namespace OptimizationEconomics
open Set

/-!
## Case M01 — Positive scaling is strictly monotone

MATHEMATICAL / ECONOMIC INTENT:
  `x ↦ α * x` is strictly monotone when `0 < α`.
VARIABLE DOMAINS: `α : ℝ`.
ASSUMPTIONS: `0 < α`.
FORMAL LEAN STATEMENT: `StrictMono (fun x : ℝ => α * x)`.
PROOF ARCHITECTURE: `mul_lt_mul_of_pos_left`.
KEY LEAN/MATHLIB MECHANISM: `StrictMono`.
EDGE CASE: `α = 0` is constant; `α < 0` is strictly antitone.
SEMANTIC FAITHFULNESS AUDIT:
  This is an order fact. Calling `α` a “productivity parameter” is commentary.
-/
theorem M01_pos_scale_strictMono {α : ℝ} (hα : 0 < α) :
    StrictMono (fun x : ℝ => α * x) :=
  fun _ _ hxy => mul_lt_mul_of_pos_left hxy hα

theorem M01_neg_scale_strictAnti {α : ℝ} (hα : α < 0) :
    StrictAnti (fun x : ℝ => α * x) :=
  fun _ _ hxy => mul_lt_mul_of_neg_left hxy hα

/-!
## Case M02 — Monotone maps preserve weak inequalities

MATHEMATICAL / ECONOMIC INTENT:
  If `f` is monotone and `x ≤ y` then `f x ≤ f y`.
VARIABLE DOMAINS: `f : ℝ → ℝ`, `x y : ℝ`.
ASSUMPTIONS: `Monotone f`, `x ≤ y`.
FORMAL LEAN STATEMENT: `f x ≤ f y`.
PROOF ARCHITECTURE: definition of `Monotone`.
KEY LEAN/MATHLIB MECHANISM: `Monotone`.
EDGE CASE: the conclusion is weak even if `x < y`.
SEMANTIC FAITHFULNESS AUDIT:
  Order preservation is not “more is better” as an empirical claim. It is the
  definition of monotonicity applied to two points.
-/
theorem M02_monotone_preserves {f : ℝ → ℝ} (hf : Monotone f) {x y : ℝ}
    (hxy : x ≤ y) : f x ≤ f y :=
  hf hxy

/-!
## Case M03 — Strict monotonicity implies injectivity

MATHEMATICAL / ECONOMIC INTENT:
  A strictly monotone real function cannot take the same value at two distinct
  points. This is the algebraic core of many uniqueness arguments.
VARIABLE DOMAINS: `f : ℝ → ℝ`.
ASSUMPTIONS: `StrictMono f`.
FORMAL LEAN STATEMENT: `Function.Injective f`.
PROOF ARCHITECTURE: mathlib `StrictMono.injective`.
KEY LEAN/MATHLIB MECHANISM: `StrictMono.injective`.
EDGE CASE: monotone-but-not-strict maps need not be injective.
SEMANTIC FAITHFULNESS AUDIT:
  Injectivity is not uniqueness of an optimizer. Uniqueness of a maximizer
  needs a feasible set and an optimality predicate as well.
-/
theorem M03_strictMono_injective {f : ℝ → ℝ} (hf : StrictMono f) :
    Function.Injective f :=
  hf.injective

/-!
## Case M04 — Constrained comparison on a totally ordered feasible set

MATHEMATICAL / ECONOMIC INTENT:
  If the feasible set is a subset of `ℝ` and `f` is monotone, then among two
  feasible points the larger one has weakly larger `f`.
VARIABLE DOMAINS: `s : Set ℝ`, `f : ℝ → ℝ`, `x y : ℝ`.
ASSUMPTIONS: `Monotone f`, `x ∈ s`, `y ∈ s`, `x ≤ y`.
FORMAL LEAN STATEMENT: `f x ≤ f y`.
PROOF ARCHITECTURE: apply monotonicity; feasibility is context.
KEY LEAN/MATHLIB MECHANISM: `Monotone`.
EDGE CASE: if the feasible set is not totally ordered (e.g. two goods),
  “larger” is not defined by `≤` on the ambient type.
SEMANTIC FAITHFULNESS AUDIT:
  The theorem does not select a maximizer. It only compares two named points.
-/
theorem M04_feasible_pair_compared {s : Set ℝ} {f : ℝ → ℝ}
    (hf : Monotone f) {x y : ℝ}
    (_hx : x ∈ s) (_hy : y ∈ s) (hxy : x ≤ y) :
    f x ≤ f y :=
  hf hxy

/-!
## Case M05 — Constant maps are monotone and not strictly monotone

MATHEMATICAL / ECONOMIC INTENT:
  Weak monotonicity does not imply strict monotonicity.
VARIABLE DOMAINS: constant `0` map on `ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `Monotone (fun _ : ℝ => 0)` and
  `¬ StrictMono (fun _ : ℝ => 0)`.
PROOF ARCHITECTURE: definition plus a two-point counterexample `0 < 1`.
KEY LEAN/MATHLIB MECHANISM: `Monotone`, `StrictMono`.
EDGE CASE: any constant has the same pattern.
SEMANTIC FAITHFULNESS AUDIT:
  A “weakly increasing utility” may be flat. Treating it as strictly increasing
  is a stronger, different claim.
-/
theorem M05_constant_monotone_not_strict :
    Monotone (fun _ : ℝ => (0 : ℝ)) ∧ ¬ StrictMono (fun _ : ℝ => (0 : ℝ)) := by
  refine ⟨fun _ _ _ => le_rfl, ?_⟩
  intro h
  exact lt_irrefl (0 : ℝ) (h (show (0 : ℝ) < 1 from one_pos))

/-!
## Case M06 — Identity is strictly monotone

MATHEMATICAL / ECONOMIC INTENT:
  `id` is the canonical strictly monotone utility `u(x) = x`.
VARIABLE DOMAINS: `ℝ`.
ASSUMPTIONS: none.
FORMAL LEAN STATEMENT: `StrictMono (id : ℝ → ℝ)`.
PROOF ARCHITECTURE: `strictMono_id`.
KEY LEAN/MATHLIB MECHANISM: `strictMono_id`.
EDGE CASE: none; this is global on `ℝ`.
SEMANTIC FAITHFULNESS AUDIT:
  `u(x) = x` is a mathematical function. Calling it “linear utility” is a
  name, not extra structure.
-/
theorem M06_id_strictMono : StrictMono (id : ℝ → ℝ) :=
  strictMono_id

end OptimizationEconomics

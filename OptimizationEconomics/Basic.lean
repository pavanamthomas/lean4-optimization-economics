import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

/-!
# Shared model primitives

This module records the reusable sets and maps used throughout the project.
Every definition keeps its domain explicit. Economic language in comments is
interpretation only; the Lean statements are the mathematical content.
-/

namespace OptimizationEconomics
noncomputable section
open Set

/-- Affine real objective `x ↦ a * x + b`. -/
def affineObj (a b : ℝ) (x : ℝ) : ℝ := a * x + b

/-- Quadratic real objective `x ↦ a * x^2 + b * x + c`. -/
def quadraticObj (a b c : ℝ) (x : ℝ) : ℝ := a * x ^ 2 + b * x + c

/-- Weighted linear utility of a two-good bundle. -/
def weightedUtility (w₁ w₂ : ℝ) (x y : ℝ) : ℝ := w₁ * x + w₂ * y

/-- Linear production `ℓ ↦ α * ℓ`. -/
def linearProduction (α : ℝ) (ℓ : ℝ) : ℝ := α * ℓ

/-- Linear cost of output under constant input price `w` and productivity `α`. -/
def linearCost (w α : ℝ) (q : ℝ) : ℝ := w * q / α

/-- Average cost, defined only when the caller assumes `q ≠ 0`. -/
def averageCost (totalCost q : ℝ) : ℝ := totalCost / q

/-- One-dimensional nonnegative budget set `{ x | 0 ≤ x ∧ p * x ≤ m }`. -/
def budget1D (p m : ℝ) : Set ℝ :=
  { x | 0 ≤ x ∧ p * x ≤ m }

/-- Two-good nonnegative budget set
`{ (x, y) | 0 ≤ x ∧ 0 ≤ y ∧ p₁ * x + p₂ * y ≤ m }`. -/
def budgetSet (p₁ p₂ m : ℝ) : Set (ℝ × ℝ) :=
  { xy | 0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ p₁ * xy.1 + p₂ * xy.2 ≤ m }

/-- Affordability is membership in `budgetSet`. -/
def Affordable (p₁ p₂ m : ℝ) (x y : ℝ) : Prop :=
  (x, y) ∈ budgetSet p₁ p₂ m

/-- Closed interval resource set `{ x | 0 ≤ x ∧ x ≤ m }`. -/
def resourceInterval (m : ℝ) : Set ℝ := Icc (0 : ℝ) m

@[simp] theorem mem_budget1D {p m x : ℝ} :
    x ∈ budget1D p m ↔ 0 ≤ x ∧ p * x ≤ m :=
  Iff.rfl

@[simp] theorem mem_budgetSet {p₁ p₂ m : ℝ} {xy : ℝ × ℝ} :
    xy ∈ budgetSet p₁ p₂ m ↔
      0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ p₁ * xy.1 + p₂ * xy.2 ≤ m :=
  Iff.rfl

@[simp] theorem affordable_iff {p₁ p₂ m x y : ℝ} :
    Affordable p₁ p₂ m x y ↔
      0 ≤ x ∧ 0 ≤ y ∧ p₁ * x + p₂ * y ≤ m :=
  Iff.rfl

@[simp] theorem mem_resourceInterval {m x : ℝ} :
    x ∈ resourceInterval m ↔ 0 ≤ x ∧ x ≤ m :=
  mem_Icc

lemma affineObj_add (a b x : ℝ) : affineObj a b x = a * x + b := rfl

lemma quadraticObj_eval (a b c x : ℝ) :
    quadraticObj a b c x = a * x ^ 2 + b * x + c := rfl

lemma weightedUtility_eval (w₁ w₂ x y : ℝ) :
    weightedUtility w₁ w₂ x y = w₁ * x + w₂ * y := rfl

end
end OptimizationEconomics

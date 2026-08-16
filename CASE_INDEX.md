# Case index

Every row is an executable case in this repository. Reviewer cases R01–R15 are
semantic-audit cases: the defective candidate is a comment; the corrected
statement compiles.

Difficulty: **F** foundational, **I** intermediate, **A** advanced.

| Case | Topic | Formal domain | Key assumptions | Lean mechanism | Semantic risk addressed | Diff. | Source |
| --- | --- | --- | --- | --- | --- | --- | --- |
| F01 | Nonnegativity membership | `x : ℝ`, `Ici 0` | none | `Set.mem_Ici` | treating `x ≥ 0` as implicit | F | `Feasibility.lean` |
| F02 | Positivity vs nonnegativity | `Ioi 0 ⊂ Ici 0` | none | `Ioi_subset_Ici_self` | swapping `>` for `≥` | F | `Feasibility.lean` |
| F03 | Closed interval membership | `Icc 0 m` | none for membership | `mem_Icc` | writing `[0,m]` when `m < 0` | F | `Feasibility.lean` |
| F04 | Closed vs open endpoints | `Icc` / `Ioo` | `a ≤ b` for closed membership | `left_mem_Icc`, `mem_Ioo` | placing a boundary optimum in an open set | F | `Feasibility.lean` |
| F05 | Linear budget membership | `budget1D p m` | none for membership | custom set | calling the set a budget without signs | F | `Feasibility.lean` |
| F06 | Empty vs nonempty `Icc` | `Icc a b` | `a ≤ b` iff nonempty | `nonempty_Icc`, `Icc_eq_empty` | existence on an empty interval | F | `Feasibility.lean` |
| F07 | Zero bundle in 1D | `budget1D` | `0 ≤ m` | `mul_zero` | requiring `x > 0` removes the witness | F | `Feasibility.lean` |
| F08 | Empty 1D budget | `budget1D` | `0 < p`, `m < 0` | `mul_nonneg` | dropping `x ≥ 0` restores nonemptiness | I | `Feasibility.lean` |
| F09 | Two-good membership | `Affordable` | none for membership | `budgetSet` | omitting a nonnegativity conjunct | F | `Feasibility.lean` |
| I01 | Expenditure transitivity | `ℝ` | `p*x ≤ m ≤ m'` | `le_trans` | reading transitivity as a demand effect | F | `Inequalities.lean` |
| I02 | Nonnegative scaling | `ℝ` | `0 ≤ c` | `mul_le_mul_of_nonneg_left` | using the same direction for `c < 0` | F | `Inequalities.lean` |
| I03 | Negative scaling reverses | `ℝ` | `c < 0` | `mul_le_mul_of_nonpos_left` | negative prices with unflipped inequalities | I | `Inequalities.lean` |
| I04 | Strict product / zero quantity | `ℝ` | `0 < x` for the strict fact | `mul_lt_mul_of_pos_right` | strict price change at `x = 0` | I | `Inequalities.lean` |
| I05 | Sum of bounds | `ℝ` | two weak inequalities | `add_le_add` | substitution-effect reading | F | `Inequalities.lean` |
| I06 | Budget iff quantity bound | `ℝ` | `0 < p` | `le_div_iff₀` | converting `p x ≤ m` when `p ≤ 0` | I | `Inequalities.lean` |
| O01 | Affine evaluation / mono | `affineObj` | `0 ≤ a` for comparison | unfolding, `linarith` | `a < 0` reverses comparison | F | `Objectives.lean` |
| O02 | Affine `StrictMono` iff | `ℝ → ℝ` | `0 < a` | `StrictMono` | constants are monotone, not strict | I | `Objectives.lean` |
| O03 | Square nonnegative | `ℝ` | none | `sq_nonneg`, `sq_eq_zero_iff` | treating a lower bound as an upper bound | F | `Objectives.lean` |
| O04 | Completed square | `ℝ` | none | `ring` | claiming a maximizer of `(x-c)^2` on `ℝ` | I | `Objectives.lean` |
| O05 | Cube on `Ici 0` | `StrictMonoOn` | domain `Ici 0` | `Odd.strictMono_pow` | domain restriction vs global odd-power fact | A | `Objectives.lean` |
| O06 | Affine bounds on `Icc` | `Icc u v` | `0 ≤ a` | monotonicity | open interval does not contain endpoint values | I | `Objectives.lean` |
| O07 | Feasible pairwise affine | `resourceInterval` | `0 ≤ a` | reuse O01 | unused feasibility becoming a fake conclusion | I | `Objectives.lean` |
| M01 | Positive / negative scaling | `ℝ → ℝ` | `0 < α` or `α < 0` | `StrictMono`, `StrictAnti` | `α = 0` is constant | I | `Monotonicity.lean` |
| M02 | Monotone preserves `≤` | `ℝ → ℝ` | `Monotone f` | definition | upgrading to a strict conclusion | F | `Monotonicity.lean` |
| M03 | Strict mono ⇒ injective | `ℝ → ℝ` | `StrictMono f` | `StrictMono.injective` | injectivity ≠ unique maximizer | I | `Monotonicity.lean` |
| M04 | Constrained pair comparison | `s : Set ℝ` | `Monotone f` | definition | “larger” on a product set | I | `Monotonicity.lean` |
| M05 | Constant not strict | `ℝ → ℝ` | none | two-point counterexample | weak vs strict monotonicity | I | `Monotonicity.lean` |
| M06 | Identity strictly monotone | `id : ℝ → ℝ` | none | `strictMono_id` | naming `id` “utility” without extra axioms | F | `Monotonicity.lean` |
| Z01 | Affine max at right endpoint | `Icc u v` | `0 < a`, `u ≤ v` | `IsMaxOn`, injectivity | `a = 0` destroys uniqueness | I | `Optimization.lean` |
| Z02 | Unique min of `x^2` on `ℝ` | `univ` | none | `IsMinOn`, `sq_eq_zero_iff` | no maximizer on `ℝ` | I | `Optimization.lean` |
| Z03 | Unique min of `(x-c)^2` | `univ` | none | translation of Z02 | general strict convexity not claimed | I | `Optimization.lean` |
| Z04 | Pairwise feasible comparison | `resourceInterval` | membership recorded | `id` | pairwise ≠ global argmax | I | `Optimization.lean` |
| Z05 | Constant: many maxima | `Icc u v` | `u ≤ v`; uniqueness fails if `u < v` | `IsMaxOn` | existence vs uniqueness | I | `Optimization.lean` |
| Z06 | Finite nonempty max | `Finset ℝ` | `s.Nonempty` | `Finset.max'` | confusing with EVT | A | `Optimization.lean` |
| Z07 | Affine min at left endpoint | `Icc u v` | `0 < a`, `u ≤ v` | `IsMinOn` | decreasing slope swaps endpoints | I | `Optimization.lean` |
| B01 | Budget nonempty if `0 ≤ m` | `budgetSet` | `0 ≤ m` | zero bundle | interior demand not claimed | I | `BudgetConstraints.lean` |
| B02 | Empty if `m < 0` | `budgetSet` | `0 ≤ pᵢ`, `m < 0` | nonnegative expenditure | negative price restores points | I | `BudgetConstraints.lean` |
| B03 | Income weakly expands | `Set (ℝ × ℝ)` | `m ≤ m'` | `le_trans` | strict expansion is stronger | I | `BudgetConstraints.lean` |
| B04 | Higher price, fixed bundle | `Affordable` | `0 ≤ x,y`, `p₁ ≤ p₁'` | `mul_le_mul_of_nonneg_right` | not a substitution effect | I | `BudgetConstraints.lean` |
| B05 | Zero income singleton | `budgetSet p₁ p₂ 0` | `0 < p₁`, `0 < p₂` | `add_eq_zero_iff_of_nonneg` | a zero price allows a ray | I | `BudgetConstraints.lean` |
| B06 | Negative price unbounded | `budgetSet` | `p₁ < 0` | `div_le_iff_of_neg` | “price” without positivity | A | `BudgetConstraints.lean` |
| B07 | Budget set convex | `Convex ℝ` | none | convex combination | convexity ≠ compactness | A | `BudgetConstraints.lean` |
| U01 | `u(x)=x` strict mono | `ℝ → ℝ` | none | identity | interpretation vs theorem | I | `Utility.lean` |
| U02 | `u=x+y` coordinatewise | `ℝ × ℝ` | coordinatewise `≤` | `add_le_add` | not `StrictMono` on the product | I | `Utility.lean` |
| U03 | Weighted linear, `wᵢ ≥ 0` | `ℝ` | nonnegative weights | `mul_le_mul_of_nonneg_left` | negative weight reverses a coordinate | I | `Utility.lean` |
| U04 | Unique max of `id` on `[0,m]` | `Icc 0 m` | `0 ≤ m` | `IsMaxOn`, antisymmetry | empty if `m < 0` | I | `Utility.lean` |
| U05 | Nonunique `x+y` on simplex | `budgetSet 1 1 1` | none extra | segment of maxima | “unique demand” overclaim | A | `Utility.lean` |
| U06 | Corner max of `(x,y)↦x` | `budgetSet p₁ p₂ m` | `0 < pᵢ`, `0 ≤ m` | `IsMaxOn`, uniqueness | second good unvalued in the objective | A | `Utility.lean` |
| P01 | Linear production strict mono | `linearProduction` | `0 < α` | reuse M01 | `α = 0` is zero output | I | `ProductionCost.lean` |
| P02 | Nonnegative output | `ℝ` | `0 ≤ α`, `0 ≤ ℓ` | `mul_nonneg` | sign restrictions are the whole content | F | `ProductionCost.lean` |
| P03 | Linear cost cancellation | `linearCost` | `α ≠ 0` | `mul_div_cancel₀` | undefined at `α = 0` | I | `ProductionCost.lean` |
| P04 | Average cost `w/α` | `averageCost` | `α ≠ 0`, `q ≠ 0` | `field_simp` | division at `q = 0` | I | `ProductionCost.lean` |
| P05 | Cost difference quotient | `ℝ` | `α ≠ 0`, `h ≠ 0` | `field_simp`, `ring` | `h = 0` divides by zero | A | `ProductionCost.lean` |
| P06 | Linear cost monotone | `linearCost` | `0 ≤ w`, `0 < α` | nonnegative slope | `w < 0` reverses monotonicity | I | `ProductionCost.lean` |
| C01 | Resource bound expands | `Icc 0 m` | `m ≤ m'` | `Icc_subset_Icc` | weak, not strict | I | `ComparativeStatics.lean` |
| C02 | Income weakly expands | `budgetSet` | `m ≤ m'` | reuse B03 | equality possible | I | `ComparativeStatics.lean` |
| C03 | Strict 1D income expansion | `budget1D` | `0 < p`, `m < m'`, `0 ≤ m'` | `mul_div_cancel₀` | extra hypotheses vs C02 | A | `ComparativeStatics.lean` |
| C04 | Price breaks exact budget | `ℝ` | `0 < x`, `p < p'`, `p x = m` | `mul_lt_mul_of_pos_right` | fixed bundle, not demand | I | `ComparativeStatics.lean` |
| C05 | Larger slope, positive `x` | `affineObj` | `0 < x`, `a < a'` | `mul_lt_mul_of_pos_right` | invisible at `x = 0` | I | `ComparativeStatics.lean` |
| C06 | Resource family monotone | `resourceInterval` | `m₁ ≤ m₂` | C01 | monotone correspondence ≠ selection | I | `ComparativeStatics.lean` |
| C07 | Higher prices shrink budget | `budgetSet` | `pᵢ ≤ pᵢ'` | `mul_le_mul_of_nonneg_right` | weak inclusion | I | `ComparativeStatics.lean` |
| E01 | EVT on `Icc` | `ContinuousOn` | `a ≤ b` | `IsCompact.exists_isMaxOn` | existence, not uniqueness | A | `ExistenceUniqueness.lean` |
| E02 | `Icc` is compact | `ℝ` | none (empty is compact) | `isCompact_Icc` | compactness ≠ a maximizer | A | `ExistenceUniqueness.lean` |
| E03 | Affine EVT | `affineObj` on `Icc` | `u ≤ v` | `Continuous`, E01 | slope sign not needed for existence | A | `ExistenceUniqueness.lean` |
| E04 | Unique max, `StrictMono` | `Icc u v` | `u ≤ v`, `StrictMono f` | `ExistsUnique` | `Monotone` is not enough | A | `ExistenceUniqueness.lean` |
| E05 | No max of `id` on `Ici 0` | unbounded ray | none | explicit larger point | continuity without compactness | A | `ExistenceUniqueness.lean` |
| E06 | No max on `∅` | empty set | none | `∉ ∅` | vacuous `IsMaxOn` without membership | A | `ExistenceUniqueness.lean` |
| E07 | Existence not uniqueness | constant on `Icc` | `u < v` | reuse Z05 | “the maximizer” | A | `ExistenceUniqueness.lean` |
| E08 | `x^2` unbounded above | `ℝ` | none | `nlinarith` | min exists, max does not | A | `ExistenceUniqueness.lean` |
| R01 | Omitted nonnegativity | half-space vs `budget1D` | `p ≠ 0` vs `0 < p`, `m < 0` | nonempty vs empty | hidden `x ≥ 0` | I | `ReviewerCases.lean` |
| R02 | Omitted positive price | `∃ p, ∀ x` | `0 < p` in the negation | `|m|/p + 1` | `p = 0` witness | I | `ReviewerCases.lean` |
| R03 | `ℕ` vs `ℝ` domain | `ℕ` embed / `ℝ` | none | `Nat.cast_nonneg` | transferring nonnegativity | F | `ReviewerCases.lean` |
| R04 | Reversed price inclusion | `budgetSet` | `p ≤ p'` | C07 plus witness | inclusion direction | I | `ReviewerCases.lean` |
| R05 | Quantifier order | `∀ x, ∃ p` | `0 < m` | small positive `p` | `∃ ∀` vs `∀ ∃` | A | `ReviewerCases.lean` |
| R06 | Accidental universal max | `id` on `Icc` | `0 < m` | counterexample `x = 0` | “every feasible point is optimal” | I | `ReviewerCases.lean` |
| R07 | Existence without feasibility | `IsMaxOn` on `∅` | none | vacuity vs membership | `IsMaxOn` omits `x ∈ s` | A | `ReviewerCases.lean` |
| R08 | Uniqueness without strictness | constant on `Icc 0 1` | none | `ExistsUnique` fails | existence ⇒ uniqueness | A | `ReviewerCases.lean` |
| R09 | Max on unbounded domain | `Ici 0` vs `Icc 0 m` | compact case needs `0 ≤ m` | E05 / explicit max | omitted compactness | A | `ReviewerCases.lean` |
| R10 | English stronger than math | `x+y` on simplex | none | two distinct maxima | unique consumer demand | A | `ReviewerCases.lean` |
| R11 | Division without `q ≠ 0` | `averageCost` | `α ≠ 0`, `q ≠ 0` | P04 | `0/0` | I | `ReviewerCases.lean` |
| R12 | Boundary ignored | `Icc` vs `Ioo` | `u ≤ v` for closed | F04 | endpoint of an open interval | F | `ReviewerCases.lean` |
| R13 | Strict expansion overclaim | zero prices | `0 ≤ m`, `0 ≤ m'` | equality of sets | `⊂` vs `⊆` | I | `ReviewerCases.lean` |
| R14 | Parameter direction reversed | `affineObj` | `0 < x`, `a < a'` | C05 | inequality direction | I | `ReviewerCases.lean` |
| R15 | Weak vs strict inequality | constant map | none | M05 / M01 | `Monotone` as `StrictMono` | I | `ReviewerCases.lean` |

## Counts

| Group | Cases |
| --- | --- |
| Foundational | F01–F07, F09, I01, I02, I05, O01, O03, M02, M06, P02, R03, R12 (18) |
| Intermediate | F08, I03, I04, I06, O02, O04, O06, O07, M01, M03–M05, Z01–Z05, Z07, B01–B05, U01–U04, P01, P03, P04, P06, C01, C02, C04–C07, R01, R02, R04, R06, R11, R13–R15 (45) |
| Advanced | O05, Z06, B06, B07, U05, U06, P05, C03, E01–E08, R05, R07–R10 (21) |
| **Total indexed cases** | **84** |

Topic subtotals (excluding reviewer rows): feasibility 9, inequalities 6, objectives 7, monotonicity 6, optimization 7, budget 7, utility 6, production/cost 6, comparative statics 7, existence/uniqueness 8. Reviewer cases: 15.

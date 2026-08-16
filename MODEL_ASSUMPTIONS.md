# Model assumption dictionary

This table describes assumptions that actually appear in compiled theorems.
“Failure if omitted” is a mathematical failure of *that* statement, not a
claim about the world.

| Model / theorem | Variable | Lean type | Mathematical domain | Assumption | Why required | Failure if omitted | Representative case |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Nonnegativity membership | `x` | `ℝ` | real line | none | membership is the statement | — | F01 |
| Positivity constraint | `x` | `ℝ` | `Ioi 0` | `0 < x` for membership | excludes the origin | `0` would be feasible | F02 |
| Closed resource interval | `m`, `x` | `ℝ` | `Icc 0 m` | `0 ≤ m` for nonemptiness | `Icc` nonempty iff `0 ≤ m` | empty feasible set | F03, F06 |
| Open vs closed interval | `a`, `b` | `ℝ` | `Icc` / `Ioo` | `a ≤ b` for closed endpoints | endpoints of `Ioo` are excluded | false “boundary optimum” | F04, R12 |
| 1D budget membership | `p`, `m`, `x` | `ℝ` | `{x \| 0 ≤ x ∧ p*x ≤ m}` | none for the iff | definition | a different set | F05 |
| 1D zero bundle | `p`, `m` | `ℝ` | `budget1D` | `0 ≤ m` | `p*0 = 0 ≤ m` | zero bundle unaffordable | F07 |
| Empty 1D budget | `p`, `m` | `ℝ` | `budget1D` | `0 < p`, `m < 0` | expenditure `≥ 0 > m` | nonempty if `x` may be negative | F08, R01 |
| Two-good affordability | `p₁,p₂,m,x,y` | `ℝ` | `budgetSet` | none for membership iff | three conjuncts | drop one conjunct, change the set | F09 |
| Expenditure transitivity | `p,x,m,m'` | `ℝ` | ordered field | `p*x ≤ m`, `m ≤ m'` | `le_trans` | cannot raise the bound | I01 |
| Nonnegative scaling | `a,b,c` | `ℝ` | ordered ring | `0 ≤ c` | preserves `≤` | reverses if `c < 0` | I02 |
| Negative scaling | `a,b,c` | `ℝ` | ordered ring | `c < 0` | flips `≤` | unflipped inequality is false | I03 |
| Strict price effect | `p,p',x` | `ℝ` | ordered ring | `0 < x`, `p < p'` | strict mul on the right | equality at `x = 0` | I04, C04 |
| Budget as quantity bound | `p,m,x` | `ℝ` | `ℝ` with division | `0 < p` | divide without flipping | false for `p ≤ 0` | I06 |
| Affine comparison | `a,b,x,y` | `ℝ` | affine maps | `0 ≤ a` for weak increase | slope sign | reverse if `a < 0` | O01, O06 |
| Affine strict monotonicity | `a,b` | `ℝ` | `ℝ → ℝ` | `0 < a` | `StrictMono` | constant if `a = 0` | O02, Z01 |
| Square objective | `x` | `ℝ` | `ℝ` | none | `sq_nonneg` | claiming an upper bound fails | O03, Z02, E08 |
| Completed square | `c,x` | `ℝ` | `ℝ` | none | `(x-c)^2 ≥ 0` | unique min lost if identity dropped | O04, Z03 |
| Cube on nonnegative ray | `x` | `ℝ` | `Ici 0` | `x ∈ Ici 0` in `StrictMonoOn` | stated domain | global odd-power fact is stronger, still true | O05 |
| Positive scaling | `α` | `ℝ` | `x ↦ α x` | `0 < α` | `StrictMono` | `StrictAnti` if `α < 0` | M01, P01 |
| Monotone map | `f` | `ℝ → ℝ` | preorder maps | `Monotone f` | weak preservation | not a strict conclusion | M02, M05, R15 |
| Strict mono injectivity | `f` | `ℝ → ℝ` | `ℝ` | `StrictMono f` | uniqueness of values | constants not injective | M03, E04 |
| Affine max on `[u,v]` | `a,b,u,v` | `ℝ` | `Icc u v` | `0 < a`, `u ≤ v` | right endpoint feasible and unique | empty if `v < u`; many max if `a = 0` | Z01 |
| Affine min on `[u,v]` | `a,b,u,v` | `ℝ` | `Icc u v` | `0 < a`, `u ≤ v` | left endpoint | swapped if `a < 0` | Z07 |
| Finite choice | `s` | `Finset ℝ` | finite nonempty | `s.Nonempty` | `max'` | no greatest element if empty | Z06 |
| Constant objective | `u,v,c` | `ℝ` | `Icc u v` | `u ≤ v` for membership; `u < v` for nonuniqueness | every point maximal | uniqueness false | Z05, E07, R08 |
| Two-good nonemptiness | `p₁,p₂,m` | `ℝ` | `budgetSet` | `0 ≤ m` | zero bundle | empty for `m < 0` with `pᵢ ≥ 0` | B01 |
| Two-good emptiness | `p₁,p₂,m` | `ℝ` | `budgetSet` | `0 ≤ pᵢ`, `m < 0` | nonnegative spend | nonempty if a price is negative | B02 |
| Income expansion | `m,m'` | `ℝ` | inclusion of sets | `m ≤ m'` | transitivity of `≤` | reverse inclusion false | B03, C02, R13 |
| Price increase, fixed bundle | `p₁,p₁',x,y` | `ℝ` | `Affordable` | `0 ≤ x,y`, `p₁ ≤ p₁'` | larger expenditure | reverse if `x < 0` | B04, C07, R04 |
| Zero income singleton | `p₁,p₂` | `ℝ` | `budgetSet _ _ 0` | `0 < p₁`, `0 < p₂` | each term vanishes | a zero price yields a ray | B05 |
| Negative price | `p₁` | `ℝ` | `budgetSet` | `p₁ < 0` | inequality flips | set unbounded in `x` | B06 |
| Budget convexity | `p₁,p₂,m` | `ℝ` | `Convex ℝ` | none | linear inequalities | not compactness | B07 |
| `u(x)=x` on `[0,m]` | `m,x` | `ℝ` | `Icc 0 m` | `0 ≤ m` | unique max at `m` | empty / no max if `m < 0` | U04 |
| `u=x+y` on unit simplex | `t` | `ℝ` | `budgetSet 1 1 1` | `t ∈ Icc 0 1` for the segment | many maxima | uniqueness false | U05, R10 |
| Corner utility `(x,y)↦x` | `p₁,p₂,m` | `ℝ` | `budgetSet` | `0 < pᵢ`, `0 ≤ m` | unique corner `(m/p₁, 0)` | nonunique if `y` is also valued equally | U06 |
| Linear cost definition | `w,α,q` | `ℝ` | field | `α ≠ 0` | `w q / α` | expression not a specified real | P03 |
| Average cost | `w,α,q` | `ℝ` | field | `α ≠ 0`, `q ≠ 0` | divide by output | `0/0` | P04, R11 |
| Cost difference quotient | `h` | `ℝ` | field | `h ≠ 0`, `α ≠ 0` | divide by increment | undefined increment | P05 |
| Linear cost monotone | `w,α` | `ℝ` | `ℝ → ℝ` | `0 ≤ w`, `0 < α` | slope `w/α ≥ 0` | decreasing if `w < 0` | P06 |
| Strict 1D income expansion | `p,m,m'` | `ℝ` | `budget1D` | `0 < p`, `m < m'`, `0 ≤ m'` | new point `m'/p` | not strict for zero prices | C03, R13 |
| Affine slope comparative static | `a,a',x` | `ℝ` | `affineObj` | `0 < x`, `a < a'` | positive multiplier | reverse direction is false | C05, R14 |
| EVT on an interval | `a,b,f` | `ℝ`, `ℝ → ℝ` | `Icc a b` | `a ≤ b`, `ContinuousOn f (Icc a b)` | compact nonempty + continuous | no max if empty or unbounded | E01, E03, R09 |
| Compactness of `Icc` | `a,b` | `ℝ` | `Icc a b` | none | empty compact | compactness ≠ existence of a point | E02, E06 |
| Unique max, strict mono | `f,u,v` | `ℝ → ℝ` | `Icc u v` | `u ≤ v`, `StrictMono f` | right endpoint unique | uniqueness fails for constants | E04, R08 |
| No max on `[0,∞)` | `id` | `ℝ → ℝ` | `Ici 0` | none | `x+1` larger | false existence claim | E05, R09 |
| No universal positive price | `p,m,x` | `ℝ` | nonnegative quantities | `0 < p` in the negated statement | `∀ x, p x ≤ m` fails | true if `p ≤ 0` allowed | R02, R05 |
| `ℕ` quantity | `n` | `ℕ` | nonnegative integers | none | cast is nonnegative | `-1 : ℝ` is a counterexample | R03 |
| Unrestricted half-space | `p,m` | `ℝ` | `{x \| p x ≤ m}` | `p ≠ 0` | `m/p` is a witness | different from `budget1D` | R01 |

## Modeling notes that are easy to drop

1. **`IsMaxOn f s x` does not include `x ∈ s`.** Existence of a choice is
   `∃ x, x ∈ s ∧ IsMaxOn f s x` (E06, R07).
2. **`0 < p` is not implied by writing the letter `p`.** Zero and negative
   prices change emptiness, boundedness, and affordability (B06, R02).
3. **`x : ℝ` is not automatically nonnegative.** `x : ℕ` is (R03).
4. **`m ≤ m'` gives `⊆`, not `⊂`.** Zero prices are a counterexample to
   automatic strict expansion (R13).
5. **Division hypotheses are part of the model.** Average cost at `q = 0` is
   not defined here (R11).

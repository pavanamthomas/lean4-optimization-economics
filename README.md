# lean4-optimization-economics

A Lean 4 + mathlib project that turns small optimization and economic *models* into
explicit domains, assumptions, theorem statements, and compiled proofs.

The repository is a formal-mathematics artifact. Economic language appears only as
commentary that names a model. If a sentence is not a Lean theorem, it is not a
claim of the project.

## 1. Purpose

The working pattern is:

**mathematical model → explicit domain → assumptions → formal statement → proof → boundary cases → semantic audit.**

The files under `OptimizationEconomics/` contain executable cases at three
difficulties (foundational, intermediate, advanced), plus fifteen semantic-review
cases that record a defective candidate in comments and a corrected compiling
statement beside it.

## 2. Economic interpretation versus formal theorem

| Layer | Status in this repository |
| --- | --- |
| A Lean `def` or `theorem` | Mathematical content. Domains, quantifiers, and inequality directions are exact. |
| A comment labeled `ECONOMIC INTERPRETATION` | Informal reading. It is not a theorem and is not used by Lean. |
| A comment labeled `DEFECTIVE FORMALIZATION` | A rejected candidate. It is not an executable declaration. |

Examples of the split:

- `StrictMono (fun x : ℝ => x)` is a theorem. “More of the good is better” is not.
- `budgetSet p₁ p₂ m ⊆ budgetSet p₁ p₂ m'` under `m ≤ m'` is a theorem. “Demand rises with income” is not.
- Existence of a maximizer of `x + y` on the unit budget simplex is a theorem. Uniqueness of that maximizer is false, and is proved false.

## 3. Exact Lean / mathlib environment

Pinned in the repository:

| Item | Pin |
| --- | --- |
| Lean toolchain file | `leanprover/lean4:v4.33.0` |
| Lean 4 release | `4.33.0` (`x86_64-unknown-linux-gnu`, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`) |
| mathlib input revision | `v4.33.0` in `lakefile.toml` |
| mathlib git revision | `db584cd6d46c92f209a44c0f1c829460d327499d` in `lake-manifest.json` |

These values were read from `lean --version`, `lean-toolchain`, and
`lake-manifest.json` after `lake update` on the machine that produced the
first successful `lake build`.

## 4. Modeling philosophy

- Prefer a small theorem that matches the intended model over a large theorem
  that compiles only after changing the model.
- Write every sign restriction that the proof uses (`0 ≤ x`, `0 < p`, `α ≠ 0`,
  `q ≠ 0`, `a ≤ b`, …).
- Keep existence, uniqueness, and existence+uniqueness as separate statements.
- Treat `IsMaxOn f s x` as a comparison property. A maximizer also requires
  `x ∈ s`.
- Do not use `sorry`, `admit`, or custom `axiom` declarations.

## 5. Repository architecture

```
OptimizationEconomics.lean          -- library root; imports every module
OptimizationEconomics/
  Basic.lean                        -- shared maps and budget sets
  Feasibility.lean                  -- constraints, empty/nonempty sets, boundaries
  Inequalities.lean                 -- linear inequalities used as constraints
  Objectives.lean                   -- affine, quadratic, elementary polynomial maps
  Monotonicity.lean                 -- Monotone / StrictMono, constrained comparison
  Optimization.lean                 -- interval optima, squares, finite choice
  BudgetConstraints.lean            -- two-good budget set
  Utility.lean                      -- controlled utility maps
  ProductionCost.lean               -- linear production and cost algebra
  ComparativeStatics.lean           -- parameter implications
  ExistenceUniqueness.lean          -- EVT, compactness, missing maxima
  ReviewerCases.lean                -- semantic defects and corrections
scripts/build_and_check.sh
scripts/check_no_sorry.sh
.github/workflows/ci.yml
CASE_INDEX.md
MODEL_ASSUMPTIONS.md
AUDIT_CHECKLIST.md
lakefile.toml
lean-toolchain
lake-manifest.json
```

## 6. Mathematical domains covered

- Nonnegativity, positivity, intervals, linear inequalities, empty versus nonempty sets
- Affine, quadratic, and cubic objectives
- Monotonicity and strict monotonicity
- Maximization/minimization on closed intervals, unique minima of squares, finite choice
- Two-good budgets `p₁ x + p₂ y ≤ m` with explicit signs
- Utility maps `u(x)=x`, `u(x,y)=x+y`, weighted linear utility, corner versus simplex optima
- Linear production and cost, average cost, difference quotients
- Comparative statics of income, prices, resource bounds, and slopes
- Compactness of `Icc`, continuity of affine maps, extreme value theorem
- Existence versus uniqueness versus neither

## 7. Assumption discipline

`MODEL_ASSUMPTIONS.md` lists, for the actual theorems in this repository, the Lean
type, mathematical domain, required hypothesis, why it is required, and what
fails if it is omitted. Hidden domain conventions are treated as defects (see
`ReviewerCases.lean`).

## 8. How to build

```bash
# toolchain is read from lean-toolchain (Lean 4.33.0)
lake exe cache get    # mathlib oleans; already run by lake update hooks
lake build
```

Or:

```bash
bash scripts/build_and_check.sh
```

The check script prints the toolchain, the mathlib revision from
`lake-manifest.json`, rejects `sorry` / `admit` / custom `axiom` in project
`.lean` files (excluding `.lake`), and runs `lake build`.

## 9. How verification works

1. `lake build` type-checks every module imported by `OptimizationEconomics.lean`.
2. `scripts/check_no_sorry.sh` searches project Lean sources only.
3. GitHub Actions (`.github/workflows/ci.yml`) runs that search, then
   `leanprover/lean-action@v1` with `build: true` and `use-mathlib-cache: true`.
   `nanoda` is not enabled.
4. Defective candidates live in comments. They are not declarations.

## 10. Known limitations

- The examples are intentionally small. There is no general constrained-optimization
  API, no Karush–Kuhn–Tucker theorem, and no revealed-preference theory.
- Two-good compactness of `budgetSet` is not proved; convexity is (case B07).
  Compact extrema are proved on real intervals (`Icc`).
- Average cost and linear cost use division and therefore exclude `q = 0` or
  `α = 0` by hypothesis. Those points are not given a separate extended-real encoding.
- Continuity is used for the extreme value theorem. Several named optima (linear
  objectives on `Icc`, `x^2` on `ℝ`) are identified algebraically without analysis.
- Downstream mathlib axioms (classical logic, quotients, …) are those of mathlib.
  This project does not add axioms.

## 11. Reproducibility

Commit `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` with the
source. Matching those three files, then `lake exe cache get` and `lake build`,
is the intended reproduction path. Do not treat an unpinned `mathlib` `master`
as the same environment.

## License

Apache License 2.0. See `LICENSE`.

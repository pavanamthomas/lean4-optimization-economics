# Audit checklist

Completed against the repository state after a successful `lake build` on the
machine that pinned the toolchain below. Items marked **PASS** were checked
with the listed command or inspection. Items not run are marked **NOT RUN**.

## Toolchain and dependencies

| Check | Result | Evidence |
| --- | --- | --- |
| Exact Lean version | **PASS** | `lean --version` → Lean 4.33.0, `x86_64-unknown-linux-gnu`, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`, Release |
| `lean-toolchain` pin | **PASS** | `leanprover/lean4:v4.33.0` |
| mathlib input revision | **PASS** | `lakefile.toml` `rev = "v4.33.0"` |
| Exact mathlib revision | **PASS** | `lake-manifest.json` `rev = "db584cd6d46c92f209a44c0f1c829460d327499d"`, `inputRev = "v4.33.0"` |
| mathlib cache used | **PASS** | `lake update` ran cache post-hooks and downloaded 8690 files from the mathlib4 cache |

## Build and placeholders

| Check | Result | Evidence |
| --- | --- | --- |
| Targeted builds | **PASS** | Modules built individually during development (`Basic`, `Feasibility`, `Inequalities`, `Objectives`, `Monotonicity`, `Optimization`, `BudgetConstraints`, `Utility`, `ProductionCost`, `ComparativeStatics`, `ExistenceUniqueness`, `ReviewerCases`) |
| Full `lake build` | **PASS** | Final `lake build` after all Lean edits: `Build completed successfully (3021 jobs)`. |
| No `sorry` | **PASS** | `bash scripts/check_no_sorry.sh` |
| No `admit` | **PASS** | same script, token `\badmit\b` |
| No custom `axiom` | **PASS** | same script, declaration pattern `(^|[[:space:]])axiom[[:space:]]` in project `.lean` files excluding `.lake` |

## Semantic audits

| Check | Result | Notes |
| --- | --- | --- |
| Explicit variable domains | **PASS** | Cases use `ℝ`, `ℕ`, `Finset ℝ`, `ℝ × ℝ` as declared; `autoImplicit = false` in `lakefile.toml` |
| Assumption completeness | **PASS** | Sign, nonemptiness, positivity, and nonzero hypotheses match `MODEL_ASSUMPTIONS.md` |
| Feasibility audit | **PASS** | Membership is explicit; empty-set cases F06, F08, B02, E06, R07 |
| Existence audit | **PASS** | E01/E03/Z06 require nonempty (and compactness/continuity or finiteness); E05/E06/E08 are negative results |
| Uniqueness audit | **PASS** | Unique cases use strict monotonicity or vanishing of a square; nonunique cases Z05, U05, E07, R08, R10 |
| Inequality-direction audit | **PASS** | I02 vs I03; C07 vs R04; C05 vs R14 |
| Quantifier audit | **PASS** | R02 is `¬ ∃ p, 0 < p ∧ ∀ x, …`; R05 is `∀ x, ∃ p` |
| Statement-faithfulness audit | **PASS** | Reviewer cases R01–R15; utility file splits MATHEMATICAL THEOREM / ECONOMIC INTERPRETATION |
| Edge-case audit | **PASS** | Zero income B05; zero quantity I04; negative price B06; unbounded E05; empty F08/E06; multiple optima Z05/U05; division P04/R11; `ℕ` vs `ℝ` R03 |
| CASE_INDEX consistency | **PASS** | All indexed case IDs exist as theorems in the listed files (F01–F09, I01–I06, O01–O07, M01–M06, Z01–Z07, B01–B07, U01–U06, P01–P06, C01–C07, E01–E08, R01–R15) |
| MODEL_ASSUMPTIONS consistency | **PASS** | Rows cite those cases; no extra models invented in the dictionary |
| README consistency | **PASS** | Versions, architecture, and limitations match the tree and the successful build |

## CI

| Check | Result | Notes |
| --- | --- | --- |
| Workflow file present | **PASS** | `.github/workflows/ci.yml` |
| Triggers | **PASS** | `push` to `main`, `pull_request` to `main` |
| Checkout | **PASS** | `actions/checkout@v4` |
| Reject sorry/admit | **PASS** | `bash scripts/check_no_sorry.sh` before the Lean action |
| `leanprover/lean-action@v1` | **PASS** | `build: true`, `use-mathlib-cache: true` |
| nanoda | **PASS** | `nanoda: false` (not enabled) |
| CI run on GitHub | **NOT RUN in this document** | Status depends on GitHub Actions after push. Local `lake build` is the compilation evidence recorded here. |

## Warnings

- `linter.unnecessarySimpa` fired during development on a few `simpa` proofs; those membership goals were rewritten to `simp` where the linter asked. Remaining `simpa` uses are for definitional mismatches such as `1 - 0` vs `1`.
- `linter.unusedVariables` was addressed by prefixing unused binders with `_`.
- Project files import substantial mathlib analysis/topology modules for EVT and convexity; compile time is dominated by those imports, not by the project proofs.

## Limitations (repeated from README, checked against code)

- No general nonlinear programming framework.
- No compactness proof for the two-good `budgetSet` (convexity is proved).
- Average/linear cost undefined at zero output or zero productivity.
- mathlib’s own axioms are inherited; none are declared in this project.

## Intentionally non-executable material

Defective formalizations appear only inside comments in `ReviewerCases.lean`
(and in this documentation). They are not `theorem` / `def` / `example`
declarations.

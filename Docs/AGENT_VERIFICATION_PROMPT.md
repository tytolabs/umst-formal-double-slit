# Agent verification prompt — `umst-formal-double-slit`

Copy everything below the line into a new chat / agent task.

---

You are verifying the repository at **`umst-formal-double-slit`** (workspace root). Produce a **short report** with **PASS/FAIL** per section, exact **command output tails** (or error snippets) on failure, and **counts** where requested.

## 1) Environment

- State: OS, `python3 --version`, whether GHC/cabal, `coqc`, `agda` are on PATH.
- Note if `pip install -r sim/requirements-optional.txt` was run (affects Python test skips).

## 2) Lean

- Run: `cd Lean && lake build`
- **Expected:** success.
- **Sorry audit (project sources only):** search `Lean/*.lean` but **exclude** `Lean/.lake/**`. Report total count and file:line list. **Expected:** **10** `sorry` in `DensityState.lean` (4) and `MeasurementChannel.lean` (6) unless the codebase changed.
- **Axiom audit:** report any `axiom` in project `Lean/*.lean` (excluding `.lake`). **Expected:** at least **`physicalSecondLaw`** in `LandauerLaw.lean`.
- **Lake roots:** count entries in `lakefile.lean` `roots` array. **Expected:** **37** modules (double-slit stack + vendored parent modules) unless `lakefile` changed.
- Cross-check `Lean/VERIFY.md` module table vs `lakefile` roots for obvious drift.

## 3) Python / sim

- Run from repo root: `make ci-local` (or at minimum `make sim` + `make sim-test`).
- Report: unittest **passed/failed** count and **skipped** count (if any).
- If skips > 0, say whether `requirements-optional.txt` was installed.

## 4) Haskell

- Run: `cd Haskell && cabal test`
- **Expected:** **2** test suites run: `umst-formal-double-slit-test` and `landauer-einstein-sanity`; all PASS.
- Count `quickCheckResult` calls in `Haskell/test/Main.hs` (expected **14** unless changed).
- Confirm `umst-formal-double-slit.cabal` `exposed-modules` matches files under `Haskell/src/`.

## 5) Optional formal (if tools installed)

- `make coq-check` (from repo root) — report PASS/FAIL or SKIP.
- `make agda-check` — report PASS/FAIL or SKIP.

## 6) Docs / coordination sanity

- `Docs/PARALLEL_WORK.md` cross-lang table: spot-check that **DONE** rows have matching paths on disk (`glob` or `ls`).
- `Docs/TODO-TRACKING.md` vs `PARALLEL_WORK.md`: no contradictory **CLAIMED** vs **DONE** for the same ticket.

## 7) CI awareness

- Note: `.github/workflows/lean.yml` and `haskell.yml` use **`paths` filters** — docs-only PRs may skip jobs. Say whether that matters for the user’s branch protection.

## Deliverable format

1. One-line **overall verdict** (PASS / PASS with notes / FAIL).
2. Bullet **findings** with numbers (sorry count, lake roots, QC blocks, test skips).
3. **Residual risks** (optional deps, path filters, axioms vs sorries).

---

*Canonical numbers and errata:* `Docs/DEEP_VERIFICATION_REPORT.md` · *Vendored sync checklist:* `Docs/VENDOR_SYNC.md`

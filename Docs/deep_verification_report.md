# UMST-Formal-Double-Slit: Deep Verification Report

*Archived from an internal audit. **Errata** (post-audit fixes to claims) are in §8.*

**Canonical filename:** `Docs/DEEP_VERIFICATION_REPORT.md` (use this path in links; case-sensitive CI).

## 0) Environment & Scope

- **Root**: your clone of `umst-formal-double-slit` (path varies by machine).
- **OS / Python / GHC:** record versions when auditing.
- **Dependencies:** `python3 -m pip install -r sim/requirements-optional.txt` when running the full unittest battery without skips.

## 1) Build & Test Gates

- `cd Lean && lake build`: **PASS** (completed successfully)
- `make ci-local`: **PASS**
- `make ci-full`: **PASS**

Optional (not in default CI): `make coq-check`, `make agda-check` — require `coqc` / `agda` on `PATH`.

## 2) Lean — Structural Rigour

### Sorry inventory (project sources only)

**Scope:** `Lean/*.lean` **excluding** `Lean/.lake/**` (do not grep dependencies).

**Total: 10** — all intentional stubs (Mathlib / API drift workarounds unless noted otherwise in-file):

| File | Lines (approx.) |
|------|------------------|
| `Lean/DensityState.lean` | 52, 55, 58, 61 |
| `Lean/MeasurementChannel.lean` | 204, 207, 211, 215, 226, 231 |

### Axiom inventory (distinct from `sorry`)

- `Lean/LandauerLaw.lean`: **`axiom physicalSecondLaw`** — explicit **physical** second-law hypothesis for the `T_LandauerLaw` extension (documented in-module). Not a proof gap; it is the formalized axiom base for Landauer’s bound in that layer.

### Lakefile & entry points

- **`Lean/lakefile.lean`** declares **37** module roots in `lean_lib «UMST.DoubleSlit»` (double-slit track + vendored upstream reference modules: `LandauerLaw`, `Gate`, `MonoidalState`, …).  
- Canonical map: **`Lean/VERIFY.md`** (kept in sync with roots + vendored rows).

### Spot check (leaf modules)

- `DoubleSlit`, `MeasurementChannel`, `EpistemicRuntimeContract` compile under `lake build`.

## 3) Haskell — Structural Rigour

- `cabal build` & `cabal test`: **PASS**
- **Test suites:** **2** Cabal test targets — `umst-formal-double-slit-test` (`test/Main.hs`) and `landauer-einstein-sanity` (`test/LandauerEinsteinSanity.hs`). Running `cabal test` executes **both**.
- **QuickCheck:** `test/Main.hs` runs **14** `quickCheckResult` blocks (complementarity, which-path, Landauer bounds, MeasurementCost, EpistemicGalois, LandauerExtension, MonoidalState, …).
- `umst-formal-double-slit.cabal` **exposed-modules** vs `Haskell/src/`: should list every shipped module (`DensityState`, `MeasurementChannel`, `DoubleSlit`, `MeasurementCost`, `EpistemicGalois`, `LandauerExtension`, `MonoidalState`).
- **`cabal.project.freeze`:** re-run `cabal freeze` in `Haskell/` after changing `build-depends`.

## 4) Python / `sim/` — Per-file rigour

**Sim scripts:** validate with `main()` / `--validate` as documented in `sim/README.md`.

**Tests:** `python3 -m unittest discover -s sim/tests -p "test_*.py"`

- With **optional** deps installed (per `sim/requirements-optional.txt`), QuTiP / SciPy / matplotlib tests typically run with **fewer skips**.
- Without those deps, many tests **skip** by design — this is **not** a failure of `make ci-local`, but it **reduces** exercised coverage; engineers should note skip counts in logs.

**Hygiene:** avoid committing secrets under `sim/out/`; keep requirements files accurate.

## 5) CI Workflows

- **`lean.yml`:** `lake build` → `pip install -r sim/requirements-optional.txt` → `make sim` + `unittest` (see workflow for exact steps).
- **`haskell.yml`:** `cabal test` in `Haskell/`.
- **Branch protection caveat:** path filters may **skip** jobs on docs-only PRs. If policy requires green checks on every merge, widen `paths` or add a lightweight “always run” job.

## 6) Documentation consistency

- **`README.md`:** high-level list + **vendored** section; exhaustive module listing lives in **`Lean/VERIFY.md`**.
- **`Docs/PARALLEL_WORK.md` / `Docs/TODO-TRACKING.md`:** should agree on cross-lang DONE/CLAIMED rows; reconcile after large merges.

## 7) Deliverables summary

| Component | Status | Note |
|-----------|--------|------|
| Lean | PASS | 10 intentional `sorry` in `DensityState` / `MeasurementChannel`; 1 explicit `axiom` in `LandauerLaw` |
| ci-local | PASS | Lean + default sim + unittest |
| ci-full | PASS | ci-local + `cabal test` (both Haskell suites) |
| Unittest | PASS | count varies with optional deps; check skip lines when deps missing |

**Residual risks**

- Python: without optional packages, **skipped** tests can hide regressions unless CI installs the same extras as “full” local runs.
- GitHub: docs-only PRs + strict path filters can **bypass** Lean/Haskell workflows — align branch rules with intent.

---

## 8) Errata (corrections to the original audit text)

| Original claim | Correction |
|----------------|------------|
| “30 module roots” | **37** roots in `lakefile.lean` (as of vendored upstream reference modules). |
| “9 suites in `Main.hs`” | **14** QuickCheck runs in `test/Main.hs`; **2** Cabal **test suites** total. |
| “Admit inventory: None” | List **`axiom physicalSecondLaw`** in `LandauerLaw.lean` as an explicit axiom (not a `sorry`). |
| Sorry grep | Always **exclude** `Lean/.lake/` when counting project sorries. |

## 9) How to re-verify quickly

```bash
cd Lean && lake build
cd .. && make ci-full
# Optional:
make coq-check && make agda-check
```

Count sorries (project only):

```bash
rg '^\s*sorry\b' Lean --glob '*.lean' --glob '!**/.lake/**'
```

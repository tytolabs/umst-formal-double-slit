# Parallel agents / swarm coordination (double-slit fork)

Use this checklist so multiple assistants (or humans) don’t overwrite the same work.

**Also read:** root **`CONTRIBUTING.md`**, **`scripts/README.md`** (Lean stats helper), **`sim/README.md`** (what’s already in `sim/` vs open roadmap), **`Docs/TODO-TRACKING.md`** (milestone reconciliation vs swarm todos), **`Docs/SCOPE_PARENT_AND_SEPARATE_REPO.md`** (plain-language: this folder vs parent repo, separate-repo option).

## Before you add or replace a file

1. **Search** the repo for the filename or feature (e.g. `glob **/Foo.md`, `grep Foo`).
2. If the file **already exists**, **edit** it instead of creating `Foo-v2.md` unless the user asked for a duplicate.
3. **Hot paths** (high merge-conflict risk — pull/re-read before editing):
   - `.github/workflows/lean.yml`
   - `.github/workflows/haskell.yml` (Cabal / QuickCheck)
   - `Makefile`
   - `Lean/lakefile.lean`, `Lean/EpistemicGalois.lean`, vendored **`Lean/Gate.lean`**, **`Lean/LandauerLaw.lean`**, **`Lean/MonoidalState.lean`**, …
   - **`Haskell/`** (`.cabal`, **`cabal.project`**, **`cabal.project.freeze`**, `src/` incl. **`EpistemicGalois.hs`**, **`LandauerExtension.hs`**, **`MonoidalState.hs`**, `test/`, `app/`) — often owned by a **parallel Haskell track**; avoid mixing Lean/Python edits in the same commit unless coordinated.
   - **`Coq/`**, **`Agda/`** (vendored stubs; run **`make coq-check`** / **`make agda-check`** locally)
   - `README.md`, `CHANGELOG.md`, `PROOF-STATUS.md`, `Lean/VERIFY.md`
   - `sim/toy_double_slit_mi_gate.py`, `sim/qubit_kraus_sweep.py`, `sim/qutip_qubit_kraus.py`, `sim/qutip_schrodinger_2d_free_parity.py`, `sim/qutip_schrodinger_2d_slit_parity.py`, `sim/plot_*_svg.py` (incl. `plot_schrodinger_*_svg.py`), `sim/spatial_free_gaussian_1d.py`, `sim/classical_double_slit_far_field.py`, `sim/schrodinger_1d_free_fft.py`, `sim/schrodinger_1d_split_step.py`, `sim/schrodinger_1d_soft_double_slit.py`, `sim/schrodinger_1d_absorbing_edges.py`, `sim/schrodinger_2d_soft_double_slit.py`, `sim/schrodinger_2d_absorbing_edges.py`, `sim/schrodinger_2d_complex_absorb_mask.py`, `sim/benchmark_schrodinger_2d_split_step_vs_fd.py`, `sim/schrodinger_2d_sparse_fd_expm_smoke.py`, `sim/requirements-optional.txt`
   - `sim/tests/test_*.py` (Python regression tests — coordinate when adding overlapping smoke tests)
   - `scripts/lean_decl_stats.py` (declaration heuristics; keep in sync with `PROOF-STATUS` paste workflow)

## Python / CI

- **Default local check:** `make ci-local` from `umst-formal-double-slit/` (Lean + stdlib sim + tests).
- **`lean.yml`:** after `lake build`, `pip install -r sim/requirements-optional.txt`, then the four sim scripts + **`unittest`** (matplotlib/GIF/QuTiP smoke tests when imports succeed). **Path filters:** runs only when **`Lean/**`**, **`sim/**`**, root **`Makefile`**, or **`lean.yml`** changes (docs-only PRs skip this job).
- **`haskell.yml`:** `cabal test` in `Haskell/` (separate job). **Path filters:** **`Haskell/**`** or **`haskell.yml`** only.
- **Local env without pip extras:** QuTiP / GIF tests may **skip**; core sim + Lean should still pass.
- **Full local check (optional):** `make ci-full` → `ci-local` + `haskell-test` (needs GHC/cabal).

## Suggested next jobs (coordinate before claiming)

Pick a row, **glob/grep for the output path**, then implement. Avoid two agents on the same **hot path** in one PR.

| Track | Next job (high value) | Typical owner | Before you start |
|-------|------------------------|---------------|------------------|
| **Python** | Beyond **`schrodinger_2d_sparse_fd_expm_smoke.py`** (SciPy **CSR** FD H + **`expm_multiply`** vs dense): **stretched-coordinate PML**, split-field / **3D**, **QuTiP** wired to same sparse **H**, analytic ABC references; optional deps / not in default `make sim` | Sim agent | `glob sim/qutip*.py` `glob sim/schrodinger*.py` `glob sim/benchmark*.py` `glob sim/*sparse*` — don’t duplicate starters |
| **Lean / formal** | Ground ODE–PPO / runtime evidence for **`p3-epistemic-sensing`** (telemetry ε lemmas already exist) | Formal agent | `Lean/Epistemic*.lean`, `Lean/VERIFY.md`; `lake build` |
| **Haskell** | Extend QuickCheck as Lean surface grows (baseline: `DoubleSlit`, `MeasurementChannel`, `MeasurementCost`) | Parity agent | `Haskell/test/Main.hs`, `*.cabal`; **`cabal freeze`** after `build-depends` edits |
| **CI** | **DONE** — **`lean.yml`** / **`haskell.yml`** use **`on.push` / `on.pull_request` `paths`** (see **Python / CI** above). **Open:** optional `workflow_dispatch`, status badges, or `paths` tweaks (e.g. include root `README.md`) | Either | read `.github/workflows/*.yml` |
| **Docs / meta** | Refresh **Lean declaration statistics** in `PROOF-STATUS.md` via **`make lean-stats-md`** (paste; keep relative **`Lean`** root) | Either | `scripts/README.md` |
| **Cross-lang** | **`a1-measurement-cost`** | **DONE** — `Lean/MeasurementCost.lean` + `Haskell/src/MeasurementCost.hs` in fork; Coq/Agda in base | `glob **/MeasurementCost*` |
| **Cross-lang** | **`a1-extend-landauer`** | **DONE** — vendored: `Lean/LandauerLaw.lean`, `Lean/LandauerExtension.lean`, `Lean/LandauerEinsteinBridge.lean`; `Haskell/src/LandauerExtension.hs` + test `LE.*` QC + `landauer-einstein-sanity`; `Coq/LandauerEinsteinBridge.v`; `Agda/LandauerEinsteinTrace.agda` (trace stub) | `make coq-check` / `make agda-check` optional |
| **Cross-lang** | **`a1-fibered-activation`** | **DONE (Lean)** — `Lean/FiberedActivation.lean` (+ deps `Gate`/`Naturality`/`Activation` vendored). Parent has **no** Haskell `FiberedActivation` | `lake build` |
| **Cross-lang** | **`a1-monoidal-state`** | **DONE** — `Lean/MonoidalState.lean`, `Haskell/src/MonoidalState.hs` + QC (`prop_ms_*`) | `glob **/MonoidalState*` |
| **Cross-lang** | **`a1-epistemic-galois`** | **DONE** — `Lean/EpistemicGalois.lean` & `Haskell/src/EpistemicGalois.hs` | `glob **/EpistemicGalois*` |

**Swarm log (recent):** **`Docs/TODO-TRACKING.md`** — synced with shipped **2D** sim, **CI paths**, sparse smoke. **CI:** **`lean.yml`** + **`haskell.yml`** — **`paths`** filters (Lean/sim/Makefile vs Haskell-only). **Python:** **`schrodinger_2d_sparse_fd_expm_smoke.py`** + **`sim/tests/test_schrodinger_2d_sparse_fd_expm_smoke.py`**. **`schrodinger_2d_complex_absorb_mask.py`** + **`sim/tests/test_schrodinger_2d_complex_absorb_mask.py`** (PML-style **caricature**: ``m e^{iφ}`` per axis; **κ=0** ≡ real sponge). **`benchmark_schrodinger_2d_split_step_vs_fd.py`** + **`sim/tests/test_benchmark_schrodinger_2d_split_step_vs_fd.py`** (timing + max rel **ρ** gap vs FD+`expm`). **`qutip_schrodinger_2d_slit_parity.py`** + **`sim/tests/test_qutip_2d_slit_parity.py`** (FD kinetic + **`soft_double_slit_potential_2d`** on grid; optional split-step vs FD diagnostic). **`schrodinger_2d_absorbing_edges.py`** + **`sim/tests/test_schrodinger_2d_absorbing_edges.py`** (separable sponge; same **`x,y,rho`** CSV + 2D heatmap plotter). **`qutip_schrodinger_2d_free_parity.py`** + **`sim/tests/test_qutip_2d_free_parity.py`**; **`test_qutip_parity.py`** fix (call **`identity_kraus()`** / **`which_path_kraus()`**). **`schrodinger_2d_soft_double_slit.py`** + **`plot_schrodinger_2d_soft_double_slit_svg.py`** + tests. **`plot_schrodinger_split_step_svg.py`** + **`sim/tests/test_plot_schrodinger_split_step_svg.py`**. **`plot_schrodinger_absorbing_edges_svg.py`** + tests; **`schrodinger_1d_absorbing_edges.py`**; **`plot_schrodinger_soft_double_slit_svg.py`**; **`schrodinger_1d_soft_double_slit.py`**. Not in four-script `make sim`. **`sim/requirements-optional.txt`**: **`numpy`**. **`Haskell/cabal.project`** + **`cabal.project.freeze`**. **`lean.yml` / `haskell.yml`**: **`concurrency`**. **`scripts/README.md`**: **`make lean-stats`** / **`lean-stats-md`**. **Cross-lang table** is source of truth for DONE/CLAIMED. **active claims (swarm):** *none* for the former Landauer / monoidal / fibered rows (**vendored 2026-03** from parent `umst-formal`). Next open cross-lang work is **A0 Coq/Agda** mirrors beyond the slim `Coq/` + `Agda/` stubs (coordinate before growing trees).

**Claiming protocol (lightweight):** in your PR description, write `Tracks: Lean`, `Tracks: Haskell`, or `Tracks: Python` so reviewers see overlap risk.

**Claim hygiene:** when a **CLAIMED** row ships, update this file in the same PR: mark **DONE** with pointers (`glob` paths), and append a line to the swarm log. **Never mark cross-lang rows COMPLETED** unless matching artifacts exist in **Lean + Coq + Agda + Haskell** (or the table explicitly scopes “partial”).

**Hot-path merge conflicts:** if two branches touch the same file under **Hot paths**, prefer **rebase onto main** then a single integration push; avoid “last writer wins” on `lakefile.lean`, workflows, or `Makefile`.

## Lean

- After **any** Lean change: `cd Lean && lake build` (or `make lean`).

## Docs

- Contributor checklist: root **`CONTRIBUTING.md`**.
- Lean stat helper: **`scripts/README.md`**.
- Planned outreach files live under `Docs/` (see root `README.md` links). Do **not** reintroduce removed artifacts (e.g. social-thread drafts) unless the user explicitly requests them.

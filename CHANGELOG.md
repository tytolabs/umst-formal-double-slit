# Changelog — umst-formal-double-slit

All notable changes to this **standalone repository** are listed here. The upstream framework repo has its own history.

## [Unreleased]

### Added (formal — integrated from upstream framework)

- **Lean:** `LandauerLaw.lean`, `LandauerExtension.lean`, `LandauerEinsteinBridge.lean`, `Gate.lean`, `Naturality.lean`, `Activation.lean`, `FiberedActivation.lean`, `MonoidalState.lean` — registered as extra roots in `Lean/lakefile.lean` (alongside `UMST.DoubleSlit` modules).
- **Haskell:** `LandauerExtension.hs`, `MonoidalState.hs`; QuickCheck blocks `prop_le_*` / `prop_ms_*`; test suite **`landauer-einstein-sanity`** (`Haskell/test/LandauerEinsteinSanity.hs`).
- **Coq:** `Coq/LandauerEinsteinBridge.v`, `Coq/_CoqProject`, `Coq/README.md`; **`make coq-check`** in root `Makefile`.
- **Agda:** `Agda/LandauerEinsteinTrace.agda`; **`make agda-check`**.
- **Gitignore:** Coq `*.vo` / `*.glob` / `.*.aux`; Agda `_build/`.

### Added (docs / coordination)

- `Docs/AGENT_VERIFICATION_PROMPT.md` — copy-paste instructions for another agent to re-verify Lean/Python/Haskell/optional Coq–Agda + docs; linked from **`README.md`** + **`PARALLEL_WORK.md`**.
- `Docs/DEEP_VERIFICATION_REPORT.md` — archived deep verification audit (build gates, **10** project `sorry` sites, **`physicalSecondLaw` axiom**, lake root count, Haskell **2** Cabal suites / **14** QuickCheck blocks, CI skip caveats); **canonical path** (case-sensitive); linked from **`README.md`** + **`PARALLEL_WORK.md`**.
- `Docs/VENDOR_SYNC.md` — checklist for re-syncing vendored formal files with upstream `umst-formal`.
- `Docs/REPO_CLEANUP_PLAN.md` — phased cleanup / doc polish / per-file audit checklist; linked from **`README.md`** + **`PARALLEL_WORK.md`**.
- `Docs/SCOPE_PARENT_AND_SEPARATE_REPO.md` — sorts issues in plain language (this tree vs upstream framework), optional standalone repo; linked from **`README.md`** + **`PARALLEL_WORK.md`**.
- `Docs/TODO-TRACKING.md` — reconciles milestones vs in-editor todos; **`PARALLEL_WORK.md`** + root **`README.md`** link it; **`a1-measurement-cost`** row = **PARTIAL** (Lean + Haskell in tree). **A0 Coq/Agda** described as **tracked**, not “out of scope / cancelled.”

### Changed (docs / coordination)

- `Docs/TODO-TRACKING.md` — refreshed **Done** (2D sim, complex mask, benchmark, QuTiP 2D, **sparse FD smoke**, **CI `paths`**), **Open next**, and **CLAIMED** rows (`monoidal-state`, `epistemic-galois`); editor-todo sync note.

### Fixed (Python / tests)

- `sim/tests/test_qutip_parity.py` — pass **Kraus operator lists** (`identity_kraus()`, `which_path_kraus()`) into `kraus_apply`, not the factory functions.

### Added (Python / sim)

- `sim/schrodinger_2d_sparse_fd_expm_smoke.py` — CSR FD **H** + soft slit **V**; **`expm_multiply`** vs dense **`expm`**; `sim/tests/test_schrodinger_2d_sparse_fd_expm_smoke.py` (skips without SciPy sparse).
- `sim/schrodinger_2d_complex_absorb_mask.py` — separable **complex** edge mask (real taper × ``e^{iφ}``); **κ=0** ≡ real sponge; `sim/tests/test_schrodinger_2d_complex_absorb_mask.py`.
- `sim/benchmark_schrodinger_2d_split_step_vs_fd.py` — timings + max rel **ρ** gap (split-step vs FD+`expm`); `sim/tests/test_benchmark_schrodinger_2d_split_step_vs_fd.py` (skips without SciPy).
- `sim/qutip_schrodinger_2d_slit_parity.py` — QuTiP vs scipy on **FD H + diag soft slit V**; optional split-step vs FD ρ diagnostic; `sim/tests/test_qutip_2d_slit_parity.py`.
- `sim/schrodinger_2d_absorbing_edges.py` — 2D soft slit + separable edge sponge; `sim/tests/test_schrodinger_2d_absorbing_edges.py`; CSV matches `plot_schrodinger_2d_soft_double_slit_svg.py`.
- `sim/qutip_schrodinger_2d_free_parity.py` — QuTiP `sesolve` vs `scipy.linalg.expm` on the same 2D periodic FD free Hamiltonian; optional FFT-vs-FD diagnostic; `sim/tests/test_qutip_2d_free_parity.py`.
- `sim/schrodinger_2d_soft_double_slit.py` — 2D Strang split-step, soft screen + two y-openings; validate vs 2D FFT (`--v0 0`); `sim/tests/test_schrodinger_2d_soft_double_slit.py`.
- `sim/plot_schrodinger_2d_soft_double_slit_svg.py` — stdlib heatmap SVG; `sim/tests/test_plot_schrodinger_2d_soft_double_slit_svg.py`.
- `sim/schrodinger_1d_free_fft.py` — free 1D Schrödinger on a periodic grid (NumPy FFT), validated vs `spatial_free_gaussian_1d`; `sim/tests/test_schrodinger_1d_free_fft.py` (skipped without NumPy). `sim/requirements-optional.txt` — explicit **`numpy`** line.
- `sim/schrodinger_1d_split_step.py` — Strang split-step with optional Gaussian barrier; `sim/tests/test_schrodinger_1d_split_step.py` (V=0 vs FFT, barrier norm smoke).
- `sim/schrodinger_1d_soft_double_slit.py` — soft screen + two openings; `sim/tests/test_schrodinger_1d_soft_double_slit.py`.
- `sim/plot_schrodinger_split_step_svg.py` — stdlib SVG for `schrodinger_split_step_rho.csv`; `sim/tests/test_plot_schrodinger_split_step_svg.py`.
- `sim/plot_schrodinger_absorbing_edges_svg.py` — stdlib SVG for `schrodinger_absorbing_edges_rho.csv`; `sim/tests/test_plot_schrodinger_absorbing_edges_svg.py`.
- `sim/schrodinger_1d_absorbing_edges.py` — edge sponge after each Strang step; `sim/tests/test_schrodinger_1d_absorbing_edges.py`.
- `sim/plot_schrodinger_soft_double_slit_svg.py` — stdlib SVG for rho + scaled V; `sim/tests/test_plot_schrodinger_soft_double_slit_svg.py`.
- `sim/spatial_free_gaussian_1d.py` — closed-form |ψ|² for a spreading 1D Gaussian (stdlib); `sim/tests/test_spatial_free_gaussian.py`. Documented in `sim/README.md`; **not** added to default `make sim` / lean.yml four-script block (unittest covers it).
- `sim/classical_double_slit_far_field.py` — Fraunhofer double-slit intensity (stdlib); `sim/tests/test_classical_double_slit_far_field.py`. Same integration pattern as other optional sim scripts.
- `sim/plot_classical_double_slit_svg.py` — stdlib SVG for that curve; `sim/tests/test_plot_classical_double_slit_svg.py`.
- `sim/plot_spatial_free_gaussian_svg.py` — stdlib SVG for |ψ|² vs x; `sim/tests/test_plot_spatial_free_gaussian_svg.py`.

### Changed (CI / coordination)

- `.github/workflows/lean.yml`, `haskell.yml` — **`paths`** filters so jobs skip doc-only / unrelated edits (Lean+sim+`Makefile` vs `Haskell/**`); **`Docs/PARALLEL_WORK.md`** documents behavior.
- `Docs/PARALLEL_WORK.md` — **`a1-measurement-cost`** = **PARTIAL**; **`a1-extend-landauer`** + **`a1-epistemic-galois`** claims; **Python** next = post–`plot_schrodinger_absorbing_edges_svg`.
- `.github/workflows/lean.yml`, `haskell.yml` — **`concurrency`** groups (cancel superseded runs on same ref).
- `Makefile` — **`ci-full`** target (`ci-local` + `haskell-test`).
- `Docs/PARALLEL_WORK.md` — restored actionable job table; fixed **`make lean-stats-md`** wording; merged swarm notes; **`sim/README.md`** in “Also read”; claim + hot-path merge tips; **reverted false `a1-measurement-cost` COMPLETED** (no cross-lang tree in repo); stricter **claim hygiene** note.

### Added (tooling / docs)

- `scripts/README.md` — how to run `lean_decl_stats.py` / `make lean-stats-md`.

### Added (Haskell)

- `Haskell/cabal.project.freeze` — dependency pins from `cabal freeze` (Hackage `index-state` + constraints).

### Changed (docs / CI)

- `scripts/lean_decl_stats.py --markdown` prints **repo-relative** `Lean` path when run from repo root.
- `PROOF-STATUS.md` — Lean stats block uses portable `Lean` root (no machine-specific paths).
- `Haskell/cabal.project` — `packages: .` for explicit project root + future freeze; `haskell.yml` cache key includes `cabal.project` / optional `.freeze`.

### Added (repo hygiene)

- Root **`.gitignore`** — `Haskell/dist-newstyle/`, Python `__pycache__`, `.DS_Store`.

### Added (Lean)

- **UMSTCore** — ℝ Landauer scale + `ThermodynamicState` + `Admissible` conjuncts.
- **DensityState** — `DensityMatrix`, `pureDensity`, `DensityMatrix.ext`.
- **MeasurementChannel** — Kraus channels, `whichPathChannel` (Lüders dephasing), `compose` / `apply_compose`.
- **QuantumClassicalBridge** — `pathWeight`, `whichPathDistinguishability`, `fringeVisibility`, `complementarity_fringe_path`, `observationStateCanonical`.
- **InfoEntropy** — `shannonBinary` (= Mathlib `Real.binEntropy`), `vonNeumannDiagonal`, `vonNeumannDiagonal_le_log_two`.
- **LandauerBound** — `pathEntropyBits`, `landauerCostDiagonal`, `pathEntropyBits_le_one`, `landauerCostDiagonal_le_landauerBitEnergy`.
- **EpistemicSensing** — `QuantumProbe`, `nullProbe`/`whichPathProbe`, max witnesses (`Set` + finite-family argmax, strict-positive selection), collapse/preserve theorems, Landauer-from-strength bounds.
- **GateCompat** — `thermoFromQubitPath`, `admissible_thermoFromQubitPath_whichPath`.
- **Complementarity** — discoverability shims over the bridge.
- **DoubleSlit** — import closure, `measurementUpdateWhichPath`, Landauer equalities along which-path, plus narrative wrappers: `interference_preserved_identity`, `collapse_fringe_on_whichPath`, `measurementUpdateWhichPath_gateEnforcement`.
- **EpistemicMI** — probe-indexed MI (`PathProbe`) in nats/bits, with Landauer-cost links.
- **EpistemicDynamics** — probe-policy rollouts with null/which-path invariants.
- **EpistemicTrajectoryMI** — cumulative finite-horizon MI/cost and bounds.
- **EpistemicPolicy** — finite-horizon policy utility, argmax, constrained policy optimality.
- **EpistemicRuntimeContract** — trace-coherence and aggregate-contract bridge between rollout traces and policy theorems.
- **EpistemicNumericsContract** — numeric rollout record (`NumericTraceRecord`), consistency predicates, and utility equivalence to `policyUtility`.
- **EpistemicPerStepNumerics** — per-step record (`PerStepNumericRecord`), finite-fold consistency to cumulative MI/cost, and projection bridge to `NumericTraceRecord`.
- **EpistemicRuntimeSchemaContract** — emitted runtime schema (`EmittedStepRecord`, `EmittedTraceSchema`) plus transfer theorems from rollout-consistent emitted traces to per-step/aggregate utility contracts.
- **EpistemicTelemetryBridge** — runtime telemetry naming bridge (`trajMI`, `effortCost`) with explicit consistency assumptions and theorem transfer to emitted/per-step/aggregate contracts.
- **EpistemicTelemetryApproximation** — epsilon-approximation interface for runtime numerics (ODE/PPO surrogates) with zero-error transfer to exact telemetry/schema/numeric contracts.
- **EpistemicTelemetryQuantitativeUtility** — explicit nonzero-error utility deviation bounds from aggregate approximation assumptions (`εMI`, `εCost`, `λ`, `T`).
- **EpistemicTraceDerivedEpsilonCertificate** — residual-based epsilon extraction from concrete telemetry traces with direct transfer to quantitative utility bounds.
- **EpistemicTelemetrySolverCalibration** — explicit solver calibration parameters (`stepSize`, `order`, error coefficients) mapped to epsilon budgets with transfer assumptions for utility bounds.
- **EpistemicTraceDrivenCalibrationWitness** — trace witness wrapper (`TraceCalibrationWitnessAt`) that packages telemetry and calibration assumptions and transfers directly to utility-bound theorems.
- **PrototypeSolverCalibration** — concrete prototype calibration constants with explicit epsilon-budget formulas and specialized utility-bound wrappers.
- **ProbeOptimization** — `ProbeUtility`, finite argmax selection, admissibility-constrained optimality existence.
- **ExamplesQubit** — `rhoPlus`, `rhoZero`, `rhoOne`; imports **`ProbeOptimization`**; epistemic/optimization + measurement-update corollaries.
- **Docs** — `ASSUMPTIONS-DOUBLE-SLIT.md` (scope / non-claims).

### Added (tooling / docs)

- `Lean/VERIFY.md`, `PROOF-STATUS.md`, `Docs/DoubleSlit-Derivation.md`.
- `Docs/EpistemicSensingQuantum.md` — index of epistemic + quantum Lean modules and sim parity (working note).
- `Docs/PARALLEL_WORK.md` — checklist for multi-agent edits (hot paths, CI vs local).
- `CONTRIBUTING.md` — PR checklist (`make ci-local`, optional pip, Lean note).
- `sim/tests/test_toy_matplotlib_smoke.py` — optional smoke test for `toy_double_slit_mi_gate.py --plot` when matplotlib is installed.
- `sim/tests/test_toy_gif_smoke.py` — optional smoke test for `--generate-gif` when matplotlib + imageio are installed.
- `scripts/lean_decl_stats.py` + **`make lean-stats`** — heuristic Lean declaration counts (`.lake` excluded).
- `Haskell/README.md` — build/test instructions for the Cabal mirror.
- `.github/workflows/haskell.yml` — CI `cabal test` on Ubuntu (GHC 9.14); **Cabal store + `dist-newstyle` cache** (`actions/cache@v4`).
- **`make haskell-test`** — local Cabal test from repo `Makefile`.
- `Docs/OnePager-DoubleSlit.tex` — compact LaTeX one-pager (`pdflatex` locally).
- `Makefile` (`lean`, `lean-clean`, `sim`, `sim-test`, `ci-local`).
- `.github/workflows/lean.yml`.
- `sim/tests/test_toy_double_slit.py` (toy simulator regression checks).
- `sim/qubit_kraus_sweep.py` — stdlib 2×2 Kraus (identity + Lüders which-path) with Lean-aligned `V`, `I`, `V²+I²` checks; default `sim/out/qubit_kraus_sweep.csv`.
- `sim/tests/test_qubit_kraus_sweep.py`.
- `sim/plot_complementarity_svg.py` — stdlib SVG Englert quarter-disk from `qubit_kraus_sweep.csv` (`sim/out/complementarity_qubit_sweep.svg`); `--validate` checks `V²+I²≤1`.
- `sim/plot_toy_complementarity_svg.py` — stdlib SVG (I,V) curve from `results_double_slit_toy.csv` (`sim/out/complementarity_toy_sweep.svg`).
- `sim/tests/test_complementarity_svg.py`.
- `sim/tests/test_toy_complementarity_svg.py`.
- `sim/qutip_qubit_kraus.py` + `sim/requirements-optional.txt` + `sim/tests/test_qutip_parity.py` (QuTiP parity; tests skip if `qutip` missing).
- `sim/README.md` (simulator usage, output paths, Python roadmap).
- `.github/workflows/lean.yml` — post-Lean Python `sim` + `unittest` on Ubuntu.

### Not in scope (yet)

- Full spatial double-slit / Schrödinger dynamics; matplotlib animation / GIF export; physical `dissipation ≥ Landauer` for a concrete process; Haskell QC in CI; theorem-count automation in CI.

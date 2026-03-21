# TODO / milestone tracking (double-slit repository)

Reconciled periodically with the repo and any **in-editor todo list** (Cursor).
If editor todos drift, treat **this file** as the reconciliation source.

## Done in tree (high level)

- **Lean:** double-slit stack (`UMSTCore` … `DoubleSlit`), measurement channel / Lüders bridge, `LandauerBound` (+ Principle of Maximal Information Collapse), complementarity, **`MeasurementCost.lean`**, **`EpistemicGalois.lean`**, extensive **`Epistemic*.lean`** telemetry bridges; **integrated upstream reference core:** **`LandauerLaw` / `LandauerExtension` / `LandauerEinsteinBridge`**, **`Gate` / `Naturality` / `Activation` / `FiberedActivation` / `MonoidalState`** (registered in `lakefile.lean`). **All sorry eliminated** (DensityState + MeasurementChannel projector properties proved).
- **Haskell:** `DoubleSlit`, `MeasurementChannel`, **`MeasurementCost.hs`**, **`EpistemicGalois.hs`**, **`LandauerExtension.hs`**, **`MonoidalState.hs`**, QuickCheck + **`landauer-einstein-sanity`**, Cabal CI (`haskell.yml`).
- **Coq / Agda:** slim trees — **`Coq/LandauerEinsteinBridge.v`**, **`Agda/LandauerEinsteinTrace.agda`**; local **`make coq-check`** / **`make agda-check`**.
- **Python:** toy + Kraus + QuTiP qubit parity; stdlib SVG plots; closed-form Gaussian + classical Fraunhofer; **`schrodinger_1d_*`** (FFT, split-step, soft slit, absorbing); **`schrodinger_2d_soft_double_slit`**, **`schrodinger_2d_absorbing_edges`**, **`schrodinger_2d_complex_absorb_mask`**; **QuTiP** 2D free + slit FD parity; **`benchmark_schrodinger_2d_split_step_vs_fd`**; **`schrodinger_2d_sparse_fd_expm_smoke`** (sparse `expm_multiply` vs dense); tests under `sim/tests/`.
- **CI:** `lean.yml` (Lake + optional pip + sim + unittest), `haskell.yml`, **`paths` filters**, concurrency, `make ci-local` / `make ci-full`.

## In progress / owned elsewhere

- **`p3-epistemic-sensing`:** ground ODE–PPO / runtime evidence vs existing Epistemic modules (see `Lean/Epistemic*.lean`, `Lean/VERIFY.md`).

## Open next

- **Python:** stretched-coordinate **PML**, split-field / 3D strips, **QuTiP** on large sparse workflows; analytic ABC reference checks.
- **Lean:** extend `InfoEntropy` (general n, MI, DPI); calibrated thermo map in `GateCompat`.
- **Haskell:** more QC properties as Lean surface grows; keep **`cabal freeze`** in sync.
- **CI:** optional `workflow_dispatch`, badges.
- **Docs:** re-paste **`make lean-stats-md`** into `PROOF-STATUS.md` after large Lean edits.

## Tracked cross-formalism work (`Coq/` + `Agda/` started — mostly stubs)

- **A0 Coq parity** / **A0 Agda parity:** beyond **`LandauerEinsteinBridge.v`** and **`LandauerEinsteinTrace.agda`**, port **`Gate`**, **`MonoidalState`**, **`InfoTheory`**, etc. from upstream reference **`umst-formal`** when you want full 4-language alignment.

## Cross-lang `a1-measurement-cost`

**Repository status:** **Lean + Haskell** artifacts exist (`Lean/MeasurementCost.lean`, `Haskell/src/MeasurementCost.hs`).
**Coq/Agda:** **partial** — slim trees exist (`Coq/LandauerEinsteinBridge.v`, `Agda/LandauerEinsteinTrace.agda`); there is **no** `MeasurementCost` in Coq/Agda **here** yet → full 4-language parity for this ticket remains **partial**.

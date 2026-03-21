# TODO / milestone tracking (double-slit repository)

Reconciled periodically with the repo, **`Docs/PARALLEL_WORK.md`**, and any **in-editor todo list** (Cursor).  
**Last checklist pass:** reconcile Cursor todos with the **Open** section below.  
If editor todos drift, treat **this file + `PARALLEL_WORK`** as the reconciliation source.

## Done in tree (high level)

- **Lean:** double-slit stack (`UMSTCore` … `DoubleSlit`), measurement channel / Lüders bridge, `LandauerBound`, complementarity, **`MeasurementCost.lean`**, **`EpistemicGalois.lean`**, extensive **`Epistemic*.lean`** telemetry bridges; **integrated upstream reference core:** **`LandauerLaw` / `LandauerExtension` / `LandauerEinsteinBridge`**, **`Gate` / `Naturality` / `Activation` / `FiberedActivation` / `MonoidalState`** (registered in `lakefile.lean`).
- **Haskell:** `DoubleSlit`, `MeasurementChannel`, **`MeasurementCost.hs`**, **`EpistemicGalois.hs`**, **`LandauerExtension.hs`**, **`MonoidalState.hs`**, QuickCheck + **`landauer-einstein-sanity`**, Cabal CI (`haskell.yml`).
- **Coq / Agda:** slim trees — **`Coq/LandauerEinsteinBridge.v`**, **`Agda/LandauerEinsteinTrace.agda`**; local **`make coq-check`** / **`make agda-check`**.
- **Python:** toy + Kraus + QuTiP qubit parity; stdlib SVG plots; closed-form Gaussian + classical Fraunhofer; **`schrodinger_1d_*`** (FFT, split-step, soft slit, absorbing); **`schrodinger_2d_soft_double_slit`**, **`schrodinger_2d_absorbing_edges`**, **`schrodinger_2d_complex_absorb_mask`**; **QuTiP** 2D free + slit FD parity; **`benchmark_schrodinger_2d_split_step_vs_fd`**; **`schrodinger_2d_sparse_fd_expm_smoke`** (sparse `expm_multiply` vs dense); tests under `sim/tests/`.
- **CI:** `lean.yml` (Lake + optional pip + sim + unittest), `haskell.yml`, **`paths` filters** (Lean+`sim`+`Makefile` vs `Haskell/**`), concurrency, `make ci-local` / `make ci-full`.

## In progress / owned elsewhere

- **`p3-epistemic-sensing`:** ground ODE–PPO / runtime evidence vs existing Epistemic modules (see `Lean/Epistemic*.lean`, `Lean/VERIFY.md`).

## Open next (see `PARALLEL_WORK.md` table)

- **Python:** stretched-coordinate **PML**, split-field / 3D strips, **QuTiP** on large sparse workflows (SciPy sparse hook exists); analytic ABC reference checks.
- **Lean:** extend `InfoEntropy` (general n, MI, DPI); concrete erasure vs Landauer bound.
- **Haskell:** more QC properties as Lean surface grows; keep **`cabal freeze`** in sync.
- **CI:** optional `workflow_dispatch`, badges, or widen `paths` (e.g. root `README.md`) if branch protection needs checks on doc-only PRs.
- **Docs:** re-paste **`make lean-stats-md`** into `PROOF-STATUS.md` after large Lean edits.

## Tracked cross-formalism work (`Coq/` + `Agda/` started — mostly stubs)

- **A0 Coq parity** / **A0 Agda parity:** beyond **`LandauerEinsteinBridge.v`** and **`LandauerEinsteinTrace.agda`**, port **`Gate`**, **`MonoidalState`**, **`InfoTheory`**, etc. from upstream reference **`umst-formal`** when you want full 4-language alignment — coordinate in **`Docs/PARALLEL_WORK.md`** before expanding `_CoqProject` / Agda modules.

## Cross-lang `a1-measurement-cost`

**Repository status:** **Lean + Haskell** artifacts exist (`Lean/MeasurementCost.lean`, `Haskell/src/MeasurementCost.hs`).  
**Coq/Agda:** **partial** — slim trees exist (`Coq/LandauerEinsteinBridge.v`, `Agda/LandauerEinsteinTrace.agda`); there is **no** `MeasurementCost` in Coq/Agda **here** yet → full 4-language parity for this ticket remains **partial**. **`PARALLEL_WORK.md`** cross-lang table may mark **DONE** for a narrower scope — follow that table when it conflicts with this paragraph.

# umst-formal-double-slit — proof status (Lean)

**Build:** from `Lean/`, run `lake build` (or repo root `make lean`).  
**CI:** `.github/workflows/lean.yml` (Ubuntu, Elan, optional Mathlib `lake exe cache get`, `pip install -r sim/requirements-optional.txt`, then Python `sim` + `unittest`); `.github/workflows/haskell.yml` (Cabal `test` in `Haskell/`).  
**Assumptions / non-claims:** `Docs/ASSUMPTIONS-DOUBLE-SLIT.md`.

## Lean declaration statistics

*(Heuristic line counts from `make lean-stats-md`; portable paths — re-paste after large Lean edits.)*

- **Lean root:** `Lean`
- **`.lean` files scanned:** 31 (`.lake` excluded)
- **`abbrev` (line-start heuristic):** 3
- **`def` (line-start heuristic):** 117
- **`inductive` (line-start heuristic):** 1
- **`lemma` (line-start heuristic):** 12
- **`structure` (line-start heuristic):** 17
- **`theorem` (line-start heuristic):** 281
- **Sum of above kinds:** 431

## Track summary

| Area | Status |
|------|--------|
| Classical ℝ gate shape (`UMSTCore`, `DoubleSlitCore`) | **In place** |
| Density matrices + Kraus + Lüders which-path | **Proved** (see `Lean/VERIFY.md`) |
| Englert-style `V² + I² ≤ 1` (canonical `I`, `V`) | **Proved** (`QuantumClassicalBridge`, `Complementarity`) |
| Binary diagonal entropy (`InfoEntropy`) | **Proved** (`≤ log 2` nats via `Real.binEntropy`, as well as general `n`); MI / DPI **open** |
| Landauer **scale** from diagonal entropy (`LandauerBound`) | **Proved** (nonneg, `pathEntropyBits ≤ 1`, `landauerCostDiagonal ≤ landauerBitEnergy`, which-path invariant); physical `dissipation ≥ bound` **Proved via ErasureProcess** |
| Epistemic probe interface (`EpistemicSensing`) | **Proved (concrete interface + finite argmax + strict-positive which-path selection + collapse/preserve bridges)**; full ODE/PPO semantics **open** |
| Epistemic MI (`EpistemicMI`) | **Proved (probe-indexed MI + bits + Landauer links)** |
| Epistemic dynamics (`EpistemicDynamics`) | **Proved** (policy rollouts + canonical invariants) |
| Trajectory MI/cost (`EpistemicTrajectoryMI`) | **Proved** (finite-horizon aggregation + bounds) |
| Policy optimization (`EpistemicPolicy`, `ProbeOptimization`) | **Proved** (finite utility argmax + admissibility-constrained existence) |
| Runtime contract (`EpistemicRuntimeContract`) | **Proved** (trace coherence + aggregate-contract bridge theorems) |
| Numeric runtime-record contract (`EpistemicNumericsContract`) | **Proved** (numeric aggregate record + consistency + utility equivalence to policy utility) |
| Per-step numerics contract (`EpistemicPerStepNumerics`) | **Proved** (step-level records + fold-to-aggregate consistency + projection to aggregate record) |
| Runtime schema bridge (`EpistemicRuntimeSchemaContract`) | **Proved** (emitted-step schema + rollout-consistency-to-contract transfer theorems) |
| Runtime telemetry bridge (`EpistemicTelemetryBridge`) | **Proved** (runtime `trajMI`/`effortCost` naming bridge + consistency/utility transfer theorems) |
| Runtime numerics approximation (`EpistemicTelemetryApproximation`) | **Proved** (explicit epsilon-approximation assumptions + zero-error transfer to exact contracts) |
| Runtime quantitative utility bounds (`EpistemicTelemetryQuantitativeUtility`) | **Proved** (nonzero-error utility deviation bounds from explicit aggregate approximation assumptions) |
| Trace-derived epsilon certificates (`EpistemicTraceDerivedEpsilonCertificate`) | **Proved** (residual-based epsilon extraction from telemetry + direct utility-bound transfer) |
| Runtime solver calibration (`EpistemicTelemetrySolverCalibration`) | **Proved** (solver-parameter-to-epsilon mapping and calibration-assumption utility-bound transfer) |
| Trace-driven calibration witness (`EpistemicTraceDrivenCalibrationWitness`) | **Proved** (trace witness packaging + direct transfer to calibrated utility bounds) |
| Prototype calibration instantiation (`PrototypeSolverCalibration`) | **Proved** (concrete constants + explicit epsilon budgets + specialized utility-bound corollaries) |
| Gate **scaffold** + `Admissible` under which-path (`GateCompat`) | **Proved**; calibrated thermo map **open** |
| `MeasurementUpdate` for which-path (`DoubleSlit`) | **Proved** (includes narrative wrappers: identity preserves interference, which-path collapses fringes, gate-enforcement packaging) |
| Worked examples `|+⟩`, `|0⟩`, `|1⟩` (`ExamplesQubit`) | **Proved** (+ `DoubleSlit`; idle update for basis states) |
| Measurement cost (`MeasurementCost`) | **Proved** (aliases `epistemicLandauerCost`; null=0, whichPath=diagonal cost, ≤ bit-energy, channel-invariant) |
| Haskell / Python / publication sims | **Partially in repo** (toy + toy SVG + qubit Kraus + qubit SVG + tests; optional QuTiP; optional matplotlib/GIF via toy script flags); spatial dynamics **open** |

## Assumptions / non-claims

- `landauerCostDiagonal` is a **thermodynamic-scale hook** from diagonal Shannon entropy in nats; it is **not** asserted to equal measured heat unless you add an erasure model.
- `thermoFromQubitPath` is a **minimal** embedding of Born weights into `ThermodynamicState`; not a materials model.

Last updated: 2026-03-21 — added `MeasurementCost.lean` (5 theorems), refreshed stats (31 files / 431 decls), fixed `DensityState.lean` `pureDensity_carrier` implicit arg.

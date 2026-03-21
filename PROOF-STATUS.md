# umst-formal-double-slit — proof status (Lean)

**Build:** from `Lean/`, run `lake build` (or repo root `make lean`).
**CI:** `.github/workflows/lean.yml` (Ubuntu, Elan, optional Mathlib `lake exe cache get`, `pip install -r sim/requirements-optional.txt`, then Python `sim` + `unittest`); `.github/workflows/haskell.yml` (Cabal `test` in `Haskell/`).
**Assumptions / non-claims:** `Docs/ASSUMPTIONS-DOUBLE-SLIT.md`.

## Lean declaration statistics

*(Heuristic line counts from `make lean-stats-md`; portable paths — re-paste after large Lean edits.)*

- **Lean root:** `Lean`
- **`.lean` files scanned:** 40 (`.lake` excluded)
- **`abbrev` (line-start heuristic):** 4
- **`axiom` (line-start heuristic):** 1
- **`def` (line-start heuristic):** 157
- **`inductive` (line-start heuristic):** 4
- **`instance` (line-start heuristic):** 1
- **`lemma` (line-start heuristic):** 27
- **`structure` (line-start heuristic):** 24
- **`theorem` (line-start heuristic):** 360
- **Sum of above kinds:** 578

## Track summary

| Area | Status |
|------|--------|
| Classical ℝ gate shape (`UMSTCore`, `DoubleSlitCore`) | **Proved** |
| Density matrices + Kraus + Lüders which-path | **Proved** (all projector properties, no sorry) |
| Englert-style `V² + I² ≤ 1` (canonical `I`, `V`) | **Proved** (`QuantumClassicalBridge`, `Complementarity`) |
| Binary diagonal entropy (`InfoEntropy`) | **Proved** (`≤ log 2` nats via `Real.binEntropy`, general `n`) |
| Landauer **scale** from diagonal entropy (`LandauerBound`) | **Proved** (nonneg, `pathEntropyBits ≤ 1`, `landauerCostDiagonal ≤ landauerBitEnergy`, which-path invariant, `ErasureProcess`) |
| **Principle of Maximal Information Collapse** (`LandauerBound`) | **Proved** (`residualCoherenceCapacity ∈ [0,1]`, tight at both endpoints, cost = bitEnergy × extracted) |
| Epistemic probe interface (`EpistemicSensing`) | **Proved** (concrete interface + finite argmax + strict-positive selection + collapse/preserve bridges) |
| Epistemic MI (`EpistemicMI`) | **Proved** (probe-indexed MI + bits + Landauer links) |
| Epistemic dynamics (`EpistemicDynamics`) | **Proved** (policy rollouts + canonical invariants) |
| Trajectory MI/cost (`EpistemicTrajectoryMI`) | **Proved** (finite-horizon aggregation + bounds) |
| Policy optimization (`EpistemicPolicy`, `ProbeOptimization`) | **Proved** (finite utility argmax + admissibility-constrained existence) |
| Runtime contract (`EpistemicRuntimeContract`) | **Proved** (trace coherence + aggregate-contract bridge theorems) |
| Numeric runtime-record contract (`EpistemicNumericsContract`) | **Proved** (numeric aggregate record + consistency + utility equivalence) |
| Per-step numerics contract (`EpistemicPerStepNumerics`) | **Proved** (step-level records + fold-to-aggregate consistency) |
| Runtime schema bridge (`EpistemicRuntimeSchemaContract`) | **Proved** (emitted-step schema + rollout-consistency-to-contract transfer) |
| Runtime telemetry bridge (`EpistemicTelemetryBridge`) | **Proved** (runtime `trajMI`/`effortCost` naming bridge + transfer theorems) |
| Runtime numerics approximation (`EpistemicTelemetryApproximation`) | **Proved** (epsilon-approximation + zero-error transfer) |
| Runtime quantitative utility bounds (`EpistemicTelemetryQuantitativeUtility`) | **Proved** (nonzero-error utility deviation bounds) |
| Trace-derived epsilon certificates (`EpistemicTraceDerivedEpsilonCertificate`) | **Proved** (residual-based epsilon extraction + utility-bound transfer) |
| Runtime solver calibration (`EpistemicTelemetrySolverCalibration`) | **Proved** (solver-parameter-to-epsilon mapping + utility-bound transfer) |
| Trace-driven calibration witness (`EpistemicTraceDrivenCalibrationWitness`) | **Proved** (trace witness packaging + calibrated utility bounds) |
| Prototype calibration instantiation (`PrototypeSolverCalibration`) | **Proved** (concrete constants + epsilon budgets + utility-bound corollaries) |
| Epistemic Galois connection (`EpistemicGalois`) | **Proved** (info extractable ↔ energy deployed adjunction) |
| Measurement cost (`MeasurementCost`) | **Proved** (null=0, whichPath=diagonal cost, ≤ bit-energy, channel-invariant) |
| Gate scaffold + `Admissible` under which-path (`GateCompat`) | **Proved** |
| `MeasurementUpdate` for which-path (`DoubleSlit`) | **Proved** (identity preserves interference, which-path collapses fringes, gate-enforcement packaging) |
| Worked examples (`ExamplesQubit`) | **Proved** (`|+⟩`, `|0⟩`, `|1⟩` with measurement-update corollaries) |
| Haskell / Python / publication sims | **In repo** (toy + Kraus + SVG + QuTiP + 1D/2D Schrödinger + 54 tests) |

## Axiom inventory

| Axiom | File | Justification |
|-------|------|---------------|
| `physicalSecondLaw` | `LandauerLaw.lean:154` | Second Law of Thermodynamics (physical constitutive law) |

## Sorry inventory

**Zero.** All 10 former `sorry` sites (4 in `DensityState.lean`, 6 in `MeasurementChannel.lean`) are now fully proved.

## Cross-language status

| Language | Artifacts | Status |
|----------|-----------|--------|
| Lean 4 | 38 modules, 578 declarations | **0 sorry, 1 axiom** |
| Haskell | 7 exposed modules, 14 QC + sanity suite | **All pass** |
| Python | 54 unit tests, 4 sim scripts | **All pass** |
| Coq | `LandauerEinsteinBridge.v` | **0 Admitted** |
| Agda | `LandauerEinsteinTrace.agda` (stub) | **Clean** |

Last updated: 2026-03-21 — eliminated all sorry (DensityState + MeasurementChannel), added Principle of Maximal Information Collapse theorems, refreshed stats (40 files / 578 decls / 360 theorems).

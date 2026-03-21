<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# umst-formal-double-slit — proof status (Lean)

**Build:** from `Lean/`, run `lake build` (or repo root `make lean`).
**CI:** `.github/workflows/lean.yml` (Ubuntu, Elan, optional Mathlib `lake exe cache get`, `pip install -r sim/requirements-optional.txt`, then Python `sim` + `unittest`); `.github/workflows/haskell.yml` (Cabal `test` in `Haskell/`); `.github/workflows/formal.yml` (`make coq-check` in Docker **`rocq/rocq-prover:9.0`**, `make agda-check` on Ubuntu with distro Agda).
**Assumptions / non-claims:** `Docs/ASSUMPTIONS-DOUBLE-SLIT.md`.

## Lean declaration statistics

*(Heuristic line counts from `make lean-stats-md`; portable paths — re-paste after large Lean edits.)*

- **Lean root:** `Lean`
- **`.lean` files scanned:** 55 (`.lake` excluded)
- **`abbrev` (line-start heuristic):** 5
- **`axiom` (line-start heuristic):** 5
- **`def` (line-start heuristic):** 190
- **`inductive` (line-start heuristic):** 4
- **`instance` (line-start heuristic):** 1
- **`lemma` (line-start heuristic):** 48
- **`structure` (line-start heuristic):** 29
- **`theorem` (line-start heuristic):** 467
- **Sum of above kinds:** 749

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
| Spectral von Neumann entropy + DPI (`VonNeumannEntropy`, `DataProcessingInequality`) | **PARTIAL** — general `Fin n` **unitary invariance** ✓; qubit-tier DPI **proved**; **full unital DPI + Klein** stated as **`axiom`** (Mathlib matrix-log gap). **0 `sorry`.** See `Lean/VERIFY.md`. |
| Haskell / Python / publication sims | **In repo** (toy + Kraus + SVG + QuTiP + 1D/2D/3D Schrödinger + 87 tests) |

## Axiom inventory

| Axiom | File | Justification |
|-------|------|---------------|
| `physicalSecondLaw` | `LandauerLaw.lean` | Second Law of Thermodynamics (physical constitutive law) |
| `klein_inequality` | `DataProcessingInequality.lean` | Klein / quantum relative entropy (placeholder until Mathlib matrix `log` + convexity) |
| `vonNeumannEntropy_nondecreasing_unital` | `DataProcessingInequality.lean` | Full **unital CPTP** entropy monotonicity (standard proof via Klein; **axiomatized** pending Mathlib) |
| `fringeVisibility_n_le_one` | `GeneralVisibility.lean` | $\ell_1$ norm of coherence ≤ 1 for arbitrary `Fin n` (requires Cauchy–Schwarz) |
| `dephasingSolution_tendsto_diagonal` | `LindbladDynamics.lean` | Off-diagonal coherences vanish as $t \to \infty$ under pure dephasing (topological limit) |

## Sorry inventory

**0 `sorry`** across all `Lean/**/*.lean` (heuristic: line-start `sorry`).

| File | Topic |
|------|--------|
| `VonNeumannEntropy.lean` | **Proved** — `vonNeumannEntropy_unitarily_invariant` (`Fin n`), `charpoly` lemmas. |
| `DataProcessingInequality.lean` | **Proved** special cases (identity, which-path qubit, diagonal ≥ spectral); **general unital DPI** via **`axiom`** above. |

**Resolved (historical):** all 10 former `sorry` sites in `DensityState.lean` (4) and `MeasurementChannel.lean` (6) are fully proved.

## Cross-language status

| Language | Artifacts | Status |
|----------|-----------|--------|
| Lean 4 | 49 `lakefile` roots; **467** `theorem` + **48** `lemma` (+ defs/structures, heuristic table) | **0 sorry**, **5 axiom** (3 quantum-info/physical + 2 analysis) |
| Haskell | 8 exposed modules, 14 QC + sanity suite | **All pass** |
| Python | 87 unit tests, 4 sim scripts + telemetry export/consumer | **All pass** |
| Coq | **9** `.v` modules; root **`make coq-check`** | **Compiles**; **`VonNeumannEntropySpec.v`** has **2** `Admitted` (binary Shannon bound + diagonal corner step) plus **axioms** for pure / maximally-mixed spectral entropy (see file) |
| Agda | **11** entry modules; root **`make agda-check`** | **Clean** typecheck (specs + `Gate` / `Helmholtz` / activation stack) |

Last updated: 2026-03-22 — `make lean-stats-md`: 55 files, **467** `theorem`, 48 `lemma`, **5** `axiom`, sum **749**; **0** `sorry`; DPI/Klein layer **axiomatized** in `DataProcessingInequality.lean`. Formal tracks: **`make formal-check`**.

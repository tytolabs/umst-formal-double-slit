<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Epistemic ↔ runtime grounding (`p3-epistemic-sensing`)

**Intent:** connect **Lean** epistemic-sensing interfaces to **Python sim / RL (e.g. ODE–PPO)** and logging without claiming proofs about external trainers.

**Stream:** **H** in [`PARALLEL_WORK.md`](PARALLEL_WORK.md) (coordinate with **E** for `SimLeanBridge` and **G** for `sim/` schema names).

## What Lean already fixes

| Lean module | Formal role | Runtime implication |
|-------------|-------------|---------------------|
| `EpistemicSensing` | `QuantumProbe`, `whichPathProbe`, strength bounds, Landauer-from-strength | Any “probe” in code should map to a `QuantumProbe`-shaped API (apply + strength in `[0,1]`). |
| `EpistemicMI` | Path MI bits + Landauer cost link | Logged “epistemic MI” should use the same diagonal / path-weight semantics as `epistemicMIBits`. |
| `EpistemicDynamics` | `stepProbe`, `rollout`, policies | Step function + finite horizon should match `rollout` fold structure. |
| `EpistemicTrajectoryMI` | Cumulative MI / cost | Aggregate metrics over trajectories align with `cumulativeEpistemic*`. |
| `EpistemicPolicy` | `policyUtility`, argmax witnesses | PPO (or any policy) is **not** formalized; utility comparison uses **abstract** policies in Lean. |
| `EpistemicRuntimeContract` | Trace coherence → policy admissibility | Runtime traces must satisfy the same conjuncts as `RuntimeTraceCoherent` (or documented deltas). |
| `EpistemicNumericsContract` | `NumericTraceRecord`, consistency | Float traces need fields that populate `NumericTraceRecord` / `NumericTraceConsistent`. |
| `EpistemicPerStepNumerics` | Per-step records → aggregate | Step logs must fold to the aggregate contract (see `PerStepNumericRecord`). |
| `EpistemicRuntimeSchemaContract` | `EmittedTraceSchema` | JSON / protobuf field names should match or alias documented schema names. |
| `EpistemicTelemetryBridge` | `trajMI`, `effortCost`, etc. | Telemetry keys in `sim/` or services should match [`Lean/EpistemicTelemetryBridge.lean`](../Lean/EpistemicTelemetryBridge.lean) identifiers. |
| `EpistemicTelemetryApproximation` | ε-bounds | Declare tolerances explicitly when comparing float MI to exact diagonal entropy. |
| `EpistemicTelemetryQuantitativeUtility` | Utility deviation from ε | Use when reporting “noisy policy vs ideal” bounds. |
| `EpistemicTraceDerivedEpsilonCertificate` | Residual-based ε | Optional: derive certificates from logged residuals. |
| `EpistemicTelemetrySolverCalibration` | Solver params → ε | Map PDE/solver knobs to ε assumptions used in proofs-as-contracts. |
| `EpistemicTraceDrivenCalibrationWitness` | Trace + calibration bundle | Pair exported traces with the calibration witness shape. |
| `PrototypeSolverCalibration` | Concrete constants | Toy end-to-end example of calibration + bound corollaries. |
| `EpistemicGalois` | Info–energy Galois layer | Conceptual; no mandatory runtime field unless you expose dual diagnostics. |

## Trust boundary (numeric PDE)

[`Lean/SimLeanBridge.lean`](../Lean/SimLeanBridge.lean) defines **propositional** contracts (`SimDensityContract`, `SimComplementarityWitness`, `SimLandauerWitness`, …). Python is responsible for **witnesses** (assertions, checks, or certificates), not Lean.

## Python consumer (`sim/telemetry_trace_consumer.py`)

| JSON field (per step) | Lean analogue | Notes |
|----------------------|---------------|--------|
| `stepMI` **or** `trajMI` | `EmittedTraceSchema.step` / `RuntimeTelemetryStep.trajMI` | **Nats** (same as `EpistemicMI`), **not** Shannon bits; require `0 ≤ MI ≤ ln 2` for the path-qubit story. |
| `stepCost` **or** `effortCost` | `stepCost` / `effortCost` | Joules; `0 ≤ cost ≤ k_B T ln 2` for `T ≥ 0`. |
| *(both MI + cost)* | `infoEnergyLowerBound` | Checks `cost ≈ k_B T · MI` with mixed rtol/atol (SI scale). |
| **Root** `aggregateMI` / `aggregateCost` (or nested `aggregate: { … }`) | `NumericTraceRecord` | Catalog bounds: `aggregateMI ≤ n ln 2`, `aggregateCost ≤ n k_B T ln 2`. If **every** step has MI+cost, also checks `Σ stepMI ≈ aggregateMI` and `Σ stepCost ≈ aggregateCost` (`PerStepNumericRecord.aggregate*` vs fold). |
| `thermodynamicAdmissible`, `confidence` (flat or inside **`emitted`**) | `EmittedStepRecord` | `confidence ∈ [0,1]`; admissible flag = bool or `0`/`1`. Nested `emitted` wins on key clashes. |
| `density_matrix_*`, `path_weights`, `visibility`, `distinguishability`, `entropy_bits` | `SimLeanBridge` | Unchanged — PSD/trace, Born weights, Englert bound, diagonal entropy bits. |

Run: `python3 sim/telemetry_trace_consumer.py trace.json`. Tests: `sim/tests/test_telemetry_trace_consumer.py`. **Golden JSON:** `python3 sim/export_sample_telemetry_trace.py --validate`.

## Explicit non-goals (today)

- No machine-checked **PPO** or **ODE discretization error** in this repo.
- No proof that a specific neural policy maximizes `policyUtility`; Lean proves **structural** statements about abstract policies and traces.

## Safe next steps (engineering)

1. ~~**Inventory** — `trajMI` / `effortCost` aliases are accepted by `telemetry_trace_consumer.py`.~~ Extend other scripts to **emit** these fields when logging rollouts.
2. ~~**Fold tests** — `aggregateMI` / `aggregateCost` + optional sum checks vs per-step rows are implemented in `telemetry_trace_consumer.py`.~~ Emit **aggregates** from long-running sims / RL loggers.
3. **Document** ε and temperature whenever comparing `simEntropyBits` to `pathEntropyBits` (see `SimLandauerWitness`).

## Related docs

- [`Lean/VERIFY.md`](../Lean/VERIFY.md) — module map + epistemic theorem index  
- [`Docs/TODO-TRACKING.md`](TODO-TRACKING.md) — milestone **`p3-epistemic-sensing`**  
- [`Docs/GAP_CLOSURE_PLAN.md`](GAP_CLOSURE_PLAN.md) — **Gap 14** telemetry consumers  
- [`Docs/REMAINING_WORK_PLAN.md`](REMAINING_WORK_PLAN.md) — Phase 5 deferred; ordered remaining work  

Reconcile this file when new `Epistemic*.lean` roots land or telemetry names change.

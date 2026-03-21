# umst-formal-double-slit

Small extension fork to test a UMST-style path from
"information + constraints" toward a double-slit style measurement model.

## Goal

Create a scoped, defensible bridge:

- Keep current `umst-formal` claims intact.
- Add a separate extension theory for observer/measurement effects.
- Avoid overclaiming "derived from L0" unless explicitly proved.

## What is included

- `Lean/UMSTCore.lean`:
  Standalone classical layer (Mathlib): SI constants, Landauer bit energy `k_B T ln 2`, mass equivalent `E/c²`, ℝ `ThermodynamicState`, and `Admissible` predicates matching the *shape* of `umst-formal`’s gate (so future `GateCompat` can relate projections). No dependency on the main `umst-formal` repo.
- `Lean/DensityState.lean`:
  Finite `n`-level quantum states: `UMST.Quantum.DensityMatrix` (positive semidefinite `n×n` complex matrix, trace `1`) and **`pureDensity`** for rank-one projectors `|ψ⟩⟨ψ|` when `dotProduct ψ (star ψ) = 1` (Mathlib `PosSemidef` + `trace_col_mul_row`). Mixed ensembles / partial trace are future work.
- `Lean/MeasurementChannel.lean`:
  Finite **Kraus** channels `KrausChannel n ι` with TP constraint `∑ Kᵢᴴ Kᵢ = 1`, channel map **`KrausChannel.map`**, **`apply`** on `DensityMatrix`, the **`identity`** channel, **`whichPathChannel`** (2-level path projectors), **`KrausChannel.compose`** with **`compose_map`**, and **`apply_compose`** (iterated `apply` = `apply` of `compose`).
- `Lean/QuantumClassicalBridge.lean`:
  For `DensityMatrix` on `Fin 2`: **Born weights** `pathWeight`, **`whichPathDistinguishability`** `I = |p₀ − p₁|`, **fringe visibility** `V = 2|ρ₀₁|`, theorem **`complementarity_fringe_path`** (`V² + I² ≤ 1`), **`observationStateCanonical`** (packaged `(I,V)`), and optional **`observationStateOf`** with user-supplied `V`.
- `Lean/InfoEntropy.lean`:
  Binary Shannon via **`Real.negMulLog`** (`0 log 0 = 0`); **`shannonBinary`** = Mathlib **`Real.binEntropy`**; **`vonNeumannDiagonal`**, **`vonNeumannDiagonal_le_log_two`** (nats); invariance under **`whichPath`**.
- `Lean/LandauerBound.lean`:
  **`pathEntropyBits`** (≤ 1 bit-equivalent), **`landauerCostDiagonal`**, **`landauerCostDiagonal_le_landauerBitEnergy`** (≤ one Landauer bit-energy at `T`), **`landauerCostDiagonal_whichPathInvariant`**.
- `Lean/GateCompat.lean`:
  **`thermoFromQubitPath`** (Born weights → `ThermodynamicState` scaffold), **`admissible_thermoFromQubitPath_whichPath`**.
- `Lean/EpistemicSensing.lean`:
  Probe interface layer: **`QuantumProbe`**, **`nullProbe`**/**`whichPathProbe`**, **`ProbeStrength`**, max witnesses (`Set` + finite-family argmax, strict-positive selection), `interference_preserved_nullProbe`, `collapse_on_whichPathProbe`, and Landauer-from-strength bounds.
- `Lean/EpistemicMI.lean`:
  Probe-indexed MI (`PathProbe.null`/`whichPath`) in nats + bit-equivalents, with Landauer-cost links (`epistemicLandauerCost_*`).
- `Lean/EpistemicDynamics.lean`:
  Policy rollouts `rollout π n ρ` with `nullPolicy`/`whichPathPolicy` invariants.
- `Lean/EpistemicTrajectoryMI.lean`:
  Cumulative MI/cost over horizons with nonnegativity and finite upper bounds.
- `Lean/EpistemicPolicy.lean`:
  Finite-horizon policy utility, argmax existence/spec, admissibility-constrained policy selection.
- `Lean/EpistemicRuntimeContract.lean`:
  Runtime-trace contract tying rollout traces to abstract MI/cost/policy theorems (no new axioms).
- `Lean/EpistemicNumericsContract.lean`:
  Numeric rollout-record contract: `NumericTraceRecord`, consistency predicates against abstract cumulative MI/Landauer sums, and utility-equivalence lemmas to `policyUtility`.
- `Lean/EpistemicPerStepNumerics.lean`:
  Per-step runtime numeric contract: `PerStepNumericRecord`, finite-horizon fold consistency to abstract cumulative MI/Landauer expressions, and projection to `NumericTraceRecord`.
- `Lean/EpistemicRuntimeSchemaContract.lean`:
  Runtime-emitted schema bridge: `EmittedStepRecord` / `EmittedTraceSchema`, well-formedness + rollout-consistency predicates, and proofs that consistent emitted traces inherit per-step/aggregate utility contracts.
- `Lean/EpistemicTelemetryBridge.lean`:
  Runtime telemetry naming bridge (`trajMI` / `effortCost`) with explicit consistency assumptions and transfer theorems into emitted/per-step/aggregate contracts.
- `Lean/EpistemicTelemetryApproximation.lean`:
  Explicit epsilon-approximation interface for ODE/PPO-style numerics; proves zero-error collapse to exact telemetry/schema/numeric contracts and policy-utility equality.
- `Lean/EpistemicTelemetryQuantitativeUtility.lean`:
  Nonzero-error quantitative utility bounds under explicit aggregate approximation assumptions (`NumericTraceApproxConsistent`), including explicit deviation bounds as functions of `εMI`, `εCost`, `λ`, and `T`.
- `Lean/EpistemicTraceDerivedEpsilonCertificate.lean`:
  Trace-derived epsilon certificates: aggregate residual-based epsilon extraction and direct utility-bound corollaries from concrete telemetry traces.
- `Lean/EpistemicTelemetrySolverCalibration.lean`:
  Explicit solver-calibration layer mapping numerical parameters (`stepSize`, method `order`, error coefficients) to epsilon budgets and utility-bound transfer assumptions.
- `Lean/EpistemicTraceDrivenCalibrationWitness.lean`:
  Trace-driven witness layer packaging concrete runtime telemetry together with calibration assumptions, with direct transfer to calibrated utility bounds.
- `Lean/PrototypeSolverCalibration.lean`:
  Concrete prototype calibration instantiation (`stepSize=1/100`, `order=2`) with explicit epsilon budgets and ready-to-use utility-bound corollaries.
- `Lean/Complementarity.lean`:
  Shim theorems **`complementarityEnglert`**, **`observationCanonical_complementary`** (wrappers over `QuantumClassicalBridge`).
- `Lean/DoubleSlit.lean`:
  Full-chain build + **`measurementUpdateWhichPath`** (coarse `MeasurementUpdate` for Lüders which-path; `V → 0`, `I` fixed on diagonal readout) + **`measurementUpdateWhichPath_landauer_eq`** / Landauer cap corollaries.
- `Lean/ProbeOptimization.lean`:
  Cost-penalized finite probe selection: **`ProbeUtility`**, argmax existence/spec, admissibility-constrained optimality over finite families.
- `Lean/ExamplesQubit.lean`:
  **`rhoPlus`**, **`rhoZero`**, **`rhoOne`**; epistemic MI/optimization + Landauer hooks; measurement-update corollaries (collapse vs idle).
- `Lean/DoubleSlitCore.lean`:
  A minimal formal skeleton for a measurement channel with:
  - which-path information `I in [0,1]`,
  - fringe visibility `V in [0,1]`,
  - complementarity axiom `V^2 + I^2 <= 1`,
  - admissibility-style measurement gate.
- `sim/toy_double_slit_mi_gate.py`:
  A small runnable simulation that maps information gain to fringe suppression.
- `sim/plot_toy_complementarity_svg.py`:
  Stdlib SVG of the toy (I,V) curve vs the feasible quarter-disk (reads toy CSV).
- `sim/qubit_kraus_sweep.py`:
  Stdlib-only 2×2 Kraus sweep: `pathWeight`, `fringeVisibility`, `whichPathDistinguishability`, Lüders which-path (matches `QuantumClassicalBridge` / `MeasurementChannel`).
- `sim/plot_complementarity_svg.py`:
  Stdlib SVG figure: `(I,V)` points vs the `V²+I²≤1` boundary from the qubit sweep CSV.

## Vendored from parent `umst-formal` (full parity track)

These files are **copies** (with the same module structure as upstream) so this checkout is self-contained. **Re-sync** from `../umst-formal` when the parent changes (diff `Lean/Gate.lean`, `LandauerLaw.lean`, etc.).

- **Lean** (all in `lake build`): `LandauerLaw.lean`, `LandauerExtension.lean`, `LandauerEinsteinBridge.lean`, `Gate.lean`, `Naturality.lean`, `Activation.lean`, `FiberedActivation.lean`, `MonoidalState.lean`.
- **Haskell:** `Haskell/src/LandauerExtension.hs`, `MonoidalState.hs`; QuickCheck in `Haskell/test/Main.hs`; rational sanity suite `landauer-einstein-sanity` (Lean bridge numerators).
- **Coq:** `Coq/LandauerEinsteinBridge.v` + `Coq/README.md` — run **`make coq-check`** (needs `coqc`).
- **Agda:** `Agda/LandauerEinsteinTrace.agda` (traceability stub) — **`make agda-check`**.

The double-slit **ℝ** scaffold `UMSTCore.lean` is unchanged; it does **not** replace `Gate.lean` (ℚ UMST core).

## Claim taxonomy (strict)

- Established in this fork:
  - A formal interface for measurement-gated updates.
  - A toy simulator that demonstrates visibility collapse as information rises.
- Extension:
  - UMST-style gating language can be reused for measurement modeling.
- Not established:
  - Full quantum derivation from Schrodinger dynamics.
  - Empirical proof of simulation-hypothesis claims.

## Next derivation steps (recommended)

1. ~~Add a finite-dimensional density-matrix layer in Lean.~~ (initial layer: `DensityState.lean`; extend with mixtures + partial trace.)
2. ~~Define a measurement channel (CPTP-like interface).~~ (initial Kraus layer: `MeasurementChannel.lean`; extend with which-path / composition.)
3. ~~Prove coarse complementarity `V² + I² ≤ 1` from qubit PSD + trace.~~ (`complementarity_fringe_path` in `QuantumClassicalBridge.lean`.)
4. ~~Link diagonal path entropy to the core Landauer scale (`LandauerBound.lean`).~~ Full “dissipation ≥ bound” for a concrete erasure process is still open.
5. Keep all assumptions listed in a PROOF-STATUS table for this fork.

## Build (Lean)

From this directory:

```bash
cd Lean && lake build
```

Or from the repo root:

```bash
make lean
```

Toy simulator (CSV output + validation):

```bash
make sim
```

Simulator unit tests:

```bash
make sim-test
```

Declaration **heuristic** stats for docs: `make lean-stats` or `make lean-stats-md` (see **`scripts/README.md`**).  
Haskell mirror: `Haskell/README.md`, optional `make haskell-test`.

See `Lean/VERIFY.md` for a module map and main theorem names.
Simulation details: `sim/README.md`.

**CI:** on push/PR to `main` or `master`: **`lean.yml`** — `lake build` in `Lean/`, then `pip install -r sim/requirements-optional.txt`, then the same Python steps as `make sim` + `make sim-test`; **`haskell.yml`** — `cabal test` in `Haskell/` (includes **`landauer-einstein-sanity`**). Coq/Agda checks are **local** via **`make coq-check`** / **`make agda-check`** (not in default CI).  
**Contributing / parallel agents:** `CONTRIBUTING.md`, `Docs/PARALLEL_WORK.md` (swarm coordination), `Docs/TODO-TRACKING.md` (milestone vs todo reconciliation). **Confused by “fork” / “parent” / what’s actually in this folder?** → `Docs/SCOPE_PARENT_AND_SEPARATE_REPO.md`. Optional all-in-one local check: **`make ci-full`** (Lean + Python + Cabal).  
**Status table:** `PROOF-STATUS.md`.  
**Derivation walkthrough (informal):** `Docs/DoubleSlit-Derivation.md`.  
**Epistemic sensing ↔ quantum (note):** `Docs/EpistemicSensingQuantum.md`.  
**One-pager (LaTeX):** `Docs/OnePager-DoubleSlit.tex`.  
**Assumptions / non-claims:** `Docs/ASSUMPTIONS-DOUBLE-SLIT.md`.  
**Changelog:** `CHANGELOG.md`.

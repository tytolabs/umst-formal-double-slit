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
- **`.lean` files scanned:** 65 (`.lake` excluded)
- **`abbrev` (line-start heuristic):** 7
- **`axiom` (line-start heuristic):** 3
- **`def` (line-start heuristic):** 207
- **`inductive` (line-start heuristic):** 4
- **`instance` (line-start heuristic):** 1
- **`lemma` (line-start heuristic):** 54
- **`structure` (line-start heuristic):** 29
- **`theorem` (line-start heuristic):** 528
- **Sum of above kinds:** 833

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
| Spectral von Neumann entropy + DPI (`VonNeumannEntropy`, `DataProcessingInequality`, `KleinInequality`) | **PARTIAL** — general `Fin n` **unitary invariance** ✓; qubit-tier unital DPI instances **proved**; **spectral relative entropy nonnegativity** **`spectralRelativeEntropy_nonneg`** **proved** in **`KleinInequality.lean`** (no Klein axiom). **General** unital CPTP DPI for all `n` not a single theorem. **0 `sorry`.** See `Lean/VERIFY.md`. |
| General-n RCC (`GeneralResidualCoherence`) | **Proved** — `RCC_n ∈ [0,1]`, `RCC_n = 0 ↔ diagonal`, `RCC_n = 1 ↔ pure`, qubit compatibility `RCC_2 = \|ρ₀₁\|²/(p₀p₁)`. Cauchy-Schwarz for PSD matrices proved from first principles. |
| Quantum Mutual Information (`QuantumMutualInfo`) | **Proved** — `I(A:B) = S(A) + S(B) - S(AB)` definition, conditional entropy, `I ≤ log nA + log nB` upper bound, `I(A:B) = 0` for product states. Tensor additivity **`vonNeumannEntropy_tensorDensity_eq`** proved in **`KroneckerEigen.lean`**. |
| Concrete erasure channel (`ErasureChannel`) | **Proved** — reset-to-`\|0⟩` Kraus operators, trace preservation, output always `\|0⟩⟨0\|`, zero output entropy, `ErasureProcess` at Landauer equality. |
| Which-path update bridge (`WhichPathMeasurementUpdate`) | **Proved** — `measurementUpdateWhichPath`, fringe collapse, Landauer invariance along update; split from `DoubleSlit` to break import cycle with `EpistemicSensing`. |
| Haskell / Python / publication sims | **In repo** (toy + Kraus + SVG + QuTiP + 1D/2D/3D Schrödinger + 87 tests) |

## Axiom inventory

| Axiom | File | Justification |
|-------|------|---------------|
| `physicalSecondLaw` | `LandauerLaw.lean` | Second Law of Thermodynamics (physical constitutive law) |
| `fringeVisibility_n_le_one` | `GeneralVisibility.lean` | $\ell_1$ norm of coherence ≤ 1 for arbitrary `Fin n` (requires Cauchy–Schwarz on coherence vector) |
| `dephasingSolution_tendsto_diagonal` | `LindbladDynamics.lean` | Off-diagonal coherences vanish as $t \to \infty$ under pure dephasing (topological limit of ODE) |

**Resolved (information theory):** `spectralRelativeEntropy_nonneg` — **theorem** in `KleinInequality.lean` (Gibbs inequality + unitary row/column `normSq` sums + concave `log` / Jensen). **0** information-theoretic Lean axioms.

## Sorry inventory

**0 `sorry`** across all `Lean/**/*.lean` (heuristic: line-start `sorry`).

| File | Topic |
|------|--------|
| `VonNeumannEntropy.lean` | **Proved** — `vonNeumannEntropy_unitarily_invariant` (`Fin n`), `charpoly` lemmas. |
| `DataProcessingInequality.lean` | **Proved** — identity channel, **algebraic unital DPI** for qubit which-path (`vonNeumannEntropy_nondecreasing_unital_whichPath`), diagonal ≥ spectral (Tier 1b). |

**Resolved (historical):** all 10 former `sorry` sites in `DensityState.lean` (4) and `MeasurementChannel.lean` (6) are fully proved.

## Cross-language status

| Language | Artifacts | Status |
|----------|-----------|--------|
| Lean 4 | 55 `lakefile` roots; **528** `theorem` + **54** `lemma` (+ defs/structures, heuristic table) | **0 sorry**, **3 axiom** (see inventory; re-run `make lean-stats-md` for fresh counts) |
| Haskell | 8 exposed modules, 14 QC + sanity suite | **All pass** |
| Python | 87 unit tests, 4 sim scripts + telemetry export/consumer | **All pass** |
| Coq | **9** `.v` modules; root **`make coq-check`** | **Compiles**; **`VonNeumannEntropySpec.v`** has **no** `Admitted`; real-analysis facts are **axioms** (`shannon_binary_le_ln2`, `negMulLog_zero_interval`) plus spectral **axioms** (see file) |
| Agda | **11** entry modules; root **`make agda-check`** | **Clean** typecheck (specs + `Gate` / `Helmholtz` / activation stack) |

Last updated: 2026-04-03 — `spectralRelativeEntropy_nonneg` is a **theorem** in `KleinInequality.lean` (no Klein axiom). Qubit-tier unital DPI instances in `DataProcessingInequality.lean`; tensor additivity in `KroneckerEigen.lean`. **3** project `axiom`s: `physicalSecondLaw`, `fringeVisibility_n_le_one`, `dephasingSolution_tendsto_diagonal`. Formal tracks: **`make formal-check`**.

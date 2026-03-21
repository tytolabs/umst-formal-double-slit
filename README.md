# umst-formal-double-slit

**Formally verified in Lean 4 &bull; Live simulator &bull; Principle of Maximal Information Collapse proved**

> 38 Lean modules &bull; 360 theorems &bull; 0 sorry &bull; 1 physical axiom &bull; 54 Python tests &bull; 14 QuickCheck properties

![Interference collapse](Docs/double-slit-collapse.gif)

---

## What this repository proves

A formally verified bridge from quantum measurement theory to classical thermodynamics:

1. **Englert complementarity** (`V² + I² ≤ 1`) — proved from density matrix PSD constraint
2. **Landauer bound** — diagonal path entropy costs `≤ k_B T ln 2` per bit
3. **Principle of Maximal Information Collapse** — residual coherence = `1 − pathEntropyBits`, proved in `[0, 1]`
4. **Kraus channels** — trace-preserving completely positive maps with Lüders which-path dephasing
5. **Erasure thermodynamics** — `ErasureProcess` with `dissipatedHeat ≥ landauerCostDiagonal`

## Lean modules (38 roots, `lake build` — zero sorry)

### Quantum core
| Module | Key theorems |
|--------|-------------|
| `DensityState` | `DensityMatrix`, `pureDensity`, diagonal properties (all proved) |
| `MeasurementChannel` | Kraus channels, `whichPathChannel`, `compose`, projector properties (all proved) |
| `QuantumClassicalBridge` | `complementarity_fringe_path` (`V² + I² ≤ 1`), `observationStateCanonical` |
| `InfoEntropy` | `shannonBinary = Real.binEntropy`, `vonNeumannDiagonal ≤ log 2` |
| `LandauerBound` | `pathEntropyBits ≤ 1`, `principle_of_maximal_information_collapse`, `ErasureProcess` |
| `DoubleSlit` | `measurementUpdateWhichPath`, gate enforcement, Landauer cap |

### Epistemic sensing stack
| Module | Purpose |
|--------|---------|
| `EpistemicSensing` | Probe interface, `nullProbe`/`whichPathProbe`, collapse/preserve bridges |
| `EpistemicMI` | Probe-indexed MI in nats/bits + Landauer links |
| `EpistemicDynamics` | Policy rollouts with null/which-path invariants |
| `EpistemicTrajectoryMI` | Cumulative MI/cost with finite upper bounds |
| `EpistemicPolicy` | Finite-horizon utility argmax + constrained optimality |
| `EpistemicGalois` | Galois connection: info extractable ↔ energy deployed |
| `ProbeOptimization` | Cost-penalized finite probe selection |
| `ExamplesQubit` | Worked examples: `\|+⟩`, `\|0⟩`, `\|1⟩` |

### Runtime contract stack
| Module | Purpose |
|--------|---------|
| `EpistemicRuntimeContract` | Trace coherence → policy theorem bridge |
| `EpistemicNumericsContract` | Numeric aggregate record → utility equivalence |
| `EpistemicPerStepNumerics` | Per-step fold → cumulative consistency |
| `EpistemicRuntimeSchemaContract` | Emitted schema → contract transfer |
| `EpistemicTelemetryBridge` | Runtime naming bridge (`trajMI`, `effortCost`) |
| `EpistemicTelemetryApproximation` | Epsilon-approximation with zero-error collapse |
| `EpistemicTelemetryQuantitativeUtility` | Nonzero-error deviation bounds |
| `EpistemicTraceDerivedEpsilonCertificate` | Residual-based epsilon extraction |
| `EpistemicTelemetrySolverCalibration` | Solver params → epsilon budgets |
| `EpistemicTraceDrivenCalibrationWitness` | Trace + calibration → utility bounds |
| `PrototypeSolverCalibration` | Concrete instantiation (step=1/100, order=2) |

### Classical / upstream integration
| Module | Purpose |
|--------|---------|
| `UMSTCore` | ℝ SI constants, Landauer bit energy, `ThermodynamicState`, `Admissible` |
| `DoubleSlitCore` | Coarse `MeasurementUpdate` skeleton |
| `GateCompat` | Born weights → `ThermodynamicState` scaffold |
| `Complementarity` | Discoverability shims |
| `Gate`, `Naturality`, `Activation`, `FiberedActivation`, `MonoidalState` | Upstream ℚ core (vendored) |
| `LandauerLaw`, `LandauerExtension`, `LandauerEinsteinBridge` | Upstream Landauer stack (vendored) |

## Cross-language verification

| Language | Artifact | Check command |
|----------|----------|---------------|
| **Lean 4** | 38 modules, 360 theorems, 0 sorry | `cd Lean && lake build` |
| **Haskell** | 7 modules, 14 QuickCheck + sanity | `cd Haskell && cabal test` |
| **Python** | 54 unit tests, 4 sim scripts | `make sim && make sim-test` |
| **Coq** | `LandauerEinsteinBridge.v` (0 Admitted) | `make coq-check` |
| **Agda** | `LandauerEinsteinTrace.agda` | `make agda-check` |

## Build

```bash
# Full verification (Lean + Python + Haskell)
make ci-full

# Individual layers
cd Lean && lake build          # Lean 4 (zero sorry)
make sim && make sim-test      # Python (54 tests)
cd Haskell && cabal test       # Haskell (14 QC + sanity)
make coq-check                 # Coq (optional, needs coqc)
make agda-check                # Agda (optional, needs agda)
```

## Claim taxonomy (strict)

**Established:**
- Formal interface for measurement-gated updates with full Kraus channel semantics.
- Englert complementarity `V² + I² ≤ 1` from qubit PSD + trace constraint.
- Landauer thermodynamic bound on which-path information extraction.
- Principle of Maximal Information Collapse: residual coherence ∈ [0, 1], tight at both endpoints.
- Concrete `ErasureProcess` with `dissipatedHeat ≥ landauerCostDiagonal`.
- Live simulator demonstrating visibility collapse as information rises.

**Not established:**
- Full quantum derivation from Schrödinger dynamics.
- Empirical proof of simulation-hypothesis claims.

## Documentation

| Document | Path |
|----------|------|
| Proof status & declaration counts | `PROOF-STATUS.md` |
| Module map & theorem names | `Lean/VERIFY.md` |
| Mathematical foundations | `Docs/Mathematical-Foundations.md` |
| Assumptions & non-claims | `Docs/ASSUMPTIONS-DOUBLE-SLIT.md` |
| Epistemic sensing note | `Docs/EpistemicSensingQuantum.md` |
| One-pager (LaTeX) | `Docs/OnePager-DoubleSlit.tex` |
| Simulator details | `sim/README.md` |
| Haskell mirror | `Haskell/README.md` |
| Contributing | `CONTRIBUTING.md` |
| Changelog | `CHANGELOG.md` |

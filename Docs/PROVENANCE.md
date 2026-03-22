<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Formal Provenance — Module Authorship & Verification Chain

This document traces the **formal authorship and verification provenance** of each module in
the UMST Formal Double-Slit project, establishing a rigorous audit trail from mathematical
specification to machine-checked proof.

## Programme authors

| Name | Affiliation | Email |
|------|-------------|-------|
| **Santhosh Shyamsundar** | Studio TYTO; IAAC Barcelona | `santhosh@tyto.studio` |
| **Santosh Prabhu Shenbagamoorthy** | Studio TYTO; IAAC Barcelona | `santosh@tyto.studio` |

Same contacts as in the repo [`README.md`](../README.md).

## Lean Modules — Formal Proofs

| Module | Gap | Author/Agent | Verified | Sorry |
|--------|-----|-------------|----------|-------|
| `UMSTCore.lean` | — | Original | `lake build` ✅ | 0 |
| `DensityState.lean` | 1 | Original + Antigravity | `lake build` ✅ | 0 |
| `TensorPartialTrace.lean` | 3 | Cursor (Stream B) | `lake build` ✅ | 0 |
| `MeasurementChannel.lean` | fix | Antigravity (Stream C) | `lake build` ✅ | 0 |
| `DoubleSlitCore.lean` | — | Original | `lake build` ✅ | 0 |
| `QuantumClassicalBridge.lean` | — | Original | `lake build` ✅ | 0 |
| `InfoEntropy.lean` | — | Original | `lake build` ✅ | 0 |
| `GeneralDimension.lean` | 2 | Cursor (Stream A) | `lake build` ✅ | 0 |
| `LandauerBound.lean` | — | Original + Stream A | `lake build` ✅ | 0 |
| `PMICEntropyInterior.lean` | — | Original | `lake build` ✅ | 0 |
| `PMICVisibility.lean` | 13 | Original + Antigravity | `lake build` ✅ | 0 |
| `SchrodingerDynamics.lean` | 5 | Antigravity (Stream C) | `lake build` ✅ | 0 |
| `LindbladDynamics.lean` | 12 | Antigravity (Stream C) | `lake build` ✅ | 0 |
| `GateCompat.lean` | 10 | Original + Antigravity | `lake build` ✅ | 0 |
| `QRBridge.lean` | 17 | Original | `lake build` ✅ | 0 |
| `SimLeanBridge.lean` | 18 | Antigravity (Stream E) | `lake build` ✅ | 0 |
| `VonNeumannEntropy.lean` | 4 | Claude Code (Stream D) | `lake build` ✅ | 1* |
| `DataProcessingInequality.lean` | 11 | Claude Code (Stream D) | `lake build` ✅ | 1* |
| `Complementarity.lean` | — | Original | `lake build` ✅ | 0 |
| `DoubleSlit.lean` | — | Original | `lake build` ✅ | 0 |

\* Sorry items are Mathlib infrastructure gaps (eigenvalue multiset bridge, Klein's inequality),
not proof logic errors. All physically relevant qubit-level theorems are sorry-free.

## Python Simulation Layer

| Module | Purpose | Tests |
|--------|---------|-------|
| `sim/qubit_kraus_sweep.py` | Kraus channel parameter sweep | `test_qubit_kraus_sweep.py` |
| `sim/telemetry_trace_consumer.py` | Runtime trace contract validator (Gap 14) | CLI `--validate` |
| `sim/schrodinger_*.py` | 1D/2D Schrödinger PDE solvers | `test_schrodinger_*.py` |
| `sim/qutip_*.py` | QuTiP parity checks | `test_qutip_*.py` |

## Haskell Mirror

| Module | Purpose |
|--------|---------|
| `Haskell/InfoTheory.hs` | Shannon/binary entropy |
| `Haskell/MeasurementCost.hs` | Landauer costing |
| `Haskell/KleisliDIB.hs` | Kleisli category bridge |
| `Haskell/MonoidalState.hs` | Monoidal composition |

## Verification Chain

```
Mathlib 4.14  →  DensityState  →  MeasurementChannel  →  DoubleSlitCore
                      ↓                    ↓                    ↓
              TensorPartialTrace    SchrodingerDynamics    Complementarity
                                    LindbladDynamics       PMICVisibility
                                           ↓                    ↓
                                      GateCompat ←——— LandauerBound
                                           ↓
                                      QRBridge  →  SimLeanBridge
```

## Audit Policy

- **Machine verification:** Every Lean module must pass `lake build` with 0 errors.
- **Sorry disclosure:** Any `sorry` must be documented with its mathematical nature.
- **Multi-agent coordination:** See `Docs/PARALLEL_WORK.md` for claim/merge protocol.
- **CI enforcement:** `.github/workflows/lean.yml` runs full `lake build` on every push.

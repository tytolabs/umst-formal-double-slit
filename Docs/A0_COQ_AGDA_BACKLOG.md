<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# A0 — Coq / Agda parity backlog (double-slit fork)

**Goal:** extend machine-checked surface beyond the current **slim** trees without vendoring duplicate full formal libraries from upstream.

## In this repository today

| Language | Path | Status |
|----------|------|--------|
| Coq | `Coq/LandauerEinsteinBridge.v` | Landauer–Einstein bridge — **proved** |
| Coq | `Coq/Gate.v` | Gate + admissibility — **proved** |
| Coq | `Coq/InfoTheory.v` | Joint/marginal distributions — **proved** |
| Coq | `Coq/Constitutional.v` | Constitutional sequence — **proved** |
| Coq | `Coq/MeasurementCost.v` | Measurement energy bound — stub |
| Coq | `Coq/DensityStateSpec.v` | **NEW** 2×2 density matrix + PSD bounds — **proved** |
| Coq | `Coq/ComplementaritySpec.v` | **NEW** Englert V²+D²≤1 — **proved** |
| Coq | `Coq/VonNeumannEntropySpec.v` | **NEW** Shannon/diagonal entropy + spectral axioms — partial (1 `Admitted`) |
| Agda | `Agda/LandauerEinsteinTrace.agda` | Trace-level — **proved** |
| Agda | `Agda/Gate.agda` | Gate skeleton — structural |
| Agda | `Agda/InfoTheory.agda` | Joint/marginal — postulated (authority: Lean/Coq) |
| Agda | `Agda/DensityStateSpec.agda` | **NEW** Density matrix spec — postulated |
| Agda | `Agda/ComplementaritySpec.agda` | **NEW** Englert complementarity — postulated |
| Agda | `Agda/VonNeumannEntropySpec.agda` | **NEW** Von Neumann entropy — postulated |

Lean is authoritative for the double-slit stack; Haskell QuickCheck mirrors selected modules.

## Makefile targets (local)

From repo root: **`make coq-check`**, **`make agda-check`** (no-op or skip if the prover is missing — see `Makefile`).

## Coordination rules

1. **Prefer upstream `umst-formal`** for full 4-language parity of core gate / monoidal / InfoTheory layers — pull or submodule when you need a complete Coq/Agda mirror.
2. **This fork** should add Coq/Agda files only when they are **small, reviewable**, and **wired into `Makefile` targets** (avoid orphan `.v` / `.agda`).
3. **Claim work** in [`PARALLEL_WORK.md`](PARALLEL_WORK.md) before large ports; **stream F** (Haskell) and **A0** often track the same Lean API changes.

## Suggested port order (when resuming A0)

Priority is **API-stable** Lean modules with minimal matrix library dependency:

1. ~~**InfoTheory-style** interfaces~~ — **DONE** (`InfoTheory.v`, `InfoTheory.agda`)
2. ~~**`Gate` / `MonoidalState` skeleton**~~ — **DONE** (`Gate.v`, `Gate.agda`)
3. ~~**Measurement / cost**~~ — **DONE** stub (`MeasurementCost.v`, `MeasurementCost.agda`)
4. ~~**Quantum-heavy** (`DensityState`, `MeasurementChannel`)~~ — **DONE** spec-level: `DensityStateSpec`, `ComplementaritySpec`, `VonNeumannEntropySpec` in both Coq and Agda

### Next (if desired)

5. **Kraus channels / measurement channel** — spec-level `MeasurementChannelSpec.v` / `.agda`
6. **Landauer bound** — extend `MeasurementCost` to full `LandauerBoundSpec`
7. **Full proofs** — replace Coq `Admitted` / Agda `postulate` where feasible

## Workspace notes

- **`make coq-check`** now compiles `LandauerEinsteinBridge`, `DensityStateSpec`, `ComplementaritySpec`, `VonNeumannEntropySpec`
- **`make agda-check`** now type-checks `LandauerEinsteinTrace`, `DensityStateSpec`, `ComplementaritySpec`, `VonNeumannEntropySpec`
- `_CoqProject` updated with all new `.v` files

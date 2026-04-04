<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Assumptions & non-claims — umst-formal-double-slit

Companion to **`PROOF-STATUS.md`** and **`Lean/VERIFY.md`**. Everything below is **scope control**, not a proof gap inside the stated formal statements.

## What the Lean track **does** assume

1. **Standard finite-dimensional QM** as encoded in Mathlib: complex matrices, `PosSemidef`, trace, Kraus form for CPTP maps on the matrix algebra.
2. **Path qubit only**: Hilbert space **`Fin 2 → ℂ`** for the which-path degree of freedom — no spatial fringe pattern in position/momentum bases inside this layer.
3. **Coarse readout `(I, V)`**: `I = |p₀ − p₁|` and `V = 2|ρ₀₁|` are **defined** proxies, not derived von Neumann entropy of an apparatus or spatial interference unless explicitly linked later.
4. **Diagonal entropy hook**: `vonNeumannDiagonal` / `shannonBinary` use **computational-basis diagonals**; for general pure states with coherence this can **differ** from full **`S(ρ) = −Tr(ρ log ρ)`** (e.g. |+⟩ has **`S(ρ)=0`** but diagonal Shannon is **`log 2`** nats).
5. **Landauer layer**: `landauerCostDiagonal` is a **scale** **`k_B T log 2 × (diagonal entropy in bit-equivalents)`** — **not** a claim that any measured heat equals this without an explicit erasure / bath model.
6. **Probe-strength cost hook**: `LandauerCostFromProbeStrength` uses `ProbeStrength` (often distinguishability-based) as a bit-equivalent surrogate for optimization/selection; it is a formal utility/cost hook, not a derived thermodynamic equality.
7. **`thermoFromQubitPath`**: minimal **scaffold** mapping Born weights into `ThermodynamicState`; not a materials or continuum model.
8. **Examples** (`rhoPlus`, `rhoZero`, `rhoOne`): concrete vectors; no claim they model a full laboratory double-slit geometry.
9. **ODE/PPO numerics hooks**: runtime telemetry (`trajMI`, `effortCost`) and epsilon-approximation contracts are **defined** interfaces / surrogates, not derived convergence or stability theorems.
10. **Telemetry approximation bounds**: exact equivalence theorems from numerics to abstract rollout contracts are proved in the explicit **zero-error** limit; a separate quantitative-utility layer provides nonzero-error deviation bounds under explicit approximation assumptions.

## What is **not** claimed

- Derivation from a relativistic / gravitational UMST layer.
- Identification of `I` with a specific **experimental** which-path meter without calibration axioms.
- **Full unital CPTP DPI for arbitrary `Fin n` and general Kraus families** as one packaged theorem — **not** in this repo; qubit-tier instances (e.g. which-path channel) are **proved** in `DataProcessingInequality.lean`. **`spectralRelativeEntropy_nonneg`** (spectral relative entropy ≥ 0) is a **theorem** in `KleinInequality.lean`, not an axiom.
- **Mixed ensembles** as formal convex sums in `DensityState` (future).
- Certified ODE/PPO solver convergence / stability / generalization claims without an explicit numerical analysis layer.

## When you extend the story, narrow or add axioms explicitly

- Coupling **`landauerCostDiagonal`** to **dissipation** `D` or `ΔF` (e.g. inequality `D ≥ …`).
- A **spatial** Hilbert space (transverse momentum / position) and reduction to the path qubit.
- **Apparatus** + classical register models for bit erasure costs.

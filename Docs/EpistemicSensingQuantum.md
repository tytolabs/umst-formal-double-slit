<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Epistemic Sensing: From Materials to Quantum Observers

This document bridges the information-theoretic selection logic found in continuum materials models (like the `prototype-2a` active inference loop) to the rigorous formal quantum mechanics of `umst-formal-double-slit`.

## 1. The Classical Epistemic Selector (Materials)
In classical active materials `(prototype-2a)`, an `EpistemicSelector` picks a sensing policy $\pi^*$ that maximizes information gain about some hidden state $X$, conditioned on measurements $Y$:
$$ \pi^* = \arg\max_\pi I(X; Y \mid \pi) $$
This requires continuous trajectories, numerical ODE solutions, and surrogate PPO telemetry. It operates on a classical notion of Shannon entropy.

## 2. The Quantum Epistemic Selector (Double-Slit)
In the quantum path qubit model, the "probe" is a Kraus channel $M_{path}$.
The information gained is strictly bound by the distinguishability $I = |p_0 - p_1|$.
The quantum epistemic observer seeks to maximize $I$.

Instead of an infinite-dimensional ODE trajectory, the formal Lean representation packages this cleanly:
- **`IsMaxMIProbeAt`** formally enforces that a chosen probe (e.g., the `whichPathChannel`) maximizes mutual information.
- The **`EpistemicSensing`** module translates the abstract utility maximization into exact symbolic logic.

## 3. The Landauer Constraint Bridge
Whether in a continuum cementitious material or a 2D quantum path qubit, the measurement exacts a thermodynamic toll. 
$$ W \ge k_B T \ln(2) \cdot H $$
In `umst-formal-double-slit`, this is rigorously proven as an algebraic hook (`landauerCostDiagonal`), showing that any epistemic gain directly incurs a physical bound that limits subsequent gate operations.

## 4. Runtime and simulation alignment

For **telemetry names**, **numeric trace shapes**, and the **`SimLeanBridge`** trust boundary when wiring ODE/PPO-style logs to Lean contracts, see **[`sim/README.md`](../sim/README.md)** (section *Telemetry trace consumer (Gap 14)*) and the `Epistemic*.lean` module map in **`Lean/VERIFY.md`**.

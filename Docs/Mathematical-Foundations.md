# Mathematical Foundations: The Thermodynamic Cost of Knowing

### Observation as Irreversible Payment

This document serves as the comprehensive, single point of truth for the mathematical definitions, theorems, and physical explanations mechanized within the `umst-formal-double-slit` repository — a formally verified bridge from quantum measurement theory to classical thermodynamics.

## 1. The Quantum State (Path Qubit)
The formalization models the spatial degree of freedom of a particle traversing a double-slit interferometer as a two-level continuous quantum system (a qubit).

The state is defined mathematically via a **Density Matrix** $\rho \in \mathbb{C}^{2 \times 2}$. 
To be physically valid, $\rho$ must satisfy three mathematical properties:
1. **Hermitian**: $\rho = \rho^\dagger$
2. **Positive Semi-Definite (PSD)**: For any state vector $|\psi\rangle$, $\langle \psi | \rho | \psi \rangle \ge 0$.
3. **Unit Trace**: $\mathrm{Tr}(\rho) = \rho_{00} + \rho_{11} = 1$.

The diagonal elements represent the classical "Born weights" (probabilities) of the particle traversing each slit:
- $p_0 = \rho_{00}$ (Probability of slit 0)
- $p_1 = \rho_{11}$ (Probability of slit 1)

The off-diagonal elements $\rho_{01} = \rho_{10}^*$ represent the complex **coherence** between the two paths (the quantum interference capability).

## 2. Information and Visibility (Englert's Complementarity)
The physical observables in the double-slit experiment are strictly bound by the density matrix structure. 

### Path Distinguishability ($I$)
The which-path information available to an observer is quantified by the distinguishability:
$$ I = |p_0 - p_1| $$
If $p_0 = p_1 = 0.5$, then $I = 0$ (we have zero knowledge of which path the particle took).

### Fringe Visibility ($V$)
The interference fringe contrast on the detection screen is strictly proportional to the magnitude of the quantum coherence:
$$ V = 2|\rho_{01}| $$

### Englert's Relation Proof
The mechanized proofs in the repository (e.g., `complementarity_fringe_path`) derive Englert's famous duality relation mathematically from the physical PSD constraint of the density matrix.
Because $\rho$ is PSD, its determinant must be non-negative:
$$ \rho_{00}\rho_{11} - |\rho_{01}|^2 \ge 0 \implies |\rho_{01}|^2 \le p_0 p_1 $$

Substituting this into the definitions of $V$ and $I$:
$$ V^2 + I^2 = 4|\rho_{01}|^2 + (p_0 - p_1)^2 $$
$$ V^2 + I^2 \le 4p_0 p_1 + (p_0 - p_1)^2 = (p_0 + p_1)^2 = \mathrm{Tr}(\rho)^2 = 1 $$
**Thus, $V^2 + I^2 \le 1$.** Any gain in which-path distinguishability $I$ mathematically necessitates a rigid destruction of interference visibility $V$.

## 3. The Measurement Channel
The act of a "detector" sitting at the slits is modeled as a **Kraus Trace-Preserving Completely Positive Map**. Specifically, an ideal which-path interaction is a Lüders dephasing channel:
$$ \mathcal{E}_{path}(\rho) = \Pi_0 \rho \Pi_0 + \Pi_1 \rho \Pi_1 $$
where $\Pi_0, \Pi_1$ are the spatial projectors.

This mathematical operation preserves the diagonal entries ($p_0, p_1$ are unmodified) but strictly forces the off-diagonal coherences to zero ($\rho_{01} \to 0$), forcing $V \to 0$ post-measurement, mathematically formalizing wavefunction collapse on the path basis.

## 4. Logical Entropy and Landauer’s Principle

The repository links quantum path distinguishability to the UMST thermodynamic gate.

### Diagonal Information Entropy

$$H = -p_0 \ln p_0 - p_1 \ln p_1$$

This is the von Neumann entropy evaluated on the diagonal frame (the classical thermodynamic projection), capped at $\ln 2$ nats.

### The Landauer Bound

$$Q \ge k_B T \cdot H$$

Extracting the which-path bit from the measurement channel to the macro-world incurs a strict physical constraint via Landauer’s Principle. The minimum heat dissipated against a thermal bath at temperature $T$ is bounded by $k_B T \ln 2$ per bit.

### Principle of Maximal Information Collapse

Given measured $\text{MI}_{\text{extracted}}$ (in joules), the remaining coherence capacity is:

$$\text{Residual Logical Uncertainty} = 1 - \frac{\text{MI}_{\text{extracted}}}{k_B T \ln 2}$$

This is the thermodynamic bound enforced by the UMST gate on top of $V^2 + I^2 \le 1$.

- $\text{MI}_{\text{extracted}} = 0 \implies \text{residual} = 1$ (full visibility possible).
- $\text{MI}_{\text{extracted}} = k_B T \ln 2 \implies \text{residual} = 0$ (complete decoherence).

**Formally proved in Lean 4** (`LandauerBound.lean`):
- `principle_of_maximal_information_collapse` — residual $\in [0, 1]$
- `maximal_extraction_collapses_coherence` — 1-bit extraction $\implies$ residual $= 0$
- `null_extraction_preserves_coherence` — zero extraction $\implies$ residual $= 1$
- `landauerCost_eq_bitEnergy_times_extracted` — cost $= k_B T \ln 2 \cdot (1 - \text{residual})$

This closes the self-consistent loop: macroscopic energy expenditure of the intelligent probe maps directly to microscopic destruction of interference.

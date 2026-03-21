# Mathematical Foundations: UMST Formal Double-Slit

This document serves as the comprehensive, single point of truth for the mathematical definitions, theorems, and physical explanations mechanized within the `umst-formal-double-slit` repository.

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

## 4. Logical Entropy and Landauer's Principle

The repository securely links the quantum path distinguishability to the classical continuum thermodynamics of the UMST gate.

### Diagonal Information Entropy
Given the extracted path distribution after measurement, the logical uncertainty of the system is given by the discrete Shannon entropy over the diagonals (in natural units):

\[ H = -p_0 \ln p_0 - p_1 \ln p_1 \]

This is mathematically equivalent to the von Neumann entropy evaluated strictly on the diagonal frame (the classical thermodynamic projection) and is capped at \(\ln 2\) bits.

### The Landauer Bound
If the observer extracts the which-path bit from the measurement channel to the macro-world, that computational memory trace incurs a strict physical constraint via **Landauer’s Principle**. To erase or isolate that bit computationally against a thermal bath at temperature \(T\), the minimum heat dissipated \(Q\) (or work required \(W\)) is strictly bound:

\[ Q \ge k_B T \cdot H \]

In bits, the scale is exactly \(k_B T \ln 2\).

The formalized modules (`LandauerLaw`, `LandauerExtension`, and `EpistemicGalois`) rigorously establish this Galois connection: the maximal information \(I_{\text{bits}}\) extractable from the quantum system is bounded by the minimum thermodynamic energetic mass-equivalent \(E\) deployed by the classical observer.

### Principle of Maximal Information Collapse
By normalizing the physical energy scale against the Landauer bound, we quantify the exact thermodynamic constraint that the UMST gate imposes on remaining quantum coherence.

Given an experimentally measured \(\text{MI extracted}\) (in energy/Joules), dividing by \(k_B T \ln 2\) yields the extracted information \(I_{\text{bits}}\). The remaining capacity for interference after this irreversible dissipation is dictated by the **Principle of Maximal Information Collapse**:

\[ \text{Residual Logical Uncertainty} = 1 - \frac{\text{MI extracted}}{k_B T \ln 2} \]

This algebraic ratio represents the *normalized remaining coherence capacity* after the observer has paid the Landauer cost.  
- If no information is extracted (\(\text{MI extracted} = 0\)), the residual is exactly **1** (full quantum visibility possible: \(V \le 1\)).  
- If the maximum possible information is extracted (\(\text{MI extracted} = k_B T \ln 2\)), the residual collapses to **0** (complete decoherence: \(V = 0\)).

This thermodynamic bound is strictly enforced by the UMST gate on top of the standard quantum limit \(V^2 + I^2 \le 1\). It directly maps the macroscopic energy expenditure of the intelligent probe to the microscopic destruction of interference, closing the self-consistent loop between sensing, entropy production, and classical emergence.

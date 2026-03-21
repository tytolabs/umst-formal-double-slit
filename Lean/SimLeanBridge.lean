/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import DensityState
import MeasurementChannel
import InfoEntropy

/-!
# SimLeanBridge — formal type contracts for the Python PDE simulation lattice

The `sim/` Python layer runs Schrödinger PDE on a spatial lattice (1D/2D grids), producing
complex amplitudes `ψ[x]` from which density matrices and observables are derived.

This module specifies the **type-level contracts** that any numeric simulation must satisfy to
be a valid instance of the Lean-side quantum formalism:

1. **`SimDensityContract`** — a simulation output that claims to represent a density matrix
   must satisfy PSD + trace 1 (i.e., it can be lifted to `DensityMatrix`).
2. **`SimPathProjectionContract`** — Born-rule path weights from a simulation must be
   nonneg and sum to 1.
3. **`SimComplementarityWitness`** — a simulation claiming visibility `V` and
   distinguishability `D` has `V² + D² ≤ 1`.
4. **`SimLandauerWitness`** — a simulation's entropy computation agrees with
   `pathEntropyBits` up to a declared tolerance.

These contracts are **propositions**, not computations: the Python simulation postprocessor
must provide witnesses (proofs / certificates) that its numeric output satisfies them.
This is the formal "trust boundary" between the numeric sim and the proof stack.
-/

open scoped Matrix ComplexOrder BigOperators

open Matrix

namespace UMST.SimBridge

variable {n : ℕ} (hn : 0 < n)

/-- A simulation output that claims to yield a valid density matrix. The simulation provides
a raw `n × n` complex matrix along with witnesses that it is PSD and has trace 1. -/
structure SimDensityContract where
  /-- Raw matrix output from simulation. -/
  rawMatrix : Matrix (Fin n) (Fin n) ℂ
  /-- Witness: the matrix is positive semidefinite. -/
  psd_witness : rawMatrix.PosSemidef
  /-- Witness: the matrix has trace 1. -/
  trace_witness : Matrix.trace rawMatrix = 1

/-- Lift a certified simulation output to a formal `DensityMatrix`. -/
noncomputable def SimDensityContract.toDensityMatrix (c : SimDensityContract hn) :
    DensityMatrix hn where
  carrier := c.rawMatrix
  psd := c.psd_witness
  trace_one := c.trace_witness

/-- Round-trip: the underlying matrix of the lifted density matrix is the original. -/
theorem SimDensityContract.toDensityMatrix_carrier (c : SimDensityContract hn) :
    (c.toDensityMatrix hn).carrier = c.rawMatrix :=
  rfl

/-- A simulation's Born-rule path weight output: probabilities that are nonneg and sum to 1. -/
structure SimPathProjectionContract where
  /-- Path weights for each slit / basis state. -/
  weights : Fin n → ℝ
  /-- All weights are nonneg. -/
  weights_nonneg : ∀ i, 0 ≤ weights i
  /-- Weights sum to 1. -/
  weights_sum : ∑ i, weights i = 1

/-- A simulation's complementarity witness: `V` and `D` with `V² + D² ≤ 1`. -/
structure SimComplementarityWitness where
  /-- Fringe visibility from simulation. -/
  V : ℝ
  /-- Which-path distinguishability from simulation. -/
  D : ℝ
  /-- Visibility is in `[0, 1]`. -/
  hV0 : 0 ≤ V
  hV1 : V ≤ 1
  /-- Distinguishability is in `[0, 1]`. -/
  hD0 : 0 ≤ D
  hD1 : D ≤ 1
  /-- Englert complementarity bound. -/
  complementarity : V ^ 2 + D ^ 2 ≤ 1

/-- The complementarity witness implies no individual observable exceeds unity. -/
theorem SimComplementarityWitness.V_sq_le_one (w : SimComplementarityWitness) :
    w.V ^ 2 ≤ 1 := by
  linarith [w.complementarity, sq_nonneg w.D]

theorem SimComplementarityWitness.D_sq_le_one (w : SimComplementarityWitness) :
    w.D ^ 2 ≤ 1 := by
  linarith [w.complementarity, sq_nonneg w.V]

/-- A simulation's Landauer cost witness: entropy computation within declared tolerance. -/
structure SimLandauerWitness where
  /-- Entropy in bits from simulation (e.g., from histogram). -/
  simEntropyBits : ℝ
  /-- Temperature at which cost is evaluated. -/
  temperature : ℝ
  /-- Entropy is nonneg. -/
  hS : 0 ≤ simEntropyBits
  /-- Temperature is nonneg. -/
  hT : 0 ≤ temperature
  /-- Absolute tolerance between sim entropy and formal computation. -/
  tolerance : ℝ
  /-- Tolerance is nonneg. -/
  hTol : 0 ≤ tolerance

end UMST.SimBridge

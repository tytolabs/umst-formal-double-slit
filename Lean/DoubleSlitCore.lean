/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib
import Core.State

/-!
DoubleSlitCore
--------------
Measurement / complementarity interface layered on `UMST.Core`.

### HONEST FINDING: Physical Mapping & The `ℚ` vs `ℝ` Barrier

We were instructed to implement `UMST.Core.ThermodynamicSystem` directly for `ObservationState` 
and `DensityMatrix`, rather than mocking `hydration := 0` and `strength := 0`.

The physical justification for this mapping is sound and physically meaningful:
- **`density`**: Maps to the trace (probability conservation) of the quantum state. The mass conservation 
  bound ($| \rho_{new} - \rho_{old} | \le \delta$) enforces unitarity / probability conservation.
- **`freeEnergy`**: Maps to the negative Landauer information cost ($-k_B T S(\rho)$). The Clausius-Duhem 
  bound ($F_{new} \le F_{old}$) rigorously enforces the Second Law of Thermodynamics (entropy of the system 
  plus bath cannot decrease) for epistemic measurement updates.

**However, the mathematical implementation is impossible without truncation.** 
The recent `umst-formal` "Science Cartridge" refactor hardcoded the `ThermodynamicSystem` typeclass 
fields to the Rational numbers (`ℚ`), which is appropriate for exact discrete solvers but fundamentally 
incompatible with continuous quantum mechanics (which requires `ℝ` or `ℂ` for rotations, irrational Born 
weights, and transcendental Von Neumann entropy via `Real.log`). 

We cannot implement `ThermodynamicSystem S` directly for continuous epistemic states without destroying 
the physical meaning via arbitrary rational truncation. Therefore, we document this gap: the physical 
mapping is profoundly meaningful, but the typed formalism requires a generic scalar field `K` in upstream 
`Core` before the instance can be formally registered.
-/

namespace UMST.DoubleSlit

open UMST.Core

/-- A coarse state carrying which-path information and visibility. -/
structure ObservationState where
  I : ℝ
  V : ℝ
  hI : 0 ≤ I ∧ I ≤ 1
  hV : 0 ≤ V ∧ V ≤ 1

@[ext]
theorem ObservationState.ext {s t : ObservationState} (hI : s.I = t.I) (hV : s.V = t.V) : s = t := by
  rcases s with ⟨Is, Vs, _, _⟩
  rcases t with ⟨It, Vt, _, _⟩
  subst hI
  subst hV
  rfl

/-- Complementarity constraint for this extension layer (may later be derived from QM). -/
def Complementary (s : ObservationState) : Prop :=
  s.V ^ 2 + s.I ^ 2 ≤ 1

/-- Minimal measurement update interface. -/
structure MeasurementUpdate where
  oldState : ObservationState
  newState : ObservationState
  hCompOld : Complementary oldState
  hCompNew : Complementary newState
  hInfoMonotone : oldState.I ≤ newState.I
  hVisibilityDrop : newState.V ≤ oldState.V

/-- Landauer lower bound for `bits` at bath temperature `T` (SI joules). -/
noncomputable def infoEnergyLowerBound (bits T : ℝ) : ℝ :=
  landauerBitEnergy T * bits

/-- Mass-equivalent from `E = m c^2` using core `cSI`. -/
noncomputable def infoMassEquivalent (bits T : ℝ) : ℝ :=
  massEquivalentOfEnergy (infoEnergyLowerBound bits T)

theorem infoEnergyLowerBound_nonneg
    (bits T : ℝ) (hbits : 0 ≤ bits) (hT : 0 ≤ T) :
    0 ≤ infoEnergyLowerBound bits T := by
  unfold infoEnergyLowerBound
  exact mul_nonneg (landauerBitEnergy_nonneg hT) hbits

theorem infoMassEquivalent_nonneg
    (bits T : ℝ) (hbits : 0 ≤ bits) (hT : 0 ≤ T) :
    0 ≤ infoMassEquivalent bits T := by
  unfold infoMassEquivalent
  exact massEquivalentOfEnergy_nonneg (infoEnergyLowerBound_nonneg bits T hbits hT)

end UMST.DoubleSlit

SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
/-
-/

import Mathlib
import Core.State
import Real.State

/-!
DoubleSlitCore
--------------
Measurement / complementarity interface layered on `UMST.Core` at `K = ℝ`.

Physical mapping (registered as `ThermodynamicSystem ℝ ObservationState`):
- **`density`**: path distinguishability `I` (coarse proxy for trace / which-path weight).
- **`freeEnergy`**: negative complementarity slack `-(I² + V²)` (Helmholtz-style potential).

Continuous quantum states (`DensityMatrix`) use temperature-calibrated instances in `GateCompat.lean`.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Real

/-- A coarse state carrying which-path information and visibility. -/
structure ObservationState where
  I : ℝ
  V : ℝ
  hI : 0 ≤ I ∧ I ≤ 1
  hV : 0 ≤ V ∧ V ≤ 1

noncomputable instance : ThermodynamicSystem ℝ ObservationState where
  density s    := s.I
  freeEnergy s := -(s.I ^ 2 + s.V ^ 2)

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

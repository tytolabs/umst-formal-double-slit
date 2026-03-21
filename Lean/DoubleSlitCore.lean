/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib
import UMSTCore

/-!
DoubleSlitCore
--------------
Measurement / complementarity interface layered on `UMST.Core` (Landauer scale + ℝ gate shape).

This is not a full quantum derivation. It defines:
- which-path information (`I`), fringe visibility (`V`),
- complementarity (`V^2 + I^2 ≤ 1`) as the interface (**proved** for the canonical qubit `(I,V)` in `QuantumClassicalBridge.complementarity_fringe_path`),
- `MeasurementUpdate` (information monotone + visibility drop) — instantiated for Lüders which-path in `DoubleSlit.measurementUpdateWhichPath`,
- thermodynamic information-energy lower bound via `UMST.Core.landauerBitEnergy`.
- **`ObservationState.ext`**: equality from `I` and `V` (proof fields by proof irrelevance).
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

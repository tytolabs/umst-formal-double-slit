/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import QuantumClassicalBridge
import LandauerBound

/-!
# Complementarity — Englert shim + Lüders which-path `MeasurementUpdate`

The Englert-style inequality is proved in `QuantumClassicalBridge`. This module repeats it under
`UMST.DoubleSlit` next to `Complementary` / `ObservationState` for grep-friendly discovery.

**`measurementUpdateWhichPath`** lives here (not in `DoubleSlit.lean`) so `EpistemicSensing` can
import this layer without a cycle through `GateCompat` → `EpistemicSensing` → `DoubleSlit`.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

/-- `V² + I² ≤ 1` for canonical fringe visibility and coarse which-path score. -/
theorem complementarityEnglert (ρ : DensityMatrix hnQubit) :
    fringeVisibility ρ ^ 2 + whichPathDistinguishability ρ ^ 2 ≤ 1 :=
  complementarity_fringe_path ρ

theorem observationCanonical_complementary (ρ : DensityMatrix hnQubit) :
    Complementary (observationStateCanonical ρ) :=
  observationStateCanonical_complementary ρ

/-- Lüders which-path on the path qubit, expressed in the coarse `ObservationState` / `MeasurementUpdate`
interface. -/
noncomputable def measurementUpdateWhichPath (ρ : DensityMatrix hnQubit) : MeasurementUpdate where
  oldState := observationStateCanonical ρ
  newState := observationStateCanonical (KrausChannel.whichPathChannel.apply hnQubit ρ)
  hCompOld := observationStateCanonical_complementary ρ
  hCompNew := observationStateCanonical_complementary (KrausChannel.whichPathChannel.apply hnQubit ρ)
  hInfoMonotone := by
    simp [observationStateCanonical]
    rw [whichPathDistinguishability_whichPath_apply]
  hVisibilityDrop := by
    simp [observationStateCanonical, fringeVisibility_whichPath_apply, fringeVisibility_nonneg]

@[simp]
theorem measurementUpdateWhichPath_new_V (ρ : DensityMatrix hnQubit) :
    (measurementUpdateWhichPath ρ).newState.V = 0 := by
  simp [measurementUpdateWhichPath, observationStateCanonical, fringeVisibility_whichPath_apply]

theorem measurementUpdateWhichPath_I_eq (ρ : DensityMatrix hnQubit) :
    (measurementUpdateWhichPath ρ).oldState.I = (measurementUpdateWhichPath ρ).newState.I := by
  simp [measurementUpdateWhichPath, observationStateCanonical, whichPathDistinguishability_whichPath_apply]

/-- Diagonal-path Landauer costing is unchanged along `measurementUpdateWhichPath`. -/
theorem measurementUpdateWhichPath_landauer_eq (ρ : DensityMatrix hnQubit) (T : ℝ) :
    landauerCostDiagonal ρ T =
      landauerCostDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) T :=
  (landauerCostDiagonal_whichPathInvariant ρ T).symm

/-- Before and after `measurementUpdateWhichPath`, diagonal Landauer costing is capped by one Landauer
bit-energy at temperature `T` (`0 ≤ T`). -/
theorem measurementUpdateWhichPath_landauer_le_landauerBitEnergy (ρ : DensityMatrix hnQubit) (T : ℝ)
    (hT : 0 ≤ T) :
    landauerCostDiagonal ρ T ≤ landauerBitEnergy T ∧
      landauerCostDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) T ≤ landauerBitEnergy T :=
  ⟨landauerCostDiagonal_le_landauerBitEnergy ρ T hT,
    landauerCostDiagonal_le_landauerBitEnergy (KrausChannel.whichPathChannel.apply hnQubit ρ) T hT⟩

end UMST.DoubleSlit

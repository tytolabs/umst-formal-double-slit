/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Complementarity
import GateCompat
import LandauerBound
import TensorPartialTrace

/-!
# DoubleSlit — full-chain import closure + which-path measurement update

Import this module (or run `lake build`) to ensure **complementarity**, **Landauer diagonal costing**,
and **gate compatibility** layers all compile together.

**`measurementUpdateWhichPath`:** packages Lüders which-path on a qubit density matrix as a
`DoubleSlitCore.MeasurementUpdate`: `I` unchanged (diagonal Born weights), `V` drops to `0`, both
ends complementary.

Main entry points:
* `UMST.DoubleSlit.complementarityEnglert`
* `UMST.DoubleSlit.landauerCostDiagonal_nonneg`, `landauerCostDiagonal_whichPathInvariant`
* `UMST.DoubleSlit.admissible_thermoFromQubitPath_whichPath`
* `UMST.DoubleSlit.measurementUpdateWhichPath`, `measurementUpdateWhichPath_new_V`
* `UMST.DoubleSlit.measurementUpdateWhichPath_landauer_eq`
* `UMST.DoubleSlit.measurementUpdateWhichPath_landauer_le_landauerBitEnergy`
* `UMST.DoubleSlit.interference_preserved_identity`
* `UMST.DoubleSlit.collapse_fringe_on_whichPath`
* `UMST.DoubleSlit.measurementUpdateWhichPath_gateEnforcement`
* `UMST.DoubleSlit.principle_of_maximal_information_collapse`
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

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

/-- Diagonal-path Landauer costing is unchanged along `measurementUpdateWhichPath` (diagonal / entropy invariant). -/
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

/-- Identity channel (no detector) preserves fringe visibility. -/
theorem interference_preserved_identity (ρ : DensityMatrix hnQubit) :
    fringeVisibility ((KrausChannel.identity 2).apply hnQubit ρ) = fringeVisibility ρ := by
  congr 1
  exact DensityMat.ext (KrausChannel.identity_map 2 ρ.carrier)

/-- Which-path measurement collapses fringe visibility. -/
theorem collapse_fringe_on_whichPath (ρ : DensityMatrix hnQubit) :
    fringeVisibility (KrausChannel.whichPathChannel.apply hnQubit ρ) = 0 :=
  fringeVisibility_whichPath_apply ρ

/-- Combined gate narrative: admissible thermo update + Landauer invariance + one-bit cap. -/
theorem measurementUpdateWhichPath_gateEnforcement (ρ : DensityMatrix hnQubit) (T : ℝ)
    (hT : 0 ≤ T) :
    Admissible (thermoFromQubitPath ρ)
      (thermoFromQubitPath (KrausChannel.whichPathChannel.apply hnQubit ρ)) ∧
    landauerCostDiagonal ρ T =
      landauerCostDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) T ∧
    landauerCostDiagonal ρ T ≤ landauerBitEnergy T :=
  ⟨admissible_thermoFromQubitPath_whichPath ρ,
    (landauerCostDiagonal_whichPathInvariant ρ T).symm,
    landauerCostDiagonal_le_landauerBitEnergy ρ T hT⟩

end UMST.DoubleSlit

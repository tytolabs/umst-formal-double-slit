/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Complementarity
import LandauerBound

/-!
# DoubleSlitMeasurementUpdate — which-path `MeasurementUpdate` without `GateCompat`

This fragment is split out so **`EpistemicSensing`** can import the coarse measurement interface
(`measurementUpdateWhichPath`, fringe/channel lemmas) **without** creating a module cycle
`DoubleSlit → GateCompat → EpistemicSensing → DoubleSlit`.

Import **`DoubleSlit`** for the full closure including gate compatibility.
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

/-- A channel collapses all fringes iff it zeros the `(0,1)` off-diagonal for every density matrix. -/
theorem collapse_all_fringes_iff_zeros_offdiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : KrausChannel 2 ι) :
    (∀ ρ : DensityMatrix hnQubit, fringeVisibility (κ.apply hnQubit ρ) = 0) ↔
    (∀ ρ : DensityMatrix hnQubit, (κ.map ρ.carrier) 0 1 = 0) := by
  constructor
  · intro h ρ
    rw [fringeVisibility_eq_zero_iff] at h
    exact h ρ
  · intro h ρ
    rw [fringeVisibility_eq_zero_iff]
    exact h ρ

end UMST.DoubleSlit

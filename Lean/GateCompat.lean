-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import Core.Gate
import Real.Gate
import Real.State
import MeasurementChannel
import QuantumClassicalBridge
import LandauerBound
import EpistemicSensing
import GeneralVisibility

/-!
# GateCompat — epistemic quantum states on upstream `ThermodynamicSystem ℝ`

After umst-formal Core generalization (`K`-indexed `ThermodynamicSystem`), this module consumes
`UMST.Real.RealThermodynamicState` and `UMST.Real.RealAdmissible` (= `CoreAdmissible ℝ` by `rfl`)
instead of a local scaffold. `DensityMatrix` registers a temperature-calibrated instance below.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Real UMST.Quantum

section CalibratedTemperature

variable (T : ℝ)

/-- `DensityMatrix` at bath temperature `T`: Born weight + negative Landauer free energy. -/
noncomputable instance densityMatrixThermoSystem :
    ThermodynamicSystem ℝ (DensityMatrix hnQubit) where
  density ρ    := pathWeight ρ 0
  freeEnergy ρ := -landauerCostDiagonal ρ T

/-- Minimal ℝ scaffold from computational-basis path weights. -/
noncomputable def thermoFromQubitPath (ρ : DensityMatrix hnQubit) : RealThermodynamicState where
  density := pathWeight ρ 0
  freeEnergy := pathWeight ρ 1

@[simp]
theorem thermoFromQubitPath_whichPath (ρ : DensityMatrix hnQubit) :
    thermoFromQubitPath (KrausChannel.whichPathChannel.apply hnQubit ρ) = thermoFromQubitPath ρ := by
  simp [thermoFromQubitPath, pathWeight_whichPath_apply]

theorem admissible_thermoFromQubitPath_whichPath (ρ : DensityMatrix hnQubit) :
    RealAdmissible (thermoFromQubitPath ρ)
      (thermoFromQubitPath (KrausChannel.whichPathChannel.apply hnQubit ρ)) := by
  rw [thermoFromQubitPath_whichPath]
  exact realAdmissibleRefl _

/-! ## Thermodynamic calibration: `freeEnergy = -T · S(ρ)` (Gap 10) -/

/-- Calibrated ℝ scaffold: `freeEnergy = -landauerCostDiagonal ρ T`. -/
noncomputable def thermoCalibratedScaffold (ρ : DensityMatrix hnQubit) : RealThermodynamicState where
  density := pathWeight ρ 0
  freeEnergy := -landauerCostDiagonal ρ T

@[simp]
theorem thermoCalibratedScaffold_whichPath (ρ : DensityMatrix hnQubit) :
    thermoCalibratedScaffold T (KrausChannel.whichPathChannel.apply hnQubit ρ) =
      thermoCalibratedScaffold T ρ := by
  simp [thermoCalibratedScaffold, pathWeight_whichPath_apply]

theorem admissible_thermoCalibratedScaffold_whichPath (ρ : DensityMatrix hnQubit) :
    RealAdmissible (thermoCalibratedScaffold T ρ)
      (thermoCalibratedScaffold T (KrausChannel.whichPathChannel.apply hnQubit ρ)) := by
  rw [thermoCalibratedScaffold_whichPath]
  exact realAdmissibleRefl _

theorem admissible_densityMatrix_whichPath (ρ : DensityMatrix hnQubit) :
    CoreAdmissible ℝ (DensityMatrix hnQubit) ρ
      (KrausChannel.whichPathChannel.apply hnQubit ρ) := by
  refine ⟨?mass, ?dissip⟩
  · simp only [ThermodynamicSystem.density, pathWeight_whichPath_apply, sub_self, abs_zero,
      UMST.Core.δMass_real_def]
    exact zero_le (δMass (K := ℝ))
  · simp only [ThermodynamicSystem.freeEnergy, landauerCostDiagonal_whichPathInvariant, le_refl]

/-- The calibrated free energy is nonpositive for `T ≥ 0`. -/
theorem thermoCalibratedScaffold_freeEnergy_nonpos (ρ : DensityMatrix hnQubit) (hT : 0 ≤ T) :
    (thermoCalibratedScaffold T ρ).freeEnergy ≤ 0 := by
  simp only [thermoCalibratedScaffold]
  linarith [landauerCostDiagonal_nonneg ρ T hT]

/-- `|freeEnergy| ≤ landauerBitEnergy T` — bounded by the one-bit Landauer scale. -/
theorem thermoCalibratedScaffold_freeEnergy_bounded (ρ : DensityMatrix hnQubit) (hT : 0 ≤ T) :
    |(thermoCalibratedScaffold T ρ).freeEnergy| ≤ landauerBitEnergy T := by
  simp only [thermoCalibratedScaffold]
  rw [abs_neg, abs_of_nonneg (landauerCostDiagonal_nonneg ρ T hT)]
  exact landauerCostDiagonal_le_landauerBitEnergy ρ T hT

/-! ## General Dimension `Fin n` Extensions (Gaps 2 & 10) -/

/-- Full N-dimensional calibrated gate state. -/
noncomputable def thermoCalibratedPhys_n {n : ℕ} (hn : 0 < n) (_P : QuantumProbe)
    (ρ : DensityMatrix hn) : RealThermodynamicState where
  density := (ρ.carrier ⟨0, hn⟩ ⟨0, hn⟩).re
  freeEnergy := -landauerCostDiagonal_n hn ρ T

theorem admissible_thermoCalibratedPhys_whichPath (ρ : DensityMatrix hnQubit) :
    RealAdmissible (thermoCalibratedScaffold T ρ)
      (thermoCalibratedScaffold T (KrausChannel.whichPathChannel.apply hnQubit ρ)) := by
  constructor
  · simp [thermoCalibratedScaffold, pathWeight_whichPath_apply]
  · simp [thermoCalibratedScaffold, landauerCostDiagonal_whichPathInvariant, le_refl]

end CalibratedTemperature

end UMST.DoubleSlit

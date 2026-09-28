-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  GateCompat — knowing-fibre device rail (P0-11b).

  No `DensityMatrix → RealThermodynamicState` carrier maps. Born weights and Landauer
  knowing cost live in `KnowingDeviceLedgerEntry` (device rail scalars). Acting
  `RealThermodynamicState` / `ConcreteState` hydration stays on the acting fibre only.

  `DualLedger` (acting meso, `umst-formal`) reads compute/material rails in ℚ; the
  knowing entry here is the epistemic cost record consumed by that story, not a functor
  into acting state.
-/

import Core.Gate
import Real.Gate
import Real.State
import MeasurementChannel
import QuantumClassicalBridge
import LandauerBound
import EpistemicSensing
import GeneralVisibility

namespace UMST.DoubleSlit

open UMST.Core UMST.Real UMST.Quantum

/-- `DensityMatrix` at bath temperature `T`: Born weight + negative Landauer free energy. -/
noncomputable def densityMatrixThermoSystem (T : ℝ) : ThermodynamicSystem ℝ (DensityMatrix hnQubit) where
  density ρ    := pathWeight ρ 0
  freeEnergy ρ := -landauerCostDiagonal ρ T

/-- Knowing-fibre **device rail** scalars (not an acting `ThermodynamicState` carrier). -/
structure KnowingDeviceLedgerEntry where
  bornPath0 : ℝ
  knowingCost : ℝ

/-- Ledger entry from a qubit density matrix at temperature `T`. -/
noncomputable def knowingDeviceLedgerEntry (T : ℝ) (ρ : DensityMatrix hnQubit) : KnowingDeviceLedgerEntry where
  bornPath0 := pathWeight ρ 0
  knowingCost := landauerCostDiagonal ρ T

@[simp]
theorem knowingDeviceLedgerEntry_whichPath (T : ℝ) (ρ : DensityMatrix hnQubit) :
    knowingDeviceLedgerEntry T (KrausChannel.whichPathChannel.apply hnQubit ρ) =
      knowingDeviceLedgerEntry T ρ := by
  simp [knowingDeviceLedgerEntry, pathWeight_whichPath_apply,
    landauerCostDiagonal_whichPathInvariant]

theorem admissible_densityMatrix_whichPath (T : ℝ) (ρ : DensityMatrix hnQubit) :
    @CoreAdmissible ℝ _ _ (DensityMatrix hnQubit) (densityMatrixThermoSystem T) ρ
      (KrausChannel.whichPathChannel.apply hnQubit ρ) :=
  @CoreAdmissible.mk ℝ _ _ (DensityMatrix hnQubit) (densityMatrixThermoSystem T) ρ
    (KrausChannel.whichPathChannel.apply hnQubit ρ)
    (by
      change |pathWeight (KrausChannel.whichPathChannel.apply hnQubit ρ) 0 - pathWeight ρ 0| ≤
          (δMass (K := ℝ) : ℝ)
      simp [pathWeight_whichPath_apply, UMST.Core.δMass_real_def])
    (by
      change -landauerCostDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) T ≤
          -landauerCostDiagonal ρ T
      linarith [landauerCostDiagonal_whichPathInvariant ρ T])

/-- Alias retained for importers (no `thermoFromQubitPath` carrier). -/
theorem admissible_thermoFromQubitPath_whichPath (T : ℝ) (ρ : DensityMatrix hnQubit) :
    @CoreAdmissible ℝ _ _ (DensityMatrix hnQubit) (densityMatrixThermoSystem T) ρ
      (KrausChannel.whichPathChannel.apply hnQubit ρ) :=
  admissible_densityMatrix_whichPath T ρ

theorem admissible_thermoCalibratedScaffold_whichPath (T : ℝ) (ρ : DensityMatrix hnQubit) :
    @CoreAdmissible ℝ _ _ (DensityMatrix hnQubit) (densityMatrixThermoSystem T) ρ
      (KrausChannel.whichPathChannel.apply hnQubit ρ) :=
  admissible_densityMatrix_whichPath T ρ

theorem admissible_thermoCalibratedPhys_whichPath (T : ℝ) (ρ : DensityMatrix hnQubit) :
    @CoreAdmissible ℝ _ _ (DensityMatrix hnQubit) (densityMatrixThermoSystem T) ρ
      (KrausChannel.whichPathChannel.apply hnQubit ρ) :=
  admissible_densityMatrix_whichPath T ρ

/-- Calibrated knowing cost is nonpositive for `T ≥ 0`. -/
theorem thermoCalibratedScaffold_freeEnergy_nonpos (T : ℝ) (ρ : DensityMatrix hnQubit) (hT : 0 ≤ T) :
    (densityMatrixThermoSystem T).freeEnergy ρ ≤ 0 := by
  simp only [densityMatrixThermoSystem, ThermodynamicSystem.freeEnergy]
  linarith [landauerCostDiagonal_nonneg ρ T hT]

/-- `|knowingCost| ≤ landauerBitEnergy T` on the device rail. -/
theorem thermoCalibratedScaffold_freeEnergy_bounded (T : ℝ) (ρ : DensityMatrix hnQubit) (hT : 0 ≤ T) :
    |(densityMatrixThermoSystem T).freeEnergy ρ| ≤ landauerBitEnergy T := by
  simp only [densityMatrixThermoSystem, ThermodynamicSystem.freeEnergy]
  rw [abs_neg, abs_of_nonneg (landauerCostDiagonal_nonneg ρ T hT)]
  exact landauerCostDiagonal_le_landauerBitEnergy ρ T hT

theorem knowingDeviceLedgerEntry_cost_nonpos (T : ℝ) (ρ : DensityMatrix hnQubit) (hT : 0 ≤ T) :
    (knowingDeviceLedgerEntry T ρ).knowingCost ≥ 0 :=
  landauerCostDiagonal_nonneg ρ T hT

theorem knowingDeviceLedgerEntry_cost_bounded (T : ℝ) (ρ : DensityMatrix hnQubit) (hT : 0 ≤ T) :
    (knowingDeviceLedgerEntry T ρ).knowingCost ≤ landauerBitEnergy T :=
  landauerCostDiagonal_le_landauerBitEnergy ρ T hT

end UMST.DoubleSlit

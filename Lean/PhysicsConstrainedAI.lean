/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import EpistemicMI

/-!
# PhysicsConstrainedAI — sandbox vs gating on the same Landauer scale

**DUMSTO** (Decoupled UMST observation topology, in this file): the path-qubit layer
with probes `PathProbe.null` (no readout / “sandbox imagination”) vs `PathProbe.whichPath`
(the gating / which-path measurement step).

We reuse the existing epistemic MI and Landauer hooks from `EpistemicMI` / `DoubleSlitCore`.
No new physical axioms: the “same threshold” claim is the **shared** `landauerBitEnergy` scale
and `infoEnergyLowerBound` functional.
-/

namespace UMST.AgentDynamics

open UMST.Core UMST.Quantum UMST.DoubleSlit

/-- Sandbox layer: no path readout ⇒ zero epistemic MI (nats). -/
theorem sandbox_epistemicMI_zero (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.null ρ = 0 :=
  epistemicMI_null ρ

/-- Sandbox incurs **zero** Landauer-scale information-energy lower bound at any bath `T ≥ 0`. -/
theorem sandbox_landauer_cost_zero (ρ : DensityMatrix hnQubit) (T : ℝ) (_hT : 0 ≤ T) :
    epistemicLandauerCost PathProbe.null ρ T = 0 :=
  epistemicLandauerCost_null ρ T

/-- Gating step (which-path probe): same **one-bit** Landauer cap as any physical which-path
readout using this epistemic surrogate — already `≤ landauerBitEnergy T`. -/
theorem gating_landauer_le_one_bit (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    epistemicLandauerCost PathProbe.whichPath ρ T ≤ landauerBitEnergy T :=
  epistemicLandauerCost_le_landauerBitEnergy PathProbe.whichPath ρ T hT

/-- The calibrated thermodynamic scaffold uses `landauerCostDiagonal`, which matches the
which-path epistemic Landauer hook in **bit-equivalent** terms (`epistemicMIBits.whichPath =
pathEntropyBits`). -/
theorem gating_epistemic_cost_eq_diagonal_landauer_cost (ρ : DensityMatrix hnQubit) (T : ℝ) :
    epistemicLandauerCost PathProbe.whichPath ρ T = landauerCostDiagonal ρ T := by
  simp [epistemicLandauerCost, landauerCostDiagonal, epistemicMIBits_whichPath]

/-- **Same Landauer threshold:** software-only null probe pays `0`; which-path gating pays
exactly the diagonal-path Landauer lower bound — identical to the hook used for an actuating
measurement update on the path qubit (`measurementUpdateWhichPath` in `WhichPathMeasurementUpdate`). -/
theorem software_gating_share_diagonal_landauer (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    epistemicLandauerCost PathProbe.null ρ T = 0 ∧
      epistemicLandauerCost PathProbe.whichPath ρ T = landauerCostDiagonal ρ T ∧
        landauerCostDiagonal ρ T ≤ landauerBitEnergy T :=
  ⟨sandbox_landauer_cost_zero ρ T hT,
    gating_epistemic_cost_eq_diagonal_landauer_cost ρ T,
    landauerCostDiagonal_le_landauerBitEnergy ρ T hT⟩

end UMST.AgentDynamics

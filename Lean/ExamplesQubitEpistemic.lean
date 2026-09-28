-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
import ExamplesQubit
import EpistemicMI

/-!
# ExamplesQubitEpistemic — epistemic MI and Landauer cost on |+⟩, |0⟩, |1⟩

Kept in its own module so `ExamplesQubit` stays on the `ProbeOptimization` import graph and the
epistemic layer composes on top of it.
-/

namespace UMST.Quantum.Examples

open UMST.DoubleSlit UMST.Quantum

theorem rhoPlus_epistemicMI_whichPath : EpistemicMI PathProbe.whichPath rhoPlus = Real.log 2 := by
  rw [epistemicMI_whichPath, whichPathMI, rhoPlus_vonNeumannDiagonal_eq_log_two]

theorem rhoZero_epistemicMI_whichPath : EpistemicMI PathProbe.whichPath rhoZero = 0 := by
  rw [epistemicMI_whichPath, whichPathMI, rhoZero_vonNeumannDiagonal]

theorem rhoOne_epistemicMI_whichPath : EpistemicMI PathProbe.whichPath rhoOne = 0 := by
  rw [epistemicMI_whichPath, whichPathMI, rhoOne_vonNeumannDiagonal]

theorem rhoPlus_epistemicLandauerCost_whichPath (T : ℝ) :
    epistemicLandauerCost PathProbe.whichPath rhoPlus T = landauerBitEnergy T := by
  rw [epistemicLandauerCost_whichPath, rhoPlus_landauerCostDiagonal_eq_landauerBitEnergy]

theorem rhoZero_epistemicLandauerCost_whichPath (T : ℝ) :
    epistemicLandauerCost PathProbe.whichPath rhoZero T = 0 := by
  rw [epistemicLandauerCost_whichPath, rhoZero_landauerCostDiagonal]

theorem rhoOne_epistemicLandauerCost_whichPath (T : ℝ) :
    epistemicLandauerCost PathProbe.whichPath rhoOne T = 0 := by
  rw [epistemicLandauerCost_whichPath, rhoOne_landauerCostDiagonal]

end UMST.Quantum.Examples

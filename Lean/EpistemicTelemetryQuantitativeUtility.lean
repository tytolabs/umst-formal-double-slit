-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import EpistemicTelemetryApproximation

/-!
# EpistemicTelemetryQuantitativeUtility — nonzero-error utility bounds

This module provides quantitative bounds on utility deviation under explicit
nonzero approximation assumptions for runtime telemetry aggregates.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Utility error bound induced by MI/cost aggregate approximation errors. -/
noncomputable def utilityApproxBound (εMI εCost : ℝ) (T : ℝ) (_hT : 0 < T) (lam : ℝ) : ℝ :=
  εMI + |lam| * εCost / landauerBitEnergy T

theorem utilityApproxBound_nonneg (εMI εCost : ℝ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hεMI : 0 ≤ εMI) (hεCost : 0 ≤ εCost) :
    0 ≤ utilityApproxBound εMI εCost T hT lam := by
  unfold utilityApproxBound
  refine add_nonneg hεMI ?_
  refine div_nonneg ?_ (le_of_lt (landauerBitEnergy_pos hT))
  exact mul_nonneg (abs_nonneg lam) hεCost

@[simp]
theorem utilityApproxBound_zero (T : ℝ) (hT : 0 < T) (lam : ℝ) :
    utilityApproxBound 0 0 T hT lam = 0 := by
  unfold utilityApproxBound
  ring

theorem numericApprox_utility_diff_le {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (hT : 0 < T) (lam : ℝ)
    (εMI εCost : ℝ) (h : NumericTraceApproxConsistent εMI εCost τ π ρ0) :
    |traceRecordPolicyUtility τ hT lam - policyUtility π n ρ0 T hT lam|
      ≤ utilityApproxBound εMI εCost T hT lam := by
  rcases h with ⟨hεMI, hεCost, hMI, hCost⟩
  unfold traceRecordPolicyUtility policyUtility utilityApproxBound
  set dMI : ℝ := τ.aggregateMI - cumulativeEpistemicMI π n ρ0
  set dCost : ℝ := τ.aggregateCost - cumulativeEpistemicLandauerCost π n ρ0 T
  have hdMI : |dMI| ≤ εMI := by simpa [dMI] using hMI
  have hdCost : |dCost| ≤ εCost := by simpa [dCost] using hCost
  have hsplit : |dMI - lam * (dCost / landauerBitEnergy T)| ≤
      |dMI| + |lam * (dCost / landauerBitEnergy T)| := by
    simpa using abs_sub_le dMI 0 (lam * (dCost / landauerBitEnergy T))
  have hcostTerm :
      |lam * (dCost / landauerBitEnergy T)| ≤ |lam| * εCost / landauerBitEnergy T := by
    rw [abs_mul, abs_div, abs_of_pos (landauerBitEnergy_pos hT), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdCost (abs_nonneg lam))
      (landauerBitEnergy_pos hT).le
  have hsum : |dMI| + |lam * (dCost / landauerBitEnergy T)| ≤
      εMI + |lam| * εCost / landauerBitEnergy T :=
    add_le_add hdMI hcostTerm
  have hfinal : |dMI - lam * (dCost / landauerBitEnergy T)| ≤
      εMI + |lam| * εCost / landauerBitEnergy T :=
    le_trans hsplit hsum
  rw [show (τ.aggregateMI - lam * (τ.aggregateCost / landauerBitEnergy T)) -
      (cumulativeEpistemicMI π n ρ0 - lam * (cumulativeEpistemicLandauerCost π n ρ0 T / landauerBitEnergy T)) =
      dMI - lam * (dCost / landauerBitEnergy T) by simp only [dMI, dCost]; ring]
  exact hfinal

/-- The rollout's own telemetry reproduces the policy utility exactly (zero approximation error).
Stated for `RuntimeTelemetrySchema.ofRollout`: an arbitrary telemetry record carries no such guarantee. -/
theorem telemetryApprox_zero_utility_diff_zero (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) :
    |traceRecordPolicyUtility
        ((RuntimeTelemetrySchema.ofRollout π n ρ0 T).toPerStepNumericRecord.toNumericTraceRecord) hT lam
      - policyUtility π n ρ0 T hT lam| = 0 := by
  rw [telemetryApprox_zero_policyUtility_eq _ π ρ0 hT lam (telemetryApprox_ofRollout_zero π n ρ0 T)]
  simp

end UMST.DoubleSlit

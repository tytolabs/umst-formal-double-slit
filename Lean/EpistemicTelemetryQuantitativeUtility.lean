/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
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
noncomputable def utilityApproxBound (εMI εCost : ℝ) (T : ℝ) (hT : 0 < T) (λ : ℝ) : ℝ :=
  εMI + |λ| * εCost / landauerBitEnergy T

theorem utilityApproxBound_nonneg (εMI εCost : ℝ) (T : ℝ) (hT : 0 < T) (λ : ℝ)
    (hεMI : 0 ≤ εMI) (hεCost : 0 ≤ εCost) :
    0 ≤ utilityApproxBound εMI εCost T hT λ := by
  unfold utilityApproxBound
  refine add_nonneg hεMI ?_
  refine div_nonneg ?_ (le_of_lt (landauerBitEnergy_pos hT))
  exact mul_nonneg (abs_nonneg λ) hεCost

@[simp]
theorem utilityApproxBound_zero (T : ℝ) (hT : 0 < T) (λ : ℝ) :
    utilityApproxBound 0 0 T hT λ = 0 := by
  unfold utilityApproxBound
  ring

theorem numericApprox_utility_diff_le {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (hT : 0 < T) (λ : ℝ)
    (εMI εCost : ℝ) (h : NumericTraceApproxConsistent εMI εCost τ π ρ0) :
    |traceRecordPolicyUtility τ hT λ - policyUtility π n ρ0 T hT λ|
      ≤ utilityApproxBound εMI εCost T hT λ := by
  rcases h with ⟨hεMI, hεCost, hMI, hCost⟩
  unfold traceRecordPolicyUtility policyUtility utilityApproxBound
  set dMI : ℝ := τ.aggregateMI - cumulativeEpistemicMI π n ρ0
  set dCost : ℝ := τ.aggregateCost - cumulativeEpistemicLandauerCost π n ρ0 T
  have hdMI : |dMI| ≤ εMI := by simpa [dMI] using hMI
  have hdCost : |dCost| ≤ εCost := by simpa [dCost] using hCost
  have hsplit : |dMI - λ * (dCost / landauerBitEnergy T)| ≤
      |dMI| + |λ * (dCost / landauerBitEnergy T)| := abs_sub_le _ _ _
  have hcostTerm :
      |λ * (dCost / landauerBitEnergy T)| ≤ |λ| * εCost / landauerBitEnergy T := by
    rw [abs_mul, abs_div, abs_of_pos (landauerBitEnergy_pos hT)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdCost (abs_nonneg λ))
      (landauerBitEnergy_pos hT)
  have hsum : |dMI| + |λ * (dCost / landauerBitEnergy T)| ≤
      εMI + |λ| * εCost / landauerBitEnergy T :=
    add_le_add hdMI hcostTerm
  have hfinal : |dMI - λ * (dCost / landauerBitEnergy T)| ≤
      εMI + |λ| * εCost / landauerBitEnergy T :=
    le_trans hsplit hsum
  simpa [dMI, dCost, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] using hfinal

theorem telemetryApprox_zero_utility_diff_zero {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 < T) (λ : ℝ) :
    |traceRecordPolicyUtility (τ.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      - policyUtility π n ρ0 T hT λ| = 0 := by
  have hEq := telemetryApprox_zero_policyUtility_eq τ π ρ0 hT λ
    (telemetryApprox_ofRollout_zero π n ρ0 T)
  simp [hEq]

end UMST.DoubleSlit

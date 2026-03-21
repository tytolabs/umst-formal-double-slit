/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import EpistemicRuntimeContract

/-!
# EpistemicNumericsContract — runtime numeric trace records

This module adds a compact numeric record that a runtime can emit for a finite
policy rollout, together with consistency predicates that tie record fields to
the abstract rollout quantities.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Runtime-observable numeric summary of an `n`-step rollout at temperature `T`. -/
structure NumericTraceRecord (n : ℕ) (T : ℝ) where
  aggregateMI : ℝ
  aggregateCost : ℝ

/-- Canonical record extracted from the abstract rollout layer. -/
noncomputable def NumericTraceRecord.ofRollout (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : NumericTraceRecord n T :=
  ⟨cumulativeEpistemicMI π n ρ0, cumulativeEpistemicLandauerCost π n ρ0 T⟩

/-- Record consistency with abstract cumulative MI and Landauer cost. -/
def NumericTraceConsistent {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T) (π : ProbePolicy)
    (ρ0 : DensityMatrix hnQubit) : Prop :=
  τ.aggregateMI = cumulativeEpistemicMI π n ρ0 ∧
    τ.aggregateCost = cumulativeEpistemicLandauerCost π n ρ0 T

/-- Full consistency: rollout coherence, aggregate contracts, and record equality. -/
def NumericTraceFullyConsistent (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (τ : NumericTraceRecord n T) : Prop :=
  RuntimeTraceCoherent π n ρ0 ∧
  RuntimeTraceContractMI π n ρ0 ∧
  RuntimeTraceContractLandauer π n ρ0 T ∧
  NumericTraceConsistent τ π ρ0

/-- Utility computed directly from numeric record aggregates. -/
noncomputable def traceRecordPolicyUtility {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (hT : 0 < T) (λ : ℝ) : ℝ :=
  τ.aggregateMI - λ * (τ.aggregateCost / landauerBitEnergy T)

@[simp]
theorem NumericTraceRecord.ofRollout_aggregateMI (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    (NumericTraceRecord.ofRollout π n ρ0 T).aggregateMI = cumulativeEpistemicMI π n ρ0 :=
  rfl

@[simp]
theorem NumericTraceRecord.ofRollout_aggregateCost (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    (NumericTraceRecord.ofRollout π n ρ0 T).aggregateCost =
      cumulativeEpistemicLandauerCost π n ρ0 T :=
  rfl

theorem ofRollout_consistent (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) : NumericTraceConsistent (NumericTraceRecord.ofRollout π n ρ0 T) π ρ0 := by
  constructor <;> rfl

theorem ofRollout_fullyConsistent (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) : NumericTraceFullyConsistent π n ρ0 T (NumericTraceRecord.ofRollout π n ρ0 T) := by
  exact ⟨rollout_satisfies_traceCoherent π n ρ0, rollout_satisfies_traceContractMI π n ρ0,
    rollout_satisfies_traceContractLandauer π n ρ0 T, ofRollout_consistent π n ρ0 T⟩

theorem traceRecordPolicyUtility_eq_policyUtility {n : ℕ} {T : ℝ} (π : ProbePolicy)
    (ρ0 : DensityMatrix hnQubit) (hT : 0 < T) (λ : ℝ) (τ : NumericTraceRecord n T)
    (h : NumericTraceConsistent τ π ρ0) :
    traceRecordPolicyUtility τ hT λ = policyUtility π n ρ0 T hT λ := by
  unfold traceRecordPolicyUtility policyUtility
  rw [h.1, h.2]

theorem traceRecord_aggregateMI_nonneg {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (h : NumericTraceConsistent τ π ρ0) :
    0 ≤ τ.aggregateMI := by
  rw [h.1]
  exact cumulativeEpistemicMI_nonneg π n ρ0

theorem traceRecord_aggregateCost_nonneg {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : NumericTraceConsistent τ π ρ0) (hT : 0 ≤ T) :
    0 ≤ τ.aggregateCost := by
  rw [h.2]
  exact cumulativeEpistemicLandauerCost_nonneg π n ρ0 T hT

theorem traceRecord_aggregateMI_le {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (h : NumericTraceConsistent τ π ρ0) :
    τ.aggregateMI ≤ n * Real.log 2 := by
  rw [h.1]
  exact cumulativeEpistemicMI_le π n ρ0

theorem traceRecord_aggregateCost_le {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : NumericTraceConsistent τ π ρ0) (hT : 0 ≤ T) :
    τ.aggregateCost ≤ n * landauerBitEnergy T := by
  rw [h.2]
  exact cumulativeEpistemicLandauerCost_le π n ρ0 T hT

theorem traceRecordPolicyUtility_le_aggregateMI {n : ℕ} {T : ℝ}
    (τ : NumericTraceRecord n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 < T) (λ : ℝ) (hλ : 0 ≤ λ) (h : NumericTraceConsistent τ π ρ0) :
    traceRecordPolicyUtility τ hT λ ≤ τ.aggregateMI := by
  unfold traceRecordPolicyUtility
  have hcost : 0 ≤ τ.aggregateCost :=
    traceRecord_aggregateCost_nonneg τ π ρ0 h (le_of_lt hT)
  have hnonneg : 0 ≤ λ * (τ.aggregateCost / landauerBitEnergy T) :=
    mul_nonneg hλ (div_nonneg hcost (le_of_lt (landauerBitEnergy_pos hT)))
  linarith

end UMST.DoubleSlit

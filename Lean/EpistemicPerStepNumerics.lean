/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import EpistemicNumericsContract

/-!
# EpistemicPerStepNumerics — per-step numeric runtime records

This module formalizes per-step numeric records over a finite horizon and proves
that their finite folds match the abstract cumulative MI / Landauer expressions.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Per-step numeric record for an `n`-step rollout at temperature `T`. -/
structure PerStepNumericRecord (n : ℕ) (T : ℝ) where
  stepMI : ℕ → ℝ
  stepCost : ℕ → ℝ

/-- Aggregate MI as a finite fold over the first `n` steps. -/
noncomputable def PerStepNumericRecord.aggregateMI {n : ℕ} {T : ℝ}
    (τ : PerStepNumericRecord n T) : ℝ :=
  ∑ k in Finset.range n, τ.stepMI k

/-- Aggregate Landauer cost as a finite fold over the first `n` steps. -/
noncomputable def PerStepNumericRecord.aggregateCost {n : ℕ} {T : ℝ}
    (τ : PerStepNumericRecord n T) : ℝ :=
  ∑ k in Finset.range n, τ.stepCost k

/-- Canonical per-step record extracted from the abstract rollout semantics. -/
noncomputable def PerStepNumericRecord.ofRollout (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : PerStepNumericRecord n T where
  stepMI k := EpistemicMI (π k) (traceStateAt π ρ0 k)
  stepCost k := epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T

/-- Stepwise consistency of a runtime record with abstract rollout quantities. -/
def PerStepNumericConsistent {n : ℕ} {T : ℝ} (τ : PerStepNumericRecord n T) (π : ProbePolicy)
    (ρ0 : DensityMatrix hnQubit) : Prop :=
  (∀ k, k < n → τ.stepMI k = EpistemicMI (π k) (traceStateAt π ρ0 k)) ∧
  (∀ k, k < n → τ.stepCost k = epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T)

/-- Aggregate consistency with abstract cumulative MI and Landauer expressions. -/
def PerStepAggregateConsistent {n : ℕ} {T : ℝ} (τ : PerStepNumericRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : Prop :=
  τ.aggregateMI = cumulativeEpistemicMI π n ρ0 ∧
    τ.aggregateCost = cumulativeEpistemicLandauerCost π n ρ0 T

/-- Project per-step record to aggregate-only numeric record. -/
noncomputable def PerStepNumericRecord.toNumericTraceRecord {n : ℕ} {T : ℝ}
    (τ : PerStepNumericRecord n T) : NumericTraceRecord n T :=
  ⟨τ.aggregateMI, τ.aggregateCost⟩

@[simp]
theorem PerStepNumericRecord.ofRollout_stepMI (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (k : ℕ) :
    (PerStepNumericRecord.ofRollout π n ρ0 T).stepMI k = EpistemicMI (π k) (traceStateAt π ρ0 k) :=
  rfl

@[simp]
theorem PerStepNumericRecord.ofRollout_stepCost (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (k : ℕ) :
    (PerStepNumericRecord.ofRollout π n ρ0 T).stepCost k =
      epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T :=
  rfl

theorem ofRollout_perStepConsistent (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) : PerStepNumericConsistent (PerStepNumericRecord.ofRollout π n ρ0 T) π ρ0 := by
  constructor <;> intro k hk <;> rfl

@[simp]
theorem ofRollout_aggregateMI (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    (PerStepNumericRecord.ofRollout π n ρ0 T).aggregateMI = cumulativeEpistemicMI π n ρ0 := by
  rfl

@[simp]
theorem ofRollout_aggregateCost (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    (PerStepNumericRecord.ofRollout π n ρ0 T).aggregateCost =
      cumulativeEpistemicLandauerCost π n ρ0 T := by
  rfl

theorem perStepConsistent_implies_aggregateConsistent {n : ℕ} {T : ℝ}
    (τ : PerStepNumericRecord n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : PerStepNumericConsistent τ π ρ0) :
    PerStepAggregateConsistent τ π ρ0 := by
  constructor
  · unfold PerStepNumericRecord.aggregateMI cumulativeEpistemicMI
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact h.1 k (Finset.mem_range.mp hk)
  · unfold PerStepNumericRecord.aggregateCost cumulativeEpistemicLandauerCost
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact h.2 k (Finset.mem_range.mp hk)

theorem ofRollout_aggregateConsistent (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) :
    PerStepAggregateConsistent (PerStepNumericRecord.ofRollout π n ρ0 T) π ρ0 :=
  perStepConsistent_implies_aggregateConsistent _ _ _ (ofRollout_perStepConsistent π n ρ0 T)

@[simp]
theorem ofRollout_toNumericTraceRecord (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) :
    (PerStepNumericRecord.ofRollout π n ρ0 T).toNumericTraceRecord =
      NumericTraceRecord.ofRollout π n ρ0 T := by
  ext <;> rfl

theorem toNumericTraceRecord_consistent {n : ℕ} {T : ℝ} (τ : PerStepNumericRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : PerStepAggregateConsistent τ π ρ0) :
    NumericTraceConsistent τ.toNumericTraceRecord π ρ0 := by
  exact h

theorem perStepRecordPolicyUtility_eq_policyUtility {n : ℕ} {T : ℝ}
    (τ : PerStepNumericRecord n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 < T) (λ : ℝ) (h : PerStepAggregateConsistent τ π ρ0) :
    traceRecordPolicyUtility τ.toNumericTraceRecord hT λ = policyUtility π n ρ0 T hT λ :=
  traceRecordPolicyUtility_eq_policyUtility π ρ0 hT λ τ.toNumericTraceRecord h

end UMST.DoubleSlit

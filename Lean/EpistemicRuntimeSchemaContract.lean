import EpistemicPerStepNumerics

/-!
# EpistemicRuntimeSchemaContract — emitted runtime schema bridge

This module formalizes a minimal runtime-emitted step schema and proves that
if emitted step fields match abstract rollout quantities on the first `n` steps,
then all existing per-step/aggregate numeric contracts hold.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Minimal emitted step record used by runtime bridges.
`stepMI` and `stepCost` are mandatory; additional fields are metadata hooks. -/
structure EmittedStepRecord where
  stepMI : ℝ
  stepCost : ℝ
  thermodynamicAdmissible : Bool := true
  confidence : ℝ := 1

/-- Emitted finite-horizon trace schema at temperature `T`. -/
structure EmittedTraceSchema (n : ℕ) (T : ℝ) where
  step : ℕ → EmittedStepRecord

/-- Numeric sanity checks for emitted records over the first `n` steps. -/
def EmittedTraceWellFormed {n : ℕ} {T : ℝ} (τ : EmittedTraceSchema n T) (hT : 0 ≤ T) : Prop :=
  ∀ k, k < n →
    0 ≤ (τ.step k).stepMI ∧
      (τ.step k).stepMI ≤ Real.log 2 ∧
      0 ≤ (τ.step k).stepCost ∧
      (τ.step k).stepCost ≤ landauerBitEnergy T ∧
      0 ≤ (τ.step k).confidence ∧
      (τ.step k).confidence ≤ 1

/-- Semantic consistency: emitted MI/cost fields agree with abstract rollout terms. -/
def EmittedTraceRolloutConsistent {n : ℕ} {T : ℝ} (τ : EmittedTraceSchema n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : Prop :=
  ∀ k, k < n →
    (τ.step k).stepMI = EpistemicMI (π k) (traceStateAt π ρ0 k) ∧
      (τ.step k).stepCost = epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T

/-- Forget metadata and keep only numeric fields needed by theorems. -/
noncomputable def EmittedTraceSchema.toPerStepNumericRecord {n : ℕ} {T : ℝ}
    (τ : EmittedTraceSchema n T) : PerStepNumericRecord n T where
  stepMI k := (τ.step k).stepMI
  stepCost k := (τ.step k).stepCost

/-- Canonical emitted schema extracted from the abstract rollout. -/
noncomputable def EmittedTraceSchema.ofRollout (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : EmittedTraceSchema n T where
  step k := {
    stepMI := EpistemicMI (π k) (traceStateAt π ρ0 k)
    stepCost := epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T
    thermodynamicAdmissible := true
    confidence := 1
  }

theorem emittedRolloutConsistent_toPerStepConsistent {n : ℕ} {T : ℝ}
    (τ : EmittedTraceSchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : EmittedTraceRolloutConsistent τ π ρ0) :
    PerStepNumericConsistent τ.toPerStepNumericRecord π ρ0 := by
  constructor
  · intro k hk
    simpa [EmittedTraceSchema.toPerStepNumericRecord] using (h k hk).1
  · intro k hk
    simpa [EmittedTraceSchema.toPerStepNumericRecord] using (h k hk).2

theorem emittedRolloutConsistent_toAggregateConsistent {n : ℕ} {T : ℝ}
    (τ : EmittedTraceSchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : EmittedTraceRolloutConsistent τ π ρ0) :
    PerStepAggregateConsistent τ.toPerStepNumericRecord π ρ0 :=
  perStepConsistent_implies_aggregateConsistent _ _ _ (emittedRolloutConsistent_toPerStepConsistent τ π ρ0 h)

theorem emittedRolloutConsistent_toNumericTraceConsistent {n : ℕ} {T : ℝ}
    (τ : EmittedTraceSchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : EmittedTraceRolloutConsistent τ π ρ0) :
    NumericTraceConsistent (τ.toPerStepNumericRecord.toNumericTraceRecord) π ρ0 :=
  toNumericTraceRecord_consistent _ _ _
    (emittedRolloutConsistent_toAggregateConsistent τ π ρ0 h)

theorem emittedRolloutConsistent_policyUtility_eq {n : ℕ} {T : ℝ}
    (τ : EmittedTraceSchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 < T) (λ : ℝ) (h : EmittedTraceRolloutConsistent τ π ρ0) :
    traceRecordPolicyUtility (τ.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      = policyUtility π n ρ0 T hT λ :=
  perStepRecordPolicyUtility_eq_policyUtility _ _ _ hT λ
    (emittedRolloutConsistent_toAggregateConsistent τ π ρ0 h)

theorem ofRollout_rolloutConsistent (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    EmittedTraceRolloutConsistent (EmittedTraceSchema.ofRollout π n ρ0 T) π ρ0 := by
  intro k hk
  constructor <;> rfl

theorem ofRollout_wellFormed (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    EmittedTraceWellFormed (EmittedTraceSchema.ofRollout π n ρ0 T) hT := by
  intro k hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [EmittedTraceSchema.ofRollout] using
      (epistemicMI_nonneg (π k) (traceStateAt π ρ0 k))
  · simpa [EmittedTraceSchema.ofRollout] using
      (epistemicMI_le_log_two (π k) (traceStateAt π ρ0 k))
  · simpa [EmittedTraceSchema.ofRollout] using
      (epistemicLandauerCost_nonneg (π k) (traceStateAt π ρ0 k) T hT)
  · simpa [EmittedTraceSchema.ofRollout] using
      (epistemicLandauerCost_le_landauerBitEnergy (π k) (traceStateAt π ρ0 k) T hT)
  · norm_num [EmittedTraceSchema.ofRollout]
  · norm_num [EmittedTraceSchema.ofRollout]

theorem ofRollout_numericTraceConsistent (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    NumericTraceConsistent
      ((EmittedTraceSchema.ofRollout π n ρ0 T).toPerStepNumericRecord.toNumericTraceRecord) π ρ0 :=
  emittedRolloutConsistent_toNumericTraceConsistent _ _ _
    (ofRollout_rolloutConsistent π n ρ0 T)

theorem ofRollout_policyUtility_eq (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (λ : ℝ) :
    traceRecordPolicyUtility
        ((EmittedTraceSchema.ofRollout π n ρ0 T).toPerStepNumericRecord.toNumericTraceRecord) hT λ
      = policyUtility π n ρ0 T hT λ :=
  emittedRolloutConsistent_policyUtility_eq _ _ _ hT λ
    (ofRollout_rolloutConsistent π n ρ0 T)

end UMST.DoubleSlit

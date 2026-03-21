import EpistemicRuntimeSchemaContract

/-!
# EpistemicTelemetryBridge — runtime telemetry naming bridge

Runtime systems commonly emit per-step telemetry under names like `trajMI` and
`effortCost`. This module bridges that naming layer to existing formal contracts
(`EmittedTraceSchema`, `PerStepNumericRecord`, `NumericTraceRecord`) under explicit
consistency assumptions.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Aggregate telemetry payload with runtime-oriented field names. -/
structure RuntimeTelemetryAggregate (n : ℕ) (T : ℝ) where
  trajMI : ℝ
  effortCost : ℝ

/-- Per-step telemetry entry with runtime-oriented field names. -/
structure RuntimeTelemetryStep where
  trajMI : ℝ
  effortCost : ℝ

/-- Per-step telemetry schema over a finite horizon `n`. -/
structure RuntimeTelemetrySchema (n : ℕ) (T : ℝ) where
  step : ℕ → RuntimeTelemetryStep

/-- Aggregate telemetry consistency with abstract cumulative quantities. -/
def RuntimeTelemetryAggregateConsistent {n : ℕ} {T : ℝ} (τ : RuntimeTelemetryAggregate n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : Prop :=
  τ.trajMI = cumulativeEpistemicMI π n ρ0 ∧
    τ.effortCost = cumulativeEpistemicLandauerCost π n ρ0 T

/-- Per-step telemetry consistency with abstract rollout quantities. -/
def RuntimeTelemetrySchemaConsistent {n : ℕ} {T : ℝ} (τ : RuntimeTelemetrySchema n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : Prop :=
  ∀ k, k < n →
    (τ.step k).trajMI = EpistemicMI (π k) (traceStateAt π ρ0 k) ∧
      (τ.step k).effortCost = epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T

/-- Projection from aggregate telemetry to numeric aggregate record. -/
def RuntimeTelemetryAggregate.toNumericTraceRecord {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetryAggregate n T) : NumericTraceRecord n T :=
  ⟨τ.trajMI, τ.effortCost⟩

/-- Projection from per-step telemetry to per-step numeric record. -/
def RuntimeTelemetrySchema.toPerStepNumericRecord {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) : PerStepNumericRecord n T where
  stepMI k := (τ.step k).trajMI
  stepCost k := (τ.step k).effortCost

/-- Projection from per-step telemetry to emitted schema (adds metadata defaults). -/
def RuntimeTelemetrySchema.toEmittedTraceSchema {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) : EmittedTraceSchema n T where
  step k := {
    stepMI := (τ.step k).trajMI
    stepCost := (τ.step k).effortCost
    thermodynamicAdmissible := true
    confidence := 1
  }

/-- Optional numeric well-formedness constraints for telemetry over the first `n` steps. -/
def RuntimeTelemetrySchemaWellFormed {n : ℕ} {T : ℝ} (τ : RuntimeTelemetrySchema n T)
    (hT : 0 ≤ T) : Prop :=
  ∀ k, k < n →
    0 ≤ (τ.step k).trajMI ∧
      (τ.step k).trajMI ≤ Real.log 2 ∧
      0 ≤ (τ.step k).effortCost ∧
      (τ.step k).effortCost ≤ landauerBitEnergy T

theorem telemetrySchemaConsistent_toPerStepConsistent {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : RuntimeTelemetrySchemaConsistent τ π ρ0) :
    PerStepNumericConsistent τ.toPerStepNumericRecord π ρ0 := by
  constructor
  · intro k hk
    simpa [RuntimeTelemetrySchema.toPerStepNumericRecord] using (h k hk).1
  · intro k hk
    simpa [RuntimeTelemetrySchema.toPerStepNumericRecord] using (h k hk).2

theorem telemetrySchemaConsistent_toAggregateConsistent {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : RuntimeTelemetrySchemaConsistent τ π ρ0) :
    PerStepAggregateConsistent τ.toPerStepNumericRecord π ρ0 :=
  perStepConsistent_implies_aggregateConsistent _ _ _
    (telemetrySchemaConsistent_toPerStepConsistent τ π ρ0 h)

theorem telemetrySchemaConsistent_toNumericTraceConsistent {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : RuntimeTelemetrySchemaConsistent τ π ρ0) :
    NumericTraceConsistent (τ.toPerStepNumericRecord.toNumericTraceRecord) π ρ0 :=
  toNumericTraceRecord_consistent _ _ _
    (telemetrySchemaConsistent_toAggregateConsistent τ π ρ0 h)

theorem telemetrySchemaConsistent_toEmittedRolloutConsistent {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : RuntimeTelemetrySchemaConsistent τ π ρ0) :
    EmittedTraceRolloutConsistent τ.toEmittedTraceSchema π ρ0 := by
  intro k hk
  simpa [RuntimeTelemetrySchema.toEmittedTraceSchema] using (h k hk)

theorem telemetryAggregateConsistent_toNumericTraceConsistent {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetryAggregate n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : RuntimeTelemetryAggregateConsistent τ π ρ0) :
    NumericTraceConsistent τ.toNumericTraceRecord π ρ0 := by
  exact h

theorem telemetrySchemaConsistent_policyUtility_eq {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 < T) (λ : ℝ) (h : RuntimeTelemetrySchemaConsistent τ π ρ0) :
    traceRecordPolicyUtility (τ.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      = policyUtility π n ρ0 T hT λ :=
  perStepRecordPolicyUtility_eq_policyUtility _ _ _ hT λ
    (telemetrySchemaConsistent_toAggregateConsistent τ π ρ0 h)

theorem telemetryAggregateConsistent_policyUtility_eq {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetryAggregate n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 < T) (λ : ℝ) (h : RuntimeTelemetryAggregateConsistent τ π ρ0) :
    traceRecordPolicyUtility τ.toNumericTraceRecord hT λ = policyUtility π n ρ0 T hT λ :=
  traceRecordPolicyUtility_eq_policyUtility π ρ0 hT λ τ.toNumericTraceRecord h

/-- Canonical per-step telemetry payload extracted from abstract rollout semantics. -/
noncomputable def RuntimeTelemetrySchema.ofRollout (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : RuntimeTelemetrySchema n T where
  step k := {
    trajMI := EpistemicMI (π k) (traceStateAt π ρ0 k)
    effortCost := epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T
  }

/-- Canonical aggregate telemetry payload extracted from abstract rollout semantics. -/
noncomputable def RuntimeTelemetryAggregate.ofRollout (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : RuntimeTelemetryAggregate n T where
  trajMI := cumulativeEpistemicMI π n ρ0
  effortCost := cumulativeEpistemicLandauerCost π n ρ0 T

theorem ofRollout_schemaConsistent (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    RuntimeTelemetrySchemaConsistent (RuntimeTelemetrySchema.ofRollout π n ρ0 T) π ρ0 := by
  intro k hk
  constructor <;> rfl

theorem ofRollout_aggregateConsistent (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    RuntimeTelemetryAggregateConsistent (RuntimeTelemetryAggregate.ofRollout π n ρ0 T) π ρ0 := by
  constructor <;> rfl

theorem telemetrySchemaConsistent_wellFormed {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 ≤ T) (h : RuntimeTelemetrySchemaConsistent τ π ρ0) :
    RuntimeTelemetrySchemaWellFormed τ hT := by
  intro k hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(h k hk).1]
    exact epistemicMI_nonneg (π k) (traceStateAt π ρ0 k)
  · rw [(h k hk).1]
    exact epistemicMI_le_log_two (π k) (traceStateAt π ρ0 k)
  · rw [(h k hk).2]
    exact epistemicLandauerCost_nonneg (π k) (traceStateAt π ρ0 k) T hT
  · rw [(h k hk).2]
    exact epistemicLandauerCost_le_landauerBitEnergy (π k) (traceStateAt π ρ0 k) T hT

theorem ofRollout_schemaWellFormed (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    RuntimeTelemetrySchemaWellFormed (RuntimeTelemetrySchema.ofRollout π n ρ0 T) hT :=
  telemetrySchemaConsistent_wellFormed _ _ _ hT (ofRollout_schemaConsistent π n ρ0 T)

end UMST.DoubleSlit

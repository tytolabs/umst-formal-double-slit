import EpistemicTelemetryBridge

/-!
# EpistemicTelemetryApproximation — explicit numerics approximation interface

This module introduces explicit approximation assumptions for runtime numerics
(e.g., ODE/PPO surrogate outputs) and shows how the exact formal contracts are
recovered in the zero-error limit.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Per-step epsilon-approximate consistency between emitted telemetry and abstract rollout
quantities. The constants `εMI` and `εCost` are explicit assumptions. -/
def RuntimeTelemetrySchemaApproxConsistent {n : ℕ} {T : ℝ}
    (εMI εCost : ℝ) (τ : RuntimeTelemetrySchema n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : Prop :=
  0 ≤ εMI ∧
    0 ≤ εCost ∧
      ∀ k, k < n →
        |(τ.step k).trajMI - EpistemicMI (π k) (traceStateAt π ρ0 k)| ≤ εMI ∧
          |(τ.step k).effortCost - epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T| ≤ εCost

/-- Aggregate epsilon-approximate consistency for a numeric aggregate record. -/
def NumericTraceApproxConsistent {n : ℕ} {T : ℝ}
    (εMI εCost : ℝ) (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : Prop :=
  0 ≤ εMI ∧
    0 ≤ εCost ∧
      |τ.aggregateMI - cumulativeEpistemicMI π n ρ0| ≤ εMI ∧
      |τ.aggregateCost - cumulativeEpistemicLandauerCost π n ρ0 T| ≤ εCost

theorem telemetryApprox_zero_implies_exact {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : RuntimeTelemetrySchemaApproxConsistent 0 0 τ π ρ0) :
    RuntimeTelemetrySchemaConsistent τ π ρ0 := by
  intro k hk
  rcases h with ⟨_, _, hstep⟩
  specialize hstep k hk
  constructor
  · have hmi0 : |(τ.step k).trajMI - EpistemicMI (π k) (traceStateAt π ρ0 k)| = 0 :=
      le_antisymm hstep.1 (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hmi0)
  · have hcost0 : |(τ.step k).effortCost - epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T| = 0 :=
      le_antisymm hstep.2 (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hcost0)

theorem numericApprox_zero_implies_exact {n : ℕ} {T : ℝ}
    (τ : NumericTraceRecord n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (h : NumericTraceApproxConsistent 0 0 τ π ρ0) :
    NumericTraceConsistent τ π ρ0 := by
  rcases h with ⟨_, _, hmi, hcost⟩
  constructor
  · have hmi0 : |τ.aggregateMI - cumulativeEpistemicMI π n ρ0| = 0 :=
      le_antisymm hmi (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hmi0)
  · have hcost0 : |τ.aggregateCost - cumulativeEpistemicLandauerCost π n ρ0 T| = 0 :=
      le_antisymm hcost (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hcost0)

theorem telemetryApprox_zero_policyUtility_eq {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 < T) (λ : ℝ) (h : RuntimeTelemetrySchemaApproxConsistent 0 0 τ π ρ0) :
    traceRecordPolicyUtility (τ.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      = policyUtility π n ρ0 T hT λ :=
  telemetrySchemaConsistent_policyUtility_eq τ π ρ0 hT λ
    (telemetryApprox_zero_implies_exact τ π ρ0 h)

theorem telemetryApprox_ofRollout_zero (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    RuntimeTelemetrySchemaApproxConsistent 0 0 (RuntimeTelemetrySchema.ofRollout π n ρ0 T) π ρ0 := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  intro k hk
  constructor <;> simp [RuntimeTelemetrySchema.ofRollout]

end UMST.DoubleSlit

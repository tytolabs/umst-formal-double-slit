/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import EpistemicTelemetryQuantitativeUtility

/-!
# EpistemicTraceDerivedEpsilonCertificate — trace-derived epsilon certificates

This module derives explicit epsilon budgets directly from a runtime telemetry
trace by taking aggregate residuals against abstract rollout quantities.

These derived residuals immediately satisfy `NumericTraceApproxConsistent`, and
therefore yield utility deviation bounds via `numericApprox_utility_diff_le`.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Trace-derived MI residual (aggregate absolute error). -/
noncomputable def traceResidualMI {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : ℝ :=
  |τ.aggregateMI - cumulativeEpistemicMI π n ρ0|

/-- Trace-derived cost residual (aggregate absolute error). -/
noncomputable def traceResidualCost {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : ℝ :=
  |τ.aggregateCost - cumulativeEpistemicLandauerCost π n ρ0 T|

theorem traceResidualMI_nonneg {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) :
    0 ≤ traceResidualMI τ π ρ0 :=
  abs_nonneg _

theorem traceResidualCost_nonneg {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) :
    0 ≤ traceResidualCost τ π ρ0 :=
  abs_nonneg _

theorem traceResidual_numericApproxConsistent {n : ℕ} {T : ℝ} (τ : NumericTraceRecord n T)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) :
    NumericTraceApproxConsistent (traceResidualMI τ π ρ0) (traceResidualCost τ π ρ0) τ π ρ0 := by
  refine ⟨traceResidualMI_nonneg τ π ρ0, traceResidualCost_nonneg τ π ρ0, ?_, ?_⟩
  · unfold traceResidualMI
    rfl
  · unfold traceResidualCost
    rfl

/-- Trace-derived epsilon certificate at fixed horizon/policy/initial state. -/
structure TraceEpsilonCertificate (n : ℕ) (T : ℝ) (π : ProbePolicy)
    (ρ0 : DensityMatrix hnQubit) where
  telemetry : RuntimeTelemetrySchema n T

/-- Constructor helper for trace-derived certificates. -/
def TraceEpsilonCertificate.mk {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) :
    TraceEpsilonCertificate n T π ρ0 where
  telemetry := τ

theorem traceEpsilonCertificate_utility_diff_le {n : ℕ} {T : ℝ}
    (c : TraceEpsilonCertificate n T π ρ0) (hT : 0 < T) (λ : ℝ) :
    |traceRecordPolicyUtility (c.telemetry.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      - policyUtility π n ρ0 T hT λ|
      ≤ utilityApproxBound
          (traceResidualMI (c.telemetry.toPerStepNumericRecord.toNumericTraceRecord) π ρ0)
          (traceResidualCost (c.telemetry.toPerStepNumericRecord.toNumericTraceRecord) π ρ0)
          T hT λ :=
  numericApprox_utility_diff_le _ _ _ hT λ _ _
    (traceResidual_numericApproxConsistent
      (c.telemetry.toPerStepNumericRecord.toNumericTraceRecord) π ρ0)

theorem traceEpsilonCertificate_bound_nonneg {n : ℕ} {T : ℝ}
    (c : TraceEpsilonCertificate n T π ρ0) (hT : 0 < T) (λ : ℝ) :
    0 ≤ utilityApproxBound
        (traceResidualMI (c.telemetry.toPerStepNumericRecord.toNumericTraceRecord) π ρ0)
        (traceResidualCost (c.telemetry.toPerStepNumericRecord.toNumericTraceRecord) π ρ0)
        T hT λ :=
  utilityApproxBound_nonneg _ _ _ hT λ
    (traceResidualMI_nonneg (c.telemetry.toPerStepNumericRecord.toNumericTraceRecord) π ρ0)
    (traceResidualCost_nonneg (c.telemetry.toPerStepNumericRecord.toNumericTraceRecord) π ρ0)

end UMST.DoubleSlit

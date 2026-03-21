import EpistemicTelemetrySolverCalibration

/-!
# EpistemicTraceDrivenCalibrationWitness — trace-driven calibration witness layer

This module packages runtime telemetry traces together with explicit calibration
assumptions, then exposes direct transfer theorems to quantitative utility
bounds.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Lightweight witness form avoiding fixed policy/state in the structure. -/
structure TraceCalibrationWitnessAt (n : ℕ) (T : ℝ)
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (cal : SolverCalibration) where
  telemetry : RuntimeTelemetrySchema n T
  hSchema : SolverCalibrationSchemaAssumption cal telemetry π ρ0
  hAgg : SolverCalibrationAggregateAssumption cal telemetry π ρ0

/-- Any witness-at immediately yields the calibrated utility deviation bound. -/
theorem traceCalibrationWitnessAt_utility_diff_le {n : ℕ} {T : ℝ}
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (cal : SolverCalibration)
    (w : TraceCalibrationWitnessAt n T π ρ0 cal) (hT : 0 < T) (λ : ℝ) :
    |traceRecordPolicyUtility (w.telemetry.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      - policyUtility π n ρ0 T hT λ|
      ≤ utilityApproxBound (cal.epsMIAgg n) (cal.epsCostAgg n) T hT λ :=
  solverCalibration_utility_diff_le cal w.telemetry π ρ0 hT λ w.hAgg

/-- The witness-at bound is itself nonnegative by construction of calibration epsilons. -/
theorem traceCalibrationWitnessAt_bound_nonneg {n : ℕ} {T : ℝ}
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (cal : SolverCalibration)
    (w : TraceCalibrationWitnessAt n T π ρ0 cal) (hT : 0 < T) (λ : ℝ) :
    0 ≤ utilityApproxBound (cal.epsMIAgg n) (cal.epsCostAgg n) T hT λ :=
  solverCalibration_utilityBound_nonneg cal hT λ

end UMST.DoubleSlit

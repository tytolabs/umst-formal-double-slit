import EpistemicTraceDrivenCalibrationWitness

/-!
# PrototypeSolverCalibration — concrete calibration instantiation

This module instantiates `SolverCalibration` with concrete prototype-style
constants and exposes ready-to-use utility-bound corollaries.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Concrete prototype calibration:
step size `1/100`, order `2`, and unit MI/cost error coefficients. -/
def prototypeCalibration : SolverCalibration where
  stepSize := (1 : ℝ) / 100
  order := 2
  cMI := 1
  cCost := 1
  hStepSize := by norm_num
  hCMI := by norm_num
  hCCost := by norm_num

theorem prototypeCalibration_epsMIStep :
    prototypeCalibration.epsMIStep = (1 : ℝ) / 10000 := by
  unfold SolverCalibration.epsMIStep prototypeCalibration
  norm_num

theorem prototypeCalibration_epsCostStep :
    prototypeCalibration.epsCostStep = (1 : ℝ) / 10000 := by
  unfold SolverCalibration.epsCostStep prototypeCalibration
  norm_num

theorem prototypeCalibration_epsMIAgg (n : ℕ) :
    prototypeCalibration.epsMIAgg n = (n : ℝ) * ((1 : ℝ) / 10000) := by
  unfold SolverCalibration.epsMIAgg
  rw [prototypeCalibration_epsMIStep]
  ring

theorem prototypeCalibration_epsCostAgg (n : ℕ) :
    prototypeCalibration.epsCostAgg n = (n : ℝ) * ((1 : ℝ) / 10000) := by
  unfold SolverCalibration.epsCostAgg
  rw [prototypeCalibration_epsCostStep]
  ring

theorem prototypeCalibration_utility_diff_le {n : ℕ} {T : ℝ}
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (hT : 0 < T) (λ : ℝ)
    (h : SolverCalibrationAggregateAssumption prototypeCalibration τ π ρ0) :
    |traceRecordPolicyUtility (τ.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      - policyUtility π n ρ0 T hT λ|
      ≤ utilityApproxBound
          (prototypeCalibration.epsMIAgg n) (prototypeCalibration.epsCostAgg n) T hT λ :=
  solverCalibration_utility_diff_le prototypeCalibration τ π ρ0 hT λ h

theorem prototypeCalibration_utilityBound_nonneg {n : ℕ} {T : ℝ}
    (hT : 0 < T) (λ : ℝ) :
    0 ≤ utilityApproxBound
        (prototypeCalibration.epsMIAgg n) (prototypeCalibration.epsCostAgg n) T hT λ :=
  solverCalibration_utilityBound_nonneg prototypeCalibration hT λ

theorem prototypeWitness_utility_diff_le {n : ℕ} {T : ℝ}
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (w : TraceCalibrationWitnessAt n T π ρ0 prototypeCalibration)
    (hT : 0 < T) (λ : ℝ) :
    |traceRecordPolicyUtility (w.telemetry.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      - policyUtility π n ρ0 T hT λ|
      ≤ utilityApproxBound
          (prototypeCalibration.epsMIAgg n) (prototypeCalibration.epsCostAgg n) T hT λ :=
  traceCalibrationWitnessAt_utility_diff_le π ρ0 prototypeCalibration w hT λ

theorem prototypeWitness_bound_nonneg {n : ℕ} {T : ℝ}
    (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit)
    (w : TraceCalibrationWitnessAt n T π ρ0 prototypeCalibration)
    (hT : 0 < T) (λ : ℝ) :
    0 ≤ utilityApproxBound
        (prototypeCalibration.epsMIAgg n) (prototypeCalibration.epsCostAgg n) T hT λ :=
  traceCalibrationWitnessAt_bound_nonneg π ρ0 prototypeCalibration w hT λ

end UMST.DoubleSlit

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import EpistemicTelemetryQuantitativeUtility

/-!
# EpistemicTelemetrySolverCalibration — explicit solver-to-epsilon calibration

This module introduces an explicit calibration layer that maps numerical method
parameters (step size, order, error coefficients) to epsilon budgets used by
the telemetry approximation and quantitative-utility theorems.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Calibration parameters for numerical telemetry surrogates. -/
structure SolverCalibration where
  stepSize : ℝ
  order : ℕ
  cMI : ℝ
  cCost : ℝ
  hStepSize : 0 ≤ stepSize
  hCMI : 0 ≤ cMI
  hCCost : 0 ≤ cCost

/-- Per-step MI epsilon induced by calibration. -/
def SolverCalibration.epsMIStep (cal : SolverCalibration) : ℝ :=
  cal.cMI * cal.stepSize ^ cal.order

/-- Per-step cost epsilon induced by calibration. -/
def SolverCalibration.epsCostStep (cal : SolverCalibration) : ℝ :=
  cal.cCost * cal.stepSize ^ cal.order

/-- Aggregate MI epsilon budget over horizon `n` (coarse linear scaling). -/
def SolverCalibration.epsMIAgg (cal : SolverCalibration) (n : ℕ) : ℝ :=
  n * cal.epsMIStep

/-- Aggregate cost epsilon budget over horizon `n` (coarse linear scaling). -/
def SolverCalibration.epsCostAgg (cal : SolverCalibration) (n : ℕ) : ℝ :=
  n * cal.epsCostStep

theorem SolverCalibration.epsMIStep_nonneg (cal : SolverCalibration) :
    0 ≤ cal.epsMIStep := by
  unfold SolverCalibration.epsMIStep
  exact mul_nonneg cal.hCMI (pow_nonneg cal.hStepSize _)

theorem SolverCalibration.epsCostStep_nonneg (cal : SolverCalibration) :
    0 ≤ cal.epsCostStep := by
  unfold SolverCalibration.epsCostStep
  exact mul_nonneg cal.hCCost (pow_nonneg cal.hStepSize _)

theorem SolverCalibration.epsMIAgg_nonneg (cal : SolverCalibration) (n : ℕ) :
    0 ≤ cal.epsMIAgg n := by
  unfold SolverCalibration.epsMIAgg
  exact mul_nonneg (Nat.cast_nonneg n) cal.epsMIStep_nonneg

theorem SolverCalibration.epsCostAgg_nonneg (cal : SolverCalibration) (n : ℕ) :
    0 ≤ cal.epsCostAgg n := by
  unfold SolverCalibration.epsCostAgg
  exact mul_nonneg (Nat.cast_nonneg n) cal.epsCostStep_nonneg

/-- Optional assumption layer: runtime per-step telemetry respects step-level calibration epsilons. -/
def SolverCalibrationSchemaAssumption {n : ℕ} {T : ℝ} (cal : SolverCalibration)
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : Prop :=
  RuntimeTelemetrySchemaApproxConsistent cal.epsMIStep cal.epsCostStep τ π ρ0

/-- Aggregate assumption layer used by quantitative utility bounds. -/
def SolverCalibrationAggregateAssumption {n : ℕ} {T : ℝ} (cal : SolverCalibration)
    (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) : Prop :=
  NumericTraceApproxConsistent (cal.epsMIAgg n) (cal.epsCostAgg n)
    (τ.toPerStepNumericRecord.toNumericTraceRecord) π ρ0

theorem solverCalibration_utility_diff_le {n : ℕ} {T : ℝ}
    (cal : SolverCalibration) (τ : RuntimeTelemetrySchema n T) (π : ProbePolicy)
    (ρ0 : DensityMatrix hnQubit) (hT : 0 < T) (λ : ℝ)
    (h : SolverCalibrationAggregateAssumption cal τ π ρ0) :
    |traceRecordPolicyUtility (τ.toPerStepNumericRecord.toNumericTraceRecord) hT λ
      - policyUtility π n ρ0 T hT λ|
      ≤ utilityApproxBound (cal.epsMIAgg n) (cal.epsCostAgg n) T hT λ := by
  exact numericApprox_utility_diff_le _ _ _ hT λ _ _ h

theorem solverCalibration_utilityBound_nonneg {n : ℕ} {T : ℝ}
    (cal : SolverCalibration) (hT : 0 < T) (λ : ℝ) :
    0 ≤ utilityApproxBound (cal.epsMIAgg n) (cal.epsCostAgg n) T hT λ :=
  utilityApproxBound_nonneg _ _ _ hT λ (cal.epsMIAgg_nonneg n) (cal.epsCostAgg_nonneg n)

end UMST.DoubleSlit

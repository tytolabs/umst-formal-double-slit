import Lake
open Lake DSL

package «umst-formal-double-slit» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

/-!
  Self-contained quantum / measurement extension. Build:

  `cd Lean && lake build`
-/
lean_lib «UMST.DoubleSlit» where
  roots := #[`UMSTCore, `DensityState, `MeasurementChannel, `DoubleSlitCore, `QuantumClassicalBridge,
    `InfoEntropy, `LandauerBound, `EpistemicSensing, `EpistemicMI, `EpistemicDynamics,
    `EpistemicTrajectoryMI, `EpistemicPolicy, `EpistemicRuntimeContract, `EpistemicNumericsContract,
    `EpistemicPerStepNumerics, `EpistemicRuntimeSchemaContract, `EpistemicTelemetryBridge,
    `EpistemicTelemetryApproximation, `EpistemicTelemetryQuantitativeUtility,
    `EpistemicTraceDerivedEpsilonCertificate,
    `EpistemicTelemetrySolverCalibration, `EpistemicTraceDrivenCalibrationWitness,
    `PrototypeSolverCalibration, `GateCompat,
    `Complementarity, `DoubleSlit, `ProbeOptimization, `ExamplesQubit, `MeasurementCost,
    `EpistemicGalois,
    -- integrated from upstream framework (ℚ thermo gate + activation + Landauer T_LandauerLaw stack)
    `LandauerLaw, `LandauerExtension, `LandauerEinsteinBridge,
    `Gate, `Naturality, `Activation, `FiberedActivation, `MonoidalState]
  srcDir := "."

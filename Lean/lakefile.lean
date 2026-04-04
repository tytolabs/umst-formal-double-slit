/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Lake
open Lake DSL

package «umst-formal-double-slit» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

/-!
  Self-contained quantum / measurement extension. Build:

  `cd Lean && lake build`

  **Default `roots`** = quantum + epistemic formal layer plus the vendored thermodynamic
  stack.  **Excluded on purpose:** `Test*.lean`, `test_tensor_eigen.lean`, optional
  `LogSum` / `MatrixLog`, `FlashMoERuntimeScaffold.lean`, etc.  Those files are not in
  `roots` so they do not run in default CI; build them explicitly (e.g. `lake build +TestEntropy`)
  when needed.  They have been manually grep-checked for `sorry` / stray `axiom`.
-/
lean_lib «UMST.DoubleSlit» where
  roots := #[`UMSTCore, `DensityState, `TensorPartialTrace, `MeasurementChannel, `DoubleSlitCore, `QuantumClassicalBridge,
    `InfoEntropy, `KroneckerEigen, `GeneralDimension, `LandauerBound, `EpistemicSensing, `EpistemicMI, `EpistemicDynamics,
    `EpistemicTrajectoryMI, `EpistemicPolicy, `EpistemicRuntimeContract, `EpistemicNumericsContract,
    `EpistemicPerStepNumerics, `EpistemicRuntimeSchemaContract, `EpistemicTelemetryBridge,
    `EpistemicTelemetryApproximation, `EpistemicTelemetryQuantitativeUtility,
    `EpistemicTraceDerivedEpsilonCertificate,
    `EpistemicTelemetrySolverCalibration, `EpistemicTraceDrivenCalibrationWitness,
    `PrototypeSolverCalibration, `GateCompat, `QRBridge,
    `PMICEntropyInterior, `Complementarity, `PMICVisibility,
    `VonNeumannEntropy, `QuantumMutualInfo, `KleinInequality, `DataProcessingInequality,
    `DoubleSlit, `ProbeOptimization, `ExamplesQubit, `ErasureChannel, `MeasurementCost,
    `EpistemicGalois, `SchrodingerDynamics, `LindbladDynamics, `FormalFoundations, `SimLeanBridge,
    -- integrated from upstream framework (ℚ thermo gate + activation + Landauer T_LandauerLaw stack)
    `LandauerLaw, `LandauerExtension, `LandauerEinsteinBridge,
    `Gate, `Naturality, `Activation, `FiberedActivation, `MonoidalState,
    `GeneralResidualCoherence, `WhichPathMeasurementUpdate, `GeneralVisibility,
    `PhysicsConstrainedAI, `InformationCostIdentity]
    -- Optional / future: `MatrixLog, `LogSum (not in roots)
  srcDir := "."

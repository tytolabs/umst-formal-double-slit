-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-

Pinned catalog of Lean `roots` from `Lean/lakefile.lean` (`lean_lib «UMST.DoubleSlit»`).
Rebuild this list when roots change — see comment block below.
-/

import Lean.Data.Json
open System

/-! ### Catalog schema version (bump when JSON shape changes) -/
def catalogFormatVersion : String := "1"

/-! ### Logical library prefix for default roots (matches `lakefile.lean`). -/
def rootModulePrefix : String := "UMST.DoubleSlit"

/-
  Keep this array in sync with `roots := #[ … ]` in `Lean/lakefile.lean`.
-/
def pinnedRootNames : Array String := #[
  "UMSTCore", "DensityState", "TensorPartialTrace", "MeasurementChannel", "DoubleSlitCore", "QuantumClassicalBridge",
  "InfoEntropy", "KroneckerEigen", "GeneralDimension", "LandauerBound", "EpistemicSensing", "EpistemicMI", "EpistemicDynamics",
  "EpistemicTrajectoryMI", "EpistemicPolicy", "EpistemicRuntimeContract", "EpistemicNumericsContract",
  "EpistemicPerStepNumerics", "EpistemicRuntimeSchemaContract", "EpistemicTelemetryBridge",
  "EpistemicTelemetryApproximation", "EpistemicTelemetryQuantitativeUtility",
  "EpistemicTraceDerivedEpsilonCertificate",
  "EpistemicTelemetrySolverCalibration", "EpistemicTraceDrivenCalibrationWitness",
  "PrototypeSolverCalibration", "GateCompat", "QRBridge",
  "PMICEntropyInterior", "Complementarity", "PMICVisibility",
  "VonNeumannEntropy", "QuantumMutualInfo", "KleinInequality", "DataProcessingInequality",
  "DoubleSlit", "ProbeOptimization", "ExamplesQubit", "ErasureChannel", "MeasurementCost",
  "EpistemicGalois", "SchrodingerDynamics", "LindbladDynamics", "LindbladStreamD", "FormalFoundations", "SimLeanBridge",
  "LandauerLaw", "LandauerExtension", "LandauerEinsteinBridge",
  "Gate", "Naturality", "Activation", "FiberedActivation", "MonoidalState",
  "GeneralResidualCoherence", "WhichPathMeasurementUpdate", "GeneralVisibility",
  "PhysicsConstrainedAI", "InformationCostIdentity"
]

def entryJson (shortName : String) : Lean.Json :=
  let mod := s!"{rootModulePrefix}.{shortName}"
  Lean.Json.mkObj [
    ("id", mod),
    ("module", mod),
    ("kind", "root"),
    ("name", shortName)
  ]

def pinnedEntriesJson : Lean.Json :=
  Lean.Json.arr (pinnedRootNames.map entryJson)

def catalogDocument : Lean.Json :=
  Lean.Json.mkObj [
    ("version", catalogFormatVersion),
    ("entries", pinnedEntriesJson)
  ]

/--
  Resolve `<repo>/artifacts/catalog.json`:
  • cwd = repository root → `./artifacts/catalog.json`
  • cwd = `Lean/` → `../artifacts/catalog.json`
-/
def resolveCatalogPath : IO System.FilePath := do
  let cwd ← IO.currentDir
  let atRepo ← (cwd / "Lean" / "lakefile.lean").pathExists
  let atLeanPkg ← (cwd / "lakefile.lean").pathExists
  if atRepo then
    pure <| (cwd / "artifacts" / "catalog.json").normalize
  else if atLeanPkg then
    pure <| ((cwd / ".." / "artifacts" / "catalog.json")).normalize
  else
    -- Fallback when invoked from elsewhere
    pure <| (cwd / "artifacts" / "catalog.json").normalize

def main (_ : List String) : IO UInt32 := do
  let path ← resolveCatalogPath
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let text := Lean.Json.compress catalogDocument
  IO.FS.writeFile path text
  return 0

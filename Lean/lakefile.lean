-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

/-
-/

import Lake
open Lake DSL

package «umst-formal-double-slit» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

require «umst-formal» from git
  "https://github.com/tytolabs/umst-formal" @ "690fbe6" / "Lean"

/-!
  Self-contained quantum / measurement extension. Build:

  `cd Lean && lake build`

  **Default `roots`** = quantum + epistemic formal layer plus the vendored thermodynamic
  stack.  **Excluded on purpose:** `Test*.lean`, `test_tensor_eigen.lean`, optional
  `LogSum` / `MatrixLog`, `FlashMoERuntimeScaffold.lean`, etc.  Those files are not in
  `roots` so they do not run in default CI; build them explicitly (e.g. `lake build +TestEntropy`)
  when needed.  They have been manually grep-checked for `sorry` / stray `axiom`.

  **Lean root catalog (entries JSON):** From `Lean/`, run **`lake exe export_catalog`**
  to emit **`artifacts/catalog.json`** with `{ version, entries[{ id, module, kind, name }] }`.
  Details: **`tools/lean_export/README.md`**.

  **Python module scan (imports + digests):** **`make lean-catalog-export`** runs
  **`tools/lean_export/export_catalog.py`** — a different JSON shape for tooling that needs
  coarse import edges and per-file content hashes.
-/
-- LandauerLaw is supplied by the umst-formal dependency: the sole physical axiom
-- physicalSecondLaw is declared once, there, and imported here rather than vendored.
lean_lib «UMST.DoubleSlit» where
  roots := #[`DensityState, `TensorPartialTrace, `MeasurementChannel, `DoubleSlitCore, `QuantumClassicalBridge,
    `InfoEntropy, `KroneckerEigen, `GeneralDimension, `LandauerBound, `EpistemicSensing, `EpistemicMI, `EpistemicDynamics,
    `EpistemicTrajectoryMI, `EpistemicPolicy, `EpistemicRuntimeContract, `EpistemicNumericsContract,
    `EpistemicPerStepNumerics, `EpistemicRuntimeSchemaContract, `EpistemicTelemetryBridge,
    `EpistemicTelemetryApproximation, `EpistemicTelemetryQuantitativeUtility,
    `EpistemicTraceDerivedEpsilonCertificate,
    `EpistemicTelemetrySolverCalibration, `EpistemicTraceDrivenCalibrationWitness,
    `PrototypeSolverCalibration, `GateCompat,
    `PMICEntropyInterior, `Complementarity, `PMICVisibility,
    `VonNeumannEntropy, `QuantumMutualInfo, `KleinInequality, `DataProcessingInequality,
    `DoubleSlit, `ProbeOptimization, `ExamplesQubit, `ErasureChannel, `MeasurementCost,
    `EpistemicGalois, `SchrodingerDynamics, `LindbladDynamics, `LindbladStreamD, `FormalFoundations, `SimLeanBridge,
    -- integrated from upstream framework (ℚ thermo gate + activation + Landauer T_LandauerLaw stack)
    `LandauerExtension, `LandauerEinsteinBridge,
    `GeneralResidualCoherence, `WhichPathMeasurementUpdate, `GeneralVisibility,
    `PhysicsConstrainedAI, `InformationCostIdentity]
    -- Optional / future: `MatrixLog, `LogSum (not in roots)
  srcDir := "."

/-!
  Knowing-fiber chemistry (`CHEM-FORMAL-Q-LEAN-CHEM`): Q-lattice electronic quantum numbers,
  SCALE ladder, EDGE-SURFACE sign convention.  `globs` auto-picks up future `Chem*.lean`;
  `ElementElectronic` stays an explicit root until renamed under `Chem*`.

  Build: `lake build ChemGeometry`
-/
lean_lib ChemGeometry where
  roots := #[`ElementElectronic, `ChemGeometry]
  -- `Chem.+` glob activates when `Chem/` subtree exists (future geometry modules).
  srcDir := "."

/-!
  Knowing-fiber chemistry constants (`CHEM-FORMAL-Q-LEAN-EXACT-SI-RATIONAL`): SI-2019 exact
  integer mantissa identity for **k**, **N_A**, DerivedSI **R** = N_A ∘ k.

  Build: `lake build ChemConstants.ExactSiInteger`

  Named Madelung occupancy exceptions (`CHEM-FORMAL-Q-LEAN-NAMED-OCCUPANCY-EXCEPTIONS`):
  finite `NamedException` set La / Ce / Gd / Pt / Au — cites qlattice + madelung_witness, not
  second axiom.

  Build: `lake build ChemConstants.NamedOccupancyExceptions`

  Actinide qlattice occupancy exceptions (`CHEM-FORMAL-Q-LEAN-ACTINIDE-OCCUPANCY-EXCEPTIONS`):
  finite `ActinideException` set Ac / Th / Pa / U / Np / Cm / Lr — cites qlattice +
  madelung_witness, not second axiom; Lr named override agrees Madelung honest.

  Build: `lake build ChemConstants.ActinideOccupancyExceptions`

  D-block qlattice occupancy exceptions (`CHEM-FORMAL-Q-LEAN-DBLOCK-OCCUPANCY-EXCEPTIONS`):
  finite `DBlockException` set Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag — cites qlattice +
  madelung_witness, not second axiom; DISTINCT from NamedException and ActinideException.

  Build: `lake build ChemConstants.DBlockOccupancyExceptions`

  Occupancy exception Z-set disjointness (`CHEM-FORMAL-Q-LEAN-OCCUPANCY-EXCEPTION-SETS-DISJOINT`):
  Lean composition of Named / Actinide / DBlock occupancy exception modules — pairwise disjoint
  Z-sets; Z = 94 (Pu) in none; Z = 103 (Lr) in actinide not named; Unwired, not GREEN DFT.

  Build: `lake build ChemConstants.OccupancyExceptionSetsDisjoint`
-/
lean_lib ChemConstants where
  roots := #[`ChemConstants.ExactSiInteger, `ChemConstants.NamedOccupancyExceptions,
    `ChemConstants.ActinideOccupancyExceptions, `ChemConstants.DBlockOccupancyExceptions,
    `ChemConstants.OccupancyExceptionSetsDisjoint]
  srcDir := "."

/-- Emit `artifacts/catalog.json` (repo root): pinned Lake roots + schema; see `../tools/lean_export/README.md`. -/
lean_exe export_catalog where
  root := `ExportCatalog
  srcDir := "../tools/lean_export"

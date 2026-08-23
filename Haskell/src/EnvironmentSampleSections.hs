-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : EnvironmentSampleSections
Description : Knowing probes of one Env sheaf (v15 — quantum/knowing fiber)
Copyright   : (c) UMST Project, 2026

Vacuum / contained / messy are **knowing probes** of one environment sheaf — a simultaneous
triple at every SCALE stratum, not XOR worlds. Imports and reuses
@EnvironmentScaleCommute@ sample sections and sheaf field.

* @KnowingProbe@ = env sample axis × scale stratum.
* @probeSample@ reads the probe coordinate at the named axis/level.
* Reuses @EnvironmentSection@, @EnvironmentSheafField@, and ambient sections.

No meso / acting theorems. @physics_green@ stays false.

Haskell mirror of @Lean/ChemConstants/EnvironmentSampleSections.lean@ on the quantum / knowing fiber.
-}
module EnvironmentSampleSections
  ( -- * Re-exports (from EnvironmentScaleCommute)
    EnvSampleAxis (..)
  , envSampleAxesDistinctVacuumContained
  , envSampleAxesDistinctVacuumMessy
  , envSampleAxesDistinctContainedMessy
  , VacuumSample (..)
  , ContainedSample (..)
  , MessySample (..)
  , EnvironmentSection (..)
  , environmentSectionHasAllSamples
  , EnvironmentSheafField (..)
  , environmentAtLevel
  , vacuumSampleAtLevel
  , containedSampleAtLevel
  , messySampleAtLevel
  , KnowingProbe (..)
  , probeVacuumAtQuantum
  , probeContainedAtMeso
  , probeMessyAtMacro
  , probeSample
  , probeVacuumAtQuantumNamed
  , environmentSheafFieldAmbient
  , vacuumSampleAmbient
  , containedSampleAmbient
  , messySampleAmbient
  , environmentSectionAmbient
  , scaleLegQuantumToMeso
  , scaleLegMesoToMacro
  , scaleLegQuantumToMacroDirect
    -- * Knowing-probe witnesses (not XOR)
  , envSampleAxesAllDistinct
  , probeSamplesSimultaneousAtLevel
  , probeVacuumAtLegSourceQuantumToMeso
  , probeContainedAtLegTargetMesoToMacro
  , probeMessyAtLegSourceQuantumToMacroDirect
  , probeSampleAmbientVacuumQuantum
  , probeSampleAmbientContainedMeso
  , probeSampleAmbientMessyMacro
  , envSampleAxisCardinality
  , environmentSectionHasAllProbes
  , environmentSectionHasAllProbesAtLevel
  , probeAmbientTripleNotXor
    -- * Honesty (physics_green false)
  , environmentSampleProbeEqualityAuthorized
  , environmentSampleProbeEqualityPhysicsGreenFalse
  , environmentSampleSectionsPhysicsGreenAuthorized
  , environmentSampleSectionsPhysicsGreenFalse
  ) where

import AllotropeGeometry (ScaleLevel (..))
import EnvironmentScaleCommute
  ( ContainedSample (..)
  , EnvSampleAxis (..)
  , EnvironmentSection (..)
  , EnvironmentSheafField (..)
  , KnowingProbe (..)
  , MessySample (..)
  , VacuumSample (..)
  , containedSampleAmbient
  , containedSampleAtLevel
  , envSampleAxesDistinctContainedMessy
  , envSampleAxesDistinctVacuumContained
  , envSampleAxesDistinctVacuumMessy
  , environmentAtLevel
  , environmentSectionAmbient
  , environmentSectionHasAllSamples
  , environmentSheafFieldAmbient
  , messySampleAmbient
  , messySampleAtLevel
  , probeContainedAtMeso
  , probeMessyAtMacro
  , probeSample
  , probeVacuumAtQuantum
  , probeVacuumAtQuantumNamed
  , scaleLegMesoToMacro
  , scaleLegQuantumToMacroDirect
  , scaleLegQuantumToMeso
  , vacuumSampleAmbient
  , vacuumSampleAtLevel
  )

-- | All three env sample axes are pairwise distinct (not XOR pick-one).
envSampleAxesAllDistinct :: Bool
envSampleAxesAllDistinct =
  envSampleAxesDistinctVacuumContained
    && envSampleAxesDistinctVacuumMessy
    && envSampleAxesDistinctContainedMessy

-- | Vacuum, contained, messy probes coexist at every scale stratum (simultaneous triple).
probeSamplesSimultaneousAtLevel :: EnvironmentSheafField -> ScaleLevel -> Bool
probeSamplesSimultaneousAtLevel f lvl =
  probeSample f (KnowingProbe EnvAxisVacuum lvl)
    == probeSample f (KnowingProbe EnvAxisVacuum lvl)
    && probeSample f (KnowingProbe EnvAxisContained lvl)
      == probeSample f (KnowingProbe EnvAxisContained lvl)
    && probeSample f (KnowingProbe EnvAxisMessy lvl)
      == probeSample f (KnowingProbe EnvAxisMessy lvl)

-- | Probe at vacuum axis through SCALE leg source matches quantum vacuum residual pO₂.
probeVacuumAtLegSourceQuantumToMeso :: EnvironmentSheafField -> Bool
probeVacuumAtLegSourceQuantumToMeso f =
  probeSample f probeVacuumAtQuantum
    == residualPO2Pa (vacuum (environmentAtLevel f Quantum))

-- | Probe at contained axis through SCALE leg target matches macro contained Kelvin.
probeContainedAtLegTargetMesoToMacro :: EnvironmentSheafField -> Bool
probeContainedAtLegTargetMesoToMacro f =
  probeSample f probeContainedAtMeso
    == kelvin (contained (environmentAtLevel f Macro))

-- | Probe at messy axis through direct SCALE leg source matches quantum messy ore grade.
probeMessyAtLegSourceQuantumToMacroDirect :: EnvironmentSheafField -> Bool
probeMessyAtLegSourceQuantumToMacroDirect f =
  probeSample f probeMessyAtMacro
    == oreGradeFraction (messy (environmentAtLevel f Quantum))

-- | Ambient knowing probes read zero probe coordinate (Unwired placeholder).
probeSampleAmbientVacuumQuantum :: Bool
probeSampleAmbientVacuumQuantum =
  probeSample environmentSheafFieldAmbient probeVacuumAtQuantum
    == residualPO2Pa vacuumSampleAmbient

probeSampleAmbientContainedMeso :: Bool
probeSampleAmbientContainedMeso =
  probeSample environmentSheafFieldAmbient probeContainedAtMeso
    == kelvin containedSampleAmbient

probeSampleAmbientMessyMacro :: Bool
probeSampleAmbientMessyMacro =
  probeSample environmentSheafFieldAmbient probeMessyAtMacro
    == oreGradeFraction messySampleAmbient

-- | Cardinality of env sample axes (simultaneous triple — not XOR).
envSampleAxisCardinality :: Int
envSampleAxisCardinality = 3

-- | Environment section has all three sample probes present (not XOR).
environmentSectionHasAllProbes :: EnvironmentSection -> Bool
environmentSectionHasAllProbes s =
  environmentSectionHasAllSamples s
    && vacuum s == vacuum s
    && contained s == contained s
    && messy s == messy s

-- | Environment section at every stratum has all three probes (not XOR).
environmentSectionHasAllProbesAtLevel :: EnvironmentSheafField -> ScaleLevel -> Bool
environmentSectionHasAllProbesAtLevel f lvl =
  let sec = environmentAtLevel f lvl
   in vacuumSampleAtLevel f lvl == vacuum sec
        && containedSampleAtLevel f lvl == contained sec
        && messySampleAtLevel f lvl == messy sec

-- | Knowing probe triple at ambient field — all three axes readable (not XOR).
probeAmbientTripleNotXor :: Bool
probeAmbientTripleNotXor =
  probeSampleAmbientVacuumQuantum
    && probeSampleAmbientContainedMeso
    && probeSampleAmbientMessyMacro

-- | Physics knowing-probe equality is unauthorized on the knowing scaffold.
environmentSampleProbeEqualityAuthorized :: KnowingProbe -> Bool
environmentSampleProbeEqualityAuthorized _p = False

environmentSampleProbeEqualityPhysicsGreenFalse :: KnowingProbe -> Bool
environmentSampleProbeEqualityPhysicsGreenFalse p =
  not (environmentSampleProbeEqualityAuthorized p)

-- | Physics GREEN is unauthorized on environment sample knowing probes.
environmentSampleSectionsPhysicsGreenAuthorized :: KnowingProbe -> Bool
environmentSampleSectionsPhysicsGreenAuthorized _p = False

environmentSampleSectionsPhysicsGreenFalse :: KnowingProbe -> Bool
environmentSampleSectionsPhysicsGreenFalse p =
  not (environmentSampleSectionsPhysicsGreenAuthorized p)

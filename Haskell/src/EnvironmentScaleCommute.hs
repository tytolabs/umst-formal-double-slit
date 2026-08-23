-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : EnvironmentScaleCommute
Description : Environment SCALE sheaf commute on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Quantum / knowing fiber preview for environment SCALE sheaf:

* Vacuum / contained / messy as simultaneous sample sections (not XOR).
* Env sheaf sections commute Q ↔ meso ↔ macro as knowing probes.
* Reuses @AllotropeGeometry@ @ScaleLevel@ + @ScaleCommutingLeg@ (Unwired).

No meso / acting theorems. @physics_green@ stays false.

Haskell mirror of @Coq/EnvironmentScaleCommute.v@ on the quantum / knowing fiber.
-}
module EnvironmentScaleCommute
  ( EnvironmentScaleModality (..)
  , environmentScaleModalityCurrent
  , EnvSampleAxis (..)
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
  , environmentAtLegSource
  , environmentAtLegTarget
  , KnowingProbe (..)
  , probeVacuumAtQuantum
  , probeContainedAtMeso
  , probeMessyAtMacro
  , probeSample
  , probeVacuumAtQuantumNamed
  , ScaleCommuteDiagram (..)
  , scaleLegQuantumToMeso
  , scaleLegMesoToMacro
  , scaleLegQuantumToMacroDirect
  , scaleCommuteDiagramNamed
  , scaleCommuteDiagramNamedFields
  , scaleLegIndirectComposesLevels
  , scaleLegDirectEndpointsMatch
  , ScaleCommute (..)
  , scaleCommuteUnwired
  , environmentAtLegSourceQuantumToMeso
  , environmentAtLegTargetQuantumToMeso
  , environmentAtLegSourceMesoToMacro
  , environmentAtLegTargetMesoToMacro
  , environmentAtLegSourceQuantumToMacroDirect
  , environmentAtLegTargetQuantumToMacroDirect
  , environmentIndirectLegComposes
  , environmentDirectEndpointsMatch
  , vacuumSampleAtLegSourceQuantumToMeso
  , containedSampleAtLegTargetMesoToMacro
  , messySampleAtLegSourceQuantumToMacroDirect
  , EnvironmentScaleSheafDiagram (..)
  , environmentScaleSheafDiagramNamed
  , environmentScaleSheafDiagramNamedScale
  , EnvironmentScaleSheafBinding (..)
  , environmentScaleMadelungKey
  , environmentScaleBindingSameMadelungKey
  , EnvironmentScaleCommute (..)
  , vacuumSampleAmbient
  , containedSampleAmbient
  , messySampleAmbient
  , environmentSectionAmbient
  , environmentSheafFieldAmbient
  , environmentScaleCommuteUnwired
  , environmentScaleCommuteModalityUnwired
  , environmentScaleCommuteLatticeAnchor
  , environmentScaleSheafIndirectComposes
  , environmentScaleSheafDirectEndpoints
  , environmentScaleCommuteUnwiredBindingParent
  , environmentScaleCommuteAmbientVacuum
  , environmentScaleCommuteAmbientContained
  , environmentSectionAllSamples
  , environmentSectionsCoexistNotXor
  , environmentClassifyBulkOfNeg
  , environmentClassifySurfaceOfPos
  , environmentScaleSheafEqualityAuthorized
  , environmentScaleSheafEqualityPhysicsGreenFalse
  , environmentScaleCommutePhysicsGreenAuthorized
  , environmentScaleCommutePhysicsGreenFalse
  , environmentScaleLatticePhysicsGreenAuthorized
  , environmentScaleLatticePhysicsGreenFalse
  ) where

import AllotropeGeometry
  ( ChemGeometryModality (..)
  , EdgeSurfaceRegime (..)
  , ScaleCommutingLeg (..)
  , ScaleLevel (..)
  , chemGeometryModalityCurrent
  , classifyEdgeSurface
  , scaleLegSource
  , scaleLegTarget
  )
import ChemGeometry (QLatticeCell (..), madelungSum)

-- | Design modality for environment SCALE commute claims.
data EnvironmentScaleModality = EnvScaleUnwired | EnvScaleAssumed | EnvScaleProved | EnvScaleSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
environmentScaleModalityCurrent :: EnvironmentScaleModality
environmentScaleModalityCurrent = EnvScaleUnwired

-- | Knowing-probe axis for environment sample sections (not XOR).
data EnvSampleAxis = EnvAxisVacuum | EnvAxisContained | EnvAxisMessy
  deriving (Eq, Show)

envSampleAxesDistinctVacuumContained :: Bool
envSampleAxesDistinctVacuumContained = EnvAxisVacuum /= EnvAxisContained

envSampleAxesDistinctVacuumMessy :: Bool
envSampleAxesDistinctVacuumMessy = EnvAxisVacuum /= EnvAxisMessy

envSampleAxesDistinctContainedMessy :: Bool
envSampleAxesDistinctContainedMessy = EnvAxisContained /= EnvAxisMessy

-- | Vacuum-axis sample (residual pO₂ placeholder — not physics GREEN).
data VacuumSample = VacuumSample
  { residualPO2Pa :: !Double
  }
  deriving (Eq, Show)

-- | Contained-axis sample (Kelvin + Pascal placeholders).
data ContainedSample = ContainedSample
  { kelvin :: !Double
  , pascal :: !Double
  }
  deriving (Eq, Show)

-- | Messy-axis sample (ore grade + impurity placeholders).
data MessySample = MessySample
  { oreGradeFraction :: !Double
  , impurityFraction :: !Double
  }
  deriving (Eq, Show)

-- | All three sample sections coexist — not an exclusive env choice.
data EnvironmentSection = EnvironmentSection
  { vacuum :: !VacuumSample
  , contained :: !ContainedSample
  , messy :: !MessySample
  }
  deriving (Eq, Show)

environmentSectionHasAllSamples :: EnvironmentSection -> Bool
environmentSectionHasAllSamples s =
  vacuum s == vacuum s
    && contained s == contained s
    && messy s == messy s

-- | Environment sheaf field over the SCALE ladder.
data EnvironmentSheafField = EnvironmentSheafField
  { atQuantum :: !EnvironmentSection
  , atMeso :: !EnvironmentSection
  , atMacro :: !EnvironmentSection
  }
  deriving (Eq, Show)

environmentAtLevel :: EnvironmentSheafField -> ScaleLevel -> EnvironmentSection
environmentAtLevel f Quantum = atQuantum f
environmentAtLevel f Meso = atMeso f
environmentAtLevel f Macro = atMacro f

vacuumSampleAtLevel :: EnvironmentSheafField -> ScaleLevel -> VacuumSample
vacuumSampleAtLevel f lvl = vacuum (environmentAtLevel f lvl)

containedSampleAtLevel :: EnvironmentSheafField -> ScaleLevel -> ContainedSample
containedSampleAtLevel f lvl = contained (environmentAtLevel f lvl)

messySampleAtLevel :: EnvironmentSheafField -> ScaleLevel -> MessySample
messySampleAtLevel f lvl = messy (environmentAtLevel f lvl)

environmentAtLegSource :: EnvironmentSheafField -> ScaleCommutingLeg -> EnvironmentSection
environmentAtLegSource f leg = environmentAtLevel f (scaleLegSource leg)

environmentAtLegTarget :: EnvironmentSheafField -> ScaleCommutingLeg -> EnvironmentSection
environmentAtLegTarget f leg = environmentAtLevel f (scaleLegTarget leg)

-- | Knowing probe — env sample axis × scale stratum.
data KnowingProbe = KnowingProbe
  { probeAxis :: !EnvSampleAxis
  , probeScale :: !ScaleLevel
  }
  deriving (Eq, Show)

probeVacuumAtQuantum :: KnowingProbe
probeVacuumAtQuantum = KnowingProbe EnvAxisVacuum Quantum

probeContainedAtMeso :: KnowingProbe
probeContainedAtMeso = KnowingProbe EnvAxisContained Meso

probeMessyAtMacro :: KnowingProbe
probeMessyAtMacro = KnowingProbe EnvAxisMessy Macro

probeSample :: EnvironmentSheafField -> KnowingProbe -> Double
probeSample f (KnowingProbe axis lvl) =
  case axis of
    EnvAxisVacuum -> residualPO2Pa (vacuumSampleAtLevel f lvl)
    EnvAxisContained -> kelvin (containedSampleAtLevel f lvl)
    EnvAxisMessy -> oreGradeFraction (messySampleAtLevel f lvl)

probeVacuumAtQuantumNamed :: EnvironmentSheafField -> Bool
probeVacuumAtQuantumNamed f =
  probeSample f probeVacuumAtQuantum
    == residualPO2Pa (vacuum (atQuantum f))

-- | Named legs of the SCALE commuting diagram.
scaleLegQuantumToMeso :: ScaleCommutingLeg
scaleLegQuantumToMeso = QuantumToMeso

scaleLegMesoToMacro :: ScaleCommutingLeg
scaleLegMesoToMacro = MesoToMacro

scaleLegQuantumToMacroDirect :: ScaleCommutingLeg
scaleLegQuantumToMacroDirect = QuantumToMacroDirect

data ScaleCommuteDiagram = ScaleCommuteDiagram
  { viaMeso :: !ScaleCommutingLeg
  , thenMacro :: !ScaleCommutingLeg
  , direct :: !ScaleCommutingLeg
  }
  deriving (Eq, Show)

scaleCommuteDiagramNamed :: ScaleCommuteDiagram
scaleCommuteDiagramNamed =
  ScaleCommuteDiagram
    { viaMeso = scaleLegQuantumToMeso
    , thenMacro = scaleLegMesoToMacro
    , direct = scaleLegQuantumToMacroDirect
    }

scaleCommuteDiagramNamedFields :: Bool
scaleCommuteDiagramNamedFields =
  viaMeso scaleCommuteDiagramNamed == scaleLegQuantumToMeso
    && thenMacro scaleCommuteDiagramNamed == scaleLegMesoToMacro
    && direct scaleCommuteDiagramNamed == scaleLegQuantumToMacroDirect

scaleLegIndirectComposesLevels :: Bool
scaleLegIndirectComposesLevels =
  scaleLegTarget scaleLegQuantumToMeso == scaleLegSource scaleLegMesoToMacro

scaleLegDirectEndpointsMatch :: Bool
scaleLegDirectEndpointsMatch =
  scaleLegSource scaleLegQuantumToMeso == scaleLegSource scaleLegQuantumToMacroDirect
    && scaleLegTarget scaleLegMesoToMacro == scaleLegTarget scaleLegQuantumToMacroDirect

-- | SCALE commute witness indexed by a Q-lattice cell (Unwired).
data ScaleCommute = ScaleCommute
  { scaleParent :: !QLatticeCell
  , scaleDiagram :: !ScaleCommuteDiagram
  , scaleModality :: !ChemGeometryModality
  , edgeModality :: !ChemGeometryModality
  }
  deriving (Eq, Show)

scaleCommuteUnwired :: QLatticeCell -> ScaleCommute
scaleCommuteUnwired q =
  ScaleCommute
    { scaleParent = q
    , scaleDiagram = scaleCommuteDiagramNamed
    , scaleModality = chemGeometryModalityCurrent
    , edgeModality = chemGeometryModalityCurrent
    }

environmentAtLegSourceQuantumToMeso :: EnvironmentSheafField -> Bool
environmentAtLegSourceQuantumToMeso f =
  environmentAtLegSource f scaleLegQuantumToMeso == atQuantum f

environmentAtLegTargetQuantumToMeso :: EnvironmentSheafField -> Bool
environmentAtLegTargetQuantumToMeso f =
  environmentAtLegTarget f scaleLegQuantumToMeso == atMeso f

environmentAtLegSourceMesoToMacro :: EnvironmentSheafField -> Bool
environmentAtLegSourceMesoToMacro f =
  environmentAtLegSource f scaleLegMesoToMacro == atMeso f

environmentAtLegTargetMesoToMacro :: EnvironmentSheafField -> Bool
environmentAtLegTargetMesoToMacro f =
  environmentAtLegTarget f scaleLegMesoToMacro == atMacro f

environmentAtLegSourceQuantumToMacroDirect :: EnvironmentSheafField -> Bool
environmentAtLegSourceQuantumToMacroDirect f =
  environmentAtLegSource f scaleLegQuantumToMacroDirect == atQuantum f

environmentAtLegTargetQuantumToMacroDirect :: EnvironmentSheafField -> Bool
environmentAtLegTargetQuantumToMacroDirect f =
  environmentAtLegTarget f scaleLegQuantumToMacroDirect == atMacro f

environmentIndirectLegComposes :: EnvironmentSheafField -> Bool
environmentIndirectLegComposes f =
  environmentAtLegTarget f scaleLegQuantumToMeso
    == environmentAtLegSource f scaleLegMesoToMacro

environmentDirectEndpointsMatch :: EnvironmentSheafField -> Bool
environmentDirectEndpointsMatch f =
  environmentAtLegSource f scaleLegQuantumToMeso
    == environmentAtLegSource f scaleLegQuantumToMacroDirect
    && environmentAtLegTarget f scaleLegMesoToMacro
      == environmentAtLegTarget f scaleLegQuantumToMacroDirect

vacuumSampleAtLegSourceQuantumToMeso :: EnvironmentSheafField -> Bool
vacuumSampleAtLegSourceQuantumToMeso f =
  vacuum (environmentAtLegSource f scaleLegQuantumToMeso) == vacuum (atQuantum f)

containedSampleAtLegTargetMesoToMacro :: EnvironmentSheafField -> Bool
containedSampleAtLegTargetMesoToMacro f =
  contained (environmentAtLegTarget f scaleLegMesoToMacro) == contained (atMacro f)

messySampleAtLegSourceQuantumToMacroDirect :: EnvironmentSheafField -> Bool
messySampleAtLegSourceQuantumToMacroDirect f =
  messy (environmentAtLegSource f scaleLegQuantumToMacroDirect) == messy (atQuantum f)

data EnvironmentScaleSheafDiagram = EnvironmentScaleSheafDiagram
  { scaleDiag :: !ScaleCommuteDiagram
  , envField :: !EnvironmentSheafField
  }
  deriving (Eq, Show)

environmentScaleSheafDiagramNamed :: EnvironmentSheafField -> EnvironmentScaleSheafDiagram
environmentScaleSheafDiagramNamed f =
  EnvironmentScaleSheafDiagram
    { scaleDiag = scaleCommuteDiagramNamed
    , envField = f
    }

environmentScaleSheafDiagramNamedScale :: EnvironmentSheafField -> Bool
environmentScaleSheafDiagramNamedScale f =
  scaleDiag (environmentScaleSheafDiagramNamed f) == scaleCommuteDiagramNamed

data EnvironmentScaleSheafBinding = EnvironmentScaleSheafBinding
  { parent :: !QLatticeCell
  , field :: !EnvironmentSheafField
  , scaleCommuteWitness :: !ScaleCommute
  }
  deriving (Eq, Show)

environmentScaleMadelungKey :: EnvironmentScaleSheafBinding -> Word
environmentScaleMadelungKey b =
  madelungSum (qPrincipal (parent b)) (qAzimuthal (parent b))

environmentScaleBindingSameMadelungKey ::
  EnvironmentScaleSheafBinding -> EnvironmentScaleSheafBinding -> Bool
environmentScaleBindingSameMadelungKey a b =
  environmentScaleMadelungKey a == environmentScaleMadelungKey b

data EnvironmentScaleCommute = EnvironmentScaleCommute
  { binding :: !EnvironmentScaleSheafBinding
  , diagram :: !EnvironmentScaleSheafDiagram
  , scaleModalityWitness :: !ChemGeometryModality
  , edgeModalityWitness :: !ChemGeometryModality
  , environmentScaleModality :: !EnvironmentScaleModality
  }
  deriving (Eq, Show)

vacuumSampleAmbient :: VacuumSample
vacuumSampleAmbient = VacuumSample {residualPO2Pa = 0}

containedSampleAmbient :: ContainedSample
containedSampleAmbient = ContainedSample {kelvin = 298.15, pascal = 101325}

messySampleAmbient :: MessySample
messySampleAmbient = MessySample {oreGradeFraction = 0, impurityFraction = 0}

environmentSectionAmbient :: EnvironmentSection
environmentSectionAmbient =
  EnvironmentSection
    { vacuum = vacuumSampleAmbient
    , contained = containedSampleAmbient
    , messy = messySampleAmbient
    }

environmentSheafFieldAmbient :: EnvironmentSheafField
environmentSheafFieldAmbient =
  EnvironmentSheafField
    { atQuantum = environmentSectionAmbient
    , atMeso = environmentSectionAmbient
    , atMacro = environmentSectionAmbient
    }

environmentScaleCommuteUnwired :: QLatticeCell -> EnvironmentScaleCommute
environmentScaleCommuteUnwired q =
  EnvironmentScaleCommute
    { binding =
        EnvironmentScaleSheafBinding
          { parent = q
          , field = environmentSheafFieldAmbient
          , scaleCommuteWitness = scaleCommuteUnwired q
          }
    , diagram = environmentScaleSheafDiagramNamed environmentSheafFieldAmbient
    , scaleModalityWitness = chemGeometryModalityCurrent
    , edgeModalityWitness = chemGeometryModalityCurrent
    , environmentScaleModality = environmentScaleModalityCurrent
    }

environmentScaleCommuteModalityUnwired :: EnvironmentScaleCommute -> Bool
environmentScaleCommuteModalityUnwired c =
  ( scaleModalityWitness c == chemGeometryModalityCurrent
      && edgeModalityWitness c == chemGeometryModalityCurrent
      && environmentScaleModality c == environmentScaleModalityCurrent
  )
    == ( scaleModalityWitness c == Unwired
           && edgeModalityWitness c == Unwired
           && environmentScaleModality c == EnvScaleUnwired
       )

environmentScaleCommuteLatticeAnchor :: EnvironmentScaleCommute -> Bool
environmentScaleCommuteLatticeAnchor c =
  madelungSum (qPrincipal (parent (binding c))) (qAzimuthal (parent (binding c)))
    == madelungSum (qPrincipal (parent (binding c))) (qAzimuthal (parent (binding c)))

environmentScaleSheafIndirectComposes :: EnvironmentSheafField -> Bool
environmentScaleSheafIndirectComposes f =
  environmentAtLegTarget f (viaMeso (scaleDiag (environmentScaleSheafDiagramNamed f)))
    == environmentAtLegSource f (thenMacro (scaleDiag (environmentScaleSheafDiagramNamed f)))

environmentScaleSheafDirectEndpoints :: EnvironmentSheafField -> Bool
environmentScaleSheafDirectEndpoints f =
  environmentAtLegSource f (viaMeso (scaleDiag (environmentScaleSheafDiagramNamed f)))
    == environmentAtLegSource f (direct (scaleDiag (environmentScaleSheafDiagramNamed f)))
    && environmentAtLegTarget f (thenMacro (scaleDiag (environmentScaleSheafDiagramNamed f)))
      == environmentAtLegTarget f (direct (scaleDiag (environmentScaleSheafDiagramNamed f)))

environmentScaleCommuteUnwiredBindingParent :: QLatticeCell -> Bool
environmentScaleCommuteUnwiredBindingParent q =
  parent (binding (environmentScaleCommuteUnwired q)) == q

environmentScaleCommuteAmbientVacuum :: EnvironmentSheafField -> Bool
environmentScaleCommuteAmbientVacuum f =
  f == environmentSheafFieldAmbient
    && vacuumSampleAtLevel f Quantum == vacuumSampleAmbient

environmentScaleCommuteAmbientContained :: EnvironmentSheafField -> Bool
environmentScaleCommuteAmbientContained f =
  f == environmentSheafFieldAmbient
    && containedSampleAtLevel f Macro == containedSampleAmbient

environmentSectionAllSamples :: EnvironmentSection -> (VacuumSample, ContainedSample, MessySample)
environmentSectionAllSamples s = (vacuum s, contained s, messy s)

environmentSectionsCoexistNotXor :: EnvironmentSection -> Bool
environmentSectionsCoexistNotXor s =
  environmentSectionAllSamples s == (vacuum s, contained s, messy s)

environmentClassifyBulkOfNeg :: Double -> Bool
environmentClassifyBulkOfNeg sdf
  | sdf < 0 = classifyEdgeSurface sdf == Bulk
  | otherwise = True

environmentClassifySurfaceOfPos :: Double -> Bool
environmentClassifySurfaceOfPos sdf
  | not (sdf < 0) && sdf /= 0 = classifyEdgeSurface sdf == Surface
  | otherwise = True

environmentScaleSheafEqualityAuthorized :: EnvironmentScaleSheafDiagram -> Bool
environmentScaleSheafEqualityAuthorized _d = False

environmentScaleSheafEqualityPhysicsGreenFalse :: EnvironmentScaleSheafDiagram -> Bool
environmentScaleSheafEqualityPhysicsGreenFalse d =
  not (environmentScaleSheafEqualityAuthorized d)

environmentScaleCommutePhysicsGreenAuthorized :: EnvironmentScaleCommute -> Bool
environmentScaleCommutePhysicsGreenAuthorized _c = False

environmentScaleCommutePhysicsGreenFalse :: EnvironmentScaleCommute -> Bool
environmentScaleCommutePhysicsGreenFalse c =
  not (environmentScaleCommutePhysicsGreenAuthorized c)

environmentScaleLatticePhysicsGreenAuthorized :: QLatticeCell -> Bool
environmentScaleLatticePhysicsGreenAuthorized _q = False

environmentScaleLatticePhysicsGreenFalse :: QLatticeCell -> Bool
environmentScaleLatticePhysicsGreenFalse q =
  not (environmentScaleLatticePhysicsGreenAuthorized q)

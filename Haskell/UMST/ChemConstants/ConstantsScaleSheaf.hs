-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ConstantsScaleSheaf
Description : Knowing-fiber T, P, named constants as SCALE sheaf sections (Q lattice)
Copyright   : (c) UMST Project, 2026

Temperature, pressure, and named thermodynamic constants are **typed** as sheaf sections on
the Q ↔ meso ↔ macro SCALE ladder; commute along the square is **named**
(@ScaleCommutingLeg@ + @ConstantsSheafField@), not Proved as physics GREEN. Pairs
@umst-chem@ scaffold @CHEM-L0-SCALE-01@ constants remainder.

* Reuses @AllotropeGeometry@ @ScaleLevel@ + @ScaleCommutingLeg@ and @EnvironmentScaleCommute@
  diagram (Unwired).
* No meso / acting theorems. No new physics axioms.
* @physics_green@ stays false.

Haskell mirror of @Lean/ChemConstants/ConstantsScaleSheaf.lean@ on the quantum / knowing fiber.
-}
module UMST.ChemConstants.ConstantsScaleSheaf
  ( ConstantsScaleModality (..)
  , constantsScaleModalityCurrent
  , TemperatureSection (..)
  , PressureSection (..)
  , NamedConstantsSection (..)
  , ConstantsSheafSection (..)
  , ConstantsSheafField (..)
  , constantsAtLevel
  , temperatureSectionAtLevel
  , pressureSectionAtLevel
  , namedConstantsAtLevel
  , constantsAtLegSource
  , constantsAtLegTarget
  , constantsAtLegSourceQuantumToMeso
  , constantsAtLegTargetQuantumToMeso
  , constantsAtLegSourceMesoToMacro
  , constantsAtLegTargetMesoToMacro
  , constantsAtLegSourceQuantumToMacroDirect
  , constantsAtLegTargetQuantumToMacroDirect
  , constantsIndirectLegComposes
  , constantsDirectEndpointsMatch
  , temperatureSectionAtLegSourceQuantumToMeso
  , pressureSectionAtLegTargetMesoToMacro
  , namedConstantsAtLegSourceQuantumToMacroDirect
  , ConstantsScaleSheafBinding (..)
  , constantsScaleMadelungKey
  , constantsScaleBindingSameMadelungKey
  , ConstantsScaleSheafDiagram (..)
  , constantsScaleSheafDiagramNamed
  , constantsScaleSheafDiagramNamedScale
  , ConstantsScaleSheaf (..)
  , namedConstantsAmbient
  , constantsSheafSectionAmbient
  , constantsSheafFieldAmbient
  , constantsScaleSheafUnwired
  , constantsScaleSheafModalityUnwired
  , constantsScaleSheafLatticeAnchor
  , constantsScaleSheafDiagramScaleFields
  , constantsScaleSheafIndirectComposes
  , constantsScaleSheafDirectEndpoints
  , constantsScaleSheafUnwiredBindingParent
  , constantsScaleSheafAmbientTemperature
  , constantsScaleSheafAmbientPressure
  , constantsClassifyBulkOfNeg
  , constantsClassifySurfaceOfPos
  , constantsScaleSheafEqualityAuthorized
  , constantsScaleSheafEqualityPhysicsGreenFalse
  , constantsScaleSheafPhysicsGreenAuthorized
  , constantsScaleSheafPhysicsGreenFalse
  , constantsScaleLatticePhysicsGreenAuthorized
  , constantsScaleLatticePhysicsGreenFalse
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
import EnvironmentScaleCommute
  ( ScaleCommute (..)
  , ScaleCommuteDiagram (..)
  , scaleCommuteDiagramNamed
  , scaleCommuteUnwired
  , scaleLegMesoToMacro
  , scaleLegQuantumToMacroDirect
  , scaleLegQuantumToMeso
  )

-- | Design modality for constants SCALE sheaf claims (TYPE-03 preview).
data ConstantsScaleModality
  = ConstantsScaleUnwired
  | ConstantsScaleAssumed
  | ConstantsScaleProved
  | ConstantsScaleSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
constantsScaleModalityCurrent :: ConstantsScaleModality
constantsScaleModalityCurrent = ConstantsScaleUnwired

-- | Temperature sample at a scale stratum (design Kelvin placeholder — not physics GREEN).
data TemperatureSection = TemperatureSection
  { kelvin :: !Double
  }
  deriving (Eq, Show)

-- | Pressure sample at a scale stratum (design pascal placeholder — not physics GREEN).
data PressureSection = PressureSection
  { pascal :: !Double
  }
  deriving (Eq, Show)

-- | Named thermodynamic constant pins at a scale stratum (design — not physics GREEN).
data NamedConstantsSection = NamedConstantsSection
  { gasConstantR :: !Double
  , boltzmannK :: !Double
  , standardPressurePa :: !Double
  }
  deriving (Eq, Show)

-- | Coupled T, P, and named-constant sheaf section at one SCALE stratum (Unwired).
data ConstantsSheafSection = ConstantsSheafSection
  { temperature :: !TemperatureSection
  , pressure :: !PressureSection
  , named :: !NamedConstantsSection
  }
  deriving (Eq, Show)

-- | Constants sheaf field over the SCALE ladder (named sections per stratum — Unwired).
data ConstantsSheafField = ConstantsSheafField
  { atQuantum :: !ConstantsSheafSection
  , atMeso :: !ConstantsSheafSection
  , atMacro :: !ConstantsSheafSection
  }
  deriving (Eq, Show)

constantsAtLevel :: ConstantsSheafField -> ScaleLevel -> ConstantsSheafSection
constantsAtLevel f Quantum = atQuantum f
constantsAtLevel f Meso = atMeso f
constantsAtLevel f Macro = atMacro f

temperatureSectionAtLevel :: ConstantsSheafField -> ScaleLevel -> TemperatureSection
temperatureSectionAtLevel f lvl = temperature (constantsAtLevel f lvl)

pressureSectionAtLevel :: ConstantsSheafField -> ScaleLevel -> PressureSection
pressureSectionAtLevel f lvl = pressure (constantsAtLevel f lvl)

namedConstantsAtLevel :: ConstantsSheafField -> ScaleLevel -> NamedConstantsSection
namedConstantsAtLevel f lvl = named (constantsAtLevel f lvl)

constantsAtLegSource :: ConstantsSheafField -> ScaleCommutingLeg -> ConstantsSheafSection
constantsAtLegSource f leg = constantsAtLevel f (scaleLegSource leg)

constantsAtLegTarget :: ConstantsSheafField -> ScaleCommutingLeg -> ConstantsSheafSection
constantsAtLegTarget f leg = constantsAtLevel f (scaleLegTarget leg)

constantsAtLegSourceQuantumToMeso :: ConstantsSheafField -> Bool
constantsAtLegSourceQuantumToMeso f =
  constantsAtLegSource f scaleLegQuantumToMeso == atQuantum f

constantsAtLegTargetQuantumToMeso :: ConstantsSheafField -> Bool
constantsAtLegTargetQuantumToMeso f =
  constantsAtLegTarget f scaleLegQuantumToMeso == atMeso f

constantsAtLegSourceMesoToMacro :: ConstantsSheafField -> Bool
constantsAtLegSourceMesoToMacro f =
  constantsAtLegSource f scaleLegMesoToMacro == atMeso f

constantsAtLegTargetMesoToMacro :: ConstantsSheafField -> Bool
constantsAtLegTargetMesoToMacro f =
  constantsAtLegTarget f scaleLegMesoToMacro == atMacro f

constantsAtLegSourceQuantumToMacroDirect :: ConstantsSheafField -> Bool
constantsAtLegSourceQuantumToMacroDirect f =
  constantsAtLegSource f scaleLegQuantumToMacroDirect == atQuantum f

constantsAtLegTargetQuantumToMacroDirect :: ConstantsSheafField -> Bool
constantsAtLegTargetQuantumToMacroDirect f =
  constantsAtLegTarget f scaleLegQuantumToMacroDirect == atMacro f

constantsIndirectLegComposes :: ConstantsSheafField -> Bool
constantsIndirectLegComposes f =
  constantsAtLegTarget f scaleLegQuantumToMeso
    == constantsAtLegSource f scaleLegMesoToMacro

constantsDirectEndpointsMatch :: ConstantsSheafField -> Bool
constantsDirectEndpointsMatch f =
  constantsAtLegSource f scaleLegQuantumToMeso
    == constantsAtLegSource f scaleLegQuantumToMacroDirect
    && constantsAtLegTarget f scaleLegMesoToMacro
      == constantsAtLegTarget f scaleLegQuantumToMacroDirect

temperatureSectionAtLegSourceQuantumToMeso :: ConstantsSheafField -> Bool
temperatureSectionAtLegSourceQuantumToMeso f =
  temperature (constantsAtLegSource f scaleLegQuantumToMeso)
    == temperature (atQuantum f)

pressureSectionAtLegTargetMesoToMacro :: ConstantsSheafField -> Bool
pressureSectionAtLegTargetMesoToMacro f =
  pressure (constantsAtLegTarget f scaleLegMesoToMacro) == pressure (atMacro f)

namedConstantsAtLegSourceQuantumToMacroDirect :: ConstantsSheafField -> Bool
namedConstantsAtLegSourceQuantumToMacroDirect f =
  named (constantsAtLegSource f scaleLegQuantumToMacroDirect) == named (atQuantum f)

-- | Binding of a constants sheaf field to its parent Q-lattice cell + SCALE commute witness.
data ConstantsScaleSheafBinding = ConstantsScaleSheafBinding
  { parent :: !QLatticeCell
  , field :: !ConstantsSheafField
  , scaleCommuteWitness :: !ScaleCommute
  }
  deriving (Eq, Show)

constantsScaleMadelungKey :: ConstantsScaleSheafBinding -> Word
constantsScaleMadelungKey b =
  madelungSum (qPrincipal (parent b)) (qAzimuthal (parent b))

constantsScaleBindingSameMadelungKey ::
  ConstantsScaleSheafBinding -> ConstantsScaleSheafBinding -> Bool
constantsScaleBindingSameMadelungKey a b =
  constantsScaleMadelungKey a == constantsScaleMadelungKey b

-- | Named constants sheaf commute diagram (pairs SCALE diagram + field — equality not Proved).
data ConstantsScaleSheafDiagram = ConstantsScaleSheafDiagram
  { scale :: !ScaleCommuteDiagram
  , sheafField :: !ConstantsSheafField
  }
  deriving (Eq, Show)

constantsScaleSheafDiagramNamed :: ConstantsSheafField -> ConstantsScaleSheafDiagram
constantsScaleSheafDiagramNamed f =
  ConstantsScaleSheafDiagram
    { scale = scaleCommuteDiagramNamed
    , sheafField = f
    }

constantsScaleSheafDiagramNamedScale :: ConstantsSheafField -> Bool
constantsScaleSheafDiagramNamedScale f =
  scale (constantsScaleSheafDiagramNamed f) == scaleCommuteDiagramNamed

-- | Constants sheaf field + SCALE commute witness indexed by Q-lattice cell (Unwired).
data ConstantsScaleSheaf = ConstantsScaleSheaf
  { binding :: !ConstantsScaleSheafBinding
  , diagram :: !ConstantsScaleSheafDiagram
  , scaleModalityWitness :: !ChemGeometryModality
  , edgeModalityWitness :: !ChemGeometryModality
  , constantsScaleModality :: !ConstantsScaleModality
  }
  deriving (Eq, Show)

namedConstantsAmbient :: NamedConstantsSection
namedConstantsAmbient =
  NamedConstantsSection
    { gasConstantR = 8.314462618
    , boltzmannK = 1.380649e-23
    , standardPressurePa = 101325
    }

constantsSheafSectionAmbient :: ConstantsSheafSection
constantsSheafSectionAmbient =
  ConstantsSheafSection
    { temperature = TemperatureSection {kelvin = 298.15}
    , pressure = PressureSection {pascal = 101325}
    , named = namedConstantsAmbient
    }

constantsSheafFieldAmbient :: ConstantsSheafField
constantsSheafFieldAmbient =
  ConstantsSheafField
    { atQuantum = constantsSheafSectionAmbient
    , atMeso = constantsSheafSectionAmbient
    , atMacro = constantsSheafSectionAmbient
    }

constantsScaleSheafUnwired :: QLatticeCell -> ConstantsScaleSheaf
constantsScaleSheafUnwired q =
  ConstantsScaleSheaf
    { binding =
        ConstantsScaleSheafBinding
          { parent = q
          , field = constantsSheafFieldAmbient
          , scaleCommuteWitness = scaleCommuteUnwired q
          }
    , diagram = constantsScaleSheafDiagramNamed constantsSheafFieldAmbient
    , scaleModalityWitness = chemGeometryModalityCurrent
    , edgeModalityWitness = chemGeometryModalityCurrent
    , constantsScaleModality = constantsScaleModalityCurrent
    }

constantsScaleSheafModalityUnwired :: ConstantsScaleSheaf -> Bool
constantsScaleSheafModalityUnwired c =
  ( scaleModalityWitness c == chemGeometryModalityCurrent
      && edgeModalityWitness c == chemGeometryModalityCurrent
      && constantsScaleModality c == constantsScaleModalityCurrent
  )
    == ( scaleModalityWitness c == Unwired
           && edgeModalityWitness c == Unwired
           && constantsScaleModality c == ConstantsScaleUnwired
       )

constantsScaleSheafLatticeAnchor :: ConstantsScaleSheaf -> Bool
constantsScaleSheafLatticeAnchor c =
  madelungSum (qPrincipal (parent (binding c))) (qAzimuthal (parent (binding c)))
    == madelungSum (qPrincipal (parent (binding c))) (qAzimuthal (parent (binding c)))

constantsScaleSheafDiagramScaleFields :: ConstantsSheafField -> Bool
constantsScaleSheafDiagramScaleFields f =
  viaMeso (scale (constantsScaleSheafDiagramNamed f)) == scaleLegQuantumToMeso
    && thenMacro (scale (constantsScaleSheafDiagramNamed f)) == scaleLegMesoToMacro
    && direct (scale (constantsScaleSheafDiagramNamed f)) == scaleLegQuantumToMacroDirect

constantsScaleSheafIndirectComposes :: ConstantsSheafField -> Bool
constantsScaleSheafIndirectComposes f =
  constantsAtLegTarget f (viaMeso (scale (constantsScaleSheafDiagramNamed f)))
    == constantsAtLegSource f (thenMacro (scale (constantsScaleSheafDiagramNamed f)))

constantsScaleSheafDirectEndpoints :: ConstantsSheafField -> Bool
constantsScaleSheafDirectEndpoints f =
  constantsAtLegSource f (viaMeso (scale (constantsScaleSheafDiagramNamed f)))
    == constantsAtLegSource f (direct (scale (constantsScaleSheafDiagramNamed f)))
    && constantsAtLegTarget f (thenMacro (scale (constantsScaleSheafDiagramNamed f)))
      == constantsAtLegTarget f (direct (scale (constantsScaleSheafDiagramNamed f)))

constantsScaleSheafUnwiredBindingParent :: QLatticeCell -> Bool
constantsScaleSheafUnwiredBindingParent q =
  parent (binding (constantsScaleSheafUnwired q)) == q

constantsScaleSheafAmbientTemperature :: ConstantsSheafField -> Bool
constantsScaleSheafAmbientTemperature f =
  f == constantsSheafFieldAmbient
    && temperatureSectionAtLevel f Quantum == TemperatureSection {kelvin = 298.15}

constantsScaleSheafAmbientPressure :: ConstantsSheafField -> Bool
constantsScaleSheafAmbientPressure f =
  f == constantsSheafFieldAmbient
    && pressureSectionAtLevel f Macro == PressureSection {pascal = 101325}

constantsClassifyBulkOfNeg :: Double -> Bool
constantsClassifyBulkOfNeg sdf
  | sdf < 0 = classifyEdgeSurface sdf == Bulk
  | otherwise = True

constantsClassifySurfaceOfPos :: Double -> Bool
constantsClassifySurfaceOfPos sdf
  | not (sdf < 0) && sdf /= 0 = classifyEdgeSurface sdf == Surface
  | otherwise = True

constantsScaleSheafEqualityAuthorized :: ConstantsScaleSheafDiagram -> Bool
constantsScaleSheafEqualityAuthorized _d = False

constantsScaleSheafEqualityPhysicsGreenFalse :: ConstantsScaleSheafDiagram -> Bool
constantsScaleSheafEqualityPhysicsGreenFalse d =
  not (constantsScaleSheafEqualityAuthorized d)

constantsScaleSheafPhysicsGreenAuthorized :: ConstantsScaleSheaf -> Bool
constantsScaleSheafPhysicsGreenAuthorized _c = False

constantsScaleSheafPhysicsGreenFalse :: ConstantsScaleSheaf -> Bool
constantsScaleSheafPhysicsGreenFalse c =
  not (constantsScaleSheafPhysicsGreenAuthorized c)

constantsScaleLatticePhysicsGreenAuthorized :: QLatticeCell -> Bool
constantsScaleLatticePhysicsGreenAuthorized _q = False

constantsScaleLatticePhysicsGreenFalse :: QLatticeCell -> Bool
constantsScaleLatticePhysicsGreenFalse q =
  not (constantsScaleLatticePhysicsGreenAuthorized q)

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : AllotropeGeometry
Description : SCALE ladder + EDGE-SURFACE sign convention (knowing fiber)
Copyright   : (c) UMST Project, 2026

Geometry preview for L0 chemistry on @umst-formal-double-slit@ only:

* __SCALE:__ Q ↔ meso ↔ macro legs are __typed__; commute is not proved here.
* __EDGE-SURFACE:__ @sdf < 0@ bulk, @sdf = 0@ interface, @sdf > 0@ surface.

Pairs @umst-chem@ scaffolds @CHEM-L0-SCALE-01@ and @CHEM-L0-EDGE-SURFACE@. No meso acting
theorems. @physics_green@ stays false.

Haskell mirror of @Lean/ChemGeometry.lean@ on the quantum / knowing fiber.
-}
module AllotropeGeometry
  ( ScaleLevel (..)
  , ScaleCommutingLeg (..)
  , scaleLegSource
  , scaleLegTarget
  , scaleLegSourceTargetDistinct
  , ChemGeometryModality (..)
  , chemGeometryModalityCurrent
  , EdgeSurfaceRegime (..)
  , classifyEdgeSurface
  , classifyEdgeSurfaceBulkOfNeg
  , classifyEdgeSurfaceSurfaceOfPos
  , ChemGeometry (..)
  , chemGeometryUnwired
  , chemGeometryModalityUnwired
  , chemGeometryPhysicsGreenAuthorized
  , chemGeometryPhysicsGreenFalse
  ) where

import ChemGeometry (QLatticeCell (..))

-- | L0 scale stratum in the Q ↔ meso ↔ macro ladder (design names only).
data ScaleLevel = Quantum | Meso | Macro
  deriving (Eq, Ord, Show)

-- | Named legs of the scale commuting diagram (scaffold — commute not proved).
data ScaleCommutingLeg = QuantumToMeso | MesoToMacro | QuantumToMacroDirect
  deriving (Eq, Show)

-- | Source scale level of a commuting leg.
scaleLegSource :: ScaleCommutingLeg -> ScaleLevel
scaleLegSource QuantumToMeso = Quantum
scaleLegSource MesoToMacro = Meso
scaleLegSource QuantumToMacroDirect = Quantum

-- | Target scale level of a commuting leg.
scaleLegTarget :: ScaleCommutingLeg -> ScaleLevel
scaleLegTarget QuantumToMeso = Meso
scaleLegTarget MesoToMacro = Macro
scaleLegTarget QuantumToMacroDirect = Macro

-- | Every leg connects distinct scale levels (Lean: @scale_leg_source_target_distinct@).
scaleLegSourceTargetDistinct :: ScaleCommutingLeg -> Bool
scaleLegSourceTargetDistinct leg = scaleLegSource leg /= scaleLegTarget leg

-- | Design modality for geometry / SCALE / EDGE-SURFACE claims.
data ChemGeometryModality = Unwired | Assumed | Proved | Surrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
chemGeometryModalityCurrent :: ChemGeometryModality
chemGeometryModalityCurrent = Unwired

-- | EDGE-SURFACE regime from signed-distance sign convention.
data EdgeSurfaceRegime = Bulk | Interface | Surface
  deriving (Eq, Show)

-- | Classify a scalar SDF sample under the bulk-negative / surface-positive convention.
classifyEdgeSurface :: Double -> EdgeSurfaceRegime
classifyEdgeSurface sdf
  | sdf < 0 = Bulk
  | sdf == 0 = Interface
  | otherwise = Surface

-- | Lean: @classifyEdgeSurface_bulk_of_neg@.
classifyEdgeSurfaceBulkOfNeg :: Double -> Bool
classifyEdgeSurfaceBulkOfNeg sdf
  | sdf < 0 = classifyEdgeSurface sdf == Bulk
  | otherwise = True

-- | Lean: @classifyEdgeSurface_surface_of_pos@.
classifyEdgeSurfaceSurfaceOfPos :: Double -> Bool
classifyEdgeSurfaceSurfaceOfPos sdf
  | not (sdf < 0) && sdf /= 0 = classifyEdgeSurface sdf == Surface
  | otherwise = True

-- | SCALE + EDGE-SURFACE geometry witness indexed by a Q-lattice cell (Unwired).
data ChemGeometry = ChemGeometry
  { lattice :: !QLatticeCell
  , scaleModality :: !ChemGeometryModality
  , edgeModality :: !ChemGeometryModality
  }
  deriving (Eq, Show)

-- | Unwired geometry witness for a Q-lattice cell.
chemGeometryUnwired :: QLatticeCell -> ChemGeometry
chemGeometryUnwired q =
  ChemGeometry
    { lattice = q
    , scaleModality = chemGeometryModalityCurrent
    , edgeModality = chemGeometryModalityCurrent
    }

-- | Lean: @chem_geometry_modality_unwired@ (iff both modalities are Unwired).
chemGeometryModalityUnwired :: ChemGeometry -> Bool
chemGeometryModalityUnwired g =
  (scaleModality g == chemGeometryModalityCurrent
      && edgeModality g == chemGeometryModalityCurrent)
    == (scaleModality g == Unwired && edgeModality g == Unwired)

-- | Physics GREEN is unauthorized on the knowing geometry scaffold.
chemGeometryPhysicsGreenAuthorized :: ChemGeometry -> Bool
chemGeometryPhysicsGreenAuthorized _g = False

-- | Lean: @chem_geometry_physics_green_false@.
chemGeometryPhysicsGreenFalse :: ChemGeometry -> Bool
chemGeometryPhysicsGreenFalse g = not (chemGeometryPhysicsGreenAuthorized g)

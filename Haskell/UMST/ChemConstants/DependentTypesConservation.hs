-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.DependentTypesConservation
Description : Dependent-types conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Dependent-types conservation: @ElementDependentBundle@ geometry/thermo scaffold indexed by
@ElementId@ — not L1 @SpeciesId@; index identity conserved on bundle roundtrip.
TYPE-01 dependency and species L1 posture are structure witnesses only
(@type01DepProved@ = False, @speciesIsL1@ = True).

* @ElementDependentBundle@ = geometry + thermo rows — dependent carrier, not @Vec@ list.
* @dependentBundleFor@ / @rebuildDependentBundle@ — build vs rebuild distinct.
* **One** design axiom (@dependentTypesConservationAxiom@): second law + conservation.
* Element index identity conserved under geometry/thermo bundle scaffold.
* @physics_green@ stays false.

Haskell mirror of dependent-types conservation on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-DEPENDENT-TYPES-CONSERVATION@.
-}
module UMST.ChemConstants.DependentTypesConservation
  ( DependentTypesConservationModality (..)
  , dependentTypesConservationModalityCurrent
  , ElementIdTag (..)
  , ElementGeometryTier (..)
  , ElementGeometryFor (..)
  , ElementThermoFor (..)
  , ElementDependentBundle (..)
  , dependentBundleFor
  , elementBundleGeometryElement
  , elementBundleThermoElement
  , elementBundleIndexCoherent
  , sampleHydrogenBundle
  , sampleOxygenBundle
  , RebuildVerdict (..)
  , rebuildDependentBundle
  , geometryKnowingFiberOk
  , terminalBundleCoherent
  , hydrogenIndexCoherent
  , oxygenIndexCoherent
  , mismatchedIndexRefuse
  , greenInventRebuildRefuse
  , speciesIsL1
  , indexIdentityConservedOnHydrogen
  , indexIdentityConservedOnOxygen
  , indexIdentityConservedOnRoundtrip
  , geometryThermoScaffold
  , type01DepInventRefuse
  , dependentBundleNotListBacked
  , geometryThermoNotXor
  , type01DepProved
  , dependentTypesConservationFraming
  , dependentTypesConservationAxiom
  , dependentTypesConservationNamed
  , elementDependentTypesAuthority
  , chemL0Type01Authority
  , dependentTypesConservationCellId
  , dependentTypesConservationNonClaim
  , dependentTypesConservationPhysicsGreenAuthorized
  , dependentTypesConservationPhysicsGreenFalse
  , dependentTypesConservationModalityUnwired
  ) where

-- | Design modality for dependent-types conservation claims (TYPE-03 preview).
data DependentTypesConservationModality
  = DependentTypesConservationUnwired
  | DependentTypesConservationAssumed
  | DependentTypesConservationProved
  | DependentTypesConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
dependentTypesConservationModalityCurrent :: DependentTypesConservationModality
dependentTypesConservationModalityCurrent = DependentTypesConservationUnwired

-- | ElementId factor tags (bounded scaffold — not XOR enum).
data ElementIdTag
  = HScaffold
  | OScaffold
  | CaScaffold
  | SiScaffold
  deriving (Eq, Show)

-- | Geometry representation tier ladder (north-star mSDF→TE-SDF→SDF→FRep; Unwired).
data ElementGeometryTier
  = MicroSdfTier
  | TeSdfTier
  | SdfTier
  | FRepTier
  deriving (Eq, Show)

-- | Element-indexed geometry row — dependent on ElementId, not SpeciesId.
data ElementGeometryFor = ElementGeometryFor
  { geometryElement :: ElementIdTag
  , geometryTier :: ElementGeometryTier
  }
  deriving (Eq, Show)

-- | Element-indexed thermo row — dependent on ElementId, not SpeciesId.
data ElementThermoFor = ElementThermoFor
  { thermoElement :: ElementIdTag
  , thermoModality :: DependentTypesConservationModality
  }
  deriving (Eq, Show)

-- | Paired dependent geometry + thermo bundle for one ElementId.
data ElementDependentBundle = ElementDependentBundle
  { bundleGeometry :: ElementGeometryFor
  , bundleThermo :: ElementThermoFor
  }
  deriving (Eq, Show)

-- | Build an Unwired dependent bundle for element.
dependentBundleFor :: ElementIdTag -> ElementDependentBundle
dependentBundleFor element =
  ElementDependentBundle
    (ElementGeometryFor element MicroSdfTier)
    (ElementThermoFor element DependentTypesConservationUnwired)

elementBundleGeometryElement :: ElementDependentBundle -> ElementIdTag
elementBundleGeometryElement bundle = geometryElement (bundleGeometry bundle)

elementBundleThermoElement :: ElementDependentBundle -> ElementIdTag
elementBundleThermoElement bundle = thermoElement (bundleThermo bundle)

elementBundleIndexCoherent :: ElementDependentBundle -> Bool
elementBundleIndexCoherent bundle =
  elementBundleGeometryElement bundle == elementBundleThermoElement bundle

-- | Sample hydrogen dependent bundle for roundtrip witnesses.
sampleHydrogenBundle :: ElementDependentBundle
sampleHydrogenBundle = dependentBundleFor HScaffold

-- | Sample oxygen dependent bundle for roundtrip witnesses.
sampleOxygenBundle :: ElementDependentBundle
sampleOxygenBundle = dependentBundleFor OScaffold

-- | Rebuild verdict (coherent vs refuse).
data RebuildVerdict
  = RebuildCoherentOk
  | RebuildMismatchedIndexRefuse
  | RebuildGreenInventRefuse
  deriving (Eq, Show)

-- | Rebuild dependent bundle from geometry + thermo rows (refuse-closed).
rebuildDependentBundle ::
  ElementGeometryFor -> ElementThermoFor -> Bool -> (RebuildVerdict, Maybe ElementDependentBundle)
rebuildDependentBundle geometry thermo claimPhysicsGreen
  | claimPhysicsGreen = (RebuildGreenInventRefuse, Nothing)
  | geometryElement geometry /= thermoElement thermo =
      (RebuildMismatchedIndexRefuse, Nothing)
  | otherwise =
      ( RebuildCoherentOk
      , Just (ElementDependentBundle geometry thermo)
      )

-- | Geometry claims route to knowing / quantum fiber (FORMAL-00 SSOT witness).
geometryKnowingFiberOk :: Bool
geometryKnowingFiberOk = True

-- | Terminal coherent bundle decomposes without refuse.
terminalBundleCoherent :: Bool
terminalBundleCoherent = elementBundleIndexCoherent sampleHydrogenBundle

-- | Hydrogen bundle index coherence witness.
hydrogenIndexCoherent :: Bool
hydrogenIndexCoherent =
  elementBundleIndexCoherent sampleHydrogenBundle
    && elementBundleGeometryElement sampleHydrogenBundle == HScaffold

-- | Oxygen bundle index coherence witness.
oxygenIndexCoherent :: Bool
oxygenIndexCoherent =
  elementBundleIndexCoherent sampleOxygenBundle
    && elementBundleGeometryElement sampleOxygenBundle == OScaffold

-- | Mismatched geometry/thermo index is refused (no free purification).
mismatchedIndexRefuse :: Bool
mismatchedIndexRefuse =
  case
    rebuildDependentBundle
      (ElementGeometryFor HScaffold MicroSdfTier)
      (ElementThermoFor OScaffold DependentTypesConservationUnwired)
      False
    of
    (RebuildMismatchedIndexRefuse, Nothing) -> True
    _ -> False

-- | GREEN invent on rebuild is refused.
greenInventRebuildRefuse :: Bool
greenInventRebuildRefuse =
  case
    rebuildDependentBundle
      (ElementGeometryFor HScaffold MicroSdfTier)
      (ElementThermoFor HScaffold DependentTypesConservationUnwired)
      True
    of
    (RebuildGreenInventRefuse, Nothing) -> True
    _ -> False

-- | SpeciesId is L1 occupancy — geometry/thermo index ElementId at L0.
speciesIsL1 :: Bool
speciesIsL1 = True

-- | Check element index identity conserved on bundle roundtrip.
checkIndexRoundtrip :: ElementIdTag -> Bool -> Bool
checkIndexRoundtrip element claimPhysicsGreen =
  let bundle = dependentBundleFor element
      geometry = bundleGeometry bundle
      thermo = bundleThermo bundle
   in case rebuildDependentBundle geometry thermo claimPhysicsGreen of
        (RebuildCoherentOk, Just rebuilt) ->
          rebuilt == bundle && elementBundleIndexCoherent rebuilt
        _ -> False

-- | Hydrogen index identity conserved on roundtrip.
indexIdentityConservedOnHydrogen :: Bool
indexIdentityConservedOnHydrogen = checkIndexRoundtrip HScaffold False

-- | Oxygen index identity conserved on roundtrip.
indexIdentityConservedOnOxygen :: Bool
indexIdentityConservedOnOxygen = checkIndexRoundtrip OScaffold False

-- | Element index identity conserved under geometry/thermo bundle scaffold.
indexIdentityConservedOnRoundtrip :: Bool
indexIdentityConservedOnRoundtrip =
  indexIdentityConservedOnHydrogen
    && indexIdentityConservedOnOxygen
    && terminalBundleCoherent

-- | Both geometry and thermo scaffolds admissible under Unwired design rules.
geometryThermoScaffold :: Bool
geometryThermoScaffold =
  indexIdentityConservedOnRoundtrip
    && geometryKnowingFiberOk
    && hydrogenIndexCoherent
    && oxygenIndexCoherent

-- | TYPE-01 dependency invent refuse-closed scaffold witness.
type01DepInventRefuse :: Bool
type01DepInventRefuse = not type01DepProved

-- | ElementDependentBundle algebra is not list-backed (geometry/thermo scaffold).
dependentBundleNotListBacked :: Bool
dependentBundleNotListBacked =
  sampleHydrogenBundle /= sampleOxygenBundle
    && elementBundleIndexCoherent sampleHydrogenBundle
    && elementBundleIndexCoherent sampleOxygenBundle

-- | Geometry and thermo facets are concurrent Π_c — not XOR enum bucket.
geometryThermoNotXor :: Bool
geometryThermoNotXor =
  hydrogenIndexCoherent
    && oxygenIndexCoherent
    && mismatchedIndexRefuse
    && greenInventRebuildRefuse
    && sampleHydrogenBundle /= sampleOxygenBundle

-- | TYPE-01 dependency proved (always false on this Unwired cell).
type01DepProved :: Bool
type01DepProved = False

-- | One axiom framing: second law + conservation for dependent-types scaffold.
dependentTypesConservationFraming :: String
dependentTypesConservationFraming =
  "second_law_conservation_dependent_types_one_axiom"

-- | Single design axiom: second law + conservation dependent types (not second axiom).
dependentTypesConservationAxiom :: Bool
dependentTypesConservationAxiom =
  speciesIsL1
    && dependentBundleNotListBacked
    && geometryThermoScaffold
    && indexIdentityConservedOnRoundtrip
    && mismatchedIndexRefuse
    && greenInventRebuildRefuse
    && type01DepInventRefuse
    && geometryThermoNotXor
    && not type01DepProved
    && dependentTypesConservationFraming
      == "second_law_conservation_dependent_types_one_axiom"

dependentTypesConservationNamed :: String
dependentTypesConservationNamed =
  "dependentTypesConservation: ElementDependentBundle geometry/thermo ElementId-indexed; speciesIsL1 true type01DepProved false; index identity conserved on roundtrip; second law + conservation one axiom"

-- | Upstream ElementId-dependent geometry/thermo authority (cited, not forked).
elementDependentTypesAuthority :: String
elementDependentTypesAuthority = "umst/umst-chem/src/element_geometry_thermo_types.rs"

-- | L0 TYPE-01 dependent-types scaffold authority (crosswalk).
chemL0Type01Authority :: String
chemL0Type01Authority = "umst/umst-chem/src/element_geometry_thermo_types.rs"

dependentTypesConservationCellId :: String
dependentTypesConservationCellId = "CHEM-FORMAL-Q-HS-DEPENDENT-TYPES-CONSERVATION"

-- | Non-claim fence — dependent-types conservation Unwired ≠ Proved GREEN.
dependentTypesConservationNonClaim :: String
dependentTypesConservationNonClaim =
  "CHEM-FORMAL-Q-HS-DEPENDENT-TYPES-CONSERVATION ElementDependentBundle geometry thermo ElementId-indexed speciesIsL1 true type01DepProved false indexIdentityConservedOnRoundtrip Unwired one axiom second law conservation not XOR enum not Vec list not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing dependent-types conservation scaffold.
dependentTypesConservationPhysicsGreenAuthorized :: Bool
dependentTypesConservationPhysicsGreenAuthorized = False

dependentTypesConservationPhysicsGreenFalse :: Bool
dependentTypesConservationPhysicsGreenFalse =
  not dependentTypesConservationPhysicsGreenAuthorized

dependentTypesConservationModalityUnwired :: Bool
dependentTypesConservationModalityUnwired =
  dependentTypesConservationModalityCurrent == DependentTypesConservationUnwired

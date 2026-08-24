-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.AllotropeConservation
Description : ALLOTROPE-01 **allotrope** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Allotrope** **conservation**: same-Z geometry variants (C diamond / graphite) with
Identity⊗Geometry⊗DensityLadder product identity conserved on named pins; concurrent
Π_c not XOR enum; allotrope ≠ duplicate ElementId row. Named **allotrope** identity
conserved under honest scaffold; folklore / GREEN / trivial / proved-without-bar /
parallel-axiom refuse-closed. ALLOTROPE-01 **allotrope** laws are structure witnesses
only (@allotropeConservationProved@ = False).

* @AllotropeConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateAllotropeConservation@ — named Identity⊗Geometry⊗DensityLadder product identity conserved.
* @allotropeCommuteConservation@ — class 10⊗geometry⊗density composed equals direct (typed **conservation**).
* **One** design axiom (@allotropeConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of ALLOTROPE-01 **allotrope** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-ALLOTROPE-CONSERVATION@.
-}
module UMST.ChemConstants.AllotropeConservation
  ( AllotropeConservationModality (..)
  , allotropeConservationModalityCurrent
  , allotropeLatticeAll
  , allotropeLatticeCount
  , AllotropeElementZ (..)
  , allotropeElementZAll
  , allotropeElementZCount
  , allotropeElementZNumeric
  , AllotropeGeometryVariant (..)
  , allotropeGeometryVariantAll
  , allotropeGeometryVariantCount
  , AllotropeForm (..)
  , allotropeFormAll
  , allotropeFormCount
  , AllotropeDensityRung (..)
  , allotropeDensityRungAll
  , allotropeDensityRungCount
  , Class10IdentityWitness (..)
  , Class10GeometryWitness (..)
  , Class10DensityWitness (..)
  , AllotropeProductFactor (..)
  , allotropeProductDiamond
  , allotropeProductGraphite
  , AllotropeConservationPath (..)
  , allotropeConservationPathCarbonDiamondL1
  , allotropeConservationPathCarbonGraphiteL1
  , allotropeClassIndexOk
  , liftIdentityWitness
  , liftGeometryWitness
  , liftDensityWitness
  , directAllotropeProduct
  , allotropeIdentityConserved
  , allotropeCommuteConservation
  , AllotropeConservationVerdict (..)
  , evaluateAllotropeConservation
  , unwiredAllotropeDesignOk
  , twoVariantsNamedOk
  , composedEqualsDirectOk
  , allotropeProductNotXorOk
  , cSameZDiamondGraphiteOk
  , carbonElementZValid
  , duplicateElementIdRefuse
  , parallelAxiomRefuse
  , assumedAllotropeDesignOk
  , surrogateAllotropeDesignOk
  , greenInventAllotropeRefuse
  , folkloreListRefuse
  , trivialRefuse
  , provedWithoutBarRefuse
  , xorEnumRefuse
  , allotropeLatticeScaffold
  , allotropeLatticeNotGreenTable
  , allotropeConservationLawsScaffold
  , allotropeConservationLawsNotGreenTable
  , allotropeKnowingFiberOk
  , allotropeInventRefuse
  , allotropeLatticeNotXor
  , allotropeConservationProved
  , allotropeConservationFraming
  , allotropeConservationAxiom
  , allotropeConservationNamed
  , allotropeGeometryAuthority
  , chemL0EdgeAllotropeAuthority
  , allotropeConservationCellId
  , allotropeConservationNonClaim
  , allotropeConservationPhysicsGreenAuthorized
  , allotropeConservationPhysicsGreenFalse
  , allotropeConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not ALLOTROPE-01 GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Class-10 allotrope pattern index (north-star §2).
class10AllotropePatternIndex :: Int
class10AllotropePatternIndex = 10

-- | Class-geometry geometry-variant pattern index (X5 product factor).
classGeometryPatternIndex :: Int
classGeometryPatternIndex = 11

-- | Class-density DensityLadder pattern index (X5 product factor).
classDensityPatternIndex :: Int
classDensityPatternIndex = 12

-- | Design **allotrope** modality for ALLOTROPE-01 **conservation** claims.
data AllotropeConservationModality
  = AllotropeConservationUnwired
  | AllotropeConservationAssumed
  | AllotropeConservationProved
  | AllotropeConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **allotrope** modality — always Unwired on this cell.
allotropeConservationModalityCurrent :: AllotropeConservationModality
allotropeConservationModalityCurrent = AllotropeConservationUnwired

-- | All ALLOTROPE-01 **allotrope** lattice steps in stable order.
allotropeLatticeAll :: [AllotropeConservationModality]
allotropeLatticeAll =
  [ AllotropeConservationUnwired
  , AllotropeConservationAssumed
  , AllotropeConservationProved
  , AllotropeConservationSurrogate
  ]

allotropeLatticeCount :: Int
allotropeLatticeCount = length allotropeLatticeAll

-- | Private Z pin for **allotrope** witnesses — not L1 SpeciesId.
data AllotropeElementZ
  = AllotropeElementCarbon
  | AllotropeElementSilicon
  deriving (Eq, Show)

-- | All scaffold **allotrope** element Z pins in stable order.
allotropeElementZAll :: [AllotropeElementZ]
allotropeElementZAll =
  [ AllotropeElementCarbon
  , AllotropeElementSilicon
  ]

allotropeElementZCount :: Int
allotropeElementZCount = length allotropeElementZAll

-- | Numeric Z for an **allotrope** element pin.
allotropeElementZNumeric :: AllotropeElementZ -> Int
allotropeElementZNumeric z =
  case z of
    AllotropeElementCarbon -> 6
    AllotropeElementSilicon -> 14

-- | Whether an **allotrope** element Z is valid IUPAC Z @ scaffold.
isValidIupacZ :: AllotropeElementZ -> Bool
isValidIupacZ z =
  let n = allotropeElementZNumeric z
   in n > 0 && n <= iupacTableCardinality

-- | Named geometry-variant placeholders for L0 allotropes (Unwired — no SDF GREEN).
data AllotropeGeometryVariant
  = DiamondLatticeNamed
  | GraphiticLayeredNamed
  | AmorphousDisorderedNamed
  deriving (Eq, Show)

-- | All scaffold **allotrope** geometry variants in stable order.
allotropeGeometryVariantAll :: [AllotropeGeometryVariant]
allotropeGeometryVariantAll =
  [ DiamondLatticeNamed
  , GraphiticLayeredNamed
  , AmorphousDisorderedNamed
  ]

allotropeGeometryVariantCount :: Int
allotropeGeometryVariantCount = length allotropeGeometryVariantAll

-- | Named allotrope form for C same-Z diamond / graphite scaffold.
data AllotropeForm
  = CarbonDiamondForm
  | CarbonGraphiteForm
  | SiliconCrystallineForm
  deriving (Eq, Show)

-- | All scaffold **allotrope** forms in stable order.
allotropeFormAll :: [AllotropeForm]
allotropeFormAll =
  [ CarbonDiamondForm
  , CarbonGraphiteForm
  , SiliconCrystallineForm
  ]

allotropeFormCount :: Int
allotropeFormCount = length allotropeFormAll

-- | North-star **density** ladder rung for allotrope geometry variants.
data AllotropeDensityRung
  = AllotropeMicroSdfRung
  | AllotropeTeSdfRung
  | AllotropeSdfRung
  | AllotropeFRepRung
  deriving (Eq, Show)

-- | All **allotrope** density rungs in stable order.
allotropeDensityRungAll :: [AllotropeDensityRung]
allotropeDensityRungAll =
  [ AllotropeMicroSdfRung
  , AllotropeTeSdfRung
  , AllotropeSdfRung
  , AllotropeFRepRung
  ]

allotropeDensityRungCount :: Int
allotropeDensityRungCount = length allotropeDensityRungAll

-- | Class-10 element-identity witness on the allotrope product factor.
data Class10IdentityWitness = Class10IdentityWitness
  { identityTag :: String
  , identityClassIndex :: Int
  }
  deriving (Eq, Show)

-- | Class-geometry variant witness on the allotrope product factor.
data Class10GeometryWitness = Class10GeometryWitness
  { geometryTag :: String
  , geometryClassIndex :: Int
  }
  deriving (Eq, Show)

-- | Class-density DensityLadder witness on the allotrope product factor.
data Class10DensityWitness = Class10DensityWitness
  { densityRungTag :: String
  , densityClassIndex :: Int
  }
  deriving (Eq, Show)

-- | Named **product factor** Identity (10) ⊗ Geometry (11) ⊗ Density (12) — concurrent Π_c, not XOR enum.
data AllotropeProductFactor = AllotropeProductFactor
  { productIdentity :: Class10IdentityWitness
  , productGeometry :: Class10GeometryWitness
  , productDensity :: Class10DensityWitness
  }
  deriving (Eq, Show)

-- | Whether all three class witnesses are honest on the product factor.
allotropeProductFactorHonest :: AllotropeProductFactor -> Bool
allotropeProductFactorHonest factor =
  identityClassIndex (productIdentity factor) == class10AllotropePatternIndex
    && geometryClassIndex (productGeometry factor) == classGeometryPatternIndex
    && densityClassIndex (productDensity factor) == classDensityPatternIndex
    && not (null (identityTag (productIdentity factor)))
    && not (null (geometryTag (productGeometry factor)))
    && not (null (densityRungTag (productDensity factor)))

-- | Class indices pinned to 10 ⊗ 11 ⊗ 12.
allotropeClassIndicesMatchX5 :: AllotropeProductFactor -> Bool
allotropeClassIndicesMatchX5 factor =
  identityClassIndex (productIdentity factor) == class10AllotropePatternIndex
    && geometryClassIndex (productGeometry factor) == classGeometryPatternIndex
    && densityClassIndex (productDensity factor) == classDensityPatternIndex

-- | Pinned diamond product factor (C Z=6 sp³ lattice under DensityLadder).
allotropeProductDiamond :: AllotropeProductFactor
allotropeProductDiamond =
  AllotropeProductFactor
    { productIdentity =
        Class10IdentityWitness
          { identityTag = "c_z6_element_identity"
          , identityClassIndex = class10AllotropePatternIndex
          }
    , productGeometry =
        Class10GeometryWitness
          { geometryTag = "diamond_sp3_lattice"
          , geometryClassIndex = classGeometryPatternIndex
          }
    , productDensity =
        Class10DensityWitness
          { densityRungTag = "diamond_msdf_to_frep"
          , densityClassIndex = classDensityPatternIndex
          }
    }

-- | Pinned graphite product factor (C Z=6 layered sp² under DensityLadder).
allotropeProductGraphite :: AllotropeProductFactor
allotropeProductGraphite =
  AllotropeProductFactor
    { productIdentity =
        Class10IdentityWitness
          { identityTag = "c_z6_element_identity"
          , identityClassIndex = class10AllotropePatternIndex
          }
    , productGeometry =
        Class10GeometryWitness
          { geometryTag = "graphite_sp2_layered"
          , geometryClassIndex = classGeometryPatternIndex
          }
    , productDensity =
        Class10DensityWitness
          { densityRungTag = "graphite_msdf_to_frep"
          , densityClassIndex = classDensityPatternIndex
          }
    }

-- | A **allotrope** **conservation** path at a refinement level.
data AllotropeConservationPath = AllotropeConservationPath
  { allotropePathLevel :: Int
  , allotropePathElementZ :: AllotropeElementZ
  , allotropePathForm :: AllotropeForm
  , allotropePathVariant :: AllotropeGeometryVariant
  , allotropePathProduct :: AllotropeProductFactor
  }
  deriving (Eq, Show)

-- | Whether an **allotrope** path is non-trivial (level > 0).
allotropeConservationPathIsNontrivial :: AllotropeConservationPath -> Bool
allotropeConservationPathIsNontrivial path = allotropePathLevel path > 0

-- | Carbon diamond **allotrope** **conservation** path @ L1 scaffold (C Z=6 diamond).
allotropeConservationPathCarbonDiamondL1 :: AllotropeConservationPath
allotropeConservationPathCarbonDiamondL1 =
  AllotropeConservationPath
    { allotropePathLevel = 1
    , allotropePathElementZ = AllotropeElementCarbon
    , allotropePathForm = CarbonDiamondForm
    , allotropePathVariant = DiamondLatticeNamed
    , allotropePathProduct = allotropeProductDiamond
    }

-- | Carbon graphite **allotrope** **conservation** path @ L1 scaffold (C Z=6 graphite).
allotropeConservationPathCarbonGraphiteL1 :: AllotropeConservationPath
allotropeConservationPathCarbonGraphiteL1 =
  AllotropeConservationPath
    { allotropePathLevel = 1
    , allotropePathElementZ = AllotropeElementCarbon
    , allotropePathForm = CarbonGraphiteForm
    , allotropePathVariant = GraphiticLayeredNamed
    , allotropePathProduct = allotropeProductGraphite
    }

-- | Class 10⊗11⊗12 indices are strictly ordered and pinned.
allotropeClassIndexOk :: Bool
allotropeClassIndexOk =
  class10AllotropePatternIndex == 10
    && classGeometryPatternIndex == 11
    && classDensityPatternIndex == 12
    && class10AllotropePatternIndex < classGeometryPatternIndex
    && classGeometryPatternIndex < classDensityPatternIndex

-- | Identity (10) lift on **allotrope** identity (knowing fiber — Unwired scaffold).
liftIdentityWitness :: Int -> Int
liftIdentityWitness = id

-- | Geometry (11) lift on **allotrope** identity (knowing fiber — Unwired scaffold).
liftGeometryWitness :: Int -> Int
liftGeometryWitness = id

-- | Density (12) lift on **allotrope** identity (knowing fiber — Unwired scaffold).
liftDensityWitness :: Int -> Int
liftDensityWitness = id

-- | Direct Identity⊗Geometry⊗Density product on **allotrope** identity (knowing fiber — Unwired scaffold).
directAllotropeProduct :: Int -> Int
directAllotropeProduct = id

-- | **Allotrope** identity conserved: composed Identity⊗Geometry⊗Density equals direct product.
allotropeIdentityConserved :: Int -> Bool
allotropeIdentityConserved witness =
  liftDensityWitness (liftGeometryWitness (liftIdentityWitness witness))
    == directAllotropeProduct witness

-- | Typed **allotrope** **conservation** along the Identity⊗Geometry⊗Density commuting diagram.
allotropeCommuteConservation :: Int -> Bool
allotropeCommuteConservation = allotropeIdentityConserved

-- | Verdict for ALLOTROPE-01 **allotrope** **conservation** close (fail-closed).
data AllotropeConservationVerdict
  = AllotropeConservationDesignOk
  | AllotropeConservationNamedOk
  | AllotropeConservationTrivialRefuse
  | AllotropeConservationGreenInventRefuse
  | AllotropeConservationProvedWithoutBarRefuse
  | AllotropeConservationFolkloreListRefuse
  | AllotropeConservationXorEnumRefuse
  | AllotropeConservationDuplicateElementIdRefuse
  | AllotropeConservationParallelAxiomRefuse
  deriving (Eq, Show)

-- | Evaluate **allotrope** **conservation** under ALLOTROPE-01 bar (fail-closed).
evaluateAllotropeConservation ::
  AllotropeConservationModality
  -> AllotropeConservationPath
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> AllotropeConservationVerdict
evaluateAllotropeConservation
  modality
  path
  claimPhysicsGreen
  claimProved
  claimFolkloreList
  claimXorEnum
  claimDuplicateElementId
  claimParallelAxiom
  | claimPhysicsGreen = AllotropeConservationGreenInventRefuse
  | claimFolkloreList = AllotropeConservationFolkloreListRefuse
  | claimXorEnum = AllotropeConservationXorEnumRefuse
  | claimDuplicateElementId = AllotropeConservationDuplicateElementIdRefuse
  | claimParallelAxiom = AllotropeConservationParallelAxiomRefuse
  | claimProved = AllotropeConservationProvedWithoutBarRefuse
  | not (allotropeConservationPathIsNontrivial path) =
      AllotropeConservationTrivialRefuse
  | not (isValidIupacZ (allotropePathElementZ path)) =
      AllotropeConservationTrivialRefuse
  | not (allotropeProductFactorHonest (allotropePathProduct path)) =
      AllotropeConservationTrivialRefuse
  | otherwise =
      case modality of
        AllotropeConservationUnwired ->
          if twoVariantsNamed then AllotropeConservationNamedOk else AllotropeConservationDesignOk
        AllotropeConservationAssumed -> AllotropeConservationDesignOk
        AllotropeConservationSurrogate -> AllotropeConservationDesignOk
        AllotropeConservationProved -> AllotropeConservationProvedWithoutBarRefuse

-- | Two named diamond / graphite variants on C same-Z scaffold.
twoVariantsNamed :: Bool
twoVariantsNamed =
  allotropeGeometryVariantCount >= 2
    && allotropeProductFactorHonest allotropeProductDiamond
    && allotropeProductFactorHonest allotropeProductGraphite
    && allotropeClassIndicesMatchX5 allotropeProductDiamond
    && allotropeClassIndicesMatchX5 allotropeProductGraphite
    && identityTag (productIdentity allotropeProductDiamond)
      == identityTag (productIdentity allotropeProductGraphite)
    && allotropeProductDiamond /= allotropeProductGraphite

-- | Unwired **allotrope** modality OK without geometry break.
unwiredAllotropeDesignOk :: Bool
unwiredAllotropeDesignOk =
  evaluateAllotropeConservation
    AllotropeConservationUnwired
    allotropeConservationPathCarbonDiamondL1
    False
    False
    False
    False
    False
    False
    == AllotropeConservationNamedOk

-- | Two named diamond / graphite variants on scaffold.
twoVariantsNamedOk :: Bool
twoVariantsNamedOk =
  twoVariantsNamed
    && allotropeGeometryVariantCount == 3
    && allotropeClassIndexOk

-- | Composed Identity⊗Geometry⊗Density equals direct product (**allotrope** **conservation**).
composedEqualsDirectOk :: Bool
composedEqualsDirectOk =
  allotropeCommuteConservation 42
    && allotropeIdentityConserved 42
    && liftDensityWitness (liftGeometryWitness (liftIdentityWitness 42))
      == directAllotropeProduct 42

-- | Diamond / graphite concurrent Identity⊗Geometry⊗Density product — not XOR enum.
allotropeProductNotXorOk :: Bool
allotropeProductNotXorOk =
  allotropeProductFactorHonest allotropeProductDiamond
    && allotropeProductFactorHonest allotropeProductGraphite
    && allotropeClassIndicesMatchX5 allotropeProductDiamond
    && allotropeClassIndicesMatchX5 allotropeProductGraphite
    && allotropeProductDiamond /= allotropeProductGraphite
    && geometryTag (productGeometry allotropeProductDiamond)
      /= geometryTag (productGeometry allotropeProductGraphite)

-- | C Z=6 same Z across diamond / graphite allotrope forms.
cSameZDiamondGraphiteOk :: Bool
cSameZDiamondGraphiteOk =
  allotropeElementZNumeric AllotropeElementCarbon == 6
    && allotropePathElementZ allotropeConservationPathCarbonDiamondL1
      == AllotropeElementCarbon
    && allotropePathElementZ allotropeConservationPathCarbonGraphiteL1
      == AllotropeElementCarbon
    && allotropePathForm allotropeConservationPathCarbonDiamondL1 == CarbonDiamondForm
    && allotropePathForm allotropeConservationPathCarbonGraphiteL1 == CarbonGraphiteForm
    && allotropePathVariant allotropeConservationPathCarbonDiamondL1 == DiamondLatticeNamed
    && allotropePathVariant allotropeConservationPathCarbonGraphiteL1 == GraphiticLayeredNamed

-- | C **allotrope** anchor carries valid Z=6 pin.
carbonElementZValid :: Bool
carbonElementZValid =
  isValidIupacZ AllotropeElementCarbon
    && allotropeElementZNumeric AllotropeElementCarbon == 6
    && allotropePathElementZ allotropeConservationPathCarbonDiamondL1
      == AllotropeElementCarbon

-- | Duplicate ElementId row smuggle is refused (allotrope ≠ new ElementId).
duplicateElementIdRefuse :: Bool
duplicateElementIdRefuse =
  evaluateAllotropeConservation
    AllotropeConservationUnwired
    allotropeConservationPathCarbonDiamondL1
    False
    False
    False
    False
    True
    False
    == AllotropeConservationDuplicateElementIdRefuse

-- | Parallel allotrope axiom smuggle is refused (not 26th axiom).
parallelAxiomRefuse :: Bool
parallelAxiomRefuse =
  evaluateAllotropeConservation
    AllotropeConservationUnwired
    allotropeConservationPathCarbonDiamondL1
    False
    False
    False
    False
    False
    True
    == AllotropeConservationParallelAxiomRefuse

-- | Assumed **allotrope** modality OK without geometry break (design scaffold).
assumedAllotropeDesignOk :: Bool
assumedAllotropeDesignOk =
  evaluateAllotropeConservation
    AllotropeConservationAssumed
    allotropeConservationPathCarbonDiamondL1
    False
    False
    False
    False
    False
    False
    == AllotropeConservationDesignOk

-- | Surrogate **allotrope** modality OK without geometry break (design scaffold).
surrogateAllotropeDesignOk :: Bool
surrogateAllotropeDesignOk =
  evaluateAllotropeConservation
    AllotropeConservationSurrogate
    allotropeConservationPathCarbonDiamondL1
    False
    False
    False
    False
    False
    False
    == AllotropeConservationDesignOk

-- | GREEN invent on **allotrope** **conservation** promotion is refused.
greenInventAllotropeRefuse :: Bool
greenInventAllotropeRefuse =
  evaluateAllotropeConservation
    AllotropeConservationUnwired
    allotropeConservationPathCarbonDiamondL1
    True
    False
    False
    False
    False
    False
    == AllotropeConservationGreenInventRefuse

-- | Folklore allotrope list smuggle is refused (not monoidal geometry morphism).
folkloreListRefuse :: Bool
folkloreListRefuse =
  evaluateAllotropeConservation
    AllotropeConservationUnwired
    allotropeConservationPathCarbonDiamondL1
    False
    False
    True
    False
    False
    False
    == AllotropeConservationFolkloreListRefuse

-- | Trivial (level-0) **allotrope** path is refused (fail-closed).
trivialRefuse :: Bool
trivialRefuse =
  let trivialPath =
        allotropeConservationPathCarbonDiamondL1 {allotropePathLevel = 0}
   in evaluateAllotropeConservation
        AllotropeConservationUnwired
        trivialPath
        False
        False
        False
        False
        False
        False
        == AllotropeConservationTrivialRefuse

-- | Proved allotrope split without path census is refused.
provedWithoutBarRefuse :: Bool
provedWithoutBarRefuse =
  evaluateAllotropeConservation
    AllotropeConservationUnwired
    allotropeConservationPathCarbonDiamondL1
    False
    True
    False
    False
    False
    False
    == AllotropeConservationProvedWithoutBarRefuse
    && evaluateAllotropeConservation
      AllotropeConservationProved
      allotropeConservationPathCarbonDiamondL1
      False
      False
      False
      False
      False
      False
      == AllotropeConservationProvedWithoutBarRefuse

-- | XOR allotrope enum bucket smuggle is refused.
xorEnumRefuse :: Bool
xorEnumRefuse =
  evaluateAllotropeConservation
    AllotropeConservationUnwired
    allotropeConservationPathCarbonDiamondL1
    False
    False
    False
    True
    False
    False
    == AllotropeConservationXorEnumRefuse

-- | Four-step ALLOTROPE-01 **allotrope** lattice scaffold pinned.
allotropeLatticeScaffold :: Bool
allotropeLatticeScaffold =
  allotropeLatticeCount == 4
    && unwiredAllotropeDesignOk
    && twoVariantsNamedOk
    && allotropeClassIndexOk
    && composedEqualsDirectOk
    && allotropeProductNotXorOk
    && cSameZDiamondGraphiteOk
    && carbonElementZValid
    && assumedAllotropeDesignOk
    && surrogateAllotropeDesignOk

-- | **Allotrope** lattice is structure scaffold — not 118² GREEN periodic table.
allotropeLatticeNotGreenTable :: Bool
allotropeLatticeNotGreenTable =
  allotropeLatticeCount == 4
    && allotropeLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && allotropeGeometryVariantCount /= iupacTableCardinality * iupacTableCardinality
    && allotropeFormCount /= iupacTableCardinality * iupacTableCardinality
    && allotropeElementZCount /= iupacTableCardinality * iupacTableCardinality

-- | **Allotrope** **conservation** law cells scaffold pinned.
allotropeConservationLawsScaffold :: Bool
allotropeConservationLawsScaffold =
  twoVariantsNamedOk
    && allotropeClassIndexOk
    && composedEqualsDirectOk
    && allotropeProductNotXorOk
    && cSameZDiamondGraphiteOk
    && carbonElementZValid
    && greenInventAllotropeRefuse
    && folkloreListRefuse
    && trivialRefuse
    && provedWithoutBarRefuse
    && xorEnumRefuse
    && duplicateElementIdRefuse
    && parallelAxiomRefuse

-- | **Allotrope** law cells are structure scaffold — not 118² GREEN periodic table.
allotropeConservationLawsNotGreenTable :: Bool
allotropeConservationLawsNotGreenTable =
  allotropeConservationLawsScaffold
    && allotropeGeometryVariantCount /= 118 * 118
    && allotropeFormCount /= 118 * 118

-- | ALLOTROPE-01 **allotrope** **conservation** claims route to knowing / quantum fiber.
allotropeKnowingFiberOk :: Bool
allotropeKnowingFiberOk = True

-- | ALLOTROPE-01 allotrope invent refuse-closed scaffold witness.
allotropeInventRefuse :: Bool
allotropeInventRefuse = not allotropeConservationProved

-- | **Allotrope** lattice steps are concurrent Π_c — not XOR enum bucket.
allotropeLatticeNotXor :: Bool
allotropeLatticeNotXor =
  unwiredAllotropeDesignOk
    && assumedAllotropeDesignOk
    && surrogateAllotropeDesignOk
    && composedEqualsDirectOk
    && allotropeProductNotXorOk
    && greenInventAllotropeRefuse
    && folkloreListRefuse

-- | ALLOTROPE-01 allotrope proved (always false on this Unwired cell).
allotropeConservationProved :: Bool
allotropeConservationProved = False

-- | One axiom framing: second law + **conservation** for ALLOTROPE-01 **allotrope** scaffold.
allotropeConservationFraming :: String
allotropeConservationFraming =
  "second_law_conservation_allotrope_one_axiom"

-- | Single design axiom: second law + **conservation** ALLOTROPE-01 **allotrope** (not 26th axiom).
allotropeConservationAxiom :: Bool
allotropeConservationAxiom =
  allotropeLatticeScaffold
    && allotropeLatticeNotGreenTable
    && allotropeConservationLawsScaffold
    && allotropeConservationLawsNotGreenTable
    && allotropeKnowingFiberOk
    && twoVariantsNamedOk
    && allotropeClassIndexOk
    && composedEqualsDirectOk
    && allotropeProductNotXorOk
    && cSameZDiamondGraphiteOk
    && carbonElementZValid
    && greenInventAllotropeRefuse
    && folkloreListRefuse
    && trivialRefuse
    && provedWithoutBarRefuse
    && xorEnumRefuse
    && duplicateElementIdRefuse
    && parallelAxiomRefuse
    && allotropeInventRefuse
    && allotropeLatticeNotXor
    && not allotropeConservationProved
    && allotropeConservationFraming
      == "second_law_conservation_allotrope_one_axiom"

allotropeConservationNamed :: String
allotropeConservationNamed =
  "allotropeConservation: AllotropeConservationModality Unwired Assumed Proved Surrogate four-step lattice allotropeConservationProved false evaluateAllotropeConservation allotropeCommuteConservation C Z=6 same Z diamond graphite concurrent Identity otimes Geometry otimes DensityLadder product not XOR allotrope ne duplicate ElementId parallel axiom refuse folklore GREEN trivial proved-without-bar refuse class 10 otimes 11 otimes 12 knowing fiber second law conservation one axiom not 26th axiom not 118 squared GREEN table"

-- | Upstream allotrope geometry authority (cited, not forked).
allotropeGeometryAuthority :: String
allotropeGeometryAuthority = "umst/umst-chem/src/allotrope_geometry_variants.rs"

-- | L0 EDGE-ALLOTROPE scaffold authority (crosswalk).
chemL0EdgeAllotropeAuthority :: String
chemL0EdgeAllotropeAuthority = "CHEM-L0-EDGE-ALLOTROPE"

allotropeConservationCellId :: String
allotropeConservationCellId = "CHEM-FORMAL-Q-HS-ALLOTROPE-CONSERVATION"

-- | Non-claim fence — ALLOTROPE-01 **allotrope** **conservation** Unwired ≠ Proved GREEN.
allotropeConservationNonClaim :: String
allotropeConservationNonClaim =
  "CHEM-FORMAL-Q-HS-ALLOTROPE-CONSERVATION AllotropeConservationModality Unwired Assumed Proved Surrogate four-step lattice allotropeConservationProved false evaluateAllotropeConservation allotropeCommuteConservation C Z=6 same Z diamond graphite concurrent Identity otimes Geometry otimes DensityLadder product not XOR allotrope ne duplicate ElementId parallel axiom refuse folklore GREEN trivial proved-without-bar refuse class 10 otimes 11 otimes 12 Unwired one axiom second law conservation not 26th axiom not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing ALLOTROPE-01 **allotrope** **conservation** scaffold.
allotropeConservationPhysicsGreenAuthorized :: Bool
allotropeConservationPhysicsGreenAuthorized = False

allotropeConservationPhysicsGreenFalse :: Bool
allotropeConservationPhysicsGreenFalse =
  not allotropeConservationPhysicsGreenAuthorized

allotropeConservationModalityUnwired :: Bool
allotropeConservationModalityUnwired =
  allotropeConservationModalityCurrent == AllotropeConservationUnwired

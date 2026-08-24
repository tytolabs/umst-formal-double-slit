-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.GoldschmidtConservation
Description : GOLDSCHMIDT-01 **ore-class** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Goldschmidt** **ore-class** **conservation**: lithophile / chalcophile / siderophile concurrent
Ore⊗G⊗fO₂ product **not** XOR enum; Fe Z=26 same Z metal/oxide/sulfide; Cu Z=29; Si Z=14;
He Z=2 closed-shell no-ore. Named **Goldschmidt** affinity identity conserved under honest
scaffold; folklore / GREEN / trivial / proved-without-bar refuse-closed. GOLDSCHMIDT-01
**ore-class** laws are structure witnesses only (@goldschmidtProved@ = False).

* @GoldschmidtConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateGoldschmidtConservation@ — named Ore⊗G⊗fO₂ product identity conserved; concurrent Π_c not XOR.
* @goldschmidtCommuteConservation@ — class 6⊗7⊗17 product composed equals direct (typed **conservation**).
* **One** design axiom (@goldschmidtConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of GOLDSCHMIDT-01 **ore-class** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-GOLDSCHMIDT-CONSERVATION@.
-}
module UMST.ChemConstants.GoldschmidtConservation
  ( GoldschmidtConservationModality (..)
  , goldschmidtConservationModalityCurrent
  , goldschmidtLatticeAll
  , goldschmidtLatticeCount
  , GoldschmidtElementZ (..)
  , goldschmidtElementZAll
  , goldschmidtElementZCount
  , goldschmidtElementZNumeric
  , GoldschmidtOreForm (..)
  , goldschmidtOreFormAll
  , goldschmidtOreFormCount
  , GoldschmidtAffinityTag (..)
  , goldschmidtAffinityTagAll
  , goldschmidtAffinityTagCount
  , Class6OreWitness (..)
  , Class7GStabilityWitness (..)
  , Class17Fo2Witness (..)
  , GoldschmidtProductFactor (..)
  , goldschmidtProductSiderophile
  , goldschmidtProductLithophile
  , goldschmidtProductChalcophile
  , GoldschmidtAffinityWitness (..)
  , goldschmidtAffinitySiderophile
  , goldschmidtAffinityLithophile
  , goldschmidtAffinityChalcophile
  , GoldschmidtConservationPath (..)
  , goldschmidtConservationPathFeMetalL1
  , goldschmidtConservationPathFeOxideL1
  , goldschmidtConservationPathFeSulfideL1
  , goldschmidtConservationPathCuL1
  , goldschmidtConservationPathSiL1
  , goldschmidtConservationPathHeNoOreL1
  , liftOreWitness
  , liftGStabilityWitness
  , liftFo2Witness
  , directGoldschmidtProduct
  , goldschmidtIdentityConserved
  , goldschmidtCommuteConservation
  , goldschmidtClassIndicesOk
  , GoldschmidtConservationVerdict (..)
  , evaluateGoldschmidtConservation
  , unwiredGoldschmidtDesignOk
  , threeAffinitiesNamedOk
  , composedEqualsDirectOk
  , goldschmidtProductNotXorOk
  , feSameZMetalOxideSulfideOk
  , copperElementZValid
  , siliconElementZValid
  , heliumClosedShellNoOreOk
  , assumedGoldschmidtDesignOk
  , surrogateGoldschmidtDesignOk
  , greenInventGoldschmidtRefuse
  , folkloreListRefuse
  , trivialRefuse
  , provedWithoutBarRefuse
  , goldschmidtLatticeScaffold
  , goldschmidtLatticeNotGreenTable
  , goldschmidtConservationLawsScaffold
  , goldschmidtConservationLawsNotGreenTable
  , goldschmidtKnowingFiberOk
  , goldschmidtInventRefuse
  , goldschmidtLatticeNotXor
  , goldschmidtProved
  , goldschmidtConservationFraming
  , goldschmidtConservationAxiom
  , goldschmidtConservationNamed
  , goldschmidtOreAuthority
  , chemL0Goldschmidt01Authority
  , goldschmidtConservationCellId
  , goldschmidtConservationNonClaim
  , goldschmidtConservationPhysicsGreenAuthorized
  , goldschmidtConservationPhysicsGreenFalse
  , goldschmidtConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not GOLDSCHMIDT-01 GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Class-6 natural ore assemblage pattern index (X5 product factor).
class6OrePatternIndex :: Int
class6OrePatternIndex = 6

-- | Class-7 assemblage-stability G-min pattern index (X5 product factor).
class7GStabilityPatternIndex :: Int
class7GStabilityPatternIndex = 7

-- | Class-17 redox fO₂ ladder pattern index (X5 product factor).
class17Fo2PatternIndex :: Int
class17Fo2PatternIndex = 17

-- | Design **Goldschmidt** modality for GOLDSCHMIDT-01 **conservation** claims.
data GoldschmidtConservationModality
  = GoldschmidtConservationUnwired
  | GoldschmidtConservationAssumed
  | GoldschmidtConservationProved
  | GoldschmidtConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **Goldschmidt** modality — always Unwired on this cell.
goldschmidtConservationModalityCurrent :: GoldschmidtConservationModality
goldschmidtConservationModalityCurrent = GoldschmidtConservationUnwired

-- | All GOLDSCHMIDT-01 **Goldschmidt** lattice steps in stable order.
goldschmidtLatticeAll :: [GoldschmidtConservationModality]
goldschmidtLatticeAll =
  [ GoldschmidtConservationUnwired
  , GoldschmidtConservationAssumed
  , GoldschmidtConservationProved
  , GoldschmidtConservationSurrogate
  ]

goldschmidtLatticeCount :: Int
goldschmidtLatticeCount = length goldschmidtLatticeAll

-- | Private Z pin for **Goldschmidt** witnesses — not L1 SpeciesId.
data GoldschmidtElementZ
  = GoldschmidtElementIron
  | GoldschmidtElementCopper
  | GoldschmidtElementSilicon
  | GoldschmidtElementHelium
  deriving (Eq, Show)

-- | All scaffold **Goldschmidt** element Z pins in stable order.
goldschmidtElementZAll :: [GoldschmidtElementZ]
goldschmidtElementZAll =
  [ GoldschmidtElementIron
  , GoldschmidtElementCopper
  , GoldschmidtElementSilicon
  , GoldschmidtElementHelium
  ]

goldschmidtElementZCount :: Int
goldschmidtElementZCount = length goldschmidtElementZAll

-- | Numeric Z for a **Goldschmidt** element pin.
goldschmidtElementZNumeric :: GoldschmidtElementZ -> Int
goldschmidtElementZNumeric z =
  case z of
    GoldschmidtElementIron -> 26
    GoldschmidtElementCopper -> 29
    GoldschmidtElementSilicon -> 14
    GoldschmidtElementHelium -> 2

-- | Whether a **Goldschmidt** element Z is valid IUPAC Z @ scaffold.
isValidIupacZ :: GoldschmidtElementZ -> Bool
isValidIupacZ z =
  let n = goldschmidtElementZNumeric z
   in n > 0 && n <= iupacTableCardinality

-- | Named ore form for Fe same-Z metal / oxide / sulfide scaffold.
data GoldschmidtOreForm
  = FeMetalForm
  | FeOxideForm
  | FeSulfideForm
  | CuSulfideForm
  | SiSilicateForm
  | HeClosedShellNoOre
  deriving (Eq, Show)

-- | All scaffold **Goldschmidt** ore forms in stable order.
goldschmidtOreFormAll :: [GoldschmidtOreForm]
goldschmidtOreFormAll =
  [ FeMetalForm
  , FeOxideForm
  , FeSulfideForm
  , CuSulfideForm
  , SiSilicateForm
  , HeClosedShellNoOre
  ]

goldschmidtOreFormCount :: Int
goldschmidtOreFormCount = length goldschmidtOreFormAll

-- | Named **Goldschmidt** affinity tags — derived from Ore⊗G⊗fO₂ product, not XOR enum.
data GoldschmidtAffinityTag
  = SiderophileAffinity
  | LithophileAffinity
  | ChalcophileAffinity
  deriving (Eq, Show)

-- | All **Goldschmidt** affinity tags in stable order.
goldschmidtAffinityTagAll :: [GoldschmidtAffinityTag]
goldschmidtAffinityTagAll =
  [ SiderophileAffinity
  , LithophileAffinity
  , ChalcophileAffinity
  ]

goldschmidtAffinityTagCount :: Int
goldschmidtAffinityTagCount = length goldschmidtAffinityTagAll

-- | Class-6 Ore assemblage witness on the Goldschmidt product factor.
data Class6OreWitness = Class6OreWitness
  { oreTag :: String
  , oreClassIndex :: Int
  }
  deriving (Eq, Show)

-- | Class-7 G-min / assemblage-stability witness on the Goldschmidt product factor.
data Class7GStabilityWitness = Class7GStabilityWitness
  { gMinTag :: String
  , gClassIndex :: Int
  }
  deriving (Eq, Show)

-- | Class-17 fO₂ redox-ladder witness on the Goldschmidt product factor.
data Class17Fo2Witness = Class17Fo2Witness
  { fo2LogBar :: Int
  , fo2LadderTag :: String
  , fo2ClassIndex :: Int
  }
  deriving (Eq, Show)

-- | Named **product factor** Ore (6) ⊗ G (7) ⊗ fO₂ (17) — concurrent Π_c, not XOR enum.
data GoldschmidtProductFactor = GoldschmidtProductFactor
  { productOre :: Class6OreWitness
  , productGStability :: Class7GStabilityWitness
  , productFo2 :: Class17Fo2Witness
  }
  deriving (Eq, Show)

-- | Pinned siderophile product factor (Fe core metal cluster under low fO₂).
goldschmidtProductSiderophile :: GoldschmidtProductFactor
goldschmidtProductSiderophile =
  GoldschmidtProductFactor
    { productOre =
        Class6OreWitness
          { oreTag = "fe_core_metal_cluster"
          , oreClassIndex = class6OrePatternIndex
          }
    , productGStability =
        Class7GStabilityWitness
          { gMinTag = "core_g_min_partition"
          , gClassIndex = class7GStabilityPatternIndex
          }
    , productFo2 =
        Class17Fo2Witness
          { fo2LogBar = -4
          , fo2LadderTag = "core_low_fo2_ladder"
          , fo2ClassIndex = class17Fo2PatternIndex
          }
    }

-- | Pinned lithophile product factor (Si/Al crust oxide under crust G-min + fO₂).
goldschmidtProductLithophile :: GoldschmidtProductFactor
goldschmidtProductLithophile =
  GoldschmidtProductFactor
    { productOre =
        Class6OreWitness
          { oreTag = "si_silicate_crust_ore"
          , oreClassIndex = class6OrePatternIndex
          }
    , productGStability =
        Class7GStabilityWitness
          { gMinTag = "crust_oxide_g_min_hull"
          , gClassIndex = class7GStabilityPatternIndex
          }
    , productFo2 =
        Class17Fo2Witness
          { fo2LogBar = -1
          , fo2LadderTag = "crust_intermediate_fo2_ladder"
          , fo2ClassIndex = class17Fo2PatternIndex
          }
    }

-- | Pinned chalcophile product factor (Cu sulfide under sulfide G-min partition).
goldschmidtProductChalcophile :: GoldschmidtProductFactor
goldschmidtProductChalcophile =
  GoldschmidtProductFactor
    { productOre =
        Class6OreWitness
          { oreTag = "cu_sulfide_paragenesis"
          , oreClassIndex = class6OrePatternIndex
          }
    , productGStability =
        Class7GStabilityWitness
          { gMinTag = "sulfide_g_min_partition"
          , gClassIndex = class7GStabilityPatternIndex
          }
    , productFo2 =
        Class17Fo2Witness
          { fo2LogBar = -1
          , fo2LadderTag = "crust_intermediate_fo2_ladder"
          , fo2ClassIndex = class17Fo2PatternIndex
          }
    }

-- | Whether all three class witnesses are honest on the product factor.
goldschmidtProductFactorHonest :: GoldschmidtProductFactor -> Bool
goldschmidtProductFactorHonest factor =
  oreClassIndex (productOre factor) == class6OrePatternIndex
    && gClassIndex (productGStability factor) == class7GStabilityPatternIndex
    && fo2ClassIndex (productFo2 factor) == class17Fo2PatternIndex
    && not (null (oreTag (productOre factor)))
    && not (null (gMinTag (productGStability factor)))
    && not (null (fo2LadderTag (productFo2 factor)))

-- | Class indices pinned to 6 ⊗ 7 ⊗ 17.
goldschmidtClassIndicesMatchX5 :: GoldschmidtProductFactor -> Bool
goldschmidtClassIndicesMatchX5 factor =
  oreClassIndex (productOre factor) == class6OrePatternIndex
    && gClassIndex (productGStability factor) == class7GStabilityPatternIndex
    && fo2ClassIndex (productFo2 factor) == class17Fo2PatternIndex

-- | **Goldschmidt** affinity witness — derived from Ore⊗G⊗fO₂ product, not XOR enum.
data GoldschmidtAffinityWitness = GoldschmidtAffinityWitness
  { affinityTag :: GoldschmidtAffinityTag
  , affinityProduct :: GoldschmidtProductFactor
  }
  deriving (Eq, Show)

-- | Pinned siderophile affinity derived from product factor.
goldschmidtAffinitySiderophile :: GoldschmidtAffinityWitness
goldschmidtAffinitySiderophile =
  GoldschmidtAffinityWitness
    { affinityTag = SiderophileAffinity
    , affinityProduct = goldschmidtProductSiderophile
    }

-- | Pinned lithophile affinity derived from product factor.
goldschmidtAffinityLithophile :: GoldschmidtAffinityWitness
goldschmidtAffinityLithophile =
  GoldschmidtAffinityWitness
    { affinityTag = LithophileAffinity
    , affinityProduct = goldschmidtProductLithophile
    }

-- | Pinned chalcophile affinity derived from product factor.
goldschmidtAffinityChalcophile :: GoldschmidtAffinityWitness
goldschmidtAffinityChalcophile =
  GoldschmidtAffinityWitness
    { affinityTag = ChalcophileAffinity
    , affinityProduct = goldschmidtProductChalcophile
    }

-- | Whether affinity is honestly derived from product factor (not standalone XOR bucket).
goldschmidtAffinityDerivedFromProduct :: GoldschmidtAffinityWitness -> Bool
goldschmidtAffinityDerivedFromProduct witness =
  goldschmidtProductFactorHonest (affinityProduct witness)
    && goldschmidtClassIndicesMatchX5 (affinityProduct witness)

-- | A **Goldschmidt** **conservation** path at a refinement level.
data GoldschmidtConservationPath = GoldschmidtConservationPath
  { goldschmidtPathLevel :: Int
  , goldschmidtPathElementZ :: GoldschmidtElementZ
  , goldschmidtPathOreForm :: GoldschmidtOreForm
  , goldschmidtPathAffinity :: GoldschmidtAffinityWitness
  }
  deriving (Eq, Show)

-- | Whether a **Goldschmidt** path is non-trivial (level > 0).
goldschmidtConservationPathIsNontrivial :: GoldschmidtConservationPath -> Bool
goldschmidtConservationPathIsNontrivial path = goldschmidtPathLevel path > 0

-- | Whether path is closed-shell He no-ore (Z=2 — no ore placement).
goldschmidtPathIsClosedShellNoOre :: GoldschmidtConservationPath -> Bool
goldschmidtPathIsClosedShellNoOre path =
  goldschmidtPathOreForm path == HeClosedShellNoOre
    && goldschmidtElementZNumeric (goldschmidtPathElementZ path) == 2

-- | Iron metal **Goldschmidt** **conservation** path @ L1 scaffold (Fe Z=26 siderophile).
goldschmidtConservationPathFeMetalL1 :: GoldschmidtConservationPath
goldschmidtConservationPathFeMetalL1 =
  GoldschmidtConservationPath
    { goldschmidtPathLevel = 1
    , goldschmidtPathElementZ = GoldschmidtElementIron
    , goldschmidtPathOreForm = FeMetalForm
    , goldschmidtPathAffinity = goldschmidtAffinitySiderophile
    }

-- | Iron oxide **Goldschmidt** **conservation** path @ L1 scaffold (Fe Z=26 lithophile).
goldschmidtConservationPathFeOxideL1 :: GoldschmidtConservationPath
goldschmidtConservationPathFeOxideL1 =
  GoldschmidtConservationPath
    { goldschmidtPathLevel = 1
    , goldschmidtPathElementZ = GoldschmidtElementIron
    , goldschmidtPathOreForm = FeOxideForm
    , goldschmidtPathAffinity = goldschmidtAffinityLithophile
    }

-- | Iron sulfide **Goldschmidt** **conservation** path @ L1 scaffold (Fe Z=26 chalcophile).
goldschmidtConservationPathFeSulfideL1 :: GoldschmidtConservationPath
goldschmidtConservationPathFeSulfideL1 =
  GoldschmidtConservationPath
    { goldschmidtPathLevel = 1
    , goldschmidtPathElementZ = GoldschmidtElementIron
    , goldschmidtPathOreForm = FeSulfideForm
    , goldschmidtPathAffinity = goldschmidtAffinityChalcophile
    }

-- | Copper **Goldschmidt** **conservation** path @ L1 scaffold (Cu Z=29 chalcophile).
goldschmidtConservationPathCuL1 :: GoldschmidtConservationPath
goldschmidtConservationPathCuL1 =
  GoldschmidtConservationPath
    { goldschmidtPathLevel = 1
    , goldschmidtPathElementZ = GoldschmidtElementCopper
    , goldschmidtPathOreForm = CuSulfideForm
    , goldschmidtPathAffinity = goldschmidtAffinityChalcophile
    }

-- | Silicon **Goldschmidt** **conservation** path @ L1 scaffold (Si Z=14 lithophile).
goldschmidtConservationPathSiL1 :: GoldschmidtConservationPath
goldschmidtConservationPathSiL1 =
  GoldschmidtConservationPath
    { goldschmidtPathLevel = 1
    , goldschmidtPathElementZ = GoldschmidtElementSilicon
    , goldschmidtPathOreForm = SiSilicateForm
    , goldschmidtPathAffinity = goldschmidtAffinityLithophile
    }

-- | Helium closed-shell **Goldschmidt** path @ L1 scaffold (He Z=2 no-ore).
goldschmidtConservationPathHeNoOreL1 :: GoldschmidtConservationPath
goldschmidtConservationPathHeNoOreL1 =
  GoldschmidtConservationPath
    { goldschmidtPathLevel = 1
    , goldschmidtPathElementZ = GoldschmidtElementHelium
    , goldschmidtPathOreForm = HeClosedShellNoOre
    , goldschmidtPathAffinity = goldschmidtAffinityLithophile
    }

-- | Class 6⊗7⊗17 indices are strictly ordered and pinned.
goldschmidtClassIndicesOk :: Bool
goldschmidtClassIndicesOk =
  class6OrePatternIndex == 6
    && class7GStabilityPatternIndex == 7
    && class17Fo2PatternIndex == 17
    && class6OrePatternIndex < class7GStabilityPatternIndex
    && class7GStabilityPatternIndex < class17Fo2PatternIndex

-- | Ore (6) lift on **Goldschmidt** identity (knowing fiber — Unwired scaffold).
liftOreWitness :: Int -> Int
liftOreWitness = id

-- | G (7) lift on **Goldschmidt** identity (knowing fiber — Unwired scaffold).
liftGStabilityWitness :: Int -> Int
liftGStabilityWitness = id

-- | fO₂ (17) lift on **Goldschmidt** identity (knowing fiber — Unwired scaffold).
liftFo2Witness :: Int -> Int
liftFo2Witness = id

-- | Direct Ore⊗G⊗fO₂ product on **Goldschmidt** identity (knowing fiber — Unwired scaffold).
directGoldschmidtProduct :: Int -> Int
directGoldschmidtProduct = id

-- | **Goldschmidt** identity conserved: composed Ore⊗G⊗fO₂ equals direct product.
goldschmidtIdentityConserved :: Int -> Bool
goldschmidtIdentityConserved witness =
  liftFo2Witness (liftGStabilityWitness (liftOreWitness witness))
    == directGoldschmidtProduct witness

-- | Typed **Goldschmidt** **conservation** along the Ore⊗G⊗fO₂ commuting diagram.
goldschmidtCommuteConservation :: Int -> Bool
goldschmidtCommuteConservation = goldschmidtIdentityConserved

-- | Verdict for GOLDSCHMIDT-01 **ore-class** **conservation** close (fail-closed).
data GoldschmidtConservationVerdict
  = GoldschmidtConservationDesignOk
  | GoldschmidtConservationNamedOk
  | GoldschmidtConservationTrivialRefuse
  | GoldschmidtConservationGreenInventRefuse
  | GoldschmidtConservationProvedWithoutBarRefuse
  | GoldschmidtConservationFolkloreListRefuse
  | GoldschmidtConservationClosedShellNoOreOk
  deriving (Eq, Show)

-- | Evaluate **Goldschmidt** **conservation** under GOLDSCHMIDT-01 bar (fail-closed).
evaluateGoldschmidtConservation ::
  GoldschmidtConservationModality
  -> GoldschmidtConservationPath
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> GoldschmidtConservationVerdict
evaluateGoldschmidtConservation
  modality
  path
  claimPhysicsGreen
  claimProved
  claimFolkloreList
  claimXorEnum
  | claimPhysicsGreen = GoldschmidtConservationGreenInventRefuse
  | claimFolkloreList = GoldschmidtConservationFolkloreListRefuse
  | claimXorEnum = GoldschmidtConservationTrivialRefuse
  | claimProved = GoldschmidtConservationProvedWithoutBarRefuse
  | goldschmidtPathIsClosedShellNoOre path =
      GoldschmidtConservationClosedShellNoOreOk
  | not (goldschmidtConservationPathIsNontrivial path) =
      GoldschmidtConservationTrivialRefuse
  | not (isValidIupacZ (goldschmidtPathElementZ path)) =
      GoldschmidtConservationTrivialRefuse
  | not (goldschmidtAffinityDerivedFromProduct (goldschmidtPathAffinity path)) =
      GoldschmidtConservationTrivialRefuse
  | otherwise =
      case modality of
        GoldschmidtConservationUnwired ->
          if threeAffinitiesNamed then GoldschmidtConservationNamedOk else GoldschmidtConservationDesignOk
        GoldschmidtConservationAssumed -> GoldschmidtConservationDesignOk
        GoldschmidtConservationSurrogate -> GoldschmidtConservationDesignOk
        GoldschmidtConservationProved -> GoldschmidtConservationProvedWithoutBarRefuse

-- | Three named lithophile / chalcophile / siderophile affinities on scaffold.
threeAffinitiesNamed :: Bool
threeAffinitiesNamed =
  goldschmidtAffinityTagCount == 3
    && goldschmidtAffinityDerivedFromProduct goldschmidtAffinitySiderophile
    && goldschmidtAffinityDerivedFromProduct goldschmidtAffinityLithophile
    && goldschmidtAffinityDerivedFromProduct goldschmidtAffinityChalcophile
    && affinityTag goldschmidtAffinitySiderophile == SiderophileAffinity
    && affinityTag goldschmidtAffinityLithophile == LithophileAffinity
    && affinityTag goldschmidtAffinityChalcophile == ChalcophileAffinity

-- | Unwired **Goldschmidt** modality OK without thermo break.
unwiredGoldschmidtDesignOk :: Bool
unwiredGoldschmidtDesignOk =
  evaluateGoldschmidtConservation
    GoldschmidtConservationUnwired
    goldschmidtConservationPathFeMetalL1
    False
    False
    False
    False
    == GoldschmidtConservationNamedOk

-- | Three named lithophile / chalcophile / siderophile affinities on scaffold.
threeAffinitiesNamedOk :: Bool
threeAffinitiesNamedOk =
  threeAffinitiesNamed
    && goldschmidtAffinityTagCount == 3
    && goldschmidtClassIndicesOk

-- | Composed Ore⊗G⊗fO₂ equals direct product (**Goldschmidt** **conservation**).
composedEqualsDirectOk :: Bool
composedEqualsDirectOk =
  goldschmidtCommuteConservation 42
    && goldschmidtIdentityConserved 42
    && liftFo2Witness (liftGStabilityWitness (liftOreWitness 42))
      == directGoldschmidtProduct 42

-- | Lithophile / chalcophile / siderophile concurrent Ore⊗G⊗fO₂ product — not XOR enum.
goldschmidtProductNotXorOk :: Bool
goldschmidtProductNotXorOk =
  goldschmidtAffinityDerivedFromProduct goldschmidtAffinitySiderophile
    && goldschmidtAffinityDerivedFromProduct goldschmidtAffinityLithophile
    && goldschmidtAffinityDerivedFromProduct goldschmidtAffinityChalcophile
    && goldschmidtClassIndicesMatchX5 (affinityProduct goldschmidtAffinitySiderophile)
    && goldschmidtClassIndicesMatchX5 (affinityProduct goldschmidtAffinityLithophile)
    && goldschmidtClassIndicesMatchX5 (affinityProduct goldschmidtAffinityChalcophile)
    && goldschmidtAffinitySiderophile /= goldschmidtAffinityLithophile
    && goldschmidtAffinityLithophile /= goldschmidtAffinityChalcophile

-- | Fe Z=26 same Z across metal / oxide / sulfide ore forms.
feSameZMetalOxideSulfideOk :: Bool
feSameZMetalOxideSulfideOk =
  goldschmidtElementZNumeric GoldschmidtElementIron == 26
    && goldschmidtPathElementZ goldschmidtConservationPathFeMetalL1
      == GoldschmidtElementIron
    && goldschmidtPathElementZ goldschmidtConservationPathFeOxideL1
      == GoldschmidtElementIron
    && goldschmidtPathElementZ goldschmidtConservationPathFeSulfideL1
      == GoldschmidtElementIron
    && goldschmidtPathOreForm goldschmidtConservationPathFeMetalL1 == FeMetalForm
    && goldschmidtPathOreForm goldschmidtConservationPathFeOxideL1 == FeOxideForm
    && goldschmidtPathOreForm goldschmidtConservationPathFeSulfideL1 == FeSulfideForm

-- | Cu **Goldschmidt** anchor carries valid Z=29 pin.
copperElementZValid :: Bool
copperElementZValid =
  isValidIupacZ GoldschmidtElementCopper
    && goldschmidtElementZNumeric GoldschmidtElementCopper == 29
    && goldschmidtPathElementZ goldschmidtConservationPathCuL1
      == GoldschmidtElementCopper

-- | Si **Goldschmidt** anchor carries valid Z=14 pin.
siliconElementZValid :: Bool
siliconElementZValid =
  isValidIupacZ GoldschmidtElementSilicon
    && goldschmidtElementZNumeric GoldschmidtElementSilicon == 14
    && goldschmidtPathElementZ goldschmidtConservationPathSiL1
      == GoldschmidtElementSilicon

-- | He Z=2 closed-shell no-ore scaffold honest.
heliumClosedShellNoOreOk :: Bool
heliumClosedShellNoOreOk =
  goldschmidtElementZNumeric GoldschmidtElementHelium == 2
    && goldschmidtPathIsClosedShellNoOre goldschmidtConservationPathHeNoOreL1
    && evaluateGoldschmidtConservation
      GoldschmidtConservationUnwired
      goldschmidtConservationPathHeNoOreL1
      False
      False
      False
      False
      == GoldschmidtConservationClosedShellNoOreOk

-- | Assumed **Goldschmidt** modality OK without thermo break (design scaffold).
assumedGoldschmidtDesignOk :: Bool
assumedGoldschmidtDesignOk =
  evaluateGoldschmidtConservation
    GoldschmidtConservationAssumed
    goldschmidtConservationPathFeMetalL1
    False
    False
    False
    False
    == GoldschmidtConservationDesignOk

-- | Surrogate **Goldschmidt** modality OK without thermo break (design scaffold).
surrogateGoldschmidtDesignOk :: Bool
surrogateGoldschmidtDesignOk =
  evaluateGoldschmidtConservation
    GoldschmidtConservationSurrogate
    goldschmidtConservationPathFeMetalL1
    False
    False
    False
    False
    == GoldschmidtConservationDesignOk

-- | GREEN invent on **Goldschmidt** **conservation** promotion is refused.
greenInventGoldschmidtRefuse :: Bool
greenInventGoldschmidtRefuse =
  evaluateGoldschmidtConservation
    GoldschmidtConservationUnwired
    goldschmidtConservationPathFeMetalL1
    True
    False
    False
    False
    == GoldschmidtConservationGreenInventRefuse

-- | Folklore ore list smuggle is refused (not monoidal Ore morphism).
folkloreListRefuse :: Bool
folkloreListRefuse =
  evaluateGoldschmidtConservation
    GoldschmidtConservationUnwired
    goldschmidtConservationPathFeMetalL1
    False
    False
    True
    False
    == GoldschmidtConservationFolkloreListRefuse

-- | Trivial (level-0) **Goldschmidt** path is refused (fail-closed).
trivialRefuse :: Bool
trivialRefuse =
  let trivialPath =
        goldschmidtConservationPathFeMetalL1 {goldschmidtPathLevel = 0}
   in evaluateGoldschmidtConservation
        GoldschmidtConservationUnwired
        trivialPath
        False
        False
        False
        False
        == GoldschmidtConservationTrivialRefuse

-- | Proved Goldschmidt split without path census is refused.
provedWithoutBarRefuse :: Bool
provedWithoutBarRefuse =
  evaluateGoldschmidtConservation
    GoldschmidtConservationUnwired
    goldschmidtConservationPathFeMetalL1
    False
    True
    False
    False
    == GoldschmidtConservationProvedWithoutBarRefuse
    && evaluateGoldschmidtConservation
      GoldschmidtConservationProved
      goldschmidtConservationPathFeMetalL1
      False
      False
      False
      False
      == GoldschmidtConservationProvedWithoutBarRefuse

-- | Four-step GOLDSCHMIDT-01 **Goldschmidt** lattice scaffold pinned.
goldschmidtLatticeScaffold :: Bool
goldschmidtLatticeScaffold =
  goldschmidtLatticeCount == 4
    && unwiredGoldschmidtDesignOk
    && threeAffinitiesNamedOk
    && goldschmidtClassIndicesOk
    && composedEqualsDirectOk
    && goldschmidtProductNotXorOk
    && feSameZMetalOxideSulfideOk
    && copperElementZValid
    && siliconElementZValid
    && heliumClosedShellNoOreOk
    && assumedGoldschmidtDesignOk
    && surrogateGoldschmidtDesignOk

-- | **Goldschmidt** lattice is structure scaffold — not 118² GREEN periodic table.
goldschmidtLatticeNotGreenTable :: Bool
goldschmidtLatticeNotGreenTable =
  goldschmidtLatticeCount == 4
    && goldschmidtLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && goldschmidtAffinityTagCount /= iupacTableCardinality * iupacTableCardinality
    && goldschmidtOreFormCount /= iupacTableCardinality * iupacTableCardinality
    && goldschmidtElementZCount /= iupacTableCardinality * iupacTableCardinality

-- | **Goldschmidt** **conservation** law cells scaffold pinned.
goldschmidtConservationLawsScaffold :: Bool
goldschmidtConservationLawsScaffold =
  threeAffinitiesNamedOk
    && goldschmidtClassIndicesOk
    && composedEqualsDirectOk
    && goldschmidtProductNotXorOk
    && feSameZMetalOxideSulfideOk
    && copperElementZValid
    && siliconElementZValid
    && heliumClosedShellNoOreOk
    && greenInventGoldschmidtRefuse
    && folkloreListRefuse
    && trivialRefuse
    && provedWithoutBarRefuse

-- | **Goldschmidt** law cells are structure scaffold — not 118² GREEN periodic table.
goldschmidtConservationLawsNotGreenTable :: Bool
goldschmidtConservationLawsNotGreenTable =
  goldschmidtConservationLawsScaffold
    && goldschmidtAffinityTagCount /= 118 * 118
    && goldschmidtOreFormCount /= 118 * 118

-- | GOLDSCHMIDT-01 **ore-class** **conservation** claims route to knowing / quantum fiber.
goldschmidtKnowingFiberOk :: Bool
goldschmidtKnowingFiberOk = True

-- | GOLDSCHMIDT-01 Goldschmidt invent refuse-closed scaffold witness.
goldschmidtInventRefuse :: Bool
goldschmidtInventRefuse = not goldschmidtProved

-- | **Goldschmidt** lattice steps are concurrent Π_c — not XOR enum bucket.
goldschmidtLatticeNotXor :: Bool
goldschmidtLatticeNotXor =
  unwiredGoldschmidtDesignOk
    && assumedGoldschmidtDesignOk
    && surrogateGoldschmidtDesignOk
    && composedEqualsDirectOk
    && goldschmidtProductNotXorOk
    && greenInventGoldschmidtRefuse
    && folkloreListRefuse

-- | GOLDSCHMIDT-01 Goldschmidt proved (always false on this Unwired cell).
goldschmidtProved :: Bool
goldschmidtProved = False

-- | One axiom framing: second law + **conservation** for GOLDSCHMIDT-01 **ore-class** scaffold.
goldschmidtConservationFraming :: String
goldschmidtConservationFraming =
  "second_law_conservation_goldschmidt_one_axiom"

-- | Single design axiom: second law + **conservation** GOLDSCHMIDT-01 **ore-class** (not second axiom).
goldschmidtConservationAxiom :: Bool
goldschmidtConservationAxiom =
  goldschmidtLatticeScaffold
    && goldschmidtLatticeNotGreenTable
    && goldschmidtConservationLawsScaffold
    && goldschmidtConservationLawsNotGreenTable
    && goldschmidtKnowingFiberOk
    && threeAffinitiesNamedOk
    && goldschmidtClassIndicesOk
    && composedEqualsDirectOk
    && goldschmidtProductNotXorOk
    && feSameZMetalOxideSulfideOk
    && copperElementZValid
    && siliconElementZValid
    && heliumClosedShellNoOreOk
    && greenInventGoldschmidtRefuse
    && folkloreListRefuse
    && trivialRefuse
    && provedWithoutBarRefuse
    && goldschmidtInventRefuse
    && goldschmidtLatticeNotXor
    && not goldschmidtProved
    && goldschmidtConservationFraming
      == "second_law_conservation_goldschmidt_one_axiom"

goldschmidtConservationNamed :: String
goldschmidtConservationNamed =
  "goldschmidtConservation: GoldschmidtConservationModality Unwired Assumed Proved Surrogate four-step lattice goldschmidtProved false evaluateGoldschmidtConservation goldschmidtCommuteConservation lithophile chalcophile siderophile concurrent Ore otimes G otimes fO2 product not XOR Fe Z=26 same Z metal oxide sulfide Cu Z=29 Si Z=14 He Z=2 closed-shell no-ore folklore GREEN trivial proved-without-bar refuse class 6 otimes 7 otimes 17 knowing fiber second law conservation one axiom not 118 squared GREEN table"

-- | Upstream Goldschmidt ore authority (cited, not forked).
goldschmidtOreAuthority :: String
goldschmidtOreAuthority = "umst/umst-chem/src/x_rows/goldschmidt_ore.rs"

-- | L0 GOLDSCHMIDT-01 scaffold authority (crosswalk).
chemL0Goldschmidt01Authority :: String
chemL0Goldschmidt01Authority = "CHEM-L0-GOLDSCHMIDT-01"

goldschmidtConservationCellId :: String
goldschmidtConservationCellId = "CHEM-FORMAL-Q-HS-GOLDSCHMIDT-CONSERVATION"

-- | Non-claim fence — GOLDSCHMIDT-01 **ore-class** **conservation** Unwired ≠ Proved GREEN.
goldschmidtConservationNonClaim :: String
goldschmidtConservationNonClaim =
  "CHEM-FORMAL-Q-HS-GOLDSCHMIDT-CONSERVATION GoldschmidtConservationModality Unwired Assumed Proved Surrogate four-step lattice goldschmidtProved false evaluateGoldschmidtConservation goldschmidtCommuteConservation lithophile chalcophile siderophile concurrent Ore otimes G otimes fO2 product not XOR Fe Z=26 same Z metal oxide sulfide Cu Z=29 Si Z=14 He Z=2 closed-shell no-ore folklore GREEN trivial proved-without-bar refuse class 6 otimes 7 otimes 17 Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing GOLDSCHMIDT-01 **ore-class** **conservation** scaffold.
goldschmidtConservationPhysicsGreenAuthorized :: Bool
goldschmidtConservationPhysicsGreenAuthorized = False

goldschmidtConservationPhysicsGreenFalse :: Bool
goldschmidtConservationPhysicsGreenFalse =
  not goldschmidtConservationPhysicsGreenAuthorized

goldschmidtConservationModalityUnwired :: Bool
goldschmidtConservationModalityUnwired =
  goldschmidtConservationModalityCurrent == GoldschmidtConservationUnwired

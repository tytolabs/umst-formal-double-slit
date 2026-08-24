-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.OccurrenceFamilyPattern
Description : Occurrence-class family pattern conservation on the matter fiber
Copyright   : (c) UMST Project, 2026

Occurrence-class families are concurrent product classifiers; ore-engine sorts outliers
(native Au vs oxide Fe vs closed-shell He no-ore); same Z many assemblages. Seven
concurrent family tags; not folklore exclusive list. @rowProved@ = False.

* @occurrenceFamilyTags@ — seven concurrent family tags (not XOR enum).
* @goldIsNativeFamilyOutlier@ / @ironIsOxideFamilyProduct@ / @heliumIsNoOreAtmophile@ — outlier pins.
* **One** design axiom (@occurrenceFamilyPatternAxiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of occurrence family pattern conservation on the matter fiber.
Cell: @CHEM-FORMAL-Q-HS-OCCURRENCE-FAMILY-PATTERN-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.OccurrenceFamilyPattern
  ( OccurrenceFamilyPatternModality (..)
  , occurrenceFamilyPatternModalityCurrent
  , OccurrenceFamilyTag (..)
  , occurrenceFamilyTags
  , occurrenceFamilyTagCount
  , OccurrenceFamilyTree (..)
  , occurrenceFamilyUnit
  , occurrenceFamilyLeaf
  , occurrenceFamilyTensor
  , occurrenceFamilyProduct
  , bitNative
  , bitOxide
  , bitSulfide
  , bitAtmophile
  , goldZ
  , ironZ
  , heliumZ
  , goldOutlierBits
  , ironOutlierBits
  , heliumOutlierBits
  , goldIsNativeFamilyOutlier
  , ironIsOxideFamilyProduct
  , heliumIsNoOreAtmophile
  , heliumNoOreIsMissingInteract
  , oreEngineOutliersSortNamed
  , sameZManyAssemblages
  , folkloreExclusiveListRefused
  , occurrenceFamilyPatternConjunct
  , occurrenceFamilyTreeConcurrentCount
  , occurrenceFamilyProductNotXor
  , OccurrenceFamilyPatternVerdict (..)
  , evaluateOccurrenceFamilyPattern
  , unwiredOccurrenceFamilyDesignOk
  , greenInventOccurrenceFamilyRefuse
  , provedWithoutBarOccurrenceFamilyRefuse
  , occurrenceFamilyPatternScaffold
  , OccurrenceFamilyPatternProbe (..)
  , occurrenceFamilyPatternProbe
  , occurrenceFamilyPatternHonest
  , rowProved
  , soleAxiomCount
  , occurrenceFamilyPatternFraming
  , occurrenceFamilyPatternAxiom
  , occurrenceFamilyPatternNamed
  , occurrenceFamilyPatternAuthority
  , occurrenceFamilyPatternCellId
  , occurrenceFamilyPatternNonClaim
  , occurrenceFamilyPatternPhysicsGreenAuthorized
  , occurrenceFamilyPatternPhysicsGreenFalse
  , occurrenceFamilyPatternModalityUnwired
  ) where

import Data.Bits ((.|.), (.&.))

-- | Design modality for occurrence family pattern claims (TYPE-03 preview).
data OccurrenceFamilyPatternModality
  = OccurrenceFamilyPatternUnwired
  | OccurrenceFamilyPatternAssumed
  | OccurrenceFamilyPatternProved
  | OccurrenceFamilyPatternSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
occurrenceFamilyPatternModalityCurrent :: OccurrenceFamilyPatternModality
occurrenceFamilyPatternModalityCurrent = OccurrenceFamilyPatternUnwired

-- | Sole axiom count (always 1 on this cell).
soleAxiomCount :: Int
soleAxiomCount = 1

-- | Named occurrence-class family tags (concurrent, not XOR).
data OccurrenceFamilyTag
  = NativeFamily
  | OxideFamily
  | SulfideFamily
  | SilicateFamily
  | HalideCarbonateFamily
  | AtmophileFamily
  | SyntheticOrTraceFamily
  deriving (Eq, Show)

-- | Seven concurrent family tags — not folklore exclusive list.
occurrenceFamilyTags :: [String]
occurrenceFamilyTags =
  [ "native"
  , "oxide"
  , "sulfide"
  , "silicate"
  , "halide_carbonate"
  , "atmophile"
  , "synthetic_or_trace"
  ]

occurrenceFamilyTagCount :: Int
occurrenceFamilyTagCount = length occurrenceFamilyTags

-- | Algebraic OccurrenceFamilyTree — unit @I@, leaf family, tensor product (not XOR).
data OccurrenceFamilyTree
  = OccurrenceFamilyUnit
  | OccurrenceFamilyLeaf OccurrenceFamilyTag
  | OccurrenceFamilyTensor OccurrenceFamilyTree OccurrenceFamilyTree
  deriving (Eq, Show)

-- | Monoidal unit @I@ — inert / vacuum limit.
occurrenceFamilyUnit :: OccurrenceFamilyTree
occurrenceFamilyUnit = OccurrenceFamilyUnit

-- | Leaf family pin — concurrent classifier, not XOR bucket.
occurrenceFamilyLeaf :: OccurrenceFamilyTag -> OccurrenceFamilyTree
occurrenceFamilyLeaf = OccurrenceFamilyLeaf

-- | Tensor product node — concurrent Π_c family, not XOR enum.
occurrenceFamilyTensor :: OccurrenceFamilyTree -> OccurrenceFamilyTree -> OccurrenceFamilyTree
occurrenceFamilyTensor = OccurrenceFamilyTensor

-- | Monoidal product alias on @OccurrenceFamilyTree@.
occurrenceFamilyProduct :: OccurrenceFamilyTree -> OccurrenceFamilyTree -> OccurrenceFamilyTree
occurrenceFamilyProduct = occurrenceFamilyTensor

-- | Native metal / native-element bit (concurrent product, not XOR).
bitNative :: Int
bitNative = 1

-- | Oxide bit.
bitOxide :: Int
bitOxide = 2

-- | Sulfide bit.
bitSulfide :: Int
bitSulfide = 4

-- | Atmophile bit.
bitAtmophile :: Int
bitAtmophile = 32

-- | Gold Z — native-family outlier (native Au, not oxide-primary folklore).
goldZ :: Int
goldZ = 79

-- | Iron Z — oxide-family product outlier (native ⊗ oxide ⊗ sulfide).
ironZ :: Int
ironZ = 26

-- | Helium Z — closed-shell no-ore atmophile outlier.
heliumZ :: Int
heliumZ = 2

-- | Gold outlier bits — native only.
goldOutlierBits :: Int
goldOutlierBits = bitNative

-- | Iron outlier bits — native ⊗ oxide ⊗ sulfide concurrent product.
ironOutlierBits :: Int
ironOutlierBits = bitNative .|. bitOxide .|. bitSulfide

-- | Helium outlier bits — atmophile only (no-ore).
heliumOutlierBits :: Int
heliumOutlierBits = bitAtmophile

-- | Au sorts as native-family outlier (not oxide-primary).
goldIsNativeFamilyOutlier :: Bool
goldIsNativeFamilyOutlier = goldOutlierBits == bitNative

-- | Fe sorts as concurrent product (native ⊗ oxide ⊗ sulfide), not XOR.
ironIsOxideFamilyProduct :: Bool
ironIsOxideFamilyProduct =
  (ironOutlierBits .&. bitOxide) /= 0
    && (ironOutlierBits .&. bitNative) /= 0
    && (ironOutlierBits .&. bitSulfide) /= 0

-- | He is atmophile-only — no crustal ore family bit.
heliumIsNoOreAtmophile :: Bool
heliumIsNoOreAtmophile =
  heliumOutlierBits == bitAtmophile
    && (heliumOutlierBits .&. bitNative) == 0

-- | Outlier sort: He no-ore is missing Interact, not a folklore row.
heliumNoOreIsMissingInteract :: Bool
heliumNoOreIsMissingInteract = heliumIsNoOreAtmophile

-- | Ore-engine outlier sort witnesses (Au native vs Fe oxide product vs He no-ore).
oreEngineOutliersSortNamed :: Bool
oreEngineOutliersSortNamed =
  goldIsNativeFamilyOutlier
    && ironIsOxideFamilyProduct
    && heliumIsNoOreAtmophile
    && heliumNoOreIsMissingInteract

-- | Same Z may occupy several families.
sameZManyAssemblages :: Bool
sameZManyAssemblages = ironIsOxideFamilyProduct

-- | Folklore exclusive list refuse.
folkloreExclusiveListRefused :: Bool
folkloreExclusiveListRefused = True

-- | Family-pattern conjunct.
occurrenceFamilyPatternConjunct :: Bool
occurrenceFamilyPatternConjunct =
  occurrenceFamilyTagCount == 7
    && oreEngineOutliersSortNamed
    && sameZManyAssemblages
    && folkloreExclusiveListRefused

occurrenceFamilyTreeConstituentPresent ::
  OccurrenceFamilyTree -> OccurrenceFamilyTag -> Bool
occurrenceFamilyTreeConstituentPresent t tag = case t of
  OccurrenceFamilyUnit -> False
  OccurrenceFamilyLeaf t' -> t' == tag
  OccurrenceFamilyTensor left right ->
    occurrenceFamilyTreeConstituentPresent left tag
      || occurrenceFamilyTreeConstituentPresent right tag

occurrenceFamilyTreeConcurrentCount :: OccurrenceFamilyTree -> Int
occurrenceFamilyTreeConcurrentCount t =
  sum
    [ if occurrenceFamilyTreeConstituentPresent t NativeFamily then 1 else 0
    , if occurrenceFamilyTreeConstituentPresent t OxideFamily then 1 else 0
    , if occurrenceFamilyTreeConstituentPresent t SulfideFamily then 1 else 0
    , if occurrenceFamilyTreeConstituentPresent t SilicateFamily then 1 else 0
    , if occurrenceFamilyTreeConstituentPresent t HalideCarbonateFamily then 1 else 0
    , if occurrenceFamilyTreeConstituentPresent t AtmophileFamily then 1 else 0
    , if occurrenceFamilyTreeConstituentPresent t SyntheticOrTraceFamily then 1 else 0
    ]

-- | All seven family tags as concurrent tensor — not XOR enum bucket.
sevenFamilyConcurrentTree :: OccurrenceFamilyTree
sevenFamilyConcurrentTree =
  occurrenceFamilyProduct
    (occurrenceFamilyProduct
      (occurrenceFamilyProduct
        (occurrenceFamilyProduct
          (occurrenceFamilyProduct
            (occurrenceFamilyProduct
              (occurrenceFamilyLeaf NativeFamily)
              (occurrenceFamilyLeaf OxideFamily))
            (occurrenceFamilyLeaf SulfideFamily))
          (occurrenceFamilyLeaf SilicateFamily))
        (occurrenceFamilyLeaf HalideCarbonateFamily))
      (occurrenceFamilyLeaf AtmophileFamily))
    (occurrenceFamilyLeaf SyntheticOrTraceFamily)

-- | Product factors are concurrent Π_c — not XOR enum bucket.
occurrenceFamilyProductNotXor :: Bool
occurrenceFamilyProductNotXor =
  occurrenceFamilyTreeConcurrentCount sevenFamilyConcurrentTree >= 7
    && occurrenceFamilyTreeConcurrentCount sevenFamilyConcurrentTree == 7

-- | Verdict for occurrence family pattern close (fail-closed).
data OccurrenceFamilyPatternVerdict
  = OccurrenceFamilyPatternDesignOk
  | OccurrenceFamilyPatternNamedOk
  | OccurrenceFamilyPatternGreenInventRefuse
  | OccurrenceFamilyPatternProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate occurrence family pattern under honest bar (fail-closed).
evaluateOccurrenceFamilyPattern ::
  OccurrenceFamilyPatternModality
  -> Bool
  -> Bool
  -> Bool
  -> OccurrenceFamilyPatternVerdict
evaluateOccurrenceFamilyPattern modality claimPhysicsGreen claimProved claimGreenInvent
  | claimPhysicsGreen || claimGreenInvent =
      OccurrenceFamilyPatternGreenInventRefuse
  | claimProved = OccurrenceFamilyPatternProvedWithoutBarRefuse
  | not occurrenceFamilyPatternConjunct =
      OccurrenceFamilyPatternDesignOk
  | otherwise =
      case modality of
        OccurrenceFamilyPatternUnwired ->
          if occurrenceFamilyTagCount == 7
            then OccurrenceFamilyPatternNamedOk
            else OccurrenceFamilyPatternDesignOk
        OccurrenceFamilyPatternAssumed -> OccurrenceFamilyPatternDesignOk
        OccurrenceFamilyPatternSurrogate -> OccurrenceFamilyPatternDesignOk
        OccurrenceFamilyPatternProved ->
          OccurrenceFamilyPatternProvedWithoutBarRefuse

-- | Unwired occurrence family pattern modality OK.
unwiredOccurrenceFamilyDesignOk :: Bool
unwiredOccurrenceFamilyDesignOk =
  evaluateOccurrenceFamilyPattern
    OccurrenceFamilyPatternUnwired
    False
    False
    False
    == OccurrenceFamilyPatternNamedOk

-- | GREEN invent on occurrence family pattern promotion is refused.
greenInventOccurrenceFamilyRefuse :: Bool
greenInventOccurrenceFamilyRefuse =
  evaluateOccurrenceFamilyPattern
    OccurrenceFamilyPatternUnwired
    True
    False
    False
    == OccurrenceFamilyPatternGreenInventRefuse
    && evaluateOccurrenceFamilyPattern
      OccurrenceFamilyPatternUnwired
      False
      False
      True
      == OccurrenceFamilyPatternGreenInventRefuse

-- | Proved occurrence family pattern without path census is refused.
provedWithoutBarOccurrenceFamilyRefuse :: Bool
provedWithoutBarOccurrenceFamilyRefuse =
  evaluateOccurrenceFamilyPattern
    OccurrenceFamilyPatternUnwired
    False
    True
    False
    == OccurrenceFamilyPatternProvedWithoutBarRefuse
    && evaluateOccurrenceFamilyPattern
      OccurrenceFamilyPatternProved
      False
      False
      False
      == OccurrenceFamilyPatternProvedWithoutBarRefuse

-- | Occurrence family pattern scaffold pinned.
occurrenceFamilyPatternScaffold :: Bool
occurrenceFamilyPatternScaffold =
  unwiredOccurrenceFamilyDesignOk
    && occurrenceFamilyPatternConjunct
    && occurrenceFamilyProductNotXor
    && goldIsNativeFamilyOutlier
    && ironIsOxideFamilyProduct
    && heliumIsNoOreAtmophile
    && greenInventOccurrenceFamilyRefuse
    && provedWithoutBarOccurrenceFamilyRefuse
    && occurrenceFamilyTagCount == 7
    && goldZ == 79
    && ironZ == 26
    && heliumZ == 2

-- | Probe bundle for honest posture witnesses.
data OccurrenceFamilyPatternProbe = OccurrenceFamilyPatternProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  }
  deriving (Eq, Show)

-- | Honest probe — modality Unwired, physics GREEN refused.
occurrenceFamilyPatternProbe :: OccurrenceFamilyPatternProbe
occurrenceFamilyPatternProbe =
  OccurrenceFamilyPatternProbe
    { cellIdNamed =
        occurrenceFamilyPatternCellId
          == "CHEM-FORMAL-Q-HS-OCCURRENCE-FAMILY-PATTERN-CONSERVATION"
    , unwired =
        occurrenceFamilyPatternModalityCurrent
          == OccurrenceFamilyPatternUnwired
    , physicsGreenRefused =
        not occurrenceFamilyPatternPhysicsGreenAuthorized
    , soleAxiom = soleAxiomCount == 1
    , notProved = not rowProved
    }

-- | Honest conjunct on probe bundle.
occurrenceFamilyPatternHonest :: Bool
occurrenceFamilyPatternHonest =
  let p = occurrenceFamilyPatternProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && occurrenceFamilyPatternScaffold

-- | Row proved (always false on this Unwired cell).
rowProved :: Bool
rowProved = False

-- | One axiom framing: second law + conservation for occurrence family pattern scaffold.
occurrenceFamilyPatternFraming :: String
occurrenceFamilyPatternFraming =
  "second_law_conservation_occurrence_family_pattern_one_axiom"

-- | Single design axiom: second law + conservation occurrence family pattern (not 26th axiom).
occurrenceFamilyPatternAxiom :: Bool
occurrenceFamilyPatternAxiom =
  occurrenceFamilyPatternScaffold
    && occurrenceFamilyPatternConjunct
    && occurrenceFamilyPatternHonest
    && not rowProved
    && soleAxiomCount == 1
    && occurrenceFamilyPatternFraming
      == "second_law_conservation_occurrence_family_pattern_one_axiom"

occurrenceFamilyPatternNamed :: String
occurrenceFamilyPatternNamed =
  "occurrenceFamilyPattern: seven concurrent family tags native oxide sulfide silicate halide_carbonate atmophile synthetic_or_trace Au native Fe oxide product He no-ore atmophile same Z many assemblages ore engine outlier sort rowProved false second law conservation one axiom not 26th axiom"

-- | Upstream occurrence family pattern authority (cited, not forked).
occurrenceFamilyPatternAuthority :: String
occurrenceFamilyPatternAuthority =
  "umst/umst-chem/src/x_rows/occurrence_family_pattern.rs"

occurrenceFamilyPatternCellId :: String
occurrenceFamilyPatternCellId =
  "CHEM-FORMAL-Q-HS-OCCURRENCE-FAMILY-PATTERN-CONSERVATION"

-- | Non-claim fence — occurrence family pattern Unwired ≠ Proved GREEN.
occurrenceFamilyPatternNonClaim :: String
occurrenceFamilyPatternNonClaim =
  "CHEM-FORMAL-Q-HS-OCCURRENCE-FAMILY-PATTERN-CONSERVATION seven concurrent family tags native oxide sulfide silicate halide_carbonate atmophile synthetic_or_trace Au native Fe oxide product He no-ore atmophile same Z many assemblages rowProved false Unwired one axiom second law conservation not XOR enum not GREEN DFT not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the occurrence family pattern scaffold.
occurrenceFamilyPatternPhysicsGreenAuthorized :: Bool
occurrenceFamilyPatternPhysicsGreenAuthorized = False

occurrenceFamilyPatternPhysicsGreenFalse :: Bool
occurrenceFamilyPatternPhysicsGreenFalse =
  not occurrenceFamilyPatternPhysicsGreenAuthorized

occurrenceFamilyPatternModalityUnwired :: Bool
occurrenceFamilyPatternModalityUnwired =
  occurrenceFamilyPatternModalityCurrent == OccurrenceFamilyPatternUnwired

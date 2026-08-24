-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.NaturalOccurrenceZ118
Description : Natural occurrence Z=1..118 conservation on the matter fiber
Copyright   : (c) UMST Project, 2026

Natural occurrence Z=1..118 conservation: concurrent product classifiers (native /
oxide / sulfide / silicate / halide+carbonate / atmophile / synthetic-or-trace) for
every IUPAC Z; not folklore lists; not a second periodic table. Consult
ChemistryService. Classification laws are structure witnesses only
(@classificationLawsProved@ = False).

* @occurrenceProductZ118@ — 118-entry concurrent-bit classifier table (not XOR enum).
* @occurrenceBits@ — bits for Z in 1..118 bar.
* @heliumHasNoCrustalOreBit@ / @ironIsOccurrenceProduct@ — named witness pins.
* **One** design axiom (@naturalOccurrenceZ118Axiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of natural occurrence Z=1..118 conservation on the matter fiber.
Cell: @CHEM-FORMAL-Q-HS-NATURAL-OCCURRENCE-Z118-CONSERVATION@.
WAVE100: not wired in cabal. Remainder deferred composition, not impossibility.
-}
module UMST.ChemConstants.NaturalOccurrenceZ118
  ( NaturalOccurrenceZ118Modality (..)
  , naturalOccurrenceZ118ModalityCurrent
  , OccurrenceClassifierBit (..)
  , bitNative
  , bitOxide
  , bitSulfide
  , bitSilicate
  , bitHalideCarbonate
  , bitAtmophile
  , bitSyntheticTrace
  , occurrenceClassifierBitsAll
  , occurrenceClassifierBitCount
  , occurrenceProductZ118
  , occurrenceProductZ118Count
  , occurrenceBits
  , tableCoversZ118
  , heliumHasNoCrustalOreBit
  , ironIsOccurrenceProduct
  , everyZClassified
  , occurrenceBitPresent
  , occurrenceConcurrentCount
  , occurrenceProductNotXor
  , folkloreListRefuse
  , naturalOccurrenceZ118HonestConjunct
  , NaturalOccurrenceZ118Verdict (..)
  , evaluateNaturalOccurrenceZ118
  , unwiredNaturalOccurrenceDesignOk
  , greenInventNaturalOccurrenceRefuse
  , provedWithoutBarNaturalOccurrenceRefuse
  , naturalOccurrenceZ118Scaffold
  , NaturalOccurrenceZ118Probe (..)
  , naturalOccurrenceZ118Probe
  , naturalOccurrenceZ118Honest
  , classificationLawsProved
  , naturalOccurrenceZ118Framing
  , naturalOccurrenceZ118Axiom
  , naturalOccurrenceZ118Named
  , naturalOccurrenceZ118Authority
  , chemistryServiceAuthority
  , naturalOccurrenceZ118CellId
  , naturalOccurrenceZ118NonClaim
  , naturalOccurrenceZ118PhysicsGreenAuthorized
  , naturalOccurrenceZ118PhysicsGreenFalse
  , naturalOccurrenceZ118ModalityUnwired
  ) where

import Data.Bits ((.&.))

-- | IUPAC periodic-table cardinality (Z=1..118).
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Design modality for natural occurrence Z118 claims (TYPE-03 preview).
data NaturalOccurrenceZ118Modality
  = NaturalOccurrenceZ118Unwired
  | NaturalOccurrenceZ118Assumed
  | NaturalOccurrenceZ118Proved
  | NaturalOccurrenceZ118Surrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
naturalOccurrenceZ118ModalityCurrent :: NaturalOccurrenceZ118Modality
naturalOccurrenceZ118ModalityCurrent = NaturalOccurrenceZ118Unwired

-- | Named occurrence classifier bits — concurrent product, not XOR enum.
data OccurrenceClassifierBit
  = OccurrenceNative
  | OccurrenceOxide
  | OccurrenceSulfide
  | OccurrenceSilicate
  | OccurrenceHalideCarbonate
  | OccurrenceAtmophile
  | OccurrenceSyntheticTrace
  deriving (Eq, Show)

-- | Bit values mirroring umst-chem INT row (concurrent, not XOR).
bitNative :: Int
bitNative = 1

bitOxide :: Int
bitOxide = 2

bitSulfide :: Int
bitSulfide = 4

bitSilicate :: Int
bitSilicate = 8

bitHalideCarbonate :: Int
bitHalideCarbonate = 16

bitAtmophile :: Int
bitAtmophile = 32

bitSyntheticTrace :: Int
bitSyntheticTrace = 64

-- | All classifier bits in stable order.
occurrenceClassifierBitsAll :: [OccurrenceClassifierBit]
occurrenceClassifierBitsAll =
  [ OccurrenceNative
  , OccurrenceOxide
  , OccurrenceSulfide
  , OccurrenceSilicate
  , OccurrenceHalideCarbonate
  , OccurrenceAtmophile
  , OccurrenceSyntheticTrace
  ]

occurrenceClassifierBitCount :: Int
occurrenceClassifierBitCount = length occurrenceClassifierBitsAll

-- | Numeric bit for a classifier tag.
occurrenceClassifierBitValue :: OccurrenceClassifierBit -> Int
occurrenceClassifierBitValue tag =
  case tag of
    OccurrenceNative -> bitNative
    OccurrenceOxide -> bitOxide
    OccurrenceSulfide -> bitSulfide
    OccurrenceSilicate -> bitSilicate
    OccurrenceHalideCarbonate -> bitHalideCarbonate
    OccurrenceAtmophile -> bitAtmophile
    OccurrenceSyntheticTrace -> bitSyntheticTrace

-- | Product classifier table indexed by Z-1. Concurrent bits, not XOR.
occurrenceProductZ118 :: [Int]
occurrenceProductZ118 =
  [ 48, 32, 24, 8, 18, 17, 32, 42, 16, 32, 24, 10, 10, 8, 16, 5, 16, 32
  , 24, 24, 8, 2, 6, 2, 2, 7, 4, 5, 5, 4, 4, 4, 4, 5, 16, 32
  , 8, 16, 24, 8, 2, 4, 64, 1, 1, 1, 5, 4, 4, 2, 4, 5, 16, 32
  , 8, 16, 24, 24, 24, 24, 64, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 8
  , 2, 2, 4, 1, 1, 1, 1, 5, 4, 4, 5, 64, 64, 96, 64, 64, 64, 24
  , 64, 2, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64
  , 64, 64, 64, 64, 64, 64, 64, 64, 64, 96
  ]

occurrenceProductZ118Count :: Int
occurrenceProductZ118Count = length occurrenceProductZ118

-- | Occurrence bits for Z in 1..118 bar.
occurrenceBits :: Int -> Maybe Int
occurrenceBits z =
  if z >= 1 && z <= iupacTableCardinality
    then Just (occurrenceProductZ118 !! (z - 1))
    else Nothing

-- | Whether the table covers every IUPAC Z.
tableCoversZ118 :: Bool
tableCoversZ118 = occurrenceProductZ118Count == iupacTableCardinality

-- | He (Z=2) has no crustal ore bit — atmophile only.
heliumHasNoCrustalOreBit :: Bool
heliumHasNoCrustalOreBit =
  case occurrenceBits 2 of
    Just b -> b == bitAtmophile
    Nothing -> False

-- | Fe (Z=26) is a product (native ⊗ oxide ⊗ sulfide), not XOR.
ironIsOccurrenceProduct :: Bool
ironIsOccurrenceProduct =
  case occurrenceBits 26 of
    Just b ->
      occurrenceBitPresent b OccurrenceNative
        && occurrenceBitPresent b OccurrenceOxide
        && occurrenceBitPresent b OccurrenceSulfide
    Nothing -> False

-- | Every Z has a non-zero classifier (named remainder, including synthetic).
everyZClassified :: Bool
everyZClassified = all (/= 0) occurrenceProductZ118

-- | Whether a classifier bit is present in a concurrent product (not XOR).
occurrenceBitPresent :: Int -> OccurrenceClassifierBit -> Bool
occurrenceBitPresent bits tag =
  (bits .&. occurrenceClassifierBitValue tag) /= 0

-- | Count of concurrent classifier bits set (Π_c, not XOR bucket).
occurrenceConcurrentCount :: Int -> Int
occurrenceConcurrentCount bits =
  length (filter (occurrenceBitPresent bits) occurrenceClassifierBitsAll)

-- | Fe product has concurrent Π_c ≥ 3 — not XOR enum bucket.
occurrenceProductNotXor :: Bool
occurrenceProductNotXor =
  case occurrenceBits 26 of
    Just b -> occurrenceConcurrentCount b >= 3
    Nothing -> False

-- | Folklore list invent is refused — table is typed product classifiers.
folkloreListRefuse :: Bool
folkloreListRefuse =
  tableCoversZ118
    && occurrenceClassifierBitCount == 7
    && not classificationLawsProved

-- | Honest conjunct — Z=1..118 product classifiers, not folklore.
naturalOccurrenceZ118HonestConjunct :: Bool
naturalOccurrenceZ118HonestConjunct =
  tableCoversZ118
    && heliumHasNoCrustalOreBit
    && ironIsOccurrenceProduct
    && everyZClassified
    && occurrenceProductNotXor
    && folkloreListRefuse

-- | Verdict for natural occurrence Z118 close (fail-closed).
data NaturalOccurrenceZ118Verdict
  = NaturalOccurrenceZ118DesignOk
  | NaturalOccurrenceZ118NamedOk
  | NaturalOccurrenceZ118GreenInventRefuse
  | NaturalOccurrenceZ118FolkloreRefuse
  | NaturalOccurrenceZ118ProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate natural occurrence Z118 under honest bar (fail-closed).
evaluateNaturalOccurrenceZ118 ::
  NaturalOccurrenceZ118Modality
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> NaturalOccurrenceZ118Verdict
evaluateNaturalOccurrenceZ118
  modality
  claimPhysicsGreen
  claimProved
  claimFolklore
  claimGreenInvent
  | claimPhysicsGreen || claimGreenInvent =
      NaturalOccurrenceZ118GreenInventRefuse
  | claimFolklore = NaturalOccurrenceZ118FolkloreRefuse
  | claimProved = NaturalOccurrenceZ118ProvedWithoutBarRefuse
  | not naturalOccurrenceZ118HonestConjunct =
      NaturalOccurrenceZ118DesignOk
  | otherwise =
      case modality of
        NaturalOccurrenceZ118Unwired ->
          if tableCoversZ118
            then NaturalOccurrenceZ118NamedOk
            else NaturalOccurrenceZ118DesignOk
        NaturalOccurrenceZ118Assumed -> NaturalOccurrenceZ118DesignOk
        NaturalOccurrenceZ118Surrogate -> NaturalOccurrenceZ118DesignOk
        NaturalOccurrenceZ118Proved ->
          NaturalOccurrenceZ118ProvedWithoutBarRefuse

-- | Unwired natural occurrence modality OK — typed classifiers not folklore.
unwiredNaturalOccurrenceDesignOk :: Bool
unwiredNaturalOccurrenceDesignOk =
  evaluateNaturalOccurrenceZ118
    NaturalOccurrenceZ118Unwired
    False
    False
    False
    False
    == NaturalOccurrenceZ118NamedOk

-- | GREEN invent on natural occurrence promotion is refused.
greenInventNaturalOccurrenceRefuse :: Bool
greenInventNaturalOccurrenceRefuse =
  evaluateNaturalOccurrenceZ118
    NaturalOccurrenceZ118Unwired
    True
    False
    False
    False
    == NaturalOccurrenceZ118GreenInventRefuse
    && evaluateNaturalOccurrenceZ118
      NaturalOccurrenceZ118Unwired
      False
      False
      False
      True
      == NaturalOccurrenceZ118GreenInventRefuse

-- | Proved natural occurrence without path census is refused.
provedWithoutBarNaturalOccurrenceRefuse :: Bool
provedWithoutBarNaturalOccurrenceRefuse =
  evaluateNaturalOccurrenceZ118
    NaturalOccurrenceZ118Unwired
    False
    True
    False
    False
    == NaturalOccurrenceZ118ProvedWithoutBarRefuse
    && evaluateNaturalOccurrenceZ118
      NaturalOccurrenceZ118Proved
      False
      False
      False
      False
      == NaturalOccurrenceZ118ProvedWithoutBarRefuse

-- | Natural occurrence Z118 scaffold pinned.
naturalOccurrenceZ118Scaffold :: Bool
naturalOccurrenceZ118Scaffold =
  unwiredNaturalOccurrenceDesignOk
    && naturalOccurrenceZ118HonestConjunct
    && occurrenceProductNotXor
    && folkloreListRefuse
    && greenInventNaturalOccurrenceRefuse
    && provedWithoutBarNaturalOccurrenceRefuse
    && occurrenceClassifierBitCount == 7

-- | Probe bundle for honest posture witnesses.
data NaturalOccurrenceZ118Probe = NaturalOccurrenceZ118Probe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  }
  deriving (Eq, Show)

-- | Honest probe — modality Unwired, physics GREEN refused.
naturalOccurrenceZ118Probe :: NaturalOccurrenceZ118Probe
naturalOccurrenceZ118Probe =
  NaturalOccurrenceZ118Probe
    { cellIdNamed =
        naturalOccurrenceZ118CellId
          == "CHEM-FORMAL-Q-HS-NATURAL-OCCURRENCE-Z118-CONSERVATION"
    , unwired =
        naturalOccurrenceZ118ModalityCurrent == NaturalOccurrenceZ118Unwired
    , physicsGreenRefused =
        not naturalOccurrenceZ118PhysicsGreenAuthorized
    , soleAxiom = True
    , notProved = not classificationLawsProved
    }

-- | Honest conjunct on probe bundle.
naturalOccurrenceZ118Honest :: Bool
naturalOccurrenceZ118Honest =
  let p = naturalOccurrenceZ118Probe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && naturalOccurrenceZ118Scaffold

-- | Classification laws proved (always false on this Unwired cell).
classificationLawsProved :: Bool
classificationLawsProved = False

-- | One axiom framing: second law + conservation for natural occurrence scaffold.
naturalOccurrenceZ118Framing :: String
naturalOccurrenceZ118Framing =
  "second_law_conservation_natural_occurrence_z118_one_axiom"

-- | Single design axiom: second law + conservation natural occurrence Z118.
naturalOccurrenceZ118Axiom :: Bool
naturalOccurrenceZ118Axiom =
  naturalOccurrenceZ118Scaffold
    && naturalOccurrenceZ118HonestConjunct
    && naturalOccurrenceZ118Honest
    && folkloreListRefuse
    && not classificationLawsProved
    && naturalOccurrenceZ118Framing
      == "second_law_conservation_natural_occurrence_z118_one_axiom"

naturalOccurrenceZ118Named :: String
naturalOccurrenceZ118Named =
  "naturalOccurrenceZ118: Z 1..118 natural occurrence product classifiers native oxide sulfide silicate halide carbonate atmophile synthetic trace not folklore classificationLawsProved false second law conservation one axiom"

-- | Upstream natural occurrence Z118 authority (cited, not forked).
naturalOccurrenceZ118Authority :: String
naturalOccurrenceZ118Authority =
  "umst/umst-chem/src/x_rows/natural_occurrence_z118.rs"

-- | ChemistryService consult authority — no second periodic table.
chemistryServiceAuthority :: String
chemistryServiceAuthority = "umst/umst-chem/src/chemistry_service.rs"

naturalOccurrenceZ118CellId :: String
naturalOccurrenceZ118CellId =
  "CHEM-FORMAL-Q-HS-NATURAL-OCCURRENCE-Z118-CONSERVATION"

-- | Non-claim fence — natural occurrence Z118 Unwired ≠ Proved GREEN.
naturalOccurrenceZ118NonClaim :: String
naturalOccurrenceZ118NonClaim =
  "CHEM-FORMAL-Q-HS-NATURAL-OCCURRENCE-Z118-CONSERVATION Z 1..118 natural occurrence product classifiers native oxide sulfide silicate halide carbonate atmophile synthetic trace not folklore classificationLawsProved false Unwired one axiom second law conservation not XOR enum not GREEN DFT not physics GREEN not production_wired WAVE100 deferred composition not impossibility"

-- | Physics GREEN is unauthorized on the natural occurrence Z118 scaffold.
naturalOccurrenceZ118PhysicsGreenAuthorized :: Bool
naturalOccurrenceZ118PhysicsGreenAuthorized = False

naturalOccurrenceZ118PhysicsGreenFalse :: Bool
naturalOccurrenceZ118PhysicsGreenFalse =
  not naturalOccurrenceZ118PhysicsGreenAuthorized

naturalOccurrenceZ118ModalityUnwired :: Bool
naturalOccurrenceZ118ModalityUnwired =
  naturalOccurrenceZ118ModalityCurrent == NaturalOccurrenceZ118Unwired

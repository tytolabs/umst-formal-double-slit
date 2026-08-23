-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.PartialConservation
Description : Partial Interact conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Partial** conservation: TYPE-05 Kleisli Interact is **partial** — admissible vs forbidden
morphism attempts on **conservation** claims (Unwired / Assumed / Proved / Surrogate).
Total Interact claim refuse; forbidden pairs refuse at the type layer.
TYPE-05 **partial** laws are structure witnesses only (@type05PartialProved@ = False).

* @PartialConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluatePartialConservation@ — Unwired OK; forbidden Interact refuse; total-claim refuse; admissible scaffold typed.
* **One** design axiom (@partialConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of **partial** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-PARTIAL-CONSERVATION@.
-}
module UMST.ChemConstants.PartialConservation
  ( PartialConservationModality (..)
  , partialConservationModalityCurrent
  , partialLatticeAll
  , partialLatticeCount
  , InteractElementTag (..)
  , InteractKind (..)
  , interactKindAll
  , interactKindCount
  , InteractPair (..)
  , InteractAttempt (..)
  , ForbiddenInteractReason (..)
  , PartialInteractLaw (..)
  , partialInteractLawAll
  , partialInteractLawCount
  , PartialConservationVerdict (..)
  , evaluatePartialConservation
  , sampleUnwiredOkRow
  , sampleForbiddenSelfSameRow
  , sampleAdmissibleScaffoldRow
  , sampleTotalClaimRefuseRow
  , unwiredDesignOk
  , forbiddenSelfSameRefuse
  , admissibleScaffoldOk
  , totalClaimRefuse
  , assumedWithoutForbiddenOk
  , surrogateWithoutForbiddenOk
  , greenInventPartialRefuse
  , partialLatticeScaffold
  , partialLatticeNotGreenTable
  , partialInteractLawsScaffold
  , partialInteractLawsNotGreenTable
  , partialKnowingFiberOk
  , type05PartialInventRefuse
  , partialLatticeNotXor
  , type05PartialProved
  , partialConservationFraming
  , partialConservationAxiom
  , partialConservationNamed
  , interactPartialityAuthority
  , chemL0Type05Authority
  , partialConservationCellId
  , partialConservationNonClaim
  , partialConservationPhysicsGreenAuthorized
  , partialConservationPhysicsGreenFalse
  , partialConservationModalityUnwired
  ) where

-- | Design **partial** modality for TYPE-05 **conservation** claims.
data PartialConservationModality
  = PartialConservationUnwired
  | PartialConservationAssumed
  | PartialConservationProved
  | PartialConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **partial** modality — always Unwired on this cell.
partialConservationModalityCurrent :: PartialConservationModality
partialConservationModalityCurrent = PartialConservationUnwired

-- | All TYPE-05 **partial** lattice steps in stable order.
partialLatticeAll :: [PartialConservationModality]
partialLatticeAll =
  [ PartialConservationUnwired
  , PartialConservationAssumed
  , PartialConservationProved
  , PartialConservationSurrogate
  ]

partialLatticeCount :: Int
partialLatticeCount = length partialLatticeAll

-- | Named interaction element factor tags (bounded scaffold — not XOR enum).
data InteractElementTag
  = CaScaffold
  | OScaffold
  | HScaffold
  | SiScaffold
  deriving (Eq, Show)

-- | North-star Interact kind scaffold (pattern taxonomy preview).
data InteractKind
  = BondForming
  | BondRepelling
  | StructureEnabling
  | StructureBlocking
  deriving (Eq, Show)

-- | All Interact kinds in stable order (structure scaffold — not 118² GREEN table).
interactKindAll :: [InteractKind]
interactKindAll =
  [ BondForming
  , BondRepelling
  , StructureEnabling
  , StructureBlocking
  ]

interactKindCount :: Int
interactKindCount = length interactKindAll

-- | Ordered element pair for a **partial** Interact attempt.
data InteractPair = InteractPair
  { interactPairLhs :: InteractElementTag
  , interactPairRhs :: InteractElementTag
  }
  deriving (Eq, Show)

-- | A **partial** Interact attempt before thermo witness.
data InteractAttempt = InteractAttempt
  { interactAttemptPair :: InteractPair
  , interactAttemptKind :: InteractKind
  }
  deriving (Eq, Show)

-- | Why a **partial** Interact is forbidden (partiality refusal).
data ForbiddenInteractReason
  = SelfSameElementBondForming
  | StructureBlockingOnEnablingPair
  | ConservationAxiomRefuse
  | NuclearElectronicBoundaryUnwired
  | TotalInteractClaimRefuse
  deriving (Eq, Show)

-- | **Partial** Interact law cells tracked by TYPE-05 (structure scaffold).
data PartialInteractLaw
  = AdmissibleVsForbidden
  | TotalClaimRefuse
  | ForbiddenTableRefuse
  | GreenInventRefuse
  deriving (Eq, Show)

-- | All **partial** Interact law cells in stable order.
partialInteractLawAll :: [PartialInteractLaw]
partialInteractLawAll =
  [ AdmissibleVsForbidden
  , TotalClaimRefuse
  , ForbiddenTableRefuse
  , GreenInventRefuse
  ]

partialInteractLawCount :: Int
partialInteractLawCount = length partialInteractLawAll

-- | Verdict for TYPE-05 **partial** **conservation** promotion (fail-closed).
data PartialConservationVerdict
  = PartialDesignOk
  | PartialAdmissibleOk
  | PartialForbiddenRefuse
  | PartialTotalClaimRefuse
  | PartialGreenInventRefuse
  deriving (Eq, Show)

pairMatches :: InteractPair -> InteractPair -> Bool
pairMatches attempt table =
  (interactPairLhs attempt == interactPairLhs table
    && interactPairRhs attempt == interactPairRhs table)
    || (interactPairLhs attempt == interactPairRhs table
          && interactPairRhs attempt == interactPairLhs table)

-- | Pinned forbidden **partial** Interact rows (design table — Unwired).
lookupForbidden :: InteractAttempt -> Maybe ForbiddenInteractReason
lookupForbidden attempt =
  let pair = interactAttemptPair attempt
      kind = interactAttemptKind attempt
      rows =
        [ ( InteractPair HScaffold HScaffold
          , BondForming
          , SelfSameElementBondForming
          )
        , ( InteractPair OScaffold OScaffold
          , BondForming
          , SelfSameElementBondForming
          )
        , ( InteractPair HScaffold SiScaffold
          , StructureBlocking
          , StructureBlockingOnEnablingPair
          )
        , ( InteractPair HScaffold CaScaffold
          , BondForming
          , NuclearElectronicBoundaryUnwired
          )
        ]
      matches =
        [ reason
        | (tablePair, tableKind, reason) <- rows
        , kind == tableKind
        , pairMatches pair tablePair
        ]
   in case matches of
        (reason : _) -> Just reason
        [] -> Nothing

-- | Evaluate TYPE-05 **partial** **conservation** typing (fail-closed).
evaluatePartialConservation ::
  PartialConservationModality
  -> InteractAttempt
  -> Bool
  -> Bool
  -> PartialConservationVerdict
evaluatePartialConservation modality attempt claimTotalInteract claimPhysicsGreen
  | claimPhysicsGreen = PartialGreenInventRefuse
  | claimTotalInteract = PartialTotalClaimRefuse
  | otherwise =
      case modality of
        PartialConservationUnwired -> PartialDesignOk
        PartialConservationAssumed -> PartialDesignOk
        PartialConservationSurrogate -> PartialDesignOk
        PartialConservationProved ->
          case lookupForbidden attempt of
            Just _ -> PartialForbiddenRefuse
            Nothing -> PartialAdmissibleOk

-- | Sample Unwired row — no forbidden table hit required.
sampleUnwiredOkRow :: InteractAttempt
sampleUnwiredOkRow =
  InteractAttempt
  { interactAttemptPair = InteractPair CaScaffold OScaffold
  , interactAttemptKind = BondForming
  }

-- | Sample forbidden self-same H–H bond-forming row.
sampleForbiddenSelfSameRow :: InteractAttempt
sampleForbiddenSelfSameRow =
  InteractAttempt
  { interactAttemptPair = InteractPair HScaffold HScaffold
  , interactAttemptKind = BondForming
  }

-- | Sample admissible scaffold row under Proved modality.
sampleAdmissibleScaffoldRow :: InteractAttempt
sampleAdmissibleScaffoldRow =
  InteractAttempt
  { interactAttemptPair = InteractPair CaScaffold OScaffold
  , interactAttemptKind = BondForming
  }

-- | Sample total-claim refuse row (admissible pair with total claim).
sampleTotalClaimRefuseRow :: InteractAttempt
sampleTotalClaimRefuseRow = sampleAdmissibleScaffoldRow

-- | Unwired **partial** modality OK without forbidden hit.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluatePartialConservation
    PartialConservationUnwired
    sampleUnwiredOkRow
    False
    False
    == PartialDesignOk

-- | Forbidden self-same bond-forming refused under Proved modality.
forbiddenSelfSameRefuse :: Bool
forbiddenSelfSameRefuse =
  evaluatePartialConservation
    PartialConservationProved
    sampleForbiddenSelfSameRow
    False
    False
    == PartialForbiddenRefuse

-- | Admissible scaffold pair admitted (still not physics GREEN).
admissibleScaffoldOk :: Bool
admissibleScaffoldOk =
  evaluatePartialConservation
    PartialConservationProved
    sampleAdmissibleScaffoldRow
    False
    False
    == PartialAdmissibleOk

-- | Total Interact claim refused (partiality refuses totalization).
totalClaimRefuse :: Bool
totalClaimRefuse =
  evaluatePartialConservation
    PartialConservationProved
    sampleTotalClaimRefuseRow
    True
    False
    == PartialTotalClaimRefuse

-- | Assumed **partial** modality OK without forbidden hit (design scaffold).
assumedWithoutForbiddenOk :: Bool
assumedWithoutForbiddenOk =
  evaluatePartialConservation
    PartialConservationAssumed
    sampleUnwiredOkRow
    False
    False
    == PartialDesignOk

-- | Surrogate **partial** modality OK without forbidden hit (design scaffold).
surrogateWithoutForbiddenOk :: Bool
surrogateWithoutForbiddenOk =
  evaluatePartialConservation
    PartialConservationSurrogate
    sampleAdmissibleScaffoldRow
    False
    False
    == PartialDesignOk

-- | GREEN invent on **partial** **conservation** promotion is refused.
greenInventPartialRefuse :: Bool
greenInventPartialRefuse =
  evaluatePartialConservation
    PartialConservationUnwired
    sampleUnwiredOkRow
    False
    True
    == PartialGreenInventRefuse

-- | Four-step TYPE-05 **partial** lattice scaffold pinned.
partialLatticeScaffold :: Bool
partialLatticeScaffold =
  partialLatticeCount == 4
    && unwiredDesignOk
    && forbiddenSelfSameRefuse
    && admissibleScaffoldOk
    && totalClaimRefuse
    && assumedWithoutForbiddenOk
    && surrogateWithoutForbiddenOk

-- | **Partial** lattice is structure scaffold — not 118² GREEN periodic table.
partialLatticeNotGreenTable :: Bool
partialLatticeNotGreenTable =
  partialLatticeCount == 4
    && partialLatticeCount /= 118 * 118
    && sampleUnwiredOkRow /= sampleForbiddenSelfSameRow

-- | Four **partial** Interact law cells scaffold pinned.
partialInteractLawsScaffold :: Bool
partialInteractLawsScaffold =
  partialInteractLawCount == 4
    && unwiredDesignOk
    && forbiddenSelfSameRefuse
    && admissibleScaffoldOk
    && totalClaimRefuse

-- | **Partial** law cells are structure scaffold — not 118² GREEN periodic table.
partialInteractLawsNotGreenTable :: Bool
partialInteractLawsNotGreenTable =
  partialInteractLawCount == 4
    && partialInteractLawCount /= 118 * 118
    && sampleForbiddenSelfSameRow /= sampleAdmissibleScaffoldRow

-- | **Partial** **conservation** claims route to knowing / quantum fiber (not meso acting).
partialKnowingFiberOk :: Bool
partialKnowingFiberOk = True

-- | TYPE-05 **partial** invent refuse-closed scaffold witness.
type05PartialInventRefuse :: Bool
type05PartialInventRefuse = not type05PartialProved

-- | **Partial** lattice steps are concurrent Π_c — not XOR enum bucket.
partialLatticeNotXor :: Bool
partialLatticeNotXor =
  unwiredDesignOk
    && assumedWithoutForbiddenOk
    && surrogateWithoutForbiddenOk
    && forbiddenSelfSameRefuse
    && admissibleScaffoldOk
    && totalClaimRefuse
    && greenInventPartialRefuse

-- | TYPE-05 **partial** proved (always false on this Unwired cell).
type05PartialProved :: Bool
type05PartialProved = False

-- | One axiom framing: second law + **conservation** for **partial** scaffold.
partialConservationFraming :: String
partialConservationFraming =
  "second_law_conservation_partial_one_axiom"

-- | Single design axiom: second law + **conservation** **partial** (not second axiom).
partialConservationAxiom :: Bool
partialConservationAxiom =
  partialLatticeScaffold
    && partialLatticeNotGreenTable
    && partialInteractLawsScaffold
    && partialInteractLawsNotGreenTable
    && partialKnowingFiberOk
    && unwiredDesignOk
    && forbiddenSelfSameRefuse
    && admissibleScaffoldOk
    && totalClaimRefuse
    && greenInventPartialRefuse
    && type05PartialInventRefuse
    && partialLatticeNotXor
    && not type05PartialProved
    && partialConservationFraming
      == "second_law_conservation_partial_one_axiom"

partialConservationNamed :: String
partialConservationNamed =
  "partialConservation: PartialConservationModality Unwired Assumed Proved Surrogate four-step lattice type05PartialProved false admissibleVsForbidden totalClaimRefuse forbiddenTableRefuse second law conservation one axiom"

-- | Upstream TYPE-05 Interact **partial**ity authority (cited, not forked).
interactPartialityAuthority :: String
interactPartialityAuthority = "umst/umst-chem/src/interact_partiality.rs"

-- | L0 TYPE-05 **partial** scaffold authority (crosswalk).
chemL0Type05Authority :: String
chemL0Type05Authority = "CHEM-L0-TYPE-05"

partialConservationCellId :: String
partialConservationCellId = "CHEM-FORMAL-Q-HS-PARTIAL-CONSERVATION"

-- | Non-claim fence — **partial** **conservation** Unwired ≠ Proved GREEN.
partialConservationNonClaim :: String
partialConservationNonClaim =
  "CHEM-FORMAL-Q-HS-PARTIAL-CONSERVATION PartialConservationModality Unwired Assumed Proved Surrogate four-step lattice type05PartialProved false admissibleVsForbidden totalClaimRefuse forbiddenTableRefuse Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing **partial** **conservation** scaffold.
partialConservationPhysicsGreenAuthorized :: Bool
partialConservationPhysicsGreenAuthorized = False

partialConservationPhysicsGreenFalse :: Bool
partialConservationPhysicsGreenFalse =
  not partialConservationPhysicsGreenAuthorized

partialConservationModalityUnwired :: Bool
partialConservationModalityUnwired =
  partialConservationModalityCurrent == PartialConservationUnwired

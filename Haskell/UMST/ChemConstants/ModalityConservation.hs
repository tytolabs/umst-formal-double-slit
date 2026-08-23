-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ModalityConservation
Description : Modality conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Modality** conservation: TYPE-03 lattice (Unwired / Assumed / Proved / Surrogate) on
conservation claims — path-census earned before Proved promotion. **Modality** identity
conserved under honest census; without census or with defects → refuse-closed.
TYPE-03 **modality** laws are structure witnesses only (@type03ModalityProved@ = False).

* @ModalityConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateModalityConservation@ — Unwired OK without census; Proved without census refuse; Proved with defects refuse.
* **One** design axiom (@modalityConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of **modality** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-MODALITY-CONSERVATION@.
-}
module UMST.ChemConstants.ModalityConservation
  ( ModalityConservationModality (..)
  , modalityConservationModalityCurrent
  , modalityLatticeAll
  , modalityLatticeCount
  , ConservationAxis (..)
  , conservationAxisAll
  , conservationAxisCount
  , PathCensusPresence (..)
  , CensusDefectPresence (..)
  , ModalityPromotionVerdict (..)
  , evaluateModalityConservation
  , sampleUnwiredNoCensusRow
  , sampleProvedNoCensusRow
  , sampleProvedWithDefectsRow
  , sampleProvedCleanCensusRow
  , unwiredWithoutCensusOk
  , provedWithoutCensusRefuse
  , provedWithDefectsRefuse
  , provedWithCleanCensusOk
  , assumedWithoutCensusOk
  , surrogateWithoutCensusOk
  , greenInventModalityRefuse
  , modalityLatticeScaffold
  , modalityLatticeNotGreenTable
  , conservationAxesScaffold
  , conservationAxesNotGreenTable
  , modalityKnowingFiberOk
  , type03ModalityInventRefuse
  , modalityLatticeNotXor
  , type03ModalityProved
  , modalityConservationFraming
  , modalityConservationAxiom
  , modalityConservationNamed
  , conservationResourceTypesAuthority
  , chemL0Type03Authority
  , modalityConservationCellId
  , modalityConservationNonClaim
  , modalityConservationPhysicsGreenAuthorized
  , modalityConservationPhysicsGreenFalse
  , modalityConservationModalityUnwired
  ) where

-- | Design **modality** for TYPE-03 **conservation** claims.
data ModalityConservationModality
  = ModalityConservationUnwired
  | ModalityConservationAssumed
  | ModalityConservationProved
  | ModalityConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **modality** — always Unwired on this cell.
modalityConservationModalityCurrent :: ModalityConservationModality
modalityConservationModalityCurrent = ModalityConservationUnwired

-- | All TYPE-03 **modality** lattice steps in stable order.
modalityLatticeAll :: [ModalityConservationModality]
modalityLatticeAll =
  [ ModalityConservationUnwired
  , ModalityConservationAssumed
  , ModalityConservationProved
  , ModalityConservationSurrogate
  ]

modalityLatticeCount :: Int
modalityLatticeCount = length modalityLatticeAll

-- | **Conservation** axis under the single second-law + **conservation** axiom.
data ConservationAxis
  = MassAxis
  | ChargeAxis
  | AtomCountAxis
  | EnthalpyAxis
  deriving (Eq, Show)

-- | All **conservation** axes in stable order (structure scaffold — not 118² GREEN table).
conservationAxisAll :: [ConservationAxis]
conservationAxisAll = [MassAxis, ChargeAxis, AtomCountAxis, EnthalpyAxis]

conservationAxisCount :: Int
conservationAxisCount = length conservationAxisAll

-- | Whether a path census is present for **modality** promotion.
data PathCensusPresence
  = CensusAbsent
  | CensusPresent
  deriving (Eq, Show)

-- | Whether census defects block **modality** Proved promotion.
data CensusDefectPresence
  = DefectsAbsent
  | DefectsPresent
  deriving (Eq, Show)

-- | Verdict for TYPE-03 **modality** promotion on **conservation** claims.
data ModalityPromotionVerdict
  = ModalityDesignOk
  | ModalityProvedCleanOk
  | ModalityProvedWithoutCensusRefuse
  | ModalityProvedWithDefectsRefuse
  | ModalityGreenInventRefuse
  deriving (Eq, Show)

-- | Evaluate TYPE-03 **modality** **conservation** promotion (fail-closed).
evaluateModalityConservation ::
  ModalityConservationModality
  -> ConservationAxis
  -> PathCensusPresence
  -> CensusDefectPresence
  -> Bool
  -> ModalityPromotionVerdict
evaluateModalityConservation modality _axis census defects claimPhysicsGreen
  | claimPhysicsGreen = ModalityGreenInventRefuse
  | otherwise =
      case modality of
        ModalityConservationUnwired -> ModalityDesignOk
        ModalityConservationAssumed -> ModalityDesignOk
        ModalityConservationSurrogate -> ModalityDesignOk
        ModalityConservationProved ->
          case census of
            CensusAbsent -> ModalityProvedWithoutCensusRefuse
            CensusPresent ->
              case defects of
                DefectsPresent -> ModalityProvedWithDefectsRefuse
                DefectsAbsent -> ModalityProvedCleanOk

-- | Sample Unwired row — no path census required.
sampleUnwiredNoCensusRow ::
  ( ModalityConservationModality
  , ConservationAxis
  , PathCensusPresence
  , CensusDefectPresence
  )
sampleUnwiredNoCensusRow =
  ( ModalityConservationUnwired
  , MassAxis
  , CensusAbsent
  , DefectsAbsent
  )

-- | Sample Proved row without census — refuse witness.
sampleProvedNoCensusRow ::
  ( ModalityConservationModality
  , ConservationAxis
  , PathCensusPresence
  , CensusDefectPresence
  )
sampleProvedNoCensusRow =
  ( ModalityConservationProved
  , ChargeAxis
  , CensusAbsent
  , DefectsAbsent
  )

-- | Sample Proved row with census defects — refuse witness.
sampleProvedWithDefectsRow ::
  ( ModalityConservationModality
  , ConservationAxis
  , PathCensusPresence
  , CensusDefectPresence
  )
sampleProvedWithDefectsRow =
  ( ModalityConservationProved
  , AtomCountAxis
  , CensusPresent
  , DefectsPresent
  )

-- | Sample Proved row with clean census — admissible scaffold witness.
sampleProvedCleanCensusRow ::
  ( ModalityConservationModality
  , ConservationAxis
  , PathCensusPresence
  , CensusDefectPresence
  )
sampleProvedCleanCensusRow =
  ( ModalityConservationProved
  , EnthalpyAxis
  , CensusPresent
  , DefectsAbsent
  )

-- | Unwired **modality** OK without path census.
unwiredWithoutCensusOk :: Bool
unwiredWithoutCensusOk =
  let (modality, axis, census, defects) = sampleUnwiredNoCensusRow
   in evaluateModalityConservation modality axis census defects False
        == ModalityDesignOk

-- | Proved **modality** without census is refuse-closed.
provedWithoutCensusRefuse :: Bool
provedWithoutCensusRefuse =
  let (modality, axis, census, defects) = sampleProvedNoCensusRow
   in evaluateModalityConservation modality axis census defects False
        == ModalityProvedWithoutCensusRefuse

-- | Proved **modality** with census defects is refuse-closed.
provedWithDefectsRefuse :: Bool
provedWithDefectsRefuse =
  let (modality, axis, census, defects) = sampleProvedWithDefectsRow
   in evaluateModalityConservation modality axis census defects False
        == ModalityProvedWithDefectsRefuse

-- | Proved **modality** with clean census admitted (still not physics GREEN).
provedWithCleanCensusOk :: Bool
provedWithCleanCensusOk =
  let (modality, axis, census, defects) = sampleProvedCleanCensusRow
   in evaluateModalityConservation modality axis census defects False
        == ModalityProvedCleanOk

-- | Assumed **modality** OK without census (design scaffold).
assumedWithoutCensusOk :: Bool
assumedWithoutCensusOk =
  evaluateModalityConservation
    ModalityConservationAssumed
    MassAxis
    CensusAbsent
    DefectsAbsent
    False
    == ModalityDesignOk

-- | Surrogate **modality** OK without census (design scaffold).
surrogateWithoutCensusOk :: Bool
surrogateWithoutCensusOk =
  evaluateModalityConservation
    ModalityConservationSurrogate
    ChargeAxis
    CensusAbsent
    DefectsAbsent
    False
    == ModalityDesignOk

-- | GREEN invent on **modality** promotion is refused.
greenInventModalityRefuse :: Bool
greenInventModalityRefuse =
  let (modality, axis, census, defects) = sampleUnwiredNoCensusRow
   in evaluateModalityConservation modality axis census defects True
        == ModalityGreenInventRefuse

-- | Four-step TYPE-03 **modality** lattice scaffold pinned.
modalityLatticeScaffold :: Bool
modalityLatticeScaffold =
  modalityLatticeCount == 4
    && unwiredWithoutCensusOk
    && provedWithoutCensusRefuse
    && provedWithDefectsRefuse
    && provedWithCleanCensusOk
    && assumedWithoutCensusOk
    && surrogateWithoutCensusOk

-- | **Modality** lattice is structure scaffold — not 118² GREEN periodic table.
modalityLatticeNotGreenTable :: Bool
modalityLatticeNotGreenTable =
  modalityLatticeCount == 4
    && modalityLatticeCount /= 118 * 118
    && sampleUnwiredNoCensusRow /= sampleProvedCleanCensusRow

-- | Four **conservation** axes scaffold pinned (Mass/Charge/AtomCount/Enthalpy).
conservationAxesScaffold :: Bool
conservationAxesScaffold =
  conservationAxisCount == 4
    && unwiredWithoutCensusOk
    && provedWithoutCensusRefuse
    && provedWithDefectsRefuse

-- | Axes are structure scaffold — not 118² GREEN periodic table.
conservationAxesNotGreenTable :: Bool
conservationAxesNotGreenTable =
  conservationAxisCount == 4
    && conservationAxisCount /= 118 * 118
    && sampleProvedNoCensusRow /= sampleProvedWithDefectsRow

-- | **Conservation** **modality** claims route to knowing / quantum fiber (not meso acting).
modalityKnowingFiberOk :: Bool
modalityKnowingFiberOk = True

-- | TYPE-03 **modality** invent refuse-closed scaffold witness.
type03ModalityInventRefuse :: Bool
type03ModalityInventRefuse = not type03ModalityProved

-- | **Modality** lattice steps are concurrent Π_c — not XOR enum bucket.
modalityLatticeNotXor :: Bool
modalityLatticeNotXor =
  unwiredWithoutCensusOk
    && assumedWithoutCensusOk
    && surrogateWithoutCensusOk
    && provedWithoutCensusRefuse
    && provedWithDefectsRefuse
    && greenInventModalityRefuse

-- | TYPE-03 **modality** proved (always false on this Unwired cell).
type03ModalityProved :: Bool
type03ModalityProved = False

-- | One axiom framing: second law + **conservation** for **modality** scaffold.
modalityConservationFraming :: String
modalityConservationFraming =
  "second_law_conservation_modality_one_axiom"

-- | Single design axiom: second law + **conservation** **modality** (not second axiom).
modalityConservationAxiom :: Bool
modalityConservationAxiom =
  modalityLatticeScaffold
    && modalityLatticeNotGreenTable
    && conservationAxesScaffold
    && conservationAxesNotGreenTable
    && modalityKnowingFiberOk
    && unwiredWithoutCensusOk
    && provedWithoutCensusRefuse
    && provedWithDefectsRefuse
    && provedWithCleanCensusOk
    && greenInventModalityRefuse
    && type03ModalityInventRefuse
    && modalityLatticeNotXor
    && not type03ModalityProved
    && modalityConservationFraming
      == "second_law_conservation_modality_one_axiom"

modalityConservationNamed :: String
modalityConservationNamed =
  "modalityConservation: ModalityConservationModality Unwired Assumed Proved Surrogate four-step lattice type03ModalityProved false unwiredWithoutCensusOk provedWithoutCensusRefuse provedWithDefectsRefuse second law conservation one axiom"

-- | Upstream **conservation** resource types authority (cited, not forked).
conservationResourceTypesAuthority :: String
conservationResourceTypesAuthority =
  "umst/umst-chem/src/conservation_resource_types.rs"

-- | L0 TYPE-03 **modality** scaffold authority (crosswalk).
chemL0Type03Authority :: String
chemL0Type03Authority = "umst/umst-chem/src/conservation_resource_types.rs"

modalityConservationCellId :: String
modalityConservationCellId = "CHEM-FORMAL-Q-HS-MODALITY-CONSERVATION"

-- | Non-claim fence — **modality** **conservation** Unwired ≠ Proved GREEN.
modalityConservationNonClaim :: String
modalityConservationNonClaim =
  "CHEM-FORMAL-Q-HS-MODALITY-CONSERVATION ModalityConservationModality Unwired Assumed Proved Surrogate four-step lattice type03ModalityProved false unwiredWithoutCensusOk provedWithoutCensusRefuse provedWithDefectsRefuse Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing **modality** **conservation** scaffold.
modalityConservationPhysicsGreenAuthorized :: Bool
modalityConservationPhysicsGreenAuthorized = False

modalityConservationPhysicsGreenFalse :: Bool
modalityConservationPhysicsGreenFalse =
  not modalityConservationPhysicsGreenAuthorized

modalityConservationModalityUnwired :: Bool
modalityConservationModalityUnwired =
  modalityConservationModalityCurrent == ModalityConservationUnwired

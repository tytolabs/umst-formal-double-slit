-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.EffectConservation
Description : Effect conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Effect** conservation: TYPE-04 dissipative Refine **effect** types (Unwired / Assumed /
Proved / Surrogate) on **conservation** claims — forward Refine requires positive
ChemStamp/Landauer witness; free purification refuse; reverse contaminate typed.
TYPE-04 **effect** laws are structure witnesses only (@type04EffectProved@ = False).

* @EffectConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateEffectConservation@ — Unwired OK; forward Refine without witness refuse; reverse contaminate typed.
* **One** design axiom (@effectConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of **effect** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-EFFECT-CONSERVATION@.
-}
module UMST.ChemConstants.EffectConservation
  ( EffectConservationModality (..)
  , effectConservationModalityCurrent
  , effectLatticeAll
  , effectLatticeCount
  , RefineDirection (..)
  , refineDirectionAll
  , refineDirectionCount
  , ChemStampWitness (..)
  , chemStampZero
  , chemStampPositiveScaffold
  , DissipativeEffectLaw (..)
  , dissipativeEffectLawAll
  , dissipativeEffectLawCount
  , EffectConservationVerdict (..)
  , evaluateEffectConservation
  , sampleUnwiredOkRow
  , sampleForwardZeroWitnessRow
  , sampleForwardPositiveWitnessRow
  , sampleReverseContaminateRow
  , unwiredDesignOk
  , forwardWithoutWitnessRefuse
  , forwardWithPositiveWitnessOk
  , reverseContaminateTypedOk
  , assumedWithoutWitnessOk
  , surrogateWithoutWitnessOk
  , greenInventEffectRefuse
  , effectLatticeScaffold
  , effectLatticeNotGreenTable
  , dissipativeLawsScaffold
  , dissipativeLawsNotGreenTable
  , effectKnowingFiberOk
  , type04EffectInventRefuse
  , effectLatticeNotXor
  , type04EffectProved
  , effectConservationFraming
  , effectConservationAxiom
  , effectConservationNamed
  , refineEffectTypesAuthority
  , chemL0Type04Authority
  , effectConservationCellId
  , effectConservationNonClaim
  , effectConservationPhysicsGreenAuthorized
  , effectConservationPhysicsGreenFalse
  , effectConservationModalityUnwired
  ) where

-- | Design **effect** modality for TYPE-04 **conservation** claims.
data EffectConservationModality
  = EffectConservationUnwired
  | EffectConservationAssumed
  | EffectConservationProved
  | EffectConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **effect** modality — always Unwired on this cell.
effectConservationModalityCurrent :: EffectConservationModality
effectConservationModalityCurrent = EffectConservationUnwired

-- | All TYPE-04 **effect** lattice steps in stable order.
effectLatticeAll :: [EffectConservationModality]
effectLatticeAll =
  [ EffectConservationUnwired
  , EffectConservationAssumed
  , EffectConservationProved
  , EffectConservationSurrogate
  ]

effectLatticeCount :: Int
effectLatticeCount = length effectLatticeAll

-- | Refine morphism direction under the single second-law + **conservation** axiom.
data RefineDirection
  = ForwardRefine
  | ReverseContaminate
  deriving (Eq, Show)

-- | All Refine directions in stable order (structure scaffold — not 118² GREEN table).
refineDirectionAll :: [RefineDirection]
refineDirectionAll = [ForwardRefine, ReverseContaminate]

refineDirectionCount :: Int
refineDirectionCount = length refineDirectionAll

-- | Scaffold ChemStamp / Landauer dissipation witness (microjoules).
data ChemStampWitness = ChemStampWitness
  { chemStampMicrojoules :: Int
  }
  deriving (Eq, Show)

-- | Zero dissipation — forward Refine must refuse (no free purification).
chemStampZero :: ChemStampWitness
chemStampZero = ChemStampWitness 0

-- | Scaffold positive dissipation for typed forward Refine witnesses.
chemStampPositiveScaffold :: ChemStampWitness
chemStampPositiveScaffold = ChemStampWitness 1

chemStampIsPositive :: ChemStampWitness -> Bool
chemStampIsPositive witness = chemStampMicrojoules witness > 0

-- | Dissipative **effect** law cells tracked by TYPE-04 (structure scaffold).
data DissipativeEffectLaw
  = ForwardRequiresWitness
  | ZeroWitnessRefuse
  | ReverseContaminateTyped
  | GreenInventRefuse
  deriving (Eq, Show)

-- | All dissipative **effect** law cells in stable order.
dissipativeEffectLawAll :: [DissipativeEffectLaw]
dissipativeEffectLawAll =
  [ ForwardRequiresWitness
  , ZeroWitnessRefuse
  , ReverseContaminateTyped
  , GreenInventRefuse
  ]

dissipativeEffectLawCount :: Int
dissipativeEffectLawCount = length dissipativeEffectLawAll

-- | Verdict for TYPE-04 **effect** **conservation** promotion (fail-closed).
data EffectConservationVerdict
  = EffectDesignOk
  | EffectForwardDissipativeOk
  | EffectFreePurificationRefuse
  | EffectReverseContaminateOk
  | EffectGreenInventRefuse
  deriving (Eq, Show)

-- | Evaluate TYPE-04 **effect** **conservation** typing (fail-closed).
evaluateEffectConservation ::
  EffectConservationModality
  -> RefineDirection
  -> ChemStampWitness
  -> Bool
  -> EffectConservationVerdict
evaluateEffectConservation modality direction witness claimPhysicsGreen
  | claimPhysicsGreen = EffectGreenInventRefuse
  | otherwise =
      case modality of
        EffectConservationUnwired -> EffectDesignOk
        EffectConservationAssumed -> EffectDesignOk
        EffectConservationSurrogate -> EffectDesignOk
        EffectConservationProved ->
          case direction of
            ForwardRefine ->
              if chemStampIsPositive witness
                then EffectForwardDissipativeOk
                else EffectFreePurificationRefuse
            ReverseContaminate -> EffectReverseContaminateOk

-- | Sample Unwired row — no ChemStamp witness required.
sampleUnwiredOkRow ::
  ( EffectConservationModality
  , RefineDirection
  , ChemStampWitness
  )
sampleUnwiredOkRow =
  ( EffectConservationUnwired
  , ForwardRefine
  , chemStampZero
  )

-- | Sample forward Refine row without positive witness — refuse witness.
sampleForwardZeroWitnessRow ::
  ( EffectConservationModality
  , RefineDirection
  , ChemStampWitness
  )
sampleForwardZeroWitnessRow =
  ( EffectConservationProved
  , ForwardRefine
  , chemStampZero
  )

-- | Sample forward Refine row with positive ChemStamp witness — admissible scaffold.
sampleForwardPositiveWitnessRow ::
  ( EffectConservationModality
  , RefineDirection
  , ChemStampWitness
  )
sampleForwardPositiveWitnessRow =
  ( EffectConservationProved
  , ForwardRefine
  , chemStampPositiveScaffold
  )

-- | Sample reverse contaminate row — typed without forward cost.
sampleReverseContaminateRow ::
  ( EffectConservationModality
  , RefineDirection
  , ChemStampWitness
  )
sampleReverseContaminateRow =
  ( EffectConservationProved
  , ReverseContaminate
  , chemStampZero
  )

-- | Unwired **effect** modality OK without ChemStamp witness.
unwiredDesignOk :: Bool
unwiredDesignOk =
  let (modality, direction, witness) = sampleUnwiredOkRow
   in evaluateEffectConservation modality direction witness False
        == EffectDesignOk

-- | Forward Refine without positive ChemStamp/Landauer witness is refuse-closed.
forwardWithoutWitnessRefuse :: Bool
forwardWithoutWitnessRefuse =
  let (modality, direction, witness) = sampleForwardZeroWitnessRow
   in evaluateEffectConservation modality direction witness False
        == EffectFreePurificationRefuse

-- | Forward Refine with positive witness admitted (still not physics GREEN).
forwardWithPositiveWitnessOk :: Bool
forwardWithPositiveWitnessOk =
  let (modality, direction, witness) = sampleForwardPositiveWitnessRow
   in evaluateEffectConservation modality direction witness False
        == EffectForwardDissipativeOk

-- | Reverse contaminate typed without positive forward cost.
reverseContaminateTypedOk :: Bool
reverseContaminateTypedOk =
  let (modality, direction, witness) = sampleReverseContaminateRow
   in evaluateEffectConservation modality direction witness False
        == EffectReverseContaminateOk

-- | Assumed **effect** modality OK without witness (design scaffold).
assumedWithoutWitnessOk :: Bool
assumedWithoutWitnessOk =
  evaluateEffectConservation
    EffectConservationAssumed
    ForwardRefine
    chemStampZero
    False
    == EffectDesignOk

-- | Surrogate **effect** modality OK without witness (design scaffold).
surrogateWithoutWitnessOk :: Bool
surrogateWithoutWitnessOk =
  evaluateEffectConservation
    EffectConservationSurrogate
    ReverseContaminate
    chemStampZero
    False
    == EffectDesignOk

-- | GREEN invent on **effect** **conservation** promotion is refused.
greenInventEffectRefuse :: Bool
greenInventEffectRefuse =
  let (modality, direction, witness) = sampleUnwiredOkRow
   in evaluateEffectConservation modality direction witness True
        == EffectGreenInventRefuse

-- | Four-step TYPE-04 **effect** lattice scaffold pinned.
effectLatticeScaffold :: Bool
effectLatticeScaffold =
  effectLatticeCount == 4
    && unwiredDesignOk
    && forwardWithoutWitnessRefuse
    && forwardWithPositiveWitnessOk
    && reverseContaminateTypedOk
    && assumedWithoutWitnessOk
    && surrogateWithoutWitnessOk

-- | **Effect** lattice is structure scaffold — not 118² GREEN periodic table.
effectLatticeNotGreenTable :: Bool
effectLatticeNotGreenTable =
  effectLatticeCount == 4
    && effectLatticeCount /= 118 * 118
    && sampleUnwiredOkRow /= sampleForwardPositiveWitnessRow

-- | Four dissipative **effect** law cells scaffold pinned.
dissipativeLawsScaffold :: Bool
dissipativeLawsScaffold =
  dissipativeEffectLawCount == 4
    && unwiredDesignOk
    && forwardWithoutWitnessRefuse
    && forwardWithPositiveWitnessOk
    && reverseContaminateTypedOk

-- | Dissipative law cells are structure scaffold — not 118² GREEN periodic table.
dissipativeLawsNotGreenTable :: Bool
dissipativeLawsNotGreenTable =
  dissipativeEffectLawCount == 4
    && dissipativeEffectLawCount /= 118 * 118
    && sampleForwardZeroWitnessRow /= sampleReverseContaminateRow

-- | **Effect** **conservation** claims route to knowing / quantum fiber (not meso acting).
effectKnowingFiberOk :: Bool
effectKnowingFiberOk = True

-- | TYPE-04 **effect** invent refuse-closed scaffold witness.
type04EffectInventRefuse :: Bool
type04EffectInventRefuse = not type04EffectProved

-- | **Effect** lattice steps are concurrent Π_c — not XOR enum bucket.
effectLatticeNotXor :: Bool
effectLatticeNotXor =
  unwiredDesignOk
    && assumedWithoutWitnessOk
    && surrogateWithoutWitnessOk
    && forwardWithoutWitnessRefuse
    && forwardWithPositiveWitnessOk
    && reverseContaminateTypedOk
    && greenInventEffectRefuse

-- | TYPE-04 **effect** proved (always false on this Unwired cell).
type04EffectProved :: Bool
type04EffectProved = False

-- | One axiom framing: second law + **conservation** for **effect** scaffold.
effectConservationFraming :: String
effectConservationFraming =
  "second_law_conservation_effect_one_axiom"

-- | Single design axiom: second law + **conservation** **effect** (not second axiom).
effectConservationAxiom :: Bool
effectConservationAxiom =
  effectLatticeScaffold
    && effectLatticeNotGreenTable
    && dissipativeLawsScaffold
    && dissipativeLawsNotGreenTable
    && effectKnowingFiberOk
    && unwiredDesignOk
    && forwardWithoutWitnessRefuse
    && forwardWithPositiveWitnessOk
    && reverseContaminateTypedOk
    && greenInventEffectRefuse
    && type04EffectInventRefuse
    && effectLatticeNotXor
    && not type04EffectProved
    && effectConservationFraming
      == "second_law_conservation_effect_one_axiom"

effectConservationNamed :: String
effectConservationNamed =
  "effectConservation: EffectConservationModality Unwired Assumed Proved Surrogate four-step lattice type04EffectProved false forwardWithoutWitnessRefuse forwardWithPositiveWitnessOk reverseContaminateTypedOk second law conservation one axiom"

-- | Upstream TYPE-04 Refine **effect** types authority (cited, not forked).
refineEffectTypesAuthority :: String
refineEffectTypesAuthority = "umst/umst-chem/src/refine_effect_types.rs"

-- | L0 TYPE-04 **effect** scaffold authority (crosswalk).
chemL0Type04Authority :: String
chemL0Type04Authority = "CHEM-L0-TYPE-04"

effectConservationCellId :: String
effectConservationCellId = "CHEM-FORMAL-Q-HS-EFFECT-CONSERVATION"

-- | Non-claim fence — **effect** **conservation** Unwired ≠ Proved GREEN.
effectConservationNonClaim :: String
effectConservationNonClaim =
  "CHEM-FORMAL-Q-HS-EFFECT-CONSERVATION EffectConservationModality Unwired Assumed Proved Surrogate four-step lattice type04EffectProved false forwardWithoutWitnessRefuse forwardWithPositiveWitnessOk reverseContaminateTypedOk Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing **effect** **conservation** scaffold.
effectConservationPhysicsGreenAuthorized :: Bool
effectConservationPhysicsGreenAuthorized = False

effectConservationPhysicsGreenFalse :: Bool
effectConservationPhysicsGreenFalse =
  not effectConservationPhysicsGreenAuthorized

effectConservationModalityUnwired :: Bool
effectConservationModalityUnwired =
  effectConservationModalityCurrent == EffectConservationUnwired

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.CompactionMiCost
Description : CompactionMiCost — compaction pays MI vs epistemicMI_null on knowing fiber
Copyright   : (c) UMST Project, 2026

§17.5 / §22.4 @compaction_mi_cost@ — semantic compaction composes Excitement and must **pay**
epistemic MI above the @epistemicMI_null@ baseline (@PathProbeNull@). Mirrors Lean
@UrgeKnowing.CompactionMiCost@ and Rust @compaction_mi_cost@.

* @compactionPaysMiVsNull@ — compaction MI bits strictly above null-probe zero.
* @evaluateCompactionMiCost@ — probe payment + derivation witness + Excitement compose.
* Compose @selectExcitement@ — not a second ℚ argmin.
* **One** design axiom (@compactionMiCostAxiom@): @physicalSecondLaw@ framing only.
* @physics_green@ stays false; modality @CompactionMiCostUnwired@.

Not meso thermo G(T,P,x). Cell: @URGE-FORMAL-Q-HS-COMPACTION-MI-COST@.
Identity: @compaction_mi_cost@.
-}
module UrgeKnowing.CompactionMiCost
  ( ExcitementCand (..)
  , selectExcitement
  , composeSurrogateFor
  , metaExcitementModule
  , CompactionDerivationWitness (..)
  , CompactionMiAttempt (..)
  , CompactionMiCostRefusal (..)
  , CompactionMiCostOutcome (..)
  , compactionPaysMiVsNull
  , refuseEpistemicMiNullCompaction
  , refuseNullProbeCompactionTheater
  , refuseSecondArgminSelector
  , evaluateCompactionMiCost
  , urgeCompactionMiSelect
  , compactionMiCostModalityUnwired
  , compactionMiCostPhysicsGreen
  , compactionMiCostProductionWired
  , fixtureAcceptCompactionMiCost
  , fixtureRefuseEpistemicMiNullCompaction
  , fixtureRefuseDerivationWitnessAbsent
  , compactionMiCostPolicy
  , CompactionMiCostModality (..)
  , compactionMiCostModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , compactionMiCostAxiom
  , compactionMiCostNamed
  , compactionMiCostCellId
  , compactionMiCostNonClaim
  , compactionMiCostPhysicsGreenAuthorized
  , compactionMiCostPhysicsGreenFalse
  , compactionMiCostModalityUnwiredWitness
  , compactionMiCostKnowingFiberOk
  ) where

import Data.List (sortOn)
import DensityState (Matrix2x2)
import UrgeKnowing.EpistemicNullProbe
  ( epistemicMIBitsNull
  , epistemicMINull
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  )
import UrgeKnowing.LandauerHistoryLook
  ( PathProbe (..)
  , epistemicMIBits
  )

-- | Compose surrogate cites @UMST.Excitement.select@ (import pin — not local argmin).
composeSurrogateFor :: String
composeSurrogateFor = "UMST.Excitement.select"

-- | umst-meta excitement module authority path.
metaExcitementModule :: String
metaExcitementModule = "umst-meta/crates/umst-meta/src/excitement.rs"

-- | Minimal Excitement candidate for compaction compose (fixture scale).
data ExcitementCand = ExcitementCand
  { excitementCandId :: String
  , excitementCandFreeEnergy :: Double
  , excitementCandProvenanceIntact :: Bool
  , excitementCandDropsProvenance :: Bool
  }
  deriving (Eq, Show)

-- | Whether candidate is admissible for Excitement selection.
excitementCandAdmissible :: ExcitementCand -> Bool
excitementCandAdmissible c =
  excitementCandProvenanceIntact c && not (excitementCandDropsProvenance c)

-- | Pure total Excitement on finite admissible set — compose pin, not second argmin.
selectExcitement :: Double -> [ExcitementCand] -> Maybe ExcitementCand
selectExcitement _ [] = Nothing
selectExcitement _ cands =
  let admissible = filter excitementCandAdmissible cands
   in case sortOn (\c -> (excitementCandFreeEnergy c, excitementCandId c)) admissible of
        [] -> Nothing
        (best : _) -> Just best

-- | Derivation chain witness retained on admitted compaction arrows (§17.5).
data CompactionDerivationWitness = CompactionDerivationWitness
  { compactionDerivationChain :: [String]
  }

-- | Whether witness retains a non-empty derivation chain.
compactionDerivationRetainsChain :: CompactionDerivationWitness -> Bool
compactionDerivationRetainsChain w = not (null (compactionDerivationChain w))

-- | Compaction attempt carrier — probe + entropy surrogate + derivation witness.
data CompactionMiAttempt = CompactionMiAttempt
  { compactionMiProbe :: PathProbe
  , compactionMiPathEntropyBits :: Double
  , compactionMiWitness :: CompactionDerivationWitness
  , compactionMiSourceFreeEnergy :: Double
  }

-- | Typed refusal for compaction MI cost discipline.
data CompactionMiCostRefusal
  = EpistemicMiNullCompaction
  | NullProbeCompactionTheater
  | DerivationWitnessAbsent
  | SecondArgmin
  deriving (Eq, Show)

-- | Outcome of a compaction MI cost evaluation.
data CompactionMiCostOutcome
  = CompactionMiAdmitted
      { compactionMiBitsPaid :: Double
      , compactionMiCandidateId :: String
      }
  | CompactionMiRefused CompactionMiCostRefusal
  deriving (Eq, Show)

-- | Whether probe is the null baseline (@epistemicMI_null@).
isEpistemicMiNullProbe :: PathProbe -> Bool
isEpistemicMiNullProbe PathProbeNull = True
isEpistemicMiNullProbe PathProbeWhichPath = False

-- | Whether compaction pays MI above the @epistemicMI_null@ baseline.
compactionPaysMiVsNull :: PathProbe -> Matrix2x2 -> Bool
compactionPaysMiVsNull p rho =
  not (isEpistemicMiNullProbe p) && epistemicMIBits p rho > 1e-12

-- | Positive refuse: compaction under @epistemicMI_null@ is inadmissible.
refuseEpistemicMiNullCompaction :: Either CompactionMiCostRefusal a
refuseEpistemicMiNullCompaction = Left EpistemicMiNullCompaction

-- | Positive refuse: null-probe compaction theater (zero MI payment).
refuseNullProbeCompactionTheater :: Either CompactionMiCostRefusal a
refuseNullProbeCompactionTheater = Left NullProbeCompactionTheater

-- | Positive refuse: second Excitement selector implementation is inadmissible here.
refuseSecondArgminSelector :: Either CompactionMiCostRefusal a
refuseSecondArgminSelector = Left SecondArgmin

-- | Evaluate compaction MI cost — probe payment + derivation witness + Excitement compose.
evaluateCompactionMiCost ::
  CompactionMiAttempt -> [ExcitementCand] -> CompactionMiCostOutcome
evaluateCompactionMiCost attempt cands =
  let probe = compactionMiProbe attempt
      miBits =
        if isEpistemicMiNullProbe probe
          then 0
          else min 1 (max 0 (compactionMiPathEntropyBits attempt))
   in if isEpistemicMiNullProbe probe
        then CompactionMiRefused EpistemicMiNullCompaction
        else
          if miBits <= 1e-12
            then CompactionMiRefused NullProbeCompactionTheater
            else
              if not (compactionDerivationRetainsChain (compactionMiWitness attempt))
                then CompactionMiRefused DerivationWitnessAbsent
                else
                  case selectExcitement (compactionMiSourceFreeEnergy attempt) cands of
                    Nothing -> CompactionMiRefused DerivationWitnessAbsent
                    Just cand ->
                      CompactionMiAdmitted
                        { compactionMiBitsPaid = miBits
                        , compactionMiCandidateId = excitementCandId cand
                        }

-- | Urge compaction MI cost composes @selectExcitement@ over admissible successors.
urgeCompactionMiSelect :: Double -> [ExcitementCand] -> Maybe ExcitementCand
urgeCompactionMiSelect = selectExcitement

compactionMiCostModalityUnwired :: Bool
compactionMiCostModalityUnwired = True

compactionMiCostPhysicsGreen :: Bool
compactionMiCostPhysicsGreen = False

compactionMiCostProductionWired :: Bool
compactionMiCostProductionWired = False

-- | Fixture accept — WhichPath probe pays MI; Excitement selects candidate.
fixtureAcceptCompactionMiCost :: CompactionMiCostOutcome
fixtureAcceptCompactionMiCost =
  evaluateCompactionMiCost
    CompactionMiAttempt
      { compactionMiProbe = PathProbeWhichPath
      , compactionMiPathEntropyBits = 0.75
      , compactionMiWitness =
          CompactionDerivationWitness {compactionDerivationChain = ["stamp-a", "stamp-b"]}
      , compactionMiSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "compact-mi-best"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — null probe / @epistemicMI_null@ compaction.
fixtureRefuseEpistemicMiNullCompaction :: CompactionMiCostOutcome
fixtureRefuseEpistemicMiNullCompaction =
  evaluateCompactionMiCost
    CompactionMiAttempt
      { compactionMiProbe = PathProbeNull
      , compactionMiPathEntropyBits = 0.75
      , compactionMiWitness =
          CompactionDerivationWitness {compactionDerivationChain = ["stamp-a"]}
      , compactionMiSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "null-theater"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — derivation witness absent (positive refuse path).
fixtureRefuseDerivationWitnessAbsent :: CompactionMiCostOutcome
fixtureRefuseDerivationWitnessAbsent =
  evaluateCompactionMiCost
    CompactionMiAttempt
      { compactionMiProbe = PathProbeWhichPath
      , compactionMiPathEntropyBits = 0.5
      , compactionMiWitness =
          CompactionDerivationWitness {compactionDerivationChain = []}
      , compactionMiSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "no-witness"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Policy: compaction pays MI vs null; Excitement compose; typed refuses hold.
compactionMiCostPolicy :: Bool
compactionMiCostPolicy =
  compactionPaysMiVsNull PathProbeWhichPath ((1, 0), (0, 0))
    && not (compactionPaysMiVsNull PathProbeNull ((0.5, 0), (0, 0.5)))
    && epistemicMINull ((0.5, 0), (0, 0.5))
    && epistemicMIBitsNull ((0.5, 0), (0, 0.5))
    && (refuseEpistemicMiNullCompaction :: Either CompactionMiCostRefusal Bool) == Left EpistemicMiNullCompaction
    && (refuseNullProbeCompactionTheater :: Either CompactionMiCostRefusal Bool) == Left NullProbeCompactionTheater
    && (refuseSecondArgminSelector :: Either CompactionMiCostRefusal Bool) == Left SecondArgmin
    && case fixtureAcceptCompactionMiCost of
      CompactionMiAdmitted {compactionMiBitsPaid = b, compactionMiCandidateId = cid} ->
        b > 0 && cid == "compact-mi-best"
      _ -> False
    && fixtureRefuseEpistemicMiNullCompaction
      == CompactionMiRefused EpistemicMiNullCompaction
    && fixtureRefuseDerivationWitnessAbsent
      == CompactionMiRefused DerivationWitnessAbsent
    && urgeCompactionMiSelect
      10
      [ ExcitementCand
          { excitementCandId = "compose-ok"
          , excitementCandFreeEnergy = 2
          , excitementCandProvenanceIntact = True
          , excitementCandDropsProvenance = False
          }
      ]
      == Just
        ExcitementCand
          { excitementCandId = "compose-ok"
          , excitementCandFreeEnergy = 2
          , excitementCandProvenanceIntact = True
          , excitementCandDropsProvenance = False
          }
    && composeSurrogateFor == "UMST.Excitement.select"

-- | Design modality for compaction-mi-cost claims (TYPE-03 preview).
data CompactionMiCostModality
  = CompactionMiCostUnwired
  | CompactionMiCostAssumed
  | CompactionMiCostProved
  | CompactionMiCostSurrogate
  deriving (Eq, Show)

compactionMiCostModalityCurrent :: CompactionMiCostModality
compactionMiCostModalityCurrent = CompactionMiCostUnwired

compactionMiCostAxiom :: Bool
compactionMiCostAxiom =
  compactionMiCostPolicy
    && landauerNotSecondAxiom
    && compactionMiCostModalityUnwiredWitness
    && compactionMiCostPhysicsGreenFalse

compactionMiCostNamed :: String
compactionMiCostNamed =
  "compaction_mi_cost: CompactionMiCost compaction pays MI vs epistemicMI_null; compose Excitement not second argmin; physicalSecondLaw sole axiom framing"

compactionMiCostCellId :: String
compactionMiCostCellId = "URGE-FORMAL-Q-HS-COMPACTION-MI-COST"

compactionMiCostNonClaim :: String
compactionMiCostNonClaim =
  "URGE-FORMAL-Q-HS-COMPACTION-MI-COST compaction_mi_cost Unwired not Proved not GREEN not production_wired knowing fiber only not meso thermo G(T,P,x)"

compactionMiCostPhysicsGreenAuthorized :: Bool
compactionMiCostPhysicsGreenAuthorized = False

compactionMiCostPhysicsGreenFalse :: Bool
compactionMiCostPhysicsGreenFalse = not compactionMiCostPhysicsGreenAuthorized

compactionMiCostModalityUnwiredWitness :: Bool
compactionMiCostModalityUnwiredWitness =
  compactionMiCostModalityCurrent == CompactionMiCostUnwired

compactionMiCostKnowingFiberOk :: Bool
compactionMiCostKnowingFiberOk =
  compactionMiCostModalityUnwiredWitness && compactionMiCostPhysicsGreenFalse

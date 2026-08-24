-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.EpistemicQueryLook
Description : EpistemicQueryLook — §18 query is verification cost (information-up)
Copyright   : (c) UMST Project, 2026

§18 @epistemic_query_look@ — knowing fiber query is verification cost
(information-up), not coordination theater. Mirrors Agda @UrgeKnowing.EpistemicQueryLook@,
Coq @EpistemicQueryLook.v@, and Rust @epistemic_query_look@.

* @queryLookVerificationBits@ — information-up verification bits for admitted looks.
* @queryLookLandauerCost@ — Landauer lower bound at verification bits.
* @evaluateEpistemicQueryLook@ — query admission + Excitement compose.
* Compose @selectExcitement@ — not a second ℚ argmin.
* **One** design axiom (@epistemicQueryLookAxiom@): @physicalSecondLaw@ framing only.
* @physics_green@ stays false; modality @EpistemicQueryLookUnwired@.

Not meso thermo G(T,P,x). Cell: @URGE-FORMAL-Q-HS-EPISTEMIC-QUERY-LOOK@.
Identity: @epistemic_query_look@.
-}
module UrgeKnowing.EpistemicQueryLook
  ( ExcitementCand (..)
  , selectExcitement
  , composeSurrogateFor
  , metaExcitementModule
  , QueryLookClass (..)
  , FormalFiber (..)
  , EpistemicQueryLook (..)
  , verificationCostLook
  , coordinationTheaterLook
  , queryLookClassIsVerificationCost
  , queryLookClassIsCoordinationTheater
  , queryLookVerificationBits
  , queryLookVerificationBitsNonneg
  , queryLookLandauerCost
  , queryLookLandauerCostNonneg
  , queryLookLandauerCostLeBitEnergy
  , queryLookProbeBitsAlign
  , EpistemicQueryLookRefusal (..)
  , EpistemicQueryLookOutcome (..)
  , admitEpistemicQueryLook
  , refuseCoordinationTheater
  , refuseSecondArgminSelector
  , physicalSecondLawBound
  , EpistemicQueryLookAttempt (..)
  , evaluateEpistemicQueryLook
  , urgeQueryLookSelect
  , epistemicQueryLookModalityUnwired
  , epistemicQueryLookPhysicsGreen
  , epistemicQueryLookProductionWired
  , fixtureAcceptEpistemicQueryLook
  , fixtureRefuseCoordinationTheater
  , fixtureRefuseMesoFiberMisroute
  , fixtureRefuseNonPositiveVerificationBits
  , epistemicQueryLookPolicy
  , EpistemicQueryLookModality (..)
  , epistemicQueryLookModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , epistemicQueryLookAxiom
  , epistemicQueryLookNamed
  , epistemicQueryLookCellId
  , epistemicQueryLookNonClaim
  , landauerLawAuthority
  , epistemicQueryLookPhysicsGreenAuthorized
  , epistemicQueryLookPhysicsGreenFalse
  , epistemicQueryLookModalityUnwiredWitness
  , epistemicQueryLookKnowingFiberOk
  ) where

import Data.List (sortOn)
import DoubleSlit (landauerBitEnergy)
import MeasurementCost (infoEnergyLowerBound)
import UrgeKnowing.EpistemicNullProbe
  ( physicalSecondLawAxiom
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

-- | Minimal Excitement candidate for epistemic query look compose (fixture scale).
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

-- | §18 query class — verification cost (information-up) vs coordination theater.
data QueryLookClass
  = VerificationCost Double
  | CoordinationTheater
  deriving (Eq, Show)

-- | Formal fiber — knowing vs meso acting.
data FormalFiber
  = MesoActing
  | QuantumKnowing
  deriving (Eq, Show)

-- | Epistemic query look carrier on the knowing fiber.
data EpistemicQueryLook = EpistemicQueryLook
  { epistemicQueryLookClass :: QueryLookClass
  , epistemicQueryLookFiber :: FormalFiber
  }
  deriving (Eq, Show)

-- | Construct verification-cost query look on quantum knowing fiber.
verificationCostLook :: Double -> EpistemicQueryLook
verificationCostLook bits =
  EpistemicQueryLook
    { epistemicQueryLookClass = VerificationCost bits
    , epistemicQueryLookFiber = QuantumKnowing
    }

-- | Construct coordination-theater query look (fixture for positive refuse).
coordinationTheaterLook :: EpistemicQueryLook
coordinationTheaterLook =
  EpistemicQueryLook
    { epistemicQueryLookClass = CoordinationTheater
    , epistemicQueryLookFiber = QuantumKnowing
    }

-- | Whether query class is information-up verification cost.
queryLookClassIsVerificationCost :: QueryLookClass -> Bool
queryLookClassIsVerificationCost (VerificationCost _) = True
queryLookClassIsVerificationCost CoordinationTheater = False

-- | Whether query class is coordination theater.
queryLookClassIsCoordinationTheater :: QueryLookClass -> Bool
queryLookClassIsCoordinationTheater CoordinationTheater = True
queryLookClassIsCoordinationTheater (VerificationCost _) = False

-- | Verification bits for query look — zero for coordination theater.
queryLookVerificationBits :: EpistemicQueryLook -> Double
queryLookVerificationBits look =
  case epistemicQueryLookClass look of
    VerificationCost bits -> bits
    CoordinationTheater -> 0

-- | Whether verification bits are non-negative.
queryLookVerificationBitsNonneg :: EpistemicQueryLook -> Bool
queryLookVerificationBitsNonneg look =
  queryLookVerificationBits look >= -1e-12

-- | Landauer lower bound at verification bits and temperature @t@.
queryLookLandauerCost :: Double -> EpistemicQueryLook -> Double
queryLookLandauerCost t look =
  infoEnergyLowerBound (queryLookVerificationBits look) t

-- | Whether Landauer cost is non-negative at temperature @t@.
queryLookLandauerCostNonneg :: Double -> EpistemicQueryLook -> Bool
queryLookLandauerCostNonneg t look =
  queryLookLandauerCost t look >= -1e-12

-- | Whether Landauer cost is bounded by one bit-energy when bits ≤ 1.
queryLookLandauerCostLeBitEnergy :: Double -> EpistemicQueryLook -> Bool
queryLookLandauerCostLeBitEnergy t look =
  let bits = queryLookVerificationBits look
   in bits <= 1 + 1e-12
        && queryLookLandauerCost t look <= landauerBitEnergy t + 1e-12

-- | Probe bits align — verification-cost look tracks @epistemicMIBits@.
queryLookProbeBitsAlign :: PathProbe -> Bool
queryLookProbeBitsAlign p =
  let bits = epistemicMIBits p ((0.5, 0), (0, 0.5))
   in abs (queryLookVerificationBits (verificationCostLook bits) - bits) <= 1e-12

-- | Typed refusal for epistemic query look discipline.
data EpistemicQueryLookRefusal
  = CoordinationTheaterRefused
  | MesoFiberMisroute
  | NonPositiveVerificationBits
  | SecondArgmin
  deriving (Eq, Show)

-- | Outcome of epistemic query look admission.
data EpistemicQueryLookOutcome
  = EpistemicQueryLookAdmitted
      { epistemicQueryLookBitsPaid :: Double
      , epistemicQueryLookCandidateId :: String
      }
  | EpistemicQueryLookRefused EpistemicQueryLookRefusal
  deriving (Eq, Show)

-- | Admit or refuse epistemic query look on the knowing fiber.
admitEpistemicQueryLook :: EpistemicQueryLook -> Maybe EpistemicQueryLookRefusal
admitEpistemicQueryLook look =
  case epistemicQueryLookFiber look of
    MesoActing -> Just MesoFiberMisroute
    QuantumKnowing ->
      case epistemicQueryLookClass look of
        CoordinationTheater -> Just CoordinationTheaterRefused
        VerificationCost bits ->
          if bits <= 0
            then Just NonPositiveVerificationBits
            else Nothing

-- | Positive refuse: query as coordination theater is inadmissible.
refuseCoordinationTheater :: Either EpistemicQueryLookRefusal a
refuseCoordinationTheater = Left CoordinationTheaterRefused

-- | Positive refuse: second Excitement selector implementation is inadmissible here.
refuseSecondArgminSelector :: Either EpistemicQueryLookRefusal a
refuseSecondArgminSelector = Left SecondArgmin

-- | Definitional physical-second-law bound witness (sole axiom framing hook).
physicalSecondLawBound :: Int -> Int -> Bool
physicalSecondLawBound entropyDecrease dissipatedEntropy =
  entropyDecrease <= dissipatedEntropy

-- | Epistemic query look attempt — look + temperature + source FE.
data EpistemicQueryLookAttempt = EpistemicQueryLookAttempt
  { epistemicQueryLookAttemptLook :: EpistemicQueryLook
  , epistemicQueryLookAttemptTemperature :: Double
  , epistemicQueryLookAttemptSourceFreeEnergy :: Double
  }
  deriving (Eq, Show)

-- | Evaluate epistemic query look — admission + Landauer hook + Excitement compose.
evaluateEpistemicQueryLook ::
  EpistemicQueryLookAttempt -> [ExcitementCand] -> EpistemicQueryLookOutcome
evaluateEpistemicQueryLook attempt cands =
  let look = epistemicQueryLookAttemptLook attempt
   in case admitEpistemicQueryLook look of
        Just refusal -> EpistemicQueryLookRefused refusal
        Nothing ->
          let bits = queryLookVerificationBits look
           in case selectExcitement (epistemicQueryLookAttemptSourceFreeEnergy attempt) cands of
                Nothing -> EpistemicQueryLookRefused NonPositiveVerificationBits
                Just exc ->
                  EpistemicQueryLookAdmitted
                    { epistemicQueryLookBitsPaid = bits
                    , epistemicQueryLookCandidateId = excitementCandId exc
                    }

-- | Urge epistemic query look composes @selectExcitement@ over admissible witnesses.
urgeQueryLookSelect :: Double -> [ExcitementCand] -> Maybe ExcitementCand
urgeQueryLookSelect = selectExcitement

epistemicQueryLookModalityUnwired :: Bool
epistemicQueryLookModalityUnwired = True

epistemicQueryLookPhysicsGreen :: Bool
epistemicQueryLookPhysicsGreen = False

epistemicQueryLookProductionWired :: Bool
epistemicQueryLookProductionWired = False

-- | Fixture accept — verification-cost query look with Excitement witness.
fixtureAcceptEpistemicQueryLook :: EpistemicQueryLookOutcome
fixtureAcceptEpistemicQueryLook =
  evaluateEpistemicQueryLook
    EpistemicQueryLookAttempt
      { epistemicQueryLookAttemptLook = verificationCostLook 0.75
      , epistemicQueryLookAttemptTemperature = 300
      , epistemicQueryLookAttemptSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "query-witness-best"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — coordination theater query look.
fixtureRefuseCoordinationTheater :: EpistemicQueryLookOutcome
fixtureRefuseCoordinationTheater =
  evaluateEpistemicQueryLook
    EpistemicQueryLookAttempt
      { epistemicQueryLookAttemptLook = coordinationTheaterLook
      , epistemicQueryLookAttemptTemperature = 300
      , epistemicQueryLookAttemptSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "coord-theater"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — meso acting fiber misroute.
fixtureRefuseMesoFiberMisroute :: EpistemicQueryLookOutcome
fixtureRefuseMesoFiberMisroute =
  evaluateEpistemicQueryLook
    EpistemicQueryLookAttempt
      { epistemicQueryLookAttemptLook =
          EpistemicQueryLook
            { epistemicQueryLookClass = VerificationCost 0.5
            , epistemicQueryLookFiber = MesoActing
            }
      , epistemicQueryLookAttemptTemperature = 300
      , epistemicQueryLookAttemptSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "meso-misroute"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — non-positive verification bits.
fixtureRefuseNonPositiveVerificationBits :: EpistemicQueryLookOutcome
fixtureRefuseNonPositiveVerificationBits =
  evaluateEpistemicQueryLook
    EpistemicQueryLookAttempt
      { epistemicQueryLookAttemptLook = verificationCostLook 0
      , epistemicQueryLookAttemptTemperature = 300
      , epistemicQueryLookAttemptSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "zero-bits"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Policy: verification cost information-up; coordination refused; Excitement compose.
epistemicQueryLookPolicy :: Bool
epistemicQueryLookPolicy =
  queryLookClassIsVerificationCost (VerificationCost 0.75)
    && not (queryLookClassIsCoordinationTheater (VerificationCost 0.75))
    && queryLookClassIsCoordinationTheater CoordinationTheater
    && not (queryLookClassIsVerificationCost CoordinationTheater)
    && queryLookVerificationBits (verificationCostLook 1) == 1
    && queryLookVerificationBits coordinationTheaterLook == 0
    && queryLookVerificationBitsNonneg (verificationCostLook 0.3)
    && queryLookLandauerCostNonneg 300 (verificationCostLook 0.3)
    && queryLookLandauerCostLeBitEnergy 300 (verificationCostLook 0.5)
    && queryLookProbeBitsAlign PathProbeNull
    && queryLookProbeBitsAlign PathProbeWhichPath
    && admitEpistemicQueryLook (verificationCostLook 0.75) == Nothing
    && admitEpistemicQueryLook coordinationTheaterLook
      == Just CoordinationTheaterRefused
    && admitEpistemicQueryLook
      ( EpistemicQueryLook
          { epistemicQueryLookClass = VerificationCost 0.5
          , epistemicQueryLookFiber = MesoActing
          }
      )
      == Just MesoFiberMisroute
    && admitEpistemicQueryLook (verificationCostLook 0) == Just NonPositiveVerificationBits
    && (refuseCoordinationTheater :: Either EpistemicQueryLookRefusal Bool)
      == Left CoordinationTheaterRefused
    && (refuseSecondArgminSelector :: Either EpistemicQueryLookRefusal Bool)
      == Left SecondArgmin
    && physicalSecondLawBound 2 2
    && case fixtureAcceptEpistemicQueryLook of
      EpistemicQueryLookAdmitted
        { epistemicQueryLookBitsPaid = b
        , epistemicQueryLookCandidateId = cid
        } ->
        abs (b - 0.75) <= 1e-12 && cid == "query-witness-best"
      _ -> False
    && fixtureRefuseCoordinationTheater
      == EpistemicQueryLookRefused CoordinationTheaterRefused
    && fixtureRefuseMesoFiberMisroute == EpistemicQueryLookRefused MesoFiberMisroute
    && fixtureRefuseNonPositiveVerificationBits
      == EpistemicQueryLookRefused NonPositiveVerificationBits
    && urgeQueryLookSelect
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
    && physicalSecondLawAxiom == "LandauerLaw.physicalSecondLaw"
    && landauerLawAuthority /= ""
    && not epistemicQueryLookProductionWired
    && not epistemicQueryLookPhysicsGreen

-- | Design modality for epistemic query look claims (TYPE-03 preview).
data EpistemicQueryLookModality
  = EpistemicQueryLookUnwired
  | EpistemicQueryLookAssumed
  | EpistemicQueryLookProved
  | EpistemicQueryLookSurrogate
  deriving (Eq, Show)

epistemicQueryLookModalityCurrent :: EpistemicQueryLookModality
epistemicQueryLookModalityCurrent = EpistemicQueryLookUnwired

epistemicQueryLookAxiom :: Bool
epistemicQueryLookAxiom =
  epistemicQueryLookPolicy
    && landauerNotSecondAxiom
    && epistemicQueryLookModalityUnwiredWitness
    && epistemicQueryLookPhysicsGreenFalse

epistemicQueryLookNamed :: String
epistemicQueryLookNamed =
  "epistemic_query_look: §18 query verification cost information-up not coordination theater knowing fiber LandauerBound sole axiom physicalSecondLaw"

epistemicQueryLookCellId :: String
epistemicQueryLookCellId = "URGE-FORMAL-Q-HS-EPISTEMIC-QUERY-LOOK"

epistemicQueryLookNonClaim :: String
epistemicQueryLookNonClaim =
  "URGE-FORMAL-Q-HS-EPISTEMIC-QUERY-LOOK epistemic_query_look Unwired not Proved not GREEN not production_wired knowing fiber only §18 query is verification cost information-up not coordination compose Excitement no second argmin sole axiom physicalSecondLaw"

landauerLawAuthority :: String
landauerLawAuthority = "umst/umst-formal-double-slit/Lean/LandauerLaw.lean"

epistemicQueryLookPhysicsGreenAuthorized :: Bool
epistemicQueryLookPhysicsGreenAuthorized = False

epistemicQueryLookPhysicsGreenFalse :: Bool
epistemicQueryLookPhysicsGreenFalse = not epistemicQueryLookPhysicsGreenAuthorized

epistemicQueryLookModalityUnwiredWitness :: Bool
epistemicQueryLookModalityUnwiredWitness =
  epistemicQueryLookModalityCurrent == EpistemicQueryLookUnwired

epistemicQueryLookKnowingFiberOk :: Bool
epistemicQueryLookKnowingFiberOk =
  epistemicQueryLookFiber (verificationCostLook 1) == QuantumKnowing
    && epistemicQueryLookModalityUnwiredWitness
    && epistemicQueryLookPhysicsGreenFalse

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.MeasurementCostSync
Description : MeasurementCostSync — §16 measurement cost of a sync look on knowing fiber
Copyright   : (c) UMST Project, 2026

§16 @measurement_cost_sync@ — measurement / Landauer cost of a **sync look** when an
observer inspects inbound state during Kleisli sync — distinct from rollout history
look and meso thermo G(T,P,x). Mirrors Coq @UrgeKnowing.MeasurementCostSync@ and
Rust @measurement_cost_sync@.

* @syncLookMIBits@ — probe-indexed MI bits for sync look (null / which-path).
* @syncLookMeasurementCost@ — Landauer lower bound at temperature @T@.
* @evaluateSyncLookMeasurementCost@ — probe payment + Excitement compose.
* Compose @selectExcitement@ — not a second ℚ argmin.
* **One** design axiom (@measurementCostSyncAxiom@): @physicalSecondLaw@ framing only.
* @physics_green@ stays false; modality @MeasurementCostSyncUnwired@.

Not meso thermo G(T,P,x). Cell: @URGE-FORMAL-Q-HS-MEASUREMENT-COST-SYNC@.
Identity: @measurement_cost_sync@.
-}
module UrgeKnowing.MeasurementCostSync
  ( ExcitementCand (..)
  , selectExcitement
  , composeSurrogateFor
  , metaExcitementModule
  , SyncLookMiAttempt (..)
  , SyncLookMeasurementCostRefusal (..)
  , SyncLookMeasurementCostOutcome (..)
  , clampPathEntropyBits
  , syncLookStepMIBounded
  , syncLookMIBits
  , syncLookMeasurementCost
  , syncLookMeasurementCostNullZero
  , syncLookMeasurementCostNonneg
  , syncLookMeasurementCostLeBitEnergy
  , refuseSyncLookNullProbe
  , refuseSyncLookNullProbeTheater
  , refuseSecondArgminSelector
  , evaluateSyncLookMeasurementCost
  , urgeSyncLookSelect
  , measurementCostSyncModalityUnwired
  , measurementCostSyncPhysicsGreen
  , measurementCostSyncProductionWired
  , fixtureAcceptSyncLookMeasurementCost
  , fixtureRefuseSyncLookNullProbe
  , fixtureRefuseSecondArgmin
  , measurementCostSyncPolicy
  , MeasurementCostSyncModality (..)
  , measurementCostSyncModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , measurementCostSyncAxiom
  , measurementCostSyncNamed
  , measurementCostSyncCellId
  , measurementCostSyncNonClaim
  , measurementCostSyncPhysicsGreenAuthorized
  , measurementCostSyncPhysicsGreenFalse
  , measurementCostSyncModalityUnwiredWitness
  , measurementCostSyncKnowingFiberOk
  ) where

import Data.List (sortOn)
import DoubleSlit (landauerBitEnergy)
import MeasurementCost (infoEnergyLowerBound)
import UrgeKnowing.EpistemicNullProbe
  ( physicalSecondLawAxiom
  , landauerNotSecondAxiom
  )
import UrgeKnowing.LandauerHistoryLook (PathProbe (..))

-- | Compose surrogate cites @UMST.Excitement.select@ (import pin — not local argmin).
composeSurrogateFor :: String
composeSurrogateFor = "UMST.Excitement.select"

-- | umst-meta excitement module authority path.
metaExcitementModule :: String
metaExcitementModule = "umst-meta/crates/umst-meta/src/excitement.rs"

-- | Minimal Excitement candidate for sync-look compose (fixture scale).
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

-- | Clamp path entropy bits to [0, 1] for sync-look MI surrogate.
clampPathEntropyBits :: Double -> Double
clampPathEntropyBits bits = max 0 (min 1 bits)

-- | Whether MI bits lie in [0, 1] for a sync-look step.
syncLookStepMIBounded :: Double -> Bool
syncLookStepMIBounded mi = mi >= 0 && mi <= 1 + 1e-12

-- | Probe-indexed MI bits for sync look (null probe => zero).
syncLookMIBits :: PathProbe -> Double -> Double
syncLookMIBits PathProbeNull _ = 0
syncLookMIBits PathProbeWhichPath pathEntropyBits =
  clampPathEntropyBits pathEntropyBits

-- | Landauer measurement-cost lower bound for sync look at temperature @t@.
syncLookMeasurementCost :: PathProbe -> Double -> Double -> Double
syncLookMeasurementCost probe pathEntropyBits t =
  infoEnergyLowerBound (syncLookMIBits probe pathEntropyBits) t

-- | Null probe sync look carries zero mandatory dissipation.
syncLookMeasurementCostNullZero :: Double -> Double -> Bool
syncLookMeasurementCostNullZero pathEntropyBits t =
  syncLookMeasurementCost PathProbeNull pathEntropyBits t == 0

-- | Sync-look measurement cost is non-negative at non-negative temperature.
syncLookMeasurementCostNonneg :: PathProbe -> Double -> Double -> Bool
syncLookMeasurementCostNonneg probe pathEntropyBits t =
  if t >= 0
    then syncLookMeasurementCost probe pathEntropyBits t >= 0
    else True

-- | Sync-look cost bounded by one Landauer bit-energy when MI ≤ 1 bit.
syncLookMeasurementCostLeBitEnergy :: PathProbe -> Double -> Double -> Bool
syncLookMeasurementCostLeBitEnergy probe pathEntropyBits t =
  if t >= 0 && syncLookStepMIBounded (syncLookMIBits probe pathEntropyBits)
    then
      syncLookMeasurementCost probe pathEntropyBits t
        <= landauerBitEnergy t + 1e-18
    else True

-- | Sync-look attempt carrier — probe + entropy surrogate + temperature + source FE.
data SyncLookMiAttempt = SyncLookMiAttempt
  { syncLookProbe :: PathProbe
  , syncLookPathEntropyBits :: Double
  , syncLookTemperature :: Double
  , syncLookSourceFreeEnergy :: Double
  }

-- | Typed refusal for sync-look measurement cost discipline.
data SyncLookMeasurementCostRefusal
  = SyncLookNullProbe
  | SyncLookNullProbeTheater
  | SecondArgmin
  deriving (Eq, Show)

-- | Outcome of a sync-look measurement cost evaluation.
data SyncLookMeasurementCostOutcome
  = SyncLookMeasurementAdmitted
      { syncLookMiBitsPaid :: Double
      , syncLookEnergyPaid :: Double
      , syncLookCandidateId :: String
      }
  | SyncLookMeasurementRefused SyncLookMeasurementCostRefusal
  deriving (Eq, Show)

-- | Whether probe is the null baseline.
isSyncLookNullProbe :: PathProbe -> Bool
isSyncLookNullProbe PathProbeNull = True
isSyncLookNullProbe PathProbeWhichPath = False

-- | Positive refuse: sync look under null probe is inadmissible.
refuseSyncLookNullProbe :: Either SyncLookMeasurementCostRefusal a
refuseSyncLookNullProbe = Left SyncLookNullProbe

-- | Positive refuse: null-probe sync-look theater (zero MI payment).
refuseSyncLookNullProbeTheater :: Either SyncLookMeasurementCostRefusal a
refuseSyncLookNullProbeTheater = Left SyncLookNullProbeTheater

-- | Positive refuse: second Excitement selector implementation is inadmissible here.
refuseSecondArgminSelector :: Either SyncLookMeasurementCostRefusal a
refuseSecondArgminSelector = Left SecondArgmin

-- | Evaluate sync-look measurement cost — probe payment + Excitement compose.
evaluateSyncLookMeasurementCost ::
  SyncLookMiAttempt -> [ExcitementCand] -> SyncLookMeasurementCostOutcome
evaluateSyncLookMeasurementCost attempt cands =
  let probe = syncLookProbe attempt
      miBits = syncLookMIBits probe (syncLookPathEntropyBits attempt)
      energy =
        syncLookMeasurementCost
          probe
          (syncLookPathEntropyBits attempt)
          (syncLookTemperature attempt)
   in if isSyncLookNullProbe probe
        then SyncLookMeasurementRefused SyncLookNullProbe
        else
          if miBits <= 1e-12
            then SyncLookMeasurementRefused SyncLookNullProbeTheater
            else
              case selectExcitement (syncLookSourceFreeEnergy attempt) cands of
                Nothing -> SyncLookMeasurementRefused SecondArgmin
                Just cand ->
                  SyncLookMeasurementAdmitted
                    { syncLookMiBitsPaid = miBits
                    , syncLookEnergyPaid = energy
                    , syncLookCandidateId = excitementCandId cand
                    }

-- | Urge sync-look composes @selectExcitement@ over admissible successors.
urgeSyncLookSelect :: Double -> [ExcitementCand] -> Maybe ExcitementCand
urgeSyncLookSelect = selectExcitement

measurementCostSyncModalityUnwired :: Bool
measurementCostSyncModalityUnwired = True

measurementCostSyncPhysicsGreen :: Bool
measurementCostSyncPhysicsGreen = False

measurementCostSyncProductionWired :: Bool
measurementCostSyncProductionWired = False

-- | Fixture accept — WhichPath probe pays MI; Excitement selects candidate.
fixtureAcceptSyncLookMeasurementCost :: SyncLookMeasurementCostOutcome
fixtureAcceptSyncLookMeasurementCost =
  evaluateSyncLookMeasurementCost
    SyncLookMiAttempt
      { syncLookProbe = PathProbeWhichPath
      , syncLookPathEntropyBits = 0.75
      , syncLookTemperature = 300
      , syncLookSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "sync-look-best"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — null probe sync look.
fixtureRefuseSyncLookNullProbe :: SyncLookMeasurementCostOutcome
fixtureRefuseSyncLookNullProbe =
  evaluateSyncLookMeasurementCost
    SyncLookMiAttempt
      { syncLookProbe = PathProbeNull
      , syncLookPathEntropyBits = 0.75
      , syncLookTemperature = 300
      , syncLookSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "null-theater"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — empty candidate set triggers second-argmin refusal path.
fixtureRefuseSecondArgmin :: SyncLookMeasurementCostOutcome
fixtureRefuseSecondArgmin =
  evaluateSyncLookMeasurementCost
    SyncLookMiAttempt
      { syncLookProbe = PathProbeWhichPath
      , syncLookPathEntropyBits = 0.5
      , syncLookTemperature = 300
      , syncLookSourceFreeEnergy = 10
      }
    []

-- | Policy: sync look pays MI vs null; Excitement compose; typed refuses hold.
measurementCostSyncPolicy :: Bool
measurementCostSyncPolicy =
  syncLookMIBits PathProbeNull 0.75 == 0
    && syncLookMIBits PathProbeWhichPath 0.75 > 0
    && syncLookStepMIBounded (syncLookMIBits PathProbeWhichPath 0.75)
    && syncLookMeasurementCostNullZero 0.75 300
    && syncLookMeasurementCostNonneg PathProbeWhichPath 0.5 300
    && syncLookMeasurementCostLeBitEnergy PathProbeWhichPath 0.5 300
    && (refuseSyncLookNullProbe :: Either SyncLookMeasurementCostRefusal Bool)
      == Left SyncLookNullProbe
    && (refuseSyncLookNullProbeTheater :: Either SyncLookMeasurementCostRefusal Bool)
      == Left SyncLookNullProbeTheater
    && (refuseSecondArgminSelector :: Either SyncLookMeasurementCostRefusal Bool)
      == Left SecondArgmin
    && case fixtureAcceptSyncLookMeasurementCost of
      SyncLookMeasurementAdmitted
        { syncLookMiBitsPaid = b
        , syncLookEnergyPaid = e
        , syncLookCandidateId = cid
        } ->
        b > 0 && e > 0 && cid == "sync-look-best"
      _ -> False
    && fixtureRefuseSyncLookNullProbe == SyncLookMeasurementRefused SyncLookNullProbe
    && fixtureRefuseSecondArgmin == SyncLookMeasurementRefused SecondArgmin
    && urgeSyncLookSelect
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

-- | Design modality for measurement-cost-sync claims (TYPE-03 preview).
data MeasurementCostSyncModality
  = MeasurementCostSyncUnwired
  | MeasurementCostSyncAssumed
  | MeasurementCostSyncProved
  | MeasurementCostSyncSurrogate
  deriving (Eq, Show)

measurementCostSyncModalityCurrent :: MeasurementCostSyncModality
measurementCostSyncModalityCurrent = MeasurementCostSyncUnwired

measurementCostSyncAxiom :: Bool
measurementCostSyncAxiom =
  measurementCostSyncPolicy
    && landauerNotSecondAxiom
    && measurementCostSyncModalityUnwiredWitness
    && measurementCostSyncPhysicsGreenFalse

measurementCostSyncNamed :: String
measurementCostSyncNamed =
  "measurement_cost_sync: MeasurementCostSync §16 sync look pays MI vs null probe; compose Excitement not second argmin; physicalSecondLaw sole axiom framing"

measurementCostSyncCellId :: String
measurementCostSyncCellId = "URGE-FORMAL-Q-HS-MEASUREMENT-COST-SYNC"

measurementCostSyncNonClaim :: String
measurementCostSyncNonClaim =
  "URGE-FORMAL-Q-HS-MEASUREMENT-COST-SYNC measurement_cost_sync Unwired not Proved not GREEN not production_wired knowing fiber only not meso thermo G(T,P,x)"

measurementCostSyncPhysicsGreenAuthorized :: Bool
measurementCostSyncPhysicsGreenAuthorized = False

measurementCostSyncPhysicsGreenFalse :: Bool
measurementCostSyncPhysicsGreenFalse = not measurementCostSyncPhysicsGreenAuthorized

measurementCostSyncModalityUnwiredWitness :: Bool
measurementCostSyncModalityUnwiredWitness =
  measurementCostSyncModalityCurrent == MeasurementCostSyncUnwired

measurementCostSyncKnowingFiberOk :: Bool
measurementCostSyncKnowingFiberOk =
  measurementCostSyncModalityUnwiredWitness && measurementCostSyncPhysicsGreenFalse

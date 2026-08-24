-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.MachineTemperature
Description : MachineTemperature — §17.2 Excitement T is machine temperature on knowing fiber
Copyright   : (c) UMST Project, 2026

§17.2 @machine_temperature@ — Excitement @T@ is the temperature of the coupled
repository-in-machine (Landauer erasure environment), not wall clock and not an
abstract DAG scalar. Cross-node energy witness may refuse. Mirrors Agda
@UrgeKnowing.MachineTemperature@ and Rust @machine_temperature@.

* @evaluateMachineTemperature@ — ontology admission with Landauer floor surrogate.
* Compose @selectExcitement@ — not a second ℚ argmin.
* **One** design axiom (@machineTemperatureAxiom@): @physicalSecondLaw@ framing only.
* @physics_green@ stays false; modality @MachineTemperatureUnwired@.

Not meso thermo G(T,P,x). Cell: @URGE-FORMAL-Q-HS-MACHINE-TEMPERATURE@.
Identity: @machine_temperature@.
-}
module UrgeKnowing.MachineTemperature
  ( ExcitementCand (..)
  , selectExcitement
  , composeSurrogateFor
  , metaExcitementModule
  , TemperatureSource (..)
  , MachineTemperature (..)
  , MachineTemperatureCandidate (..)
  , MachineTemperatureWitness (..)
  , MachineTemperatureRefusal (..)
  , MachineTemperatureOutcome (..)
  , kBMilli
  , tKelvinFromMilli
  , landauerFloorMilliJoule
  , machineTemperatureAdmitPred
  , evaluateMachineTemperature
  , refuseWallClockAsTemperature
  , refuseAbstractDagScalarAsTemperature
  , refuseSecondArgminSelector
  , urgeSelectAtTemperature
  , machineTemperatureModalityUnwired
  , machineTemperaturePhysicsGreen
  , machineTemperatureProductionWired
  , fixtureM3Accept
  , fixtureWallClockRefuse
  , fixtureDagScalarRefuse
  , fixtureThinkpadCrossNodeRefuse
  , fixtureAcceptMachineTemperature
  , fixtureRefuseWallClockAsTemperature
  , fixtureRefuseDagScalarAsTemperature
  , fixtureRefuseCrossNodeEnergyWitness
  , machineTemperaturePolicy
  , MachineTemperatureModality (..)
  , machineTemperatureModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , machineTemperatureAxiom
  , machineTemperatureNamed
  , machineTemperatureCellId
  , machineTemperatureNonClaim
  , machineTemperaturePhysicsGreenAuthorized
  , machineTemperaturePhysicsGreenFalse
  , machineTemperatureModalityUnwiredWitness
  , machineTemperatureKnowingFiberOk
  ) where

import Data.List (sortOn)
import UrgeKnowing.EpistemicNullProbe
  ( landauerNotSecondAxiom
  , physicalSecondLawAxiom
  )

-- | Compose surrogate cites @UMST.Excitement.select@ (import pin — not local argmin).
composeSurrogateFor :: String
composeSurrogateFor = "UMST.Excitement.select"

-- | umst-meta excitement module authority path.
metaExcitementModule :: String
metaExcitementModule = "umst-meta/crates/umst-meta/src/excitement.rs"

-- | Minimal Excitement candidate for machine-temperature compose (fixture scale).
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

-- | What Excitement T is pinned to (§17.2).
data TemperatureSource
  = RepositoryInMachine
  | WallClockTheater
  | AbstractDagScalar
  deriving (Eq, Show)

-- | Machine temperature T — coupled repository-in-machine, not wall clock.
data MachineTemperature = MachineTemperature
  { machineTemperatureKelvinMilli :: Integer
  , machineTemperatureNodeId :: String
  , machineTemperatureSource :: TemperatureSource
  }
  deriving (Eq, Show)

-- | Candidate for machine-temperature ontology admission.
data MachineTemperatureCandidate = MachineTemperatureCandidate
  { machineTemperatureCandKelvinMilli :: Integer
  , machineTemperatureCandNodeId :: String
  , machineTemperatureCandSource :: TemperatureSource
  , machineTemperatureCandErasureBits :: Integer
  , machineTemperatureCandAvailableEnergyMilliJoule :: Integer
  }
  deriving (Eq, Show)

-- | Typed witness — repository-in-machine T with energy floor satisfied.
data MachineTemperatureWitness = MachineTemperatureWitness
  { machineTemperatureWitnessTemperature :: MachineTemperature
  , machineTemperatureWitnessLandauerFloorMilliJoule :: Integer
  , machineTemperatureWitnessAvailableEnergyMilliJoule :: Integer
  }
  deriving (Eq, Show)

-- | Typed refusal for machine-temperature ontology discipline.
data MachineTemperatureRefusal
  = WallClockAsTemperature
  | AbstractDagScalarAsTemperature
  | CrossNodeEnergyWitnessMismatch
      { crossNodeNodeId :: String
      , crossNodeLandauerFloorMilliJoule :: Integer
      , crossNodeAvailableEnergyMilliJoule :: Integer
      }
  | SecondArgmin
  deriving (Eq, Show)

-- | Outcome of machine-temperature evaluation.
data MachineTemperatureOutcome
  = MachineTemperatureAdmitted MachineTemperatureWitness
  | MachineTemperatureRefused MachineTemperatureRefusal
  deriving (Eq, Show)

-- | Boltzmann constant surrogate (milli-scale integer pin — not measured physics).
kBMilli :: Integer
kBMilli = 138

-- | Kelvin from milli-Kelvin surrogate (typed integer — not wall-clock measured).
tKelvinFromMilli :: Integer -> Integer
tKelvinFromMilli 0 = 1
tKelvinFromMilli kelvinMilli =
  let raw = kelvinMilli `div` 1000
   in if raw == 0 then 1 else raw

-- | Landauer floor surrogate: k_B T ln(2) per bit at milli scale (typed, not measured).
landauerFloorMilliJoule :: Integer -> Integer -> Integer
landauerFloorMilliJoule kelvinMilli erasureBits =
  let tKelvin = tKelvinFromMilli kelvinMilli
   in (tKelvin * kBMilli * erasureBits * 693) `div` 1000000

-- | Core typed predicate — repository-in-machine source and energy floor cleared.
machineTemperatureAdmitPred :: MachineTemperatureCandidate -> Bool
machineTemperatureAdmitPred c =
  machineTemperatureCandSource c == RepositoryInMachine
    && machineTemperatureCandAvailableEnergyMilliJoule c
      >= landauerFloorMilliJoule
        (machineTemperatureCandKelvinMilli c)
        (machineTemperatureCandErasureBits c)

-- | Positive refuse: wall-clock timestamp as Excitement T is inadmissible.
refuseWallClockAsTemperature :: Either MachineTemperatureRefusal a
refuseWallClockAsTemperature = Left WallClockAsTemperature

-- | Positive refuse: abstract DAG scalar as Excitement T is inadmissible.
refuseAbstractDagScalarAsTemperature :: Either MachineTemperatureRefusal a
refuseAbstractDagScalarAsTemperature = Left AbstractDagScalarAsTemperature

-- | Positive refuse: second Excitement selector implementation is inadmissible here.
refuseSecondArgminSelector :: Either MachineTemperatureRefusal a
refuseSecondArgminSelector = Left SecondArgmin

-- | Evaluate machine-temperature ontology — honest refuse on inadmissible inputs.
evaluateMachineTemperature ::
  MachineTemperatureCandidate -> MachineTemperatureOutcome
evaluateMachineTemperature c =
  case machineTemperatureCandSource c of
    WallClockTheater -> MachineTemperatureRefused WallClockAsTemperature
    AbstractDagScalar -> MachineTemperatureRefused AbstractDagScalarAsTemperature
    RepositoryInMachine ->
      let floorMj =
            landauerFloorMilliJoule
              (machineTemperatureCandKelvinMilli c)
              (machineTemperatureCandErasureBits c)
          avail = machineTemperatureCandAvailableEnergyMilliJoule c
       in if avail < floorMj
            then
              MachineTemperatureRefused
                CrossNodeEnergyWitnessMismatch
                  { crossNodeNodeId = machineTemperatureCandNodeId c
                  , crossNodeLandauerFloorMilliJoule = floorMj
                  , crossNodeAvailableEnergyMilliJoule = avail
                  }
            else
              MachineTemperatureAdmitted
                MachineTemperatureWitness
                  { machineTemperatureWitnessTemperature =
                      MachineTemperature
                        { machineTemperatureKelvinMilli =
                            machineTemperatureCandKelvinMilli c
                        , machineTemperatureNodeId = machineTemperatureCandNodeId c
                        , machineTemperatureSource = RepositoryInMachine
                        }
                  , machineTemperatureWitnessLandauerFloorMilliJoule = floorMj
                  , machineTemperatureWitnessAvailableEnergyMilliJoule = avail
                  }

-- | Urge recovery composes @selectExcitement@ at admitted machine T.
urgeSelectAtTemperature ::
  MachineTemperatureWitness -> Double -> [ExcitementCand] -> Maybe ExcitementCand
urgeSelectAtTemperature witness srcFreeEnergy cands =
  if machineTemperatureSource (machineTemperatureWitnessTemperature witness)
       == RepositoryInMachine
    then selectExcitement srcFreeEnergy cands
    else Nothing

machineTemperatureModalityUnwired :: Bool
machineTemperatureModalityUnwired = True

machineTemperaturePhysicsGreen :: Bool
machineTemperaturePhysicsGreen = False

machineTemperatureProductionWired :: Bool
machineTemperatureProductionWired = False

-- | Fixture: M3 node — repository-in-machine T admits (§17.2 accept case).
fixtureM3Accept :: MachineTemperatureCandidate
fixtureM3Accept =
  MachineTemperatureCandidate
    { machineTemperatureCandKelvinMilli = 310000
    , machineTemperatureCandNodeId = "node-m3-rapl"
    , machineTemperatureCandSource = RepositoryInMachine
    , machineTemperatureCandErasureBits = 64
    , machineTemperatureCandAvailableEnergyMilliJoule = 50000000
    }

-- | Fixture: wall-clock theater as T (§17.2 refuse case 1).
fixtureWallClockRefuse :: MachineTemperatureCandidate
fixtureWallClockRefuse =
  MachineTemperatureCandidate
    { machineTemperatureCandKelvinMilli = 0
    , machineTemperatureCandNodeId = "wall-clock-theater"
    , machineTemperatureCandSource = WallClockTheater
    , machineTemperatureCandErasureBits = 0
    , machineTemperatureCandAvailableEnergyMilliJoule = 0
    }

-- | Fixture: abstract DAG scalar as T (§17.2 refuse case 2).
fixtureDagScalarRefuse :: MachineTemperatureCandidate
fixtureDagScalarRefuse =
  MachineTemperatureCandidate
    { machineTemperatureCandKelvinMilli = 1
    , machineTemperatureCandNodeId = "dag-scalar-theater"
    , machineTemperatureCandSource = AbstractDagScalar
    , machineTemperatureCandErasureBits = 0
    , machineTemperatureCandAvailableEnergyMilliJoule = 1000000
    }

-- | Fixture: ThinkPad node — cross-node energy witness mismatch (refuse on node-1).
fixtureThinkpadCrossNodeRefuse :: MachineTemperatureCandidate
fixtureThinkpadCrossNodeRefuse =
  MachineTemperatureCandidate
    { machineTemperatureCandKelvinMilli = 320000
    , machineTemperatureCandNodeId = "node-thinkpad"
    , machineTemperatureCandSource = RepositoryInMachine
    , machineTemperatureCandErasureBits = 64
    , machineTemperatureCandAvailableEnergyMilliJoule = 1
    }

-- | Fixture accept — M3 repository-in-machine T admits.
fixtureAcceptMachineTemperature :: MachineTemperatureOutcome
fixtureAcceptMachineTemperature = evaluateMachineTemperature fixtureM3Accept

-- | Fixture refuse — wall-clock theater as T.
fixtureRefuseWallClockAsTemperature :: MachineTemperatureOutcome
fixtureRefuseWallClockAsTemperature = evaluateMachineTemperature fixtureWallClockRefuse

-- | Fixture refuse — abstract DAG scalar as T.
fixtureRefuseDagScalarAsTemperature :: MachineTemperatureOutcome
fixtureRefuseDagScalarAsTemperature = evaluateMachineTemperature fixtureDagScalarRefuse

-- | Fixture refuse — cross-node energy witness mismatch.
fixtureRefuseCrossNodeEnergyWitness :: MachineTemperatureOutcome
fixtureRefuseCrossNodeEnergyWitness =
  evaluateMachineTemperature fixtureThinkpadCrossNodeRefuse

-- | Policy: machine T ontology, Landauer floor, Excitement compose; typed refuses hold.
machineTemperaturePolicy :: Bool
machineTemperaturePolicy =
  machineTemperatureAdmitPred fixtureM3Accept
    && not (machineTemperatureAdmitPred fixtureWallClockRefuse)
    && not (machineTemperatureAdmitPred fixtureDagScalarRefuse)
    && not (machineTemperatureAdmitPred fixtureThinkpadCrossNodeRefuse)
    && (refuseWallClockAsTemperature :: Either MachineTemperatureRefusal Bool)
      == Left WallClockAsTemperature
    && (refuseAbstractDagScalarAsTemperature :: Either MachineTemperatureRefusal Bool)
      == Left AbstractDagScalarAsTemperature
    && (refuseSecondArgminSelector :: Either MachineTemperatureRefusal Bool)
      == Left SecondArgmin
    && case fixtureAcceptMachineTemperature of
      MachineTemperatureAdmitted w ->
        machineTemperatureSource (machineTemperatureWitnessTemperature w)
          == RepositoryInMachine
          && machineTemperatureWitnessLandauerFloorMilliJoule w > 0
      _ -> False
    && fixtureRefuseWallClockAsTemperature
      == MachineTemperatureRefused WallClockAsTemperature
    && fixtureRefuseDagScalarAsTemperature
      == MachineTemperatureRefused AbstractDagScalarAsTemperature
    && case fixtureRefuseCrossNodeEnergyWitness of
      MachineTemperatureRefused CrossNodeEnergyWitnessMismatch {crossNodeNodeId = nid} ->
        nid == "node-thinkpad"
      _ -> False
    && case urgeSelectAtTemperature
      (case fixtureAcceptMachineTemperature of
        MachineTemperatureAdmitted w -> w
        _ ->
          MachineTemperatureWitness
            { machineTemperatureWitnessTemperature =
                MachineTemperature
                  { machineTemperatureKelvinMilli = 310000
                  , machineTemperatureNodeId = "node-m3-rapl"
                  , machineTemperatureSource = RepositoryInMachine
                  }
            , machineTemperatureWitnessLandauerFloorMilliJoule = 1
            , machineTemperatureWitnessAvailableEnergyMilliJoule = 50000000
            })
      10
      [ ExcitementCand
          { excitementCandId = "machine-t-ok"
          , excitementCandFreeEnergy = 2
          , excitementCandProvenanceIntact = True
          , excitementCandDropsProvenance = False
          }
      ] of
      Just cand -> excitementCandId cand == "machine-t-ok"
      Nothing -> False
    && composeSurrogateFor == "UMST.Excitement.select"

-- | Design modality for machine-temperature claims (TYPE-03 preview).
data MachineTemperatureModality
  = MachineTemperatureUnwired
  | MachineTemperatureAssumed
  | MachineTemperatureProved
  | MachineTemperatureSurrogate
  deriving (Eq, Show)

machineTemperatureModalityCurrent :: MachineTemperatureModality
machineTemperatureModalityCurrent = MachineTemperatureUnwired

machineTemperatureAxiom :: Bool
machineTemperatureAxiom =
  machineTemperaturePolicy
    && landauerNotSecondAxiom
    && machineTemperatureModalityUnwiredWitness
    && machineTemperaturePhysicsGreenFalse

machineTemperatureNamed :: String
machineTemperatureNamed =
  "machine_temperature: Excitement T repository-in-machine LandauerBound not wall clock not DAG scalar; compose Excitement not second argmin; physicalSecondLaw sole axiom framing"

machineTemperatureCellId :: String
machineTemperatureCellId = "URGE-FORMAL-Q-HS-MACHINE-TEMPERATURE"

machineTemperatureNonClaim :: String
machineTemperatureNonClaim =
  "URGE-FORMAL-Q-HS-MACHINE-TEMPERATURE machine_temperature Unwired not Proved not GREEN not production_wired knowing fiber only not meso thermo G(T,P,x) Excitement T machine temperature not wall clock not abstract DAG scalar"

machineTemperaturePhysicsGreenAuthorized :: Bool
machineTemperaturePhysicsGreenAuthorized = False

machineTemperaturePhysicsGreenFalse :: Bool
machineTemperaturePhysicsGreenFalse = not machineTemperaturePhysicsGreenAuthorized

machineTemperatureModalityUnwiredWitness :: Bool
machineTemperatureModalityUnwiredWitness =
  machineTemperatureModalityCurrent == MachineTemperatureUnwired

machineTemperatureKnowingFiberOk :: Bool
machineTemperatureKnowingFiberOk =
  machineTemperatureModalityUnwiredWitness && machineTemperaturePhysicsGreenFalse

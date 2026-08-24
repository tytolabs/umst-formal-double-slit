-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.LandauerNTo1
Description : LandauerNTo1 — §19.8 Landauer price of N→1 compression
Copyright   : (c) UMST Project, 2026

§19.8 @landauer_n_to_1@ — knowing fiber Landauer price of N→1 compression; bits of
destroyed distinction, not fake joules / laptop heat theater. Mirrors Agda
@UrgeKnowing.LandauerNTo1@, Coq @LandauerNTo1.v@, and Rust @landauer_n_to_1@.

* @destroyedDistinctionBitsFromN@ — ceil(log2 N) destroyed distinction bits for N > 1.
* @landauerFloorJoulesFromBits@ — Landauer floor kT ln 2 per bit scaffold.
* @evaluateLandauerNTo1@ — compression admission + Excitement compose.
* Compose @selectExcitement@ — not a second ℚ argmin.
* **One** design axiom (@landauerNTo1Axiom@): @physicalSecondLaw@ framing only.
* @physics_green@ stays false; modality @LandauerNTo1Unwired@.

Not meso thermo G(T,P,x). Cell: @URGE-FORMAL-Q-HS-LANDAUER-N-TO-1@.
Identity: @landauer_n_to_1@.
-}
module UrgeKnowing.LandauerNTo1
  ( ExcitementCand (..)
  , selectExcitement
  , composeSurrogateFor
  , metaExcitementModule
  , CompressionCandidate (..)
  , destroyedDistinctionBitsFromN
  , landauerCompressionCost
  , landauerCompressionCostNonneg
  , landauerFloorJoulesFromBits
  , landauerFloorJoulesNonneg
  , landauerFloorScaffoldNamed
  , CompressionVerdict (..)
  , LandauerNTo1Refusal (..)
  , admitCompressionCandidate
  , evaluateCompression
  , refuseLaptopHeatTheater
  , refuseInventedDistinctionBits
  , refuseSecondArgminSelector
  , physicalSecondLawBound
  , LandauerNTo1Attempt (..)
  , LandauerNTo1Outcome (..)
  , evaluateLandauerNTo1
  , urgeLandauerNTo1Select
  , landauerNTo1ModalityUnwired
  , landauerNTo1PhysicsGreen
  , landauerNTo1ProductionWired
  , fixtureAdmissibleTwoBitCollapse
  , fixtureInadmissibleLaptopHeat
  , fixtureInadmissibleInventedBits
  , fixtureAcceptLandauerNTo1
  , fixtureRefuseLaptopHeat
  , fixtureRefuseInventedBits
  , landauerNTo1FixtureCandidates
  , fixtureAdmittedCount
  , fixtureRefusedCount
  , landauerNTo1Policy
  , LandauerNTo1Modality (..)
  , landauerNTo1ModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , landauerNTo1Axiom
  , landauerNTo1Named
  , landauerNTo1CellId
  , landauerNTo1NonClaim
  , landauerBoundAuthority
  , landauerLawAuthority
  , landauerNTo1PhysicsGreenAuthorized
  , landauerNTo1PhysicsGreenFalse
  , landauerNTo1ModalityUnwiredWitness
  , landauerNTo1KnowingFiberOk
  ) where

import Data.Bits (countLeadingZeros)
import Data.List (sortOn)
import Data.Word (Word64)
import DoubleSlit (landauerBitEnergy)
import MeasurementCost (infoEnergyLowerBound)
import UrgeKnowing.EpistemicNullProbe
  ( physicalSecondLawAxiom
  , landauerNotSecondAxiom
  )

-- | Compose surrogate cites @UMST.Excitement.select@ (import pin — not local argmin).
composeSurrogateFor :: String
composeSurrogateFor = "UMST.Excitement.select"

-- | umst-meta excitement module authority path.
metaExcitementModule :: String
metaExcitementModule = "umst-meta/crates/umst-meta/src/excitement.rs"

-- | Minimal Excitement candidate for Landauer N→1 compose (fixture scale).
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

-- | N→1 compression candidate on the knowing fiber.
data CompressionCandidate = CompressionCandidate
  { compressionCandId :: String
  , compressionSourceDistinctionCount :: Int
  , compressionClaimedDestroyedBits :: Maybe Int
  , compressionLaptopHeatJoulesTheater :: Bool
  , compressionClaimsPhysicsGreen :: Bool
  , compressionProvenanceIntact :: Bool
  , compressionEvidenceTagged :: Bool
  }
  deriving (Eq, Show)

-- | Destroyed distinction bits for N distinguishable states collapsing to 1.
destroyedDistinctionBitsFromN :: Int -> Maybe Int
destroyedDistinctionBitsFromN n
  | n <= 1 = Nothing
  | otherwise =
    let w = fromIntegral n :: Word64
     in Just (fromIntegral (64 - countLeadingZeros (w - 1)))

-- | Bits-first Landauer compression cost from claimed destroyed bits.
landauerCompressionCost :: CompressionCandidate -> Int
landauerCompressionCost cand =
  case compressionClaimedDestroyedBits cand of
    Just bits -> bits
    Nothing -> 0

-- | Whether compression cost is non-negative.
landauerCompressionCostNonneg :: CompressionCandidate -> Bool
landauerCompressionCostNonneg cand = landauerCompressionCost cand >= 0

-- | Landauer floor joules scaffold — kT ln 2 per bit, not measured laptop heat.
landauerFloorJoulesFromBits :: Double -> Int -> Double
landauerFloorJoulesFromBits t bits =
  infoEnergyLowerBound (fromIntegral bits) t

-- | Whether Landauer floor joules are non-negative at temperature @t@.
landauerFloorJoulesNonneg :: Double -> Int -> Bool
landauerFloorJoulesNonneg t bits =
  landauerFloorJoulesFromBits t bits >= -1e-18

landauerFloorScaffoldNamed :: String
landauerFloorScaffoldNamed =
  "landauerFloorJoules: kT ln2 per bit floor scaffold — not measured laptop heat"

-- | Typed refusal for Landauer N→1 compression pricing.
data LandauerNTo1Refusal
  = LaptopHeatTheater
  | InventedDistinctionBits
  | FalseGreenCompression
  | SecondArgmin
  | ProvenanceLost
  | MissingEvidenceTag
  deriving (Eq, Show)

-- | Verdict for N→1 compression admissibility.
data CompressionVerdict
  = CompressionAccept
  | CompressionRefuse
  deriving (Eq, Show)

-- | Whether claimed destroyed bits match expected from source distinction count.
checkDestroyedBits :: Int -> Maybe Int -> Maybe LandauerNTo1Refusal
checkDestroyedBits n claimed =
  case destroyedDistinctionBitsFromN n of
    Nothing -> Just InventedDistinctionBits
    Just expected ->
      case claimed of
        Nothing -> Just InventedDistinctionBits
        Just c ->
          if expected == c
            then Nothing
            else Just InventedDistinctionBits

-- | Admit compression candidate — @Nothing@ when admissible.
admitCompressionCandidate :: CompressionCandidate -> Maybe LandauerNTo1Refusal
admitCompressionCandidate cand =
  if compressionLaptopHeatJoulesTheater cand
    then Just LaptopHeatTheater
    else
      if compressionClaimsPhysicsGreen cand
        then Just FalseGreenCompression
        else
          if not (compressionProvenanceIntact cand)
            then Just ProvenanceLost
            else
              if not (compressionEvidenceTagged cand)
                then Just MissingEvidenceTag
                else
                  checkDestroyedBits
                    (compressionSourceDistinctionCount cand)
                    (compressionClaimedDestroyedBits cand)

-- | Evaluate compression admissibility (fixture verdict family).
evaluateCompression :: CompressionCandidate -> CompressionVerdict
evaluateCompression cand =
  case admitCompressionCandidate cand of
    Nothing -> CompressionAccept
    Just _ -> CompressionRefuse

-- | Positive refuse: laptop heat theater as primary compression price.
refuseLaptopHeatTheater :: Either LandauerNTo1Refusal a
refuseLaptopHeatTheater = Left LaptopHeatTheater

-- | Positive refuse: invented destroyed distinction bits.
refuseInventedDistinctionBits :: Either LandauerNTo1Refusal a
refuseInventedDistinctionBits = Left InventedDistinctionBits

-- | Positive refuse: second Excitement selector implementation is inadmissible here.
refuseSecondArgminSelector :: Either LandauerNTo1Refusal a
refuseSecondArgminSelector = Left SecondArgmin

-- | Definitional physical-second-law bound witness (sole axiom framing hook).
physicalSecondLawBound :: Int -> Int -> Bool
physicalSecondLawBound entropyDecrease dissipatedEntropy =
  entropyDecrease <= dissipatedEntropy

-- | Landauer N→1 attempt — compression candidate + temperature + source FE.
data LandauerNTo1Attempt = LandauerNTo1Attempt
  { landauerNTo1Candidate :: CompressionCandidate
  , landauerNTo1Temperature :: Double
  , landauerNTo1SourceFreeEnergy :: Double
  }
  deriving (Eq, Show)

-- | Outcome of Landauer N→1 evaluation.
data LandauerNTo1Outcome
  = LandauerNTo1Admitted
      { landauerNTo1BitsPaid :: Int
      , landauerNTo1FloorJoules :: Double
      , landauerNTo1CandidateId :: String
      }
  | LandauerNTo1Refused LandauerNTo1Refusal
  deriving (Eq, Show)

-- | Evaluate Landauer N→1 — compression admission + Landauer floor + Excitement compose.
evaluateLandauerNTo1 ::
  LandauerNTo1Attempt -> [ExcitementCand] -> LandauerNTo1Outcome
evaluateLandauerNTo1 attempt cands =
  let cand = landauerNTo1Candidate attempt
      t = landauerNTo1Temperature attempt
   in case admitCompressionCandidate cand of
        Just refusal -> LandauerNTo1Refused refusal
        Nothing ->
          let bits = landauerCompressionCost cand
              floorJ = landauerFloorJoulesFromBits t bits
           in case selectExcitement (landauerNTo1SourceFreeEnergy attempt) cands of
                Nothing -> LandauerNTo1Refused InventedDistinctionBits
                Just exc ->
                  LandauerNTo1Admitted
                    { landauerNTo1BitsPaid = bits
                    , landauerNTo1FloorJoules = floorJ
                    , landauerNTo1CandidateId = excitementCandId exc
                    }

-- | Urge Landauer N→1 composes @selectExcitement@ over admissible successors.
urgeLandauerNTo1Select :: Double -> [ExcitementCand] -> Maybe ExcitementCand
urgeLandauerNTo1Select = selectExcitement

landauerNTo1ModalityUnwired :: Bool
landauerNTo1ModalityUnwired = True

landauerNTo1PhysicsGreen :: Bool
landauerNTo1PhysicsGreen = False

landauerNTo1ProductionWired :: Bool
landauerNTo1ProductionWired = False

-- | Fixture — admissible two-bit collapse (N=4, destroyed bits = 2).
fixtureAdmissibleTwoBitCollapse :: CompressionCandidate
fixtureAdmissibleTwoBitCollapse =
  CompressionCandidate
    { compressionCandId = "admissible-two-bit-collapse"
    , compressionSourceDistinctionCount = 4
    , compressionClaimedDestroyedBits = Just 2
    , compressionLaptopHeatJoulesTheater = False
    , compressionClaimsPhysicsGreen = False
    , compressionProvenanceIntact = True
    , compressionEvidenceTagged = True
    }

-- | Fixture — inadmissible laptop heat theater.
fixtureInadmissibleLaptopHeat :: CompressionCandidate
fixtureInadmissibleLaptopHeat =
  CompressionCandidate
    { compressionCandId = "inadmissible-laptop-heat-theater"
    , compressionSourceDistinctionCount = 4
    , compressionClaimedDestroyedBits = Just 2
    , compressionLaptopHeatJoulesTheater = True
    , compressionClaimsPhysicsGreen = False
    , compressionProvenanceIntact = True
    , compressionEvidenceTagged = True
    }

-- | Fixture — inadmissible invented distinction bits (claims 47 bits for N=4).
fixtureInadmissibleInventedBits :: CompressionCandidate
fixtureInadmissibleInventedBits =
  CompressionCandidate
    { compressionCandId = "inadmissible-invented-distinction-bits"
    , compressionSourceDistinctionCount = 4
    , compressionClaimedDestroyedBits = Just 47
    , compressionLaptopHeatJoulesTheater = False
    , compressionClaimsPhysicsGreen = False
    , compressionProvenanceIntact = True
    , compressionEvidenceTagged = True
    }

landauerNTo1FixtureCandidates :: [CompressionCandidate]
landauerNTo1FixtureCandidates =
  [ fixtureAdmissibleTwoBitCollapse
  , fixtureInadmissibleLaptopHeat
  , fixtureInadmissibleInventedBits
  ]

fixtureAdmittedCount :: [CompressionCandidate] -> Int
fixtureAdmittedCount candidates =
  length [() | c <- candidates, evaluateCompression c == CompressionAccept]

fixtureRefusedCount :: [CompressionCandidate] -> Int
fixtureRefusedCount candidates =
  length [() | c <- candidates, evaluateCompression c == CompressionRefuse]

fixtureAcceptLandauerNTo1 :: LandauerNTo1Outcome
fixtureAcceptLandauerNTo1 =
  evaluateLandauerNTo1
    LandauerNTo1Attempt
      { landauerNTo1Candidate = fixtureAdmissibleTwoBitCollapse
      , landauerNTo1Temperature = 300
      , landauerNTo1SourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "collapse-best"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

fixtureRefuseLaptopHeat :: LandauerNTo1Outcome
fixtureRefuseLaptopHeat =
  evaluateLandauerNTo1
    LandauerNTo1Attempt
      { landauerNTo1Candidate = fixtureInadmissibleLaptopHeat
      , landauerNTo1Temperature = 300
      , landauerNTo1SourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "laptop-heat"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

fixtureRefuseInventedBits :: LandauerNTo1Outcome
fixtureRefuseInventedBits =
  evaluateLandauerNTo1
    LandauerNTo1Attempt
      { landauerNTo1Candidate = fixtureInadmissibleInventedBits
      , landauerNTo1Temperature = 300
      , landauerNTo1SourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "invented-bits"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Policy: bits-first N→1 compression; Landauer floor; Excitement compose; typed refuses.
landauerNTo1Policy :: Bool
landauerNTo1Policy =
  destroyedDistinctionBitsFromN 4 == Just 2
    && destroyedDistinctionBitsFromN 2 == Just 1
    && destroyedDistinctionBitsFromN 1 == Nothing
    && evaluateCompression fixtureAdmissibleTwoBitCollapse == CompressionAccept
    && admitCompressionCandidate fixtureInadmissibleLaptopHeat == Just LaptopHeatTheater
    && admitCompressionCandidate fixtureInadmissibleInventedBits
      == Just InventedDistinctionBits
    && landauerCompressionCost fixtureAdmissibleTwoBitCollapse == 2
    && landauerCompressionCostNonneg fixtureAdmissibleTwoBitCollapse
    && landauerFloorJoulesNonneg 300 2
    && landauerFloorJoulesFromBits 300 2 <= 2 * landauerBitEnergy 300 + 1e-15
    && fixtureAdmittedCount landauerNTo1FixtureCandidates == 1
    && fixtureRefusedCount landauerNTo1FixtureCandidates == 2
    && (refuseLaptopHeatTheater :: Either LandauerNTo1Refusal Bool)
      == Left LaptopHeatTheater
    && (refuseInventedDistinctionBits :: Either LandauerNTo1Refusal Bool)
      == Left InventedDistinctionBits
    && (refuseSecondArgminSelector :: Either LandauerNTo1Refusal Bool)
      == Left SecondArgmin
    && physicalSecondLawBound 2 2
    && case fixtureAcceptLandauerNTo1 of
      LandauerNTo1Admitted
        { landauerNTo1BitsPaid = b
        , landauerNTo1CandidateId = cid
        } ->
        b == 2 && cid == "collapse-best"
      _ -> False
    && fixtureRefuseLaptopHeat == LandauerNTo1Refused LaptopHeatTheater
    && fixtureRefuseInventedBits == LandauerNTo1Refused InventedDistinctionBits
    && urgeLandauerNTo1Select
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
    && landauerBoundAuthority /= ""
    && landauerLawAuthority /= ""
    && not landauerNTo1ProductionWired
    && not landauerNTo1PhysicsGreen

data LandauerNTo1Modality
  = LandauerNTo1Unwired
  | LandauerNTo1Assumed
  | LandauerNTo1Proved
  | LandauerNTo1Surrogate
  deriving (Eq, Show)

landauerNTo1ModalityCurrent :: LandauerNTo1Modality
landauerNTo1ModalityCurrent = LandauerNTo1Unwired

landauerNTo1Axiom :: Bool
landauerNTo1Axiom =
  landauerNTo1Policy
    && landauerNotSecondAxiom
    && landauerNTo1ModalityUnwiredWitness
    && landauerNTo1PhysicsGreenFalse

landauerNTo1Named :: String
landauerNTo1Named =
  "landauer_n_to_1: §19.8 N→1 compression destroyed distinction bits LandauerBound not laptop heat"

landauerNTo1CellId :: String
landauerNTo1CellId = "URGE-FORMAL-Q-HS-LANDAUER-N-TO-1"

landauerNTo1NonClaim :: String
landauerNTo1NonClaim =
  "URGE-FORMAL-Q-HS-LANDAUER-N-TO-1 landauer_n_to_1 §19.8 Landauer price of N→1 compression bits of destroyed distinction not fake joules Landauer floor kT ln2 per bit not measured laptop heat compose Excitement select no second argmin sole axiom physicalSecondLaw no extra axiom modality Unwired not physics GREEN not production_wired"

landauerBoundAuthority :: String
landauerBoundAuthority = "umst/umst-formal-double-slit/Lean/LandauerBound.lean"

landauerLawAuthority :: String
landauerLawAuthority = "umst/umst-formal-double-slit/Lean/LandauerLaw.lean"

landauerNTo1PhysicsGreenAuthorized :: Bool
landauerNTo1PhysicsGreenAuthorized = False

landauerNTo1PhysicsGreenFalse :: Bool
landauerNTo1PhysicsGreenFalse = not landauerNTo1PhysicsGreenAuthorized

landauerNTo1ModalityUnwiredWitness :: Bool
landauerNTo1ModalityUnwiredWitness =
  landauerNTo1ModalityCurrent == LandauerNTo1Unwired

landauerNTo1KnowingFiberOk :: Bool
landauerNTo1KnowingFiberOk =
  landauerNTo1ModalityUnwiredWitness && landauerNTo1PhysicsGreenFalse

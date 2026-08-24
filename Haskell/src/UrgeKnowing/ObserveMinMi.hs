-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UrgeKnowing.ObserveMinMi
Description : ObserveMinMi — §5.2 step-1 observe local+mesh at minimal MI
Copyright   : (c) UMST Project, 2026

§5.2 step-1 @observe_min_mi@ — knowing fiber observes paired local+mesh at minimal
mutual information (Landauer accounted). Mirrors Agda @UrgeKnowing.ObserveMinMi@,
Coq @UrgeKnowing.ObserveMinMi@, and Rust @observe_min_mi@.

* @pairwiseMIBits@ — I(local;mesh) = H(local) + H(mesh) − H(joint).
* @observeMinMiLandauerCost@ — Landauer lower bound at observed MI bits.
* @evaluateObserveMinMi@ — paired observation + Excitement compose.
* Compose @selectExcitement@ — not a second ℚ argmin.
* **One** design axiom (@observeMinMiAxiom@): @physicalSecondLaw@ framing only.
* @physics_green@ stays false; modality @ObserveMinMiUnwired@.

Not meso thermo G(T,P,x). Cell: @URGE-FORMAL-Q-HS-OBSERVE-MIN-MI@.
Identity: @observe_min_mi@.
-}
module UrgeKnowing.ObserveMinMi
  ( ExcitementCand (..)
  , selectExcitement
  , composeSurrogateFor
  , metaExcitementModule
  , LocalState (..)
  , MeshState (..)
  , LocalMeshState (..)
  , LocalMeshCoalgebra (..)
  , localMeshPaired
  , pairwiseMIBits
  , observeMinMiBits
  , observeMinMiBitsNonneg
  , observeMinMiLandauerCost
  , observeMinMiLandauerCostNonneg
  , observeMinMiLandauerCostLeBitEnergy
  , ObserveMinMiAttempt (..)
  , ObserveMinMiRefusal (..)
  , ObserveMinMiOutcome (..)
  , observeMinMiFromCoalgebra
  , refuseMeshAbsentWhenPairedRequired
  , refuseMutualInformationZero
  , refuseSecondArgminSelector
  , evaluateObserveMinMi
  , urgeObserveMinMiSelect
  , observeMinMiModalityUnwired
  , observeMinMiPhysicsGreen
  , observeMinMiProductionWired
  , fixtureAcceptObserveMinMi
  , fixtureRefuseMeshAbsent
  , fixtureRefuseMutualInformationZero
  , observeMinMiPolicy
  , ObserveMinMiModality (..)
  , observeMinMiModalityCurrent
  , physicalSecondLawAxiom
  , landauerNotSecondAxiom
  , observeMinMiAxiom
  , observeMinMiNamed
  , observeMinMiCellId
  , observeMinMiNonClaim
  , observeMinMiPhysicsGreenAuthorized
  , observeMinMiPhysicsGreenFalse
  , observeMinMiModalityUnwiredWitness
  , observeMinMiKnowingFiberOk
  ) where

import Data.List (sortOn)
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

-- | Minimal Excitement candidate for observe-min-MI compose (fixture scale).
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

-- | Local entropy carrier (knowing fiber scaffold).
data LocalState = LocalState
  { localEntropyBits :: Double
  }
  deriving (Eq, Show)

-- | Mesh entropy carrier (knowing fiber scaffold).
data MeshState = MeshState
  { meshEntropyBits :: Double
  }
  deriving (Eq, Show)

-- | Paired local+mesh observation carrier.
data LocalMeshState = LocalMeshState
  { localMeshLocal :: LocalState
  , localMeshMesh :: MeshState
  }
  deriving (Eq, Show)

-- | Coalgebra tag for local-only / mesh-only / paired observation.
data LocalMeshCoalgebra
  = LocalOnly LocalState
  | MeshOnly MeshState
  | Paired LocalMeshState
  deriving (Eq, Show)

-- | Construct paired local+mesh state.
localMeshPaired :: LocalState -> MeshState -> LocalMeshState
localMeshPaired l m = LocalMeshState {localMeshLocal = l, localMeshMesh = m}

-- | Pairwise MI bits — I(local;mesh) = H(local) + H(mesh) − H(joint).
pairwiseMIBits :: Double -> Double -> Double -> Double
pairwiseMIBits hLocal hMesh jointEntropy =
  max 0 (hLocal + hMesh - jointEntropy)

-- | Minimal MI bits for paired local+mesh observation.
observeMinMiBits :: LocalMeshState -> Double -> Double
observeMinMiBits s jointEntropy =
  pairwiseMIBits
    (localEntropyBits (localMeshLocal s))
    (meshEntropyBits (localMeshMesh s))
    jointEntropy

-- | Whether MI bits are non-negative (policy pin).
observeMinMiBitsNonneg :: LocalMeshState -> Double -> Bool
observeMinMiBitsNonneg s jointEntropy =
  observeMinMiBits s jointEntropy >= -1e-12

-- | Landauer lower bound at observed minimal MI bits.
observeMinMiLandauerCost :: Double -> LocalMeshState -> Double -> Double
observeMinMiLandauerCost t s jointEntropy =
  infoEnergyLowerBound (observeMinMiBits s jointEntropy) t

-- | Whether Landauer cost is non-negative at temperature @t@.
observeMinMiLandauerCostNonneg :: Double -> LocalMeshState -> Double -> Bool
observeMinMiLandauerCostNonneg t s jointEntropy =
  observeMinMiLandauerCost t s jointEntropy >= -1e-12

-- | Whether Landauer cost is bounded by one bit-energy when MI ≤ 1.
observeMinMiLandauerCostLeBitEnergy :: Double -> LocalMeshState -> Double -> Bool
observeMinMiLandauerCostLeBitEnergy t s jointEntropy =
  let mi = observeMinMiBits s jointEntropy
   in mi <= 1 + 1e-12
        && observeMinMiLandauerCost t s jointEntropy <= landauerBitEnergy t + 1e-12

-- | Observe-min-MI attempt carrier — coalgebra + joint entropy + temperature + source FE.
data ObserveMinMiAttempt = ObserveMinMiAttempt
  { observeMinMiCoalgebra :: LocalMeshCoalgebra
  , observeMinMiJointEntropy :: Double
  , observeMinMiTemperature :: Double
  , observeMinMiSourceFreeEnergy :: Double
  }
  deriving (Eq, Show)

-- | Typed refusal for observe-min-MI discipline.
data ObserveMinMiRefusal
  = MeshAbsentWhenPairedRequired
  | MutualInformationZero
  | SecondArgmin
  deriving (Eq, Show)

-- | Outcome of an observe-min-MI evaluation.
data ObserveMinMiOutcome
  = ObserveMinMiAdmitted
      { observeMinMiBitsPaid :: Double
      , observeMinMiCandidateId :: String
      }
  | ObserveMinMiRefused ObserveMinMiRefusal
  deriving (Eq, Show)


-- | Observe minimal MI from coalgebra tag (no Excitement compose).
observeMinMiFromCoalgebra :: LocalMeshCoalgebra -> Double -> ObserveMinMiOutcome
observeMinMiFromCoalgebra (Paired s) jointEntropy =
  ObserveMinMiAdmitted
    { observeMinMiBitsPaid = observeMinMiBits s jointEntropy
    , observeMinMiCandidateId = "coalgebra-paired"
    }
observeMinMiFromCoalgebra (LocalOnly _) _ =
  ObserveMinMiRefused MeshAbsentWhenPairedRequired
observeMinMiFromCoalgebra (MeshOnly _) _ =
  ObserveMinMiRefused MeshAbsentWhenPairedRequired

-- | Positive refuse: mesh/local absent when paired observation required.
refuseMeshAbsentWhenPairedRequired :: Either ObserveMinMiRefusal a
refuseMeshAbsentWhenPairedRequired = Left MeshAbsentWhenPairedRequired

-- | Positive refuse: zero mutual-information occupancy.
refuseMutualInformationZero :: Either ObserveMinMiRefusal a
refuseMutualInformationZero = Left MutualInformationZero

-- | Positive refuse: second Excitement selector implementation is inadmissible here.
refuseSecondArgminSelector :: Either ObserveMinMiRefusal a
refuseSecondArgminSelector = Left SecondArgmin

-- | Evaluate observe-min-MI — paired observation + Landauer hook + Excitement compose.
evaluateObserveMinMi ::
  ObserveMinMiAttempt -> [ExcitementCand] -> ObserveMinMiOutcome
evaluateObserveMinMi attempt cands =
  case observeMinMiCoalgebra attempt of
    LocalOnly _ -> ObserveMinMiRefused MeshAbsentWhenPairedRequired
    MeshOnly _ -> ObserveMinMiRefused MeshAbsentWhenPairedRequired
    Paired s ->
      let miBits = observeMinMiBits s (observeMinMiJointEntropy attempt)
       in if miBits <= 1e-12
            then ObserveMinMiRefused MutualInformationZero
            else
              case selectExcitement (observeMinMiSourceFreeEnergy attempt) cands of
                Nothing -> ObserveMinMiRefused MutualInformationZero
                Just cand ->
                  ObserveMinMiAdmitted
                    { observeMinMiBitsPaid = miBits
                    , observeMinMiCandidateId = excitementCandId cand
                    }

-- | Urge observe-min-MI composes @selectExcitement@ over admissible successors.
urgeObserveMinMiSelect :: Double -> [ExcitementCand] -> Maybe ExcitementCand
urgeObserveMinMiSelect = selectExcitement

observeMinMiModalityUnwired :: Bool
observeMinMiModalityUnwired = True

observeMinMiPhysicsGreen :: Bool
observeMinMiPhysicsGreen = False

observeMinMiProductionWired :: Bool
observeMinMiProductionWired = False

-- | Fixture paired state — independent local+mesh (MI = 0 at joint H = 2).
independentLocalMesh :: LocalMeshState
independentLocalMesh =
  localMeshPaired
    (LocalState {localEntropyBits = 1})
    (MeshState {meshEntropyBits = 1})

-- | Fixture paired state — correlated local+mesh (MI = 1 at joint H = 1).
correlatedLocalMesh :: LocalMeshState
correlatedLocalMesh =
  localMeshPaired
    (LocalState {localEntropyBits = 1})
    (MeshState {meshEntropyBits = 1})

-- | Fixture accept — paired observation pays MI; Excitement selects candidate.
fixtureAcceptObserveMinMi :: ObserveMinMiOutcome
fixtureAcceptObserveMinMi =
  evaluateObserveMinMi
    ObserveMinMiAttempt
      { observeMinMiCoalgebra = Paired correlatedLocalMesh
      , observeMinMiJointEntropy = 1
      , observeMinMiTemperature = 300
      , observeMinMiSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "observe-min-mi-best"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — local-only coalgebra when paired required.
fixtureRefuseMeshAbsent :: ObserveMinMiOutcome
fixtureRefuseMeshAbsent =
  evaluateObserveMinMi
    ObserveMinMiAttempt
      { observeMinMiCoalgebra =
          LocalOnly (LocalState {localEntropyBits = 1})
      , observeMinMiJointEntropy = 2
      , observeMinMiTemperature = 300
      , observeMinMiSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "mesh-absent"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Fixture refuse — zero MI occupancy on independent paired state.
fixtureRefuseMutualInformationZero :: ObserveMinMiOutcome
fixtureRefuseMutualInformationZero =
  evaluateObserveMinMi
    ObserveMinMiAttempt
      { observeMinMiCoalgebra = Paired independentLocalMesh
      , observeMinMiJointEntropy = 2
      , observeMinMiTemperature = 300
      , observeMinMiSourceFreeEnergy = 10
      }
    [ ExcitementCand
        { excitementCandId = "mi-zero"
        , excitementCandFreeEnergy = 3
        , excitementCandProvenanceIntact = True
        , excitementCandDropsProvenance = False
        }
    ]

-- | Policy: paired observe-min-MI; Landauer hook; Excitement compose; typed refuses hold.
observeMinMiPolicy :: Bool
observeMinMiPolicy =
  observeMinMiBitsNonneg correlatedLocalMesh 1
    && observeMinMiBits correlatedLocalMesh 1 > 1e-12
    && observeMinMiBits independentLocalMesh 2 <= 1e-12
    && observeMinMiLandauerCostNonneg 300 correlatedLocalMesh 1
    && observeMinMiLandauerCostLeBitEnergy 300 correlatedLocalMesh 1
    && (refuseMeshAbsentWhenPairedRequired :: Either ObserveMinMiRefusal Bool)
      == Left MeshAbsentWhenPairedRequired
    && (refuseMutualInformationZero :: Either ObserveMinMiRefusal Bool)
      == Left MutualInformationZero
    && (refuseSecondArgminSelector :: Either ObserveMinMiRefusal Bool)
      == Left SecondArgmin
    && case fixtureAcceptObserveMinMi of
      ObserveMinMiAdmitted {observeMinMiBitsPaid = b, observeMinMiCandidateId = cid} ->
        b > 0 && cid == "observe-min-mi-best"
      _ -> False
    && fixtureRefuseMeshAbsent == ObserveMinMiRefused MeshAbsentWhenPairedRequired
    && fixtureRefuseMutualInformationZero
      == ObserveMinMiRefused MutualInformationZero
    && urgeObserveMinMiSelect
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
    && not observeMinMiProductionWired
    && not observeMinMiPhysicsGreen

-- | Design modality for observe-min-MI claims (TYPE-03 preview).
data ObserveMinMiModality
  = ObserveMinMiUnwired
  | ObserveMinMiAssumed
  | ObserveMinMiProved
  | ObserveMinMiSurrogate
  deriving (Eq, Show)

observeMinMiModalityCurrent :: ObserveMinMiModality
observeMinMiModalityCurrent = ObserveMinMiUnwired

observeMinMiAxiom :: Bool
observeMinMiAxiom =
  observeMinMiPolicy
    && landauerNotSecondAxiom
    && observeMinMiModalityUnwiredWitness
    && observeMinMiPhysicsGreenFalse

observeMinMiNamed :: String
observeMinMiNamed =
  "observe_min_mi: ObserveMinMi §5.2 step-1 observe local+mesh at minimal MI Landauer accounted; compose Excitement not second argmin; physicalSecondLaw sole axiom framing"

observeMinMiCellId :: String
observeMinMiCellId = "URGE-FORMAL-Q-HS-OBSERVE-MIN-MI"

observeMinMiNonClaim :: String
observeMinMiNonClaim =
  "URGE-FORMAL-Q-HS-OBSERVE-MIN-MI observe_min_mi Unwired not Proved not GREEN not production_wired knowing fiber only not meso thermo G(T,P,x) not acting coalgebra"

observeMinMiPhysicsGreenAuthorized :: Bool
observeMinMiPhysicsGreenAuthorized = False

observeMinMiPhysicsGreenFalse :: Bool
observeMinMiPhysicsGreenFalse = not observeMinMiPhysicsGreenAuthorized

observeMinMiModalityUnwiredWitness :: Bool
observeMinMiModalityUnwiredWitness =
  observeMinMiModalityCurrent == ObserveMinMiUnwired

observeMinMiKnowingFiberOk :: Bool
observeMinMiKnowingFiberOk =
  observeMinMiModalityUnwiredWitness && observeMinMiPhysicsGreenFalse

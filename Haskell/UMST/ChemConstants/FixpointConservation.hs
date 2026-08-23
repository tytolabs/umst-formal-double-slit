-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.FixpointConservation
Description : Fixpoint conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Fixpoint** conservation: FP-02 pattern-taxonomy monotone refinement chains and lattice
**fixpoint** combinators (meet / join) on **conservation** claims (Unwired / Assumed / Proved /
Surrogate). Lattice meet/join identity conserved under honest scaffold; monotone chain reaches
a **fixpoint** at refinement top. FP-02 **fixpoint** laws are structure witnesses only
(@fp02FixpointProved@ = False).

* @FixpointConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @latticeMeet@ / @latticeJoin@ — meet/join identity conserved on scaffold depths.
* @reachAscendingFixedPoint@ — monotone chain reaches a **fixpoint** (or budget refuse).
* **One** design axiom (@fixpointConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of pattern **fixpoint** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-FIXPOINT-CONSERVATION@.
-}
module UMST.ChemConstants.FixpointConservation
  ( FixpointConservationModality (..)
  , fixpointConservationModalityCurrent
  , fixpointLatticeAll
  , fixpointLatticeCount
  , refinementBottom
  , refinementTop
  , latticeMeet
  , latticeJoin
  , ascendingRefinementStep
  , isAscendingFixedPoint
  , FixedPointChainVerdict (..)
  , reachAscendingFixedPoint
  , LatticeFixedPointKind (..)
  , latticeFixedPointKindAll
  , latticeFixedPointKindCount
  , latticeFixedPoint
  , FixpointIdentityLaw (..)
  , fixpointIdentityLawAll
  , fixpointIdentityLawCount
  , FixpointConservationVerdict (..)
  , evaluateFixpointConservation
  , sampleMeetDepths
  , sampleJoinDepths
  , sampleChainInitial
  , sampleChainBudget
  , unwiredDesignOk
  , meetIdentityConserved
  , joinIdentityConserved
  , meetJoinCommutativeOk
  , ascendingMonotoneOk
  , monotoneChainReachesFixedPoint
  , leastFixedPointReachesTop
  , greatestFixedPointIsTop
  , budgetExhaustRefuse
  , assumedFixpointDesignOk
  , surrogateFixpointDesignOk
  , greenInventFixpointRefuse
  , fixpointLatticeScaffold
  , fixpointLatticeNotGreenTable
  , fixpointIdentityLawsScaffold
  , fixpointIdentityLawsNotGreenTable
  , fixpointKnowingFiberOk
  , fp02FixpointInventRefuse
  , fixpointLatticeNotXor
  , fp02FixpointProved
  , fixpointConservationFraming
  , fixpointConservationAxiom
  , fixpointConservationNamed
  , patternFixedPointsAuthority
  , chemL0Fp02Authority
  , fixpointConservationCellId
  , fixpointConservationNonClaim
  , fixpointConservationPhysicsGreenAuthorized
  , fixpointConservationPhysicsGreenFalse
  , fixpointConservationModalityUnwired
  ) where

-- | Design **fixpoint** modality for FP-02 **conservation** claims.
data FixpointConservationModality
  = FixpointConservationUnwired
  | FixpointConservationAssumed
  | FixpointConservationProved
  | FixpointConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **fixpoint** modality — always Unwired on this cell.
fixpointConservationModalityCurrent :: FixpointConservationModality
fixpointConservationModalityCurrent = FixpointConservationUnwired

-- | All FP-02 **fixpoint** lattice steps in stable order.
fixpointLatticeAll :: [FixpointConservationModality]
fixpointLatticeAll =
  [ FixpointConservationUnwired
  , FixpointConservationAssumed
  , FixpointConservationProved
  , FixpointConservationSurrogate
  ]

fixpointLatticeCount :: Int
fixpointLatticeCount = length fixpointLatticeAll

-- | Lattice bottom for pattern-refinement depth (design scaffold).
refinementBottom :: Int
refinementBottom = 0

-- | Lattice top for pattern-refinement depth (design scaffold).
refinementTop :: Int
refinementTop = 3

-- | Meet (∧) on the refinement lattice — smaller depth wins (**fixpoint** scaffold).
latticeMeet :: Int -> Int -> Int
latticeMeet a b =
  if a < b then a else b

-- | Join (∨) on the refinement lattice — larger depth wins (**fixpoint** scaffold).
latticeJoin :: Int -> Int -> Int
latticeJoin a b =
  if a > b then a else b

-- | Monotone ascending refinement step — never decreases depth.
ascendingRefinementStep :: Int -> Int -> Int
ascendingRefinementStep state top =
  if state >= top then state else state + 1

-- | Whether @state@ is a **fixpoint** of ascending refinement at @top@.
isAscendingFixedPoint :: Int -> Int -> Bool
isAscendingFixedPoint state top =
  ascendingRefinementStep state top == state

-- | Outcome of iterating a monotone refinement chain toward a **fixpoint**.
data FixedPointChainVerdict
  = FixedPointChainReached
  | FixedPointChainBudgetExhaustedRefuse
  deriving (Eq, Show)

reachAscendingFixedPoint :: Int -> Int -> Int -> (Int, FixedPointChainVerdict)
reachAscendingFixedPoint initial top maxIters = go initial maxIters
  where
    go state remaining =
      let next = ascendingRefinementStep state top
       in if next == state
            then (state, FixedPointChainReached)
            else
              if remaining <= 0
                then
                  if isAscendingFixedPoint state top
                    then (state, FixedPointChainReached)
                    else (state, FixedPointChainBudgetExhaustedRefuse)
                else go next (remaining - 1)

-- | Kind of lattice **fixpoint** sought (design enum — not exhaustive GREEN).
data LatticeFixedPointKind
  = LeastFixedPoint
  | GreatestFixedPoint
  deriving (Eq, Show)

latticeFixedPointKindAll :: [LatticeFixedPointKind]
latticeFixedPointKindAll = [LeastFixedPoint, GreatestFixedPoint]

latticeFixedPointKindCount :: Int
latticeFixedPointKindCount = length latticeFixedPointKindAll

-- | Compute a lattice **fixpoint** of the given kind (design scaffold).
latticeFixedPoint :: LatticeFixedPointKind -> Int -> Int
latticeFixedPoint kind top =
  case kind of
    LeastFixedPoint ->
      let (state, verdict) = reachAscendingFixedPoint refinementBottom top 16
       in case verdict of
            FixedPointChainReached -> state
            FixedPointChainBudgetExhaustedRefuse -> top
    GreatestFixedPoint -> top

-- | **Fixpoint** identity law cells tracked by FP-02 (structure scaffold).
data FixpointIdentityLaw
  = MeetIdentityConserved
  | JoinIdentityConserved
  | MeetJoinCommutativeConserved
  | MonotoneChainReachesFixedPoint
  deriving (Eq, Show)

fixpointIdentityLawAll :: [FixpointIdentityLaw]
fixpointIdentityLawAll =
  [ MeetIdentityConserved
  , JoinIdentityConserved
  , MeetJoinCommutativeConserved
  , MonotoneChainReachesFixedPoint
  ]

fixpointIdentityLawCount :: Int
fixpointIdentityLawCount = length fixpointIdentityLawAll

-- | Verdict for FP-02 **fixpoint** **conservation** promotion (fail-closed).
data FixpointConservationVerdict
  = FixpointDesignOk
  | FixpointIdentityConservedOk
  | FixpointIdentityBrokenRefuse
  | FixpointGreenInventRefuse
  deriving (Eq, Show)

fixpointIdentityWitnessOk :: Int -> Int -> Bool
fixpointIdentityWitnessOk a b =
  let meetSelf = latticeMeet a a == a
      joinSelf = latticeJoin b b == b
      meetComm = latticeMeet a b == latticeMeet b a
      joinComm = latticeJoin a b == latticeJoin b a
   in meetSelf && joinSelf && meetComm && joinComm

-- | Evaluate FP-02 **fixpoint** **conservation** typing (fail-closed).
evaluateFixpointConservation ::
  FixpointConservationModality
  -> Int
  -> Int
  -> Bool
  -> FixpointConservationVerdict
evaluateFixpointConservation modality depthA depthB claimPhysicsGreen
  | claimPhysicsGreen = FixpointGreenInventRefuse
  | otherwise =
      case modality of
        FixpointConservationUnwired -> FixpointDesignOk
        FixpointConservationAssumed -> FixpointDesignOk
        FixpointConservationSurrogate -> FixpointDesignOk
        FixpointConservationProved ->
          if fixpointIdentityWitnessOk depthA depthB
            then FixpointIdentityConservedOk
            else FixpointIdentityBrokenRefuse

sampleMeetDepths :: (Int, Int)
sampleMeetDepths = (1, 3)

sampleJoinDepths :: (Int, Int)
sampleJoinDepths = (1, 3)

sampleChainInitial :: Int
sampleChainInitial = refinementBottom

sampleChainBudget :: Int
sampleChainBudget = 16

-- | Unwired **fixpoint** modality OK without identity break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateFixpointConservation
    FixpointConservationUnwired
    (fst sampleMeetDepths)
    (snd sampleMeetDepths)
    False
    == FixpointDesignOk

-- | Meet identity conserved: @latticeMeet a a = a@.
meetIdentityConserved :: Bool
meetIdentityConserved =
  latticeMeet (fst sampleMeetDepths) (fst sampleMeetDepths)
    == fst sampleMeetDepths
    && latticeMeet refinementBottom refinementBottom == refinementBottom
    && latticeMeet refinementTop refinementTop == refinementTop

-- | Join identity conserved: @latticeJoin a a = a@.
joinIdentityConserved :: Bool
joinIdentityConserved =
  latticeJoin (snd sampleJoinDepths) (snd sampleJoinDepths)
    == snd sampleJoinDepths
    && latticeJoin refinementBottom refinementBottom == refinementBottom
    && latticeJoin refinementTop refinementTop == refinementTop

-- | Meet/join commutative on scaffold depths (lattice identity conserved).
meetJoinCommutativeOk :: Bool
meetJoinCommutativeOk =
  let (a, b) = sampleMeetDepths
   in latticeMeet a b == latticeMeet b a
        && latticeJoin a b == latticeJoin b a
        && latticeMeet 2 3 == latticeMeet 3 2
        && latticeJoin 2 3 == latticeJoin 3 2

-- | Ascending refinement step is monotone (never decreases depth).
ascendingMonotoneOk :: Bool
ascendingMonotoneOk =
  ascendingRefinementStep 1 refinementTop >= 1
    && ascendingRefinementStep refinementTop refinementTop == refinementTop
    && ascendingRefinementStep refinementBottom refinementTop
      >= refinementBottom

-- | Monotone chain reaches a **fixpoint** at refinement top.
monotoneChainReachesFixedPoint :: Bool
monotoneChainReachesFixedPoint =
  let (state, verdict) =
        reachAscendingFixedPoint sampleChainInitial refinementTop sampleChainBudget
   in verdict == FixedPointChainReached
        && state == refinementTop
        && isAscendingFixedPoint state refinementTop

-- | Least lattice **fixpoint** reaches top from bottom.
leastFixedPointReachesTop :: Bool
leastFixedPointReachesTop =
  latticeFixedPoint LeastFixedPoint refinementTop == refinementTop

-- | Greatest lattice **fixpoint** is top element.
greatestFixedPointIsTop :: Bool
greatestFixedPointIsTop =
  latticeFixedPoint GreatestFixedPoint refinementTop == refinementTop

-- | Budget exhaustion refuses when chain cannot close (no fake **fixpoint**).
budgetExhaustRefuse :: Bool
budgetExhaustRefuse =
  let (_, verdict) =
        reachAscendingFixedPoint refinementBottom refinementTop 0
   in verdict == FixedPointChainBudgetExhaustedRefuse

-- | Assumed **fixpoint** modality OK without identity break (design scaffold).
assumedFixpointDesignOk :: Bool
assumedFixpointDesignOk =
  evaluateFixpointConservation
    FixpointConservationAssumed
    (fst sampleJoinDepths)
    (snd sampleJoinDepths)
    False
    == FixpointDesignOk

-- | Surrogate **fixpoint** modality OK without identity break (design scaffold).
surrogateFixpointDesignOk :: Bool
surrogateFixpointDesignOk =
  evaluateFixpointConservation
    FixpointConservationSurrogate
    (fst sampleMeetDepths)
    (snd sampleMeetDepths)
    False
    == FixpointDesignOk

-- | GREEN invent on **fixpoint** **conservation** promotion is refused.
greenInventFixpointRefuse :: Bool
greenInventFixpointRefuse =
  evaluateFixpointConservation
    FixpointConservationUnwired
    (fst sampleMeetDepths)
    (snd sampleMeetDepths)
    True
    == FixpointGreenInventRefuse

-- | Four-step FP-02 **fixpoint** lattice scaffold pinned.
fixpointLatticeScaffold :: Bool
fixpointLatticeScaffold =
  fixpointLatticeCount == 4
    && unwiredDesignOk
    && meetIdentityConserved
    && joinIdentityConserved
    && meetJoinCommutativeOk
    && ascendingMonotoneOk
    && monotoneChainReachesFixedPoint
    && leastFixedPointReachesTop
    && greatestFixedPointIsTop
    && budgetExhaustRefuse
    && assumedFixpointDesignOk
    && surrogateFixpointDesignOk

-- | **Fixpoint** lattice is structure scaffold — not 118² GREEN periodic table.
fixpointLatticeNotGreenTable :: Bool
fixpointLatticeNotGreenTable =
  fixpointLatticeCount == 4
    && fixpointLatticeCount /= 118 * 118
    && sampleMeetDepths /= (refinementBottom, refinementBottom)

-- | Four **fixpoint** identity law cells scaffold pinned.
fixpointIdentityLawsScaffold :: Bool
fixpointIdentityLawsScaffold =
  fixpointIdentityLawCount == 4
    && meetIdentityConserved
    && joinIdentityConserved
    && meetJoinCommutativeOk
    && monotoneChainReachesFixedPoint

-- | **Fixpoint** law cells are structure scaffold — not 118² GREEN periodic table.
fixpointIdentityLawsNotGreenTable :: Bool
fixpointIdentityLawsNotGreenTable =
  fixpointIdentityLawsScaffold
    && fixpointIdentityLawCount /= 118 * 118
    && sampleJoinDepths /= (refinementTop, refinementTop)

-- | Pattern **fixpoint** **conservation** claims route to knowing / quantum fiber (not meso acting).
fixpointKnowingFiberOk :: Bool
fixpointKnowingFiberOk = True

-- | FP-02 **fixpoint** invent refuse-closed scaffold witness.
fp02FixpointInventRefuse :: Bool
fp02FixpointInventRefuse = not fp02FixpointProved

-- | **Fixpoint** lattice steps are concurrent Π_c — not XOR enum bucket.
fixpointLatticeNotXor :: Bool
fixpointLatticeNotXor =
  unwiredDesignOk
    && assumedFixpointDesignOk
    && surrogateFixpointDesignOk
    && meetIdentityConserved
    && joinIdentityConserved
    && meetJoinCommutativeOk
    && ascendingMonotoneOk
    && monotoneChainReachesFixedPoint
    && greenInventFixpointRefuse

-- | FP-02 pattern **fixpoint** proved (always false on this Unwired cell).
fp02FixpointProved :: Bool
fp02FixpointProved = False

-- | One axiom framing: second law + **conservation** for pattern **fixpoint** scaffold.
fixpointConservationFraming :: String
fixpointConservationFraming =
  "second_law_conservation_fixpoint_one_axiom"

-- | Single design axiom: second law + **conservation** pattern **fixpoint** (not second axiom).
fixpointConservationAxiom :: Bool
fixpointConservationAxiom =
  fixpointLatticeScaffold
    && fixpointLatticeNotGreenTable
    && fixpointIdentityLawsScaffold
    && fixpointIdentityLawsNotGreenTable
    && fixpointKnowingFiberOk
    && meetIdentityConserved
    && joinIdentityConserved
    && meetJoinCommutativeOk
    && monotoneChainReachesFixedPoint
    && leastFixedPointReachesTop
    && greatestFixedPointIsTop
    && budgetExhaustRefuse
    && greenInventFixpointRefuse
    && fp02FixpointInventRefuse
    && fixpointLatticeNotXor
    && not fp02FixpointProved
    && fixpointConservationFraming
      == "second_law_conservation_fixpoint_one_axiom"

fixpointConservationNamed :: String
fixpointConservationNamed =
  "fixpointConservation: FixpointConservationModality Unwired Assumed Proved Surrogate four-step lattice fp02FixpointProved false latticeMeet latticeJoin monotone chain reaches fixpoint second law conservation one axiom"

-- | Upstream FP-02 pattern **fixpoint** authority (cited, not forked).
patternFixedPointsAuthority :: String
patternFixedPointsAuthority = "umst/umst-chem/src/pattern_fixed_points.rs"

-- | L0 FP-02 pattern **fixpoint** scaffold authority (crosswalk).
chemL0Fp02Authority :: String
chemL0Fp02Authority = "CHEM-L0-FP-02"

fixpointConservationCellId :: String
fixpointConservationCellId = "CHEM-FORMAL-Q-HS-FIXPOINT-CONSERVATION"

-- | Non-claim fence — pattern **fixpoint** **conservation** Unwired ≠ Proved GREEN.
fixpointConservationNonClaim :: String
fixpointConservationNonClaim =
  "CHEM-FORMAL-Q-HS-FIXPOINT-CONSERVATION FixpointConservationModality Unwired Assumed Proved Surrogate four-step lattice fp02FixpointProved false latticeMeet latticeJoin monotone chain reaches fixpoint Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing pattern **fixpoint** **conservation** scaffold.
fixpointConservationPhysicsGreenAuthorized :: Bool
fixpointConservationPhysicsGreenAuthorized = False

fixpointConservationPhysicsGreenFalse :: Bool
fixpointConservationPhysicsGreenFalse =
  not fixpointConservationPhysicsGreenAuthorized

fixpointConservationModalityUnwired :: Bool
fixpointConservationModalityUnwired =
  fixpointConservationModalityCurrent == FixpointConservationUnwired

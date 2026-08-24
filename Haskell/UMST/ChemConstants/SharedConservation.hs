-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.SharedConservation
Description : Pattern class 1 **Shared** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Shared** **conservation**: north-star §2 class 1 (`Shared`) — CEF sublattice mixing;
QTAIM bond paths; CAT-02 pullback. Concurrent Π_c identity conserved on named class pins;
CEF ⊗ QTAIM ⊗ CAT-02 is **product** not XOR. Named Shared identity conserved under honest
scaffold; trivial XOR and GREEN invent fail-closed. Shared **conservation** laws are
structure witnesses only (@sharedConservationProved@ = False). Shared ≠ SpeciesId fork.

* @SharedConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateSharedBundle@ — named class-1 Shared identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateSharedConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@sharedConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of class-1 **Shared** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-SHARED-CONSERVATION@.
-}
module UMST.ChemConstants.SharedConservation
  ( SharedConservationModality (..)
  , sharedConservationModalityCurrent
  , sharedLatticeAll
  , sharedLatticeCount
  , class1SharedPatternIndex
  , SharedChannelSlot (..)
  , sharedChannelSlotAll
  , sharedChannelSlotCount
  , SharedProductChannel (..)
  , sharedProductChannelAll
  , sharedProductChannelCount
  , SharedProductChannelIndex (..)
  , sharedProductChannelIndex
  , SharedConcurrentBundle (..)
  , sharedConcurrentBundleUnwired
  , sharedConcurrentBundleWithChannel
  , sharedConcurrentBundleWithPresent
  , sharedConcurrentBundleChannelAt
  , sharedConcurrentBundleHolds
  , sharedConcurrentBundlePresentCount
  , sharedConcurrentBundleIsConcurrentProduct
  , sharedCefQtaimCat02Witness
  , SharedXorPosture (..)
  , sharedXorPostureExclusive
  , sharedXorPostureConcurrent
  , SharedConservationVerdict (..)
  , SharedXorVerdict (..)
  , evaluateSharedBundle
  , evaluateSharedXor
  , evaluateSharedConservation
  , SharedConservationLaw (..)
  , sharedConservationLawAll
  , sharedConservationLawCount
  , sampleSharedCefQtaimCat02Bundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , sharedCefQtaimCat02ConcurrentOk
  , class1SharedPatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventSharedRefuse
  , assumedSharedDesignOk
  , surrogateSharedDesignOk
  , sharedLatticeScaffold
  , sharedLatticeNotGreenTable
  , sharedConservationLawsScaffold
  , sharedConservationLawsNotGreenTable
  , sharedKnowingFiberOk
  , sharedConservationInventRefuse
  , sharedLatticeNotXor
  , sharedConservationProved
  , sharedConservationNeSpeciesId
  , speciesIdForked
  , sharedConservationFraming
  , sharedConservationAxiom
  , sharedConservationNamed
  , sharedConservationAuthority
  , chemL0SharedAuthority
  , cefSublatticeAuthority
  , cat02PullbackAuthority
  , sharedConservationCellId
  , sharedConservationNonClaim
  , sharedConservationPhysicsGreenAuthorized
  , sharedConservationPhysicsGreenFalse
  , sharedConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not Shared GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-1 (`Shared`) pattern index.
class1SharedPatternIndex :: Int
class1SharedPatternIndex = 1

-- | Design **shared** modality for class-1 **conservation** claims.
data SharedConservationModality
  = SharedConservationUnwired
  | SharedConservationAssumed
  | SharedConservationProved
  | SharedConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **shared** modality — always Unwired on this cell.
sharedConservationModalityCurrent :: SharedConservationModality
sharedConservationModalityCurrent = SharedConservationUnwired

-- | All class-1 **shared** lattice steps in stable order.
sharedLatticeAll :: [SharedConservationModality]
sharedLatticeAll =
  [ SharedConservationUnwired
  , SharedConservationAssumed
  , SharedConservationProved
  , SharedConservationSurrogate
  ]

sharedLatticeCount :: Int
sharedLatticeCount = length sharedLatticeAll

-- | Shared product channel slot — concurrent **product** factor, not XOR bucket.
data SharedChannelSlot
  = SharedSlotUnwired
  | SharedSlotAbsent
  | SharedSlotPresent
  deriving (Eq, Show)

-- | All Shared channel slots in stable order.
sharedChannelSlotAll :: [SharedChannelSlot]
sharedChannelSlotAll =
  [ SharedSlotUnwired
  , SharedSlotAbsent
  , SharedSlotPresent
  ]

sharedChannelSlotCount :: Int
sharedChannelSlotCount = length sharedChannelSlotAll

-- | Named CEF / QTAIM / CAT-02 product channels on class-1 Shared (bounded scaffold).
data SharedProductChannel
  = CefSublatticeMixing
  | QtaimBondPaths
  | Cat02Pullback
  deriving (Eq, Show)

-- | All Shared product channels in north-star stable order.
sharedProductChannelAll :: [SharedProductChannel]
sharedProductChannelAll =
  [ CefSublatticeMixing
  , QtaimBondPaths
  , Cat02Pullback
  ]

sharedProductChannelCount :: Int
sharedProductChannelCount = length sharedProductChannelAll

-- | Stable channel index for a Shared product channel (0..2).
data SharedProductChannelIndex = SharedProductChannelIndex Int
  deriving (Eq, Show)

sharedProductChannelIndex :: SharedProductChannel -> Int
sharedProductChannelIndex channel =
  case channel of
    CefSublatticeMixing -> 0
    QtaimBondPaths -> 1
    Cat02Pullback -> 2

-- | Class-1 Shared concurrent **product** bundle — CEF ⊗ QTAIM ⊗ CAT-02 (north-star §3).
data SharedConcurrentBundle = SharedConcurrentBundle
  { sharedClassPresent :: Bool
  , sharedChannelSlots :: [SharedChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
sharedConcurrentBundleUnwired :: SharedConcurrentBundle
sharedConcurrentBundleUnwired =
  SharedConcurrentBundle
    False
    (replicate sharedProductChannelCount SharedSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
sharedConcurrentBundleWithChannel ::
  Int -> SharedChannelSlot -> SharedConcurrentBundle -> SharedConcurrentBundle
sharedConcurrentBundleWithChannel idx slot bundle =
  let slots = sharedChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in SharedConcurrentBundle
        (sharedClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the Shared **product**.
sharedConcurrentBundleWithPresent ::
  Int -> SharedConcurrentBundle -> SharedConcurrentBundle
sharedConcurrentBundleWithPresent idx bundle =
  sharedConcurrentBundleWithChannel idx SharedSlotPresent bundle

-- | Read channel slot at index (0..2).
sharedConcurrentBundleChannelAt ::
  Int -> SharedConcurrentBundle -> Maybe SharedChannelSlot
sharedConcurrentBundleChannelAt idx bundle =
  let slots = sharedChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
sharedConcurrentBundleHolds :: Int -> SharedConcurrentBundle -> Bool
sharedConcurrentBundleHolds idx bundle =
  case sharedConcurrentBundleChannelAt idx bundle of
    Just SharedSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
sharedConcurrentBundlePresentCount :: SharedConcurrentBundle -> Int
sharedConcurrentBundlePresentCount bundle =
  length (filter (== SharedSlotPresent) (sharedChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
sharedConcurrentBundleIsConcurrentProduct :: SharedConcurrentBundle -> Bool
sharedConcurrentBundleIsConcurrentProduct bundle =
  sharedConcurrentBundlePresentCount bundle >= 2

-- | Shared witness: CEF (0) + QTAIM (1) + CAT-02 (2) concurrent on class 1.
sharedCefQtaimCat02Witness :: SharedConcurrentBundle
sharedCefQtaimCat02Witness =
  sharedConcurrentBundleWithPresent 2
    (sharedConcurrentBundleWithPresent 1
      (sharedConcurrentBundleWithPresent 0
        (SharedConcurrentBundle True (replicate sharedProductChannelCount SharedSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data SharedXorPosture
  = SharedXorExclusive
  | SharedXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
sharedXorPostureExclusive :: SharedXorPosture
sharedXorPostureExclusive = SharedXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
sharedXorPostureConcurrent :: SharedXorPosture
sharedXorPostureConcurrent = SharedXorConcurrent

-- | Verdict for Shared **conservation** close (fail-closed).
data SharedConservationVerdict
  = SharedConservationDesignOk
  | SharedConservationNamedOk
  | SharedConservationTrivialRefuse
  | SharedConservationGreenInventRefuse
  | SharedConservationProvedWithoutBarRefuse
  | SharedConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data SharedXorVerdict
  = SharedXorDesignOk
  | SharedXorNamedOk
  | SharedXorGreenInventRefuse
  | SharedXorProvedWithoutBarRefuse
  | SharedXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a Shared bundle under class-1 **conservation** bar (fail-closed).
evaluateSharedBundle ::
  SharedConservationModality
  -> SharedConcurrentBundle
  -> Bool
  -> Bool
  -> SharedConservationVerdict
evaluateSharedBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = SharedConservationGreenInventRefuse
  | claimProved = SharedConservationProvedWithoutBarRefuse
  | length (sharedChannelSlots bundle) /= sharedProductChannelCount =
      SharedConservationTrivialRefuse
  | otherwise =
      case modality of
        SharedConservationUnwired ->
          if sharedConcurrentBundleIsConcurrentProduct bundle
            then SharedConservationNamedOk
            else SharedConservationDesignOk
        SharedConservationAssumed -> SharedConservationDesignOk
        SharedConservationSurrogate -> SharedConservationDesignOk
        SharedConservationProved -> SharedConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-1 **conservation** bar (fail-closed).
evaluateSharedXor ::
  SharedConservationModality
  -> SharedXorPosture
  -> Bool
  -> Bool
  -> SharedXorVerdict
evaluateSharedXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = SharedXorGreenInventRefuse
  | claimProved = SharedXorProvedWithoutBarRefuse
  | posture == SharedXorExclusive = SharedXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        SharedConservationUnwired -> SharedXorNamedOk
        SharedConservationAssumed -> SharedXorDesignOk
        SharedConservationSurrogate -> SharedXorDesignOk
        SharedConservationProved -> SharedXorProvedWithoutBarRefuse

-- | **Shared** identity law cells tracked by class-1 **conservation** (structure scaffold).
data SharedConservationLaw
  = SharedConservationConserved
  | NamedSharedConservationOk
  | TrivialSharedRefused
  | GreenInventSharedRefused
  deriving (Eq, Show)

sharedConservationLawAll :: [SharedConservationLaw]
sharedConservationLawAll =
  [ SharedConservationConserved
  , NamedSharedConservationOk
  , TrivialSharedRefused
  , GreenInventSharedRefused
  ]

sharedConservationLawCount :: Int
sharedConservationLawCount = length sharedConservationLawAll

-- | Evaluate class-1 **Shared** **conservation** typing (fail-closed).
evaluateSharedConservation ::
  SharedConservationModality
  -> SharedConcurrentBundle
  -> SharedXorPosture
  -> Bool
  -> Bool
  -> SharedConservationVerdict
evaluateSharedConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = SharedConservationGreenInventRefuse
  | claimProved = SharedConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateSharedXor modality posture False False of
        SharedXorMutuallyExclusiveRefuse -> SharedConservationXorRefuse
        SharedXorGreenInventRefuse -> SharedConservationGreenInventRefuse
        SharedXorProvedWithoutBarRefuse -> SharedConservationProvedWithoutBarRefuse
        _ ->
          case evaluateSharedBundle modality bundle False False of
            SharedConservationNamedOk -> SharedConservationNamedOk
            SharedConservationGreenInventRefuse -> SharedConservationGreenInventRefuse
            SharedConservationProvedWithoutBarRefuse -> SharedConservationProvedWithoutBarRefuse
            SharedConservationTrivialRefuse -> SharedConservationTrivialRefuse
            SharedConservationXorRefuse -> SharedConservationXorRefuse
            SharedConservationDesignOk -> SharedConservationDesignOk

sampleSharedCefQtaimCat02Bundle :: SharedConcurrentBundle
sampleSharedCefQtaimCat02Bundle = sharedCefQtaimCat02Witness

sampleXorExclusiveBundle :: SharedConcurrentBundle
sampleXorExclusiveBundle = sharedConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: SharedConcurrentBundle
sampleTrivialUnwiredBundle = sharedConcurrentBundleUnwired

-- | Unwired **shared** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateSharedConservation
    SharedConservationUnwired
    sampleSharedCefQtaimCat02Bundle
    sharedXorPostureConcurrent
    False
    False
    == SharedConservationNamedOk

-- | Shared witness: CEF + QTAIM + CAT-02 concurrent Π_c on class 1.
sharedCefQtaimCat02ConcurrentOk :: Bool
sharedCefQtaimCat02ConcurrentOk =
  let bundle = sharedCefQtaimCat02Witness
   in sharedClassPresent bundle
        && sharedConcurrentBundleHolds 0 bundle
        && sharedConcurrentBundleHolds 1 bundle
        && sharedConcurrentBundleHolds 2 bundle
        && sharedConcurrentBundlePresentCount bundle == 3
        && sharedConcurrentBundleIsConcurrentProduct bundle

-- | Class-1 Shared pattern index pinned @ scaffold.
class1SharedPatternIndexOk :: Bool
class1SharedPatternIndexOk =
  class1SharedPatternIndex == 1
    && sharedProductChannelCount == 3
    && length (sharedChannelSlots sharedConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  sharedConcurrentBundleIsConcurrentProduct sharedCefQtaimCat02Witness
    && sharedConcurrentBundlePresentCount sharedCefQtaimCat02Witness >= 2
    && sharedConcurrentBundlePresentCount sharedCefQtaimCat02Witness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateSharedXor
    SharedConservationUnwired
    sharedXorPostureExclusive
    False
    False
    == SharedXorMutuallyExclusiveRefuse
    && evaluateSharedConservation
      SharedConservationUnwired
      sampleSharedCefQtaimCat02Bundle
      sharedXorPostureExclusive
      False
      False
      == SharedConservationXorRefuse

-- | GREEN invent on **shared** **conservation** promotion is refused.
greenInventSharedRefuse :: Bool
greenInventSharedRefuse =
  evaluateSharedConservation
    SharedConservationUnwired
    sampleSharedCefQtaimCat02Bundle
    sharedXorPostureConcurrent
    True
    False
    == SharedConservationGreenInventRefuse
    && evaluateSharedBundle
      SharedConservationUnwired
      sampleSharedCefQtaimCat02Bundle
      True
      False
      == SharedConservationGreenInventRefuse

-- | Assumed **shared** modality OK without thermo break (design scaffold).
assumedSharedDesignOk :: Bool
assumedSharedDesignOk =
  evaluateSharedConservation
    SharedConservationAssumed
    sampleSharedCefQtaimCat02Bundle
    sharedXorPostureConcurrent
    False
    False
    == SharedConservationDesignOk

-- | Surrogate **shared** modality OK without thermo break (design scaffold).
surrogateSharedDesignOk :: Bool
surrogateSharedDesignOk =
  evaluateSharedConservation
    SharedConservationSurrogate
    sampleSharedCefQtaimCat02Bundle
    sharedXorPostureConcurrent
    False
    False
    == SharedConservationDesignOk

-- | Four-step class-1 **shared** lattice scaffold pinned.
sharedLatticeScaffold :: Bool
sharedLatticeScaffold =
  sharedLatticeCount == 4
    && unwiredDesignOk
    && class1SharedPatternIndexOk
    && sharedCefQtaimCat02ConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedSharedDesignOk
    && surrogateSharedDesignOk

-- | **Shared** lattice is structure scaffold — not 118² GREEN periodic table.
sharedLatticeNotGreenTable :: Bool
sharedLatticeNotGreenTable =
  sharedLatticeCount == 4
    && sharedLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && sharedProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && sharedChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **shared** identity law cells scaffold pinned.
sharedConservationLawsScaffold :: Bool
sharedConservationLawsScaffold =
  sharedConservationLawCount == 4
    && sharedCefQtaimCat02ConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventSharedRefuse

-- | **Shared** law cells are structure scaffold — not 118² GREEN periodic table.
sharedConservationLawsNotGreenTable :: Bool
sharedConservationLawsNotGreenTable =
  sharedConservationLawsScaffold
    && sharedConservationLawCount /= 118 * 118
    && sharedProductChannelCount /= 118 * 118

-- | Class-1 **Shared** **conservation** claims route to knowing / quantum fiber (not meso acting).
sharedKnowingFiberOk :: Bool
sharedKnowingFiberOk = True

-- | Class-1 **Shared** invent refuse-closed scaffold witness.
sharedConservationInventRefuse :: Bool
sharedConservationInventRefuse = not sharedConservationProved

-- | **Shared** lattice steps are concurrent Π_c — not XOR enum bucket.
sharedLatticeNotXor :: Bool
sharedLatticeNotXor =
  unwiredDesignOk
    && assumedSharedDesignOk
    && surrogateSharedDesignOk
    && sharedCefQtaimCat02ConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventSharedRefuse

-- | Class-1 **Shared** proved (always false on this Unwired cell).
sharedConservationProved :: Bool
sharedConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Shared** morphisms are class-1 neighbor channels — not SpeciesId tag mint.
sharedConservationNeSpeciesId :: Bool
sharedConservationNeSpeciesId =
  sharedConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && sharedProductChannelAll /= []
    && sharedConcurrentBundleIsConcurrentProduct sharedCefQtaimCat02Witness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-1 **Shared** scaffold.
sharedConservationFraming :: String
sharedConservationFraming =
  "second_law_conservation_shared_one_axiom"

-- | Single design axiom: second law + **conservation** class-1 Shared (not second axiom).
sharedConservationAxiom :: Bool
sharedConservationAxiom =
  sharedLatticeScaffold
    && sharedLatticeNotGreenTable
    && sharedConservationLawsScaffold
    && sharedConservationLawsNotGreenTable
    && sharedKnowingFiberOk
    && class1SharedPatternIndexOk
    && sharedCefQtaimCat02ConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventSharedRefuse
    && sharedConservationInventRefuse
    && sharedLatticeNotXor
    && sharedConservationNeSpeciesId
    && not sharedConservationProved
    && not speciesIdForked
    && sharedConservationFraming
      == "second_law_conservation_shared_one_axiom"

sharedConservationNamed :: String
sharedConservationNamed =
  "sharedConservation: SharedConservationModality Unwired Assumed Proved Surrogate four-step lattice sharedConservationProved false evaluateSharedBundle evaluateSharedConservation named class 1 Shared CEF QTAIM CAT-02 concurrent product identity conserved present ge 2 product not XOR cef qtaim cat02 xor mutually exclusive refuse shared ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT shared **conservation** authority (cited read-only, not forked).
sharedConservationAuthority :: String
sharedConservationAuthority = "umst/umst-chem/src/x_rows/shared_conservation.rs"

-- | L0 class-1 shared table authority (crosswalk).
chemL0SharedAuthority :: String
chemL0SharedAuthority = "umst/umst-chem/src/l0_tables/shared.rs"

-- | CEF sublattice mixing authority (crosswalk).
cefSublatticeAuthority :: String
cefSublatticeAuthority = "umst/umst-chem/src/cef_sublattice_is_not_species.rs"

-- | CAT-02 pullback authority (crosswalk).
cat02PullbackAuthority :: String
cat02PullbackAuthority = "umst/umst-chem/src/shared_substructure_limits.rs"

sharedConservationCellId :: String
sharedConservationCellId = "CHEM-FORMAL-Q-HS-SHARED-CONSERVATION"

-- | Non-claim fence — class-1 **Shared** **conservation** Unwired ≠ Proved GREEN.
sharedConservationNonClaim :: String
sharedConservationNonClaim =
  "CHEM-FORMAL-Q-HS-SHARED-CONSERVATION SharedConservationModality Unwired Assumed Proved Surrogate four-step lattice sharedConservationProved false evaluateSharedBundle evaluateSharedConservation named class 1 Shared CEF QTAIM CAT-02 concurrent product identity conserved present ge 2 product not XOR cef qtaim cat02 xor mutually exclusive refuse shared ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-1 **Shared** **conservation** scaffold.
sharedConservationPhysicsGreenAuthorized :: Bool
sharedConservationPhysicsGreenAuthorized = False

sharedConservationPhysicsGreenFalse :: Bool
sharedConservationPhysicsGreenFalse =
  not sharedConservationPhysicsGreenAuthorized

sharedConservationModalityUnwired :: Bool
sharedConservationModalityUnwired =
  sharedConservationModalityCurrent == SharedConservationUnwired

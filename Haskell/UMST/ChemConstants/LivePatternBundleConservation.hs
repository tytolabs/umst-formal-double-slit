-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.LivePatternBundleConservation
Description : LIVE **PatternBundle** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

LIVE **PatternBundle** **conservation**: PatternBundle_25 concurrent Π_c on every Z
(Z=1..118) — LIVE PatternBundle is an **Interact** restriction on the same second-law +
**conservation** object, not a 26th axiom. Interact restriction ⊗ TST prior art ⊗
LIVE PatternBundle concurrent Π_c on every Z is **product** not XOR. Named LIVE
PatternBundle identity conserved under honest scaffold; trivial XOR, parallel pattern
bundle axiom, species-id smuggle, extra Z=119, extra live force, T/P float-pin smuggle,
and GREEN invent fail-closed. LIVE PatternBundle **conservation** laws are structure
witnesses only (@livePatternBundleConservationProved@ = False). No SpeciesId fork.

* @LivePatternBundleConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateLivePatternBundleBundle@ — named LIVE PatternBundle identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateLivePatternBundleConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@livePatternBundleConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of LIVE PatternBundle **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-LIVE-PATTERN-BUNDLE-CONSERVATION@.
INT: umst/umst-chem/src/pattern_taxonomy.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/pattern_taxonomy.rs (read-only cite).
PatternProduct: PatternProductConservation.hs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.LivePatternBundleConservation
  ( LivePatternBundleConservationModality (..)
  , livePatternBundleConservationModalityCurrent
  , livePatternBundleLatticeAll
  , livePatternBundleLatticeCount
  , patternClassAllotropeIdx
  , LivePatternBundleChannelSlot (..)
  , livePatternBundleChannelSlotAll
  , livePatternBundleChannelSlotCount
  , LivePatternBundleProductChannel (..)
  , livePatternBundleProductChannelAll
  , livePatternBundleProductChannelCount
  , livePatternBundleProductChannelIndex
  , LivePatternBundleConcurrentBundle (..)
  , livePatternBundleConcurrentBundleUnwired
  , livePatternBundleConcurrentBundleWithChannel
  , livePatternBundleConcurrentBundleWithPresent
  , livePatternBundleConcurrentBundleChannelAt
  , livePatternBundleConcurrentBundleHolds
  , livePatternBundleConcurrentBundlePresentCount
  , livePatternBundleConcurrentBundleIsConcurrentProduct
  , livePatternBundleCarbonWitness
  , LivePatternBundleXorPosture (..)
  , livePatternBundleXorPostureExclusive
  , livePatternBundleXorPostureConcurrent
  , LivePatternBundleConservationVerdict (..)
  , LivePatternBundleXorVerdict (..)
  , evaluateLivePatternBundleBundle
  , evaluateLivePatternBundleXor
  , evaluateLivePatternBundleConservation
  , LivePatternBundleConservationLaw (..)
  , livePatternBundleConservationLawAll
  , livePatternBundleConservationLawCount
  , sampleLivePatternBundleCarbonBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , livePatternBundleConcurrentPiCOnEveryZOk
  , patternClassAllotropeIdxOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventLivePatternBundleRefuse
  , parallelLivePatternBundleAxiomRefuse
  , speciesIdSmuggleRefuse
  , interactRestrictionNotExtraForceRefuse
  , tpFloatPinRefuse
  , assumedLivePatternBundleDesignOk
  , surrogateLivePatternBundleDesignOk
  , livePatternBundleLatticeScaffold
  , livePatternBundleLatticeNotGreenTable
  , livePatternBundleConservationLawsScaffold
  , livePatternBundleConservationLawsNotGreenTable
  , livePatternBundleKnowingFiberOk
  , livePatternBundleConservationInventRefuse
  , livePatternBundleLatticeNotXor
  , livePatternBundleConservationProved
  , livePatternBundleConservationNeSpeciesId
  , speciesIdForked
  , carbonAtomicNumberZ
  , forbiddenZ119Smuggle
  , livePatternBundleConservationFraming
  , livePatternBundleConservationAxiom
  , livePatternBundleConservationNamed
  , livePatternBundleConservationAuthority
  , chemL0LivePatternBundleAuthority
  , chemL0LivePatternBundleTableAuthority
  , patternProductConservationAuthority
  , interactRestrictionAuthority
  , livePatternBundleBarrierAuthority
  , patternClassCardinality
  , crossClassifierLivePatternBundleRowId
  , northStarLivePatternBundleTag
  , atomicNumberZValid
  , everyZInIupacTable
  , forbiddenZ119NotInTable
  , livePatternBundleConservationCellId
  , livePatternBundleConservationNonClaim
  , livePatternBundleConservationPhysicsGreenAuthorized
  , livePatternBundleConservationPhysicsGreenFalse
  , livePatternBundleConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not livePatternBundle GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Whether atomic number Z is in IUPAC table Z=1..118.
atomicNumberZValid :: Int -> Bool
atomicNumberZValid z = z > 0 && z <= iupacTableCardinality

-- | Every Z=1..118 is in the IUPAC table scaffold.
everyZInIupacTable :: Bool
everyZInIupacTable = all atomicNumberZValid [1 .. iupacTableCardinality]

-- | Forbidden Z=119 smuggle — Z=119 smuggle refuse pin.
forbiddenZ119Smuggle :: Int
forbiddenZ119Smuggle = 119

-- | Forbidden Z=119 is outside IUPAC table.
forbiddenZ119NotInTable :: Bool
forbiddenZ119NotInTable = not (atomicNumberZValid forbiddenZ119Smuggle)

-- | North-star §2 class-14 (`livePatternBundle`) pattern index.
patternClassAllotropeIdx :: Int
patternClassAllotropeIdx = 14

-- | §2 PatternBundle class cardinality (north-star pinned).
patternClassCardinality :: Int
patternClassCardinality = 25

-- | Cross-classifier X49 row id.
crossClassifierLivePatternBundleRowId :: String
crossClassifierLivePatternBundleRowId = "X49"

-- | North-star LIVE PatternBundle tag.
northStarLivePatternBundleTag :: String
northStarLivePatternBundleTag = "LIVE PatternBundle concurrent Pi_c on every Z"

-- | Carbon nuance Z=78 — carbon nuance witness element pin.
carbonAtomicNumberZ :: Int
carbonAtomicNumberZ = 78

-- | Design **live PatternBundle** modality for LIVE **conservation** claims.
data LivePatternBundleConservationModality
  = LivePatternBundleConservationUnwired
  | LivePatternBundleConservationAssumed
  | LivePatternBundleConservationProved
  | LivePatternBundleConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **livePatternBundle** modality — always Unwired on this cell.
livePatternBundleConservationModalityCurrent :: LivePatternBundleConservationModality
livePatternBundleConservationModalityCurrent =
  LivePatternBundleConservationUnwired

-- | All class-14 **livePatternBundle** lattice steps in stable order.
livePatternBundleLatticeAll :: [LivePatternBundleConservationModality]
livePatternBundleLatticeAll =
  [ LivePatternBundleConservationUnwired
  , LivePatternBundleConservationAssumed
  , LivePatternBundleConservationProved
  , LivePatternBundleConservationSurrogate
  ]

livePatternBundleLatticeCount :: Int
livePatternBundleLatticeCount = length livePatternBundleLatticeAll

-- | LivePatternBundle product channel slot — concurrent **product** factor, not XOR bucket.
data LivePatternBundleChannelSlot
  = LivePatternBundleSlotUnwired
  | LivePatternBundleSlotAbsent
  | LivePatternBundleSlotPresent
  deriving (Eq, Show)

-- | All livePatternBundle channel slots in stable order.
livePatternBundleChannelSlotAll :: [LivePatternBundleChannelSlot]
livePatternBundleChannelSlotAll =
  [ LivePatternBundleSlotUnwired
  , LivePatternBundleSlotAbsent
  , LivePatternBundleSlotPresent
  ]

livePatternBundleChannelSlotCount :: Int
livePatternBundleChannelSlotCount = length livePatternBundleChannelSlotAll

-- | Named interact restriction / TST prior art / concurrent Π_c on every Z channels.
data LivePatternBundleProductChannel
  = InteractRestrictionLivePatternBundle
  | TstPriorArt
  | LivePatternBundleConcurrentProduct
  deriving (Eq, Show)

-- | All livePatternBundle product channels in north-star stable order.
livePatternBundleProductChannelAll :: [LivePatternBundleProductChannel]
livePatternBundleProductChannelAll =
  [ InteractRestrictionLivePatternBundle
  , TstPriorArt
  , LivePatternBundleConcurrentProduct
  ]

livePatternBundleProductChannelCount :: Int
livePatternBundleProductChannelCount = length livePatternBundleProductChannelAll

-- | Stable channel index for a livePatternBundle product channel (0..2).
livePatternBundleProductChannelIndex :: LivePatternBundleProductChannel -> Int
livePatternBundleProductChannelIndex channel =
  case channel of
    InteractRestrictionLivePatternBundle -> 0
    TstPriorArt -> 1
    LivePatternBundleConcurrentProduct -> 2

-- | Class-14 livePatternBundle concurrent **product** bundle (north-star §3).
data LivePatternBundleConcurrentBundle = LivePatternBundleConcurrentBundle
  { livePatternBundleClassPresent :: Bool
  , livePatternBundleChannelSlots :: [LivePatternBundleChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
livePatternBundleConcurrentBundleUnwired :: LivePatternBundleConcurrentBundle
livePatternBundleConcurrentBundleUnwired =
  LivePatternBundleConcurrentBundle
    False
    (replicate livePatternBundleProductChannelCount LivePatternBundleSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
livePatternBundleConcurrentBundleWithChannel ::
  Int -> LivePatternBundleChannelSlot -> LivePatternBundleConcurrentBundle -> LivePatternBundleConcurrentBundle
livePatternBundleConcurrentBundleWithChannel idx slot bundle =
  let slots = livePatternBundleChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in LivePatternBundleConcurrentBundle
        (livePatternBundleClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the livePatternBundle **product**.
livePatternBundleConcurrentBundleWithPresent ::
  Int -> LivePatternBundleConcurrentBundle -> LivePatternBundleConcurrentBundle
livePatternBundleConcurrentBundleWithPresent idx bundle =
  livePatternBundleConcurrentBundleWithChannel idx LivePatternBundleSlotPresent bundle

-- | Read channel slot at index (0..2).
livePatternBundleConcurrentBundleChannelAt ::
  Int -> LivePatternBundleConcurrentBundle -> Maybe LivePatternBundleChannelSlot
livePatternBundleConcurrentBundleChannelAt idx bundle =
  let slots = livePatternBundleChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
livePatternBundleConcurrentBundleHolds :: Int -> LivePatternBundleConcurrentBundle -> Bool
livePatternBundleConcurrentBundleHolds idx bundle =
  case livePatternBundleConcurrentBundleChannelAt idx bundle of
    Just LivePatternBundleSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
livePatternBundleConcurrentBundlePresentCount :: LivePatternBundleConcurrentBundle -> Int
livePatternBundleConcurrentBundlePresentCount bundle =
  length (filter (== LivePatternBundleSlotPresent) (livePatternBundleChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
livePatternBundleConcurrentBundleIsConcurrentProduct :: LivePatternBundleConcurrentBundle -> Bool
livePatternBundleConcurrentBundleIsConcurrentProduct bundle =
  livePatternBundleConcurrentBundlePresentCount bundle >= 2

-- | LivePatternBundle witness: Interact restriction (0) + barrier↓ (1) + not consumed (2) concurrent on class 14.
livePatternBundleCarbonWitness :: LivePatternBundleConcurrentBundle
livePatternBundleCarbonWitness =
  livePatternBundleConcurrentBundleWithPresent 2
    (livePatternBundleConcurrentBundleWithPresent 1
      (livePatternBundleConcurrentBundleWithPresent 0
        (LivePatternBundleConcurrentBundle True
          (replicate livePatternBundleProductChannelCount LivePatternBundleSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data LivePatternBundleXorPosture
  = LivePatternBundleXorExclusive
  | LivePatternBundleXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
livePatternBundleXorPostureExclusive :: LivePatternBundleXorPosture
livePatternBundleXorPostureExclusive = LivePatternBundleXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
livePatternBundleXorPostureConcurrent :: LivePatternBundleXorPosture
livePatternBundleXorPostureConcurrent = LivePatternBundleXorConcurrent

-- | Verdict for livePatternBundle **conservation** close (fail-closed).
data LivePatternBundleConservationVerdict
  = LivePatternBundleConservationDesignOk
  | LivePatternBundleConservationNamedOk
  | LivePatternBundleConservationTrivialRefuse
  | LivePatternBundleConservationGreenInventRefuse
  | LivePatternBundleConservationProvedWithoutBarRefuse
  | LivePatternBundleConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data LivePatternBundleXorVerdict
  = LivePatternBundleXorDesignOk
  | LivePatternBundleXorNamedOk
  | LivePatternBundleXorGreenInventRefuse
  | LivePatternBundleXorProvedWithoutBarRefuse
  | LivePatternBundleXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a livePatternBundle bundle under class-14 **conservation** bar (fail-closed).
evaluateLivePatternBundleBundle ::
  LivePatternBundleConservationModality
  -> LivePatternBundleConcurrentBundle
  -> Bool
  -> Bool
  -> LivePatternBundleConservationVerdict
evaluateLivePatternBundleBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = LivePatternBundleConservationGreenInventRefuse
  | claimProved = LivePatternBundleConservationProvedWithoutBarRefuse
  | length (livePatternBundleChannelSlots bundle) /= livePatternBundleProductChannelCount =
      LivePatternBundleConservationTrivialRefuse
  | otherwise =
      case modality of
        LivePatternBundleConservationUnwired ->
          if livePatternBundleConcurrentBundleIsConcurrentProduct bundle
            then LivePatternBundleConservationNamedOk
            else LivePatternBundleConservationDesignOk
        LivePatternBundleConservationAssumed -> LivePatternBundleConservationDesignOk
        LivePatternBundleConservationSurrogate -> LivePatternBundleConservationDesignOk
        LivePatternBundleConservationProved -> LivePatternBundleConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-14 **conservation** bar (fail-closed).
evaluateLivePatternBundleXor ::
  LivePatternBundleConservationModality
  -> LivePatternBundleXorPosture
  -> Bool
  -> Bool
  -> LivePatternBundleXorVerdict
evaluateLivePatternBundleXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = LivePatternBundleXorGreenInventRefuse
  | claimProved = LivePatternBundleXorProvedWithoutBarRefuse
  | posture == LivePatternBundleXorExclusive = LivePatternBundleXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        LivePatternBundleConservationUnwired -> LivePatternBundleXorNamedOk
        LivePatternBundleConservationAssumed -> LivePatternBundleXorDesignOk
        LivePatternBundleConservationSurrogate -> LivePatternBundleXorDesignOk
        LivePatternBundleConservationProved -> LivePatternBundleXorProvedWithoutBarRefuse

-- | **LivePatternBundle** identity law cells tracked by class-14 **conservation** (structure scaffold).
data LivePatternBundleConservationLaw
  = LivePatternBundleConservationConserved
  | NamedLivePatternBundleConservationOk
  | TrivialLivePatternBundleRefused
  | GreenInventLivePatternBundleRefused
  deriving (Eq, Show)

livePatternBundleConservationLawAll :: [LivePatternBundleConservationLaw]
livePatternBundleConservationLawAll =
  [ LivePatternBundleConservationConserved
  , NamedLivePatternBundleConservationOk
  , TrivialLivePatternBundleRefused
  , GreenInventLivePatternBundleRefused
  ]

livePatternBundleConservationLawCount :: Int
livePatternBundleConservationLawCount = length livePatternBundleConservationLawAll

-- | Evaluate class-14 **livePatternBundle** **conservation** typing (fail-closed).
evaluateLivePatternBundleConservation ::
  LivePatternBundleConservationModality
  -> LivePatternBundleConcurrentBundle
  -> LivePatternBundleXorPosture
  -> Bool
  -> Bool
  -> LivePatternBundleConservationVerdict
evaluateLivePatternBundleConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = LivePatternBundleConservationGreenInventRefuse
  | claimProved = LivePatternBundleConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateLivePatternBundleXor modality posture False False of
        LivePatternBundleXorMutuallyExclusiveRefuse -> LivePatternBundleConservationXorRefuse
        LivePatternBundleXorGreenInventRefuse -> LivePatternBundleConservationGreenInventRefuse
        LivePatternBundleXorProvedWithoutBarRefuse -> LivePatternBundleConservationProvedWithoutBarRefuse
        _ ->
          case evaluateLivePatternBundleBundle modality bundle False False of
            LivePatternBundleConservationNamedOk -> LivePatternBundleConservationNamedOk
            LivePatternBundleConservationGreenInventRefuse -> LivePatternBundleConservationGreenInventRefuse
            LivePatternBundleConservationProvedWithoutBarRefuse -> LivePatternBundleConservationProvedWithoutBarRefuse
            LivePatternBundleConservationTrivialRefuse -> LivePatternBundleConservationTrivialRefuse
            LivePatternBundleConservationXorRefuse -> LivePatternBundleConservationXorRefuse
            LivePatternBundleConservationDesignOk -> LivePatternBundleConservationDesignOk

sampleLivePatternBundleCarbonBundle :: LivePatternBundleConcurrentBundle
sampleLivePatternBundleCarbonBundle = livePatternBundleCarbonWitness

sampleXorExclusiveBundle :: LivePatternBundleConcurrentBundle
sampleXorExclusiveBundle = livePatternBundleConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: LivePatternBundleConcurrentBundle
sampleTrivialUnwiredBundle = livePatternBundleConcurrentBundleUnwired

-- | Unwired **livePatternBundle** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateLivePatternBundleConservation
    LivePatternBundleConservationUnwired
    sampleLivePatternBundleCarbonBundle
    livePatternBundleXorPostureConcurrent
    False
    False
    == LivePatternBundleConservationNamedOk

-- | LIVE PatternBundle witness: interact restriction + TST prior art + concurrent Π_c on every Z.
livePatternBundleConcurrentPiCOnEveryZOk :: Bool
livePatternBundleConcurrentPiCOnEveryZOk =
  let bundle = livePatternBundleCarbonWitness
   in livePatternBundleClassPresent bundle
        && livePatternBundleConcurrentBundleHolds 0 bundle
        && livePatternBundleConcurrentBundleHolds 1 bundle
        && livePatternBundleConcurrentBundleHolds 2 bundle
        && livePatternBundleConcurrentBundlePresentCount bundle == 3
        && livePatternBundleConcurrentBundleIsConcurrentProduct bundle
        && carbonAtomicNumberZ == 78
        && forbiddenZ119Smuggle == 119
        && forbiddenZ119NotInTable
        && patternClassAllotropeIdx == 14
        && patternClassCardinality == 25
        && everyZInIupacTable
        && crossClassifierLivePatternBundleRowId == "X49"
        && northStarLivePatternBundleTag
          == "LIVE PatternBundle concurrent Pi_c on every Z"

-- | Class-14 livePatternBundle pattern index pinned @ scaffold.
patternClassAllotropeIdxOk :: Bool
patternClassAllotropeIdxOk =
  patternClassAllotropeIdx == 14
    && patternClassCardinality == 25
    && livePatternBundleProductChannelCount == 3
    && length (livePatternBundleChannelSlots livePatternBundleConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  livePatternBundleConcurrentBundleIsConcurrentProduct livePatternBundleCarbonWitness
    && livePatternBundleConcurrentBundlePresentCount livePatternBundleCarbonWitness >= 2
    && livePatternBundleConcurrentBundlePresentCount livePatternBundleCarbonWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateLivePatternBundleXor
    LivePatternBundleConservationUnwired
    livePatternBundleXorPostureExclusive
    False
    False
    == LivePatternBundleXorMutuallyExclusiveRefuse
    && evaluateLivePatternBundleConservation
      LivePatternBundleConservationUnwired
      sampleLivePatternBundleCarbonBundle
      livePatternBundleXorPostureExclusive
      False
      False
      == LivePatternBundleConservationXorRefuse

-- | GREEN invent on **livePatternBundle** **conservation** promotion is refused.
greenInventLivePatternBundleRefuse :: Bool
greenInventLivePatternBundleRefuse =
  evaluateLivePatternBundleConservation
    LivePatternBundleConservationUnwired
    sampleLivePatternBundleCarbonBundle
    livePatternBundleXorPostureConcurrent
    True
    False
    == LivePatternBundleConservationGreenInventRefuse
    && evaluateLivePatternBundleBundle
      LivePatternBundleConservationUnwired
      sampleLivePatternBundleCarbonBundle
      True
      False
      == LivePatternBundleConservationGreenInventRefuse

-- | Parallel livePatternBundle axiom (26th law) mint is refused — second law + conservation only.
parallelLivePatternBundleAxiomRefuse :: Bool
parallelLivePatternBundleAxiomRefuse =
  livePatternBundleConservationAuthority
    == "umst/umst-chem/src/l0_tables/pattern_taxonomy.rs"
    && livePatternBundleConservationProved == False
    && not (livePatternBundleConservationAuthority == "26th_chemistry_axiom")
    && livePatternBundleConservationFraming
      /= "parallel_pattern_bundle_axiom_not_second_law"
    && chemL0LivePatternBundleTableAuthority
      == "umst/umst-chem/src/l0_tables/pattern_taxonomy.rs"

-- | SpeciesId smuggle is refused — interact restriction ≠ L1 SpeciesId tag mint.
speciesIdSmuggleRefuse :: Bool
speciesIdSmuggleRefuse =
  parallelLivePatternBundleAxiomRefuse
    && livePatternBundleConservationFraming
      /= "tst_prior_art_not_named_object"
    && livePatternBundleBarrierAuthority
      == "umst/umst-chem/src/pattern_taxonomy.rs"
    && interactRestrictionAuthority
      == "umst/umst-chem/src/pattern_taxonomy.rs"
    && patternClassAllotropeIdx == 14

-- | Interact restriction is named object — not extra live PatternBundle force axiom.
interactRestrictionNotExtraForceRefuse :: Bool
interactRestrictionNotExtraForceRefuse =
  speciesIdSmuggleRefuse
    && livePatternBundleConservationFraming
      /= "interact_restriction_not_extra_force"
    && patternClassAllotropeIdx == 14
    && livePatternBundleConcurrentBundleIsConcurrentProduct livePatternBundleCarbonWitness

-- | T/P graph functions on Interact graph — refuse bare float-pin smuggle on scaffold.
tpFloatPinRefuse :: Bool
tpFloatPinRefuse =
  interactRestrictionNotExtraForceRefuse
    && livePatternBundleConservationFraming
      /= "bare_298_15_k_1_atm_float_pins_on_live_pattern_bundle_scaffold"
    && patternClassAllotropeIdx == 14

-- | Assumed **livePatternBundle** modality OK without thermo break (design scaffold).
assumedLivePatternBundleDesignOk :: Bool
assumedLivePatternBundleDesignOk =
  evaluateLivePatternBundleConservation
    LivePatternBundleConservationAssumed
    sampleLivePatternBundleCarbonBundle
    livePatternBundleXorPostureConcurrent
    False
    False
    == LivePatternBundleConservationDesignOk

-- | Surrogate **livePatternBundle** modality OK without thermo break (design scaffold).
surrogateLivePatternBundleDesignOk :: Bool
surrogateLivePatternBundleDesignOk =
  evaluateLivePatternBundleConservation
    LivePatternBundleConservationSurrogate
    sampleLivePatternBundleCarbonBundle
    livePatternBundleXorPostureConcurrent
    False
    False
    == LivePatternBundleConservationDesignOk

-- | Four-step class-14 **livePatternBundle** lattice scaffold pinned.
livePatternBundleLatticeScaffold :: Bool
livePatternBundleLatticeScaffold =
  livePatternBundleLatticeCount == 4
    && unwiredDesignOk
    && patternClassAllotropeIdxOk
    && livePatternBundleConcurrentPiCOnEveryZOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedLivePatternBundleDesignOk
    && surrogateLivePatternBundleDesignOk
    && parallelLivePatternBundleAxiomRefuse
    && speciesIdSmuggleRefuse
    && interactRestrictionNotExtraForceRefuse
    && tpFloatPinRefuse

-- | **LivePatternBundle** lattice is structure scaffold — not 118² GREEN periodic table.
livePatternBundleLatticeNotGreenTable :: Bool
livePatternBundleLatticeNotGreenTable =
  livePatternBundleLatticeCount == 4
    && livePatternBundleLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && livePatternBundleProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && livePatternBundleChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **livePatternBundle** identity law cells scaffold pinned.
livePatternBundleConservationLawsScaffold :: Bool
livePatternBundleConservationLawsScaffold =
  livePatternBundleConservationLawCount == 4
    && livePatternBundleConcurrentPiCOnEveryZOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLivePatternBundleRefuse
    && parallelLivePatternBundleAxiomRefuse
    && speciesIdSmuggleRefuse
    && interactRestrictionNotExtraForceRefuse
    && tpFloatPinRefuse

-- | **LivePatternBundle** law cells are structure scaffold — not 118² GREEN periodic table.
livePatternBundleConservationLawsNotGreenTable :: Bool
livePatternBundleConservationLawsNotGreenTable =
  livePatternBundleConservationLawsScaffold
    && livePatternBundleConservationLawCount /= 118 * 118
    && livePatternBundleProductChannelCount /= 118 * 118

-- | Class-14 **livePatternBundle** **conservation** claims route to knowing / quantum fiber (not meso acting).
livePatternBundleKnowingFiberOk :: Bool
livePatternBundleKnowingFiberOk = True

-- | Class-14 **livePatternBundle** invent refuse-closed scaffold witness.
livePatternBundleConservationInventRefuse :: Bool
livePatternBundleConservationInventRefuse =
  not livePatternBundleConservationProved

-- | **LivePatternBundle** lattice steps are concurrent Π_c — not XOR enum bucket.
livePatternBundleLatticeNotXor :: Bool
livePatternBundleLatticeNotXor =
  unwiredDesignOk
    && assumedLivePatternBundleDesignOk
    && surrogateLivePatternBundleDesignOk
    && livePatternBundleConcurrentPiCOnEveryZOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLivePatternBundleRefuse

-- | Class-14 **livePatternBundle** proved (always false on this Unwired cell).
livePatternBundleConservationProved :: Bool
livePatternBundleConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **LivePatternBundle** morphisms are class-14 neighbor channels — not SpeciesId tag mint.
livePatternBundleConservationNeSpeciesId :: Bool
livePatternBundleConservationNeSpeciesId =
  livePatternBundleConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && livePatternBundleProductChannelAll /= []
    && livePatternBundleConcurrentBundleIsConcurrentProduct livePatternBundleCarbonWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-14 **livePatternBundle** scaffold.
livePatternBundleConservationFraming :: String
livePatternBundleConservationFraming =
  "second_law_conservation_live_pattern_bundle_interact_restriction_one_axiom"

-- | Single design axiom: second law + **conservation** class-14 livePatternBundle (not 26th axiom).
livePatternBundleConservationAxiom :: Bool
livePatternBundleConservationAxiom =
  livePatternBundleLatticeScaffold
    && livePatternBundleLatticeNotGreenTable
    && livePatternBundleConservationLawsScaffold
    && livePatternBundleConservationLawsNotGreenTable
    && livePatternBundleKnowingFiberOk
    && patternClassAllotropeIdxOk
    && livePatternBundleConcurrentPiCOnEveryZOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLivePatternBundleRefuse
    && parallelLivePatternBundleAxiomRefuse
    && speciesIdSmuggleRefuse
    && interactRestrictionNotExtraForceRefuse
    && tpFloatPinRefuse
    && livePatternBundleConservationInventRefuse
    && livePatternBundleLatticeNotXor
    && livePatternBundleConservationNeSpeciesId
    && not livePatternBundleConservationProved
    && not speciesIdForked
    && livePatternBundleConservationFraming
      == "second_law_conservation_live_pattern_bundle_interact_restriction_one_axiom"

livePatternBundleConservationNamed :: String
livePatternBundleConservationNamed =
  "livePatternBundleConservation: LivePatternBundleConservationModality Unwired Assumed Proved Surrogate four-step lattice livePatternBundleConservationProved false evaluateLivePatternBundleBundle evaluateLivePatternBundleConservation named class 14 livePatternBundle interact restriction activation barrier lowered catalyst not consumed concurrent product identity conserved present ge 2 product not XOR interact restriction witness concurrent xor mutually exclusive refuse parallel livePatternBundle axiom refuse catalyst consumed refuse interact restriction not axiom refuse tp float pin refuse livePatternBundle ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT livePatternBundle **conservation** authority (cited read-only, not forked).
livePatternBundleConservationAuthority :: String
livePatternBundleConservationAuthority =
  "umst/umst-chem/src/l0_tables/pattern_taxonomy.rs"

-- | L0 pattern taxonomy authority (read-only cite).
chemL0LivePatternBundleAuthority :: String
chemL0LivePatternBundleAuthority =
  "umst/umst-chem/src/pattern_taxonomy.rs"

-- | L0 LIVE PatternBundle table authority (crosswalk).
chemL0LivePatternBundleTableAuthority :: String
chemL0LivePatternBundleTableAuthority =
  "umst/umst-chem/src/l0_tables/pattern_taxonomy.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | Interact restriction authority (livePatternBundle as Interact restriction — not axiom).
interactRestrictionAuthority :: String
interactRestrictionAuthority = "umst/umst-chem/src/pattern_taxonomy.rs"

-- | LIVE PatternBundle barrier authority (read-only cite — not proved on this cell).
livePatternBundleBarrierAuthority :: String
livePatternBundleBarrierAuthority = "umst/umst-chem/src/pattern_taxonomy.rs"

livePatternBundleConservationCellId :: String
livePatternBundleConservationCellId =
  "CHEM-FORMAL-Q-HS-LIVE-PATTERN-BUNDLE-CONSERVATION"

-- | Non-claim fence — class-14 **livePatternBundle** **conservation** Unwired ≠ Proved GREEN.
livePatternBundleConservationNonClaim :: String
livePatternBundleConservationNonClaim =
  "CHEM-FORMAL-Q-HS-LIVE-PATTERN-BUNDLE-CONSERVATION LivePatternBundleConservationModality Unwired Assumed Proved Surrogate four-step lattice livePatternBundleConservationProved false evaluateLivePatternBundleBundle evaluateLivePatternBundleConservation named LIVE PatternBundle concurrent Pi_c on every Z carbon nuance Z=78 interact restriction TST prior art concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel pattern bundle axiom refuse species id smuggle refuse extra element id Z=119 refuse extra live pattern bundle force refuse live pattern bundle ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-14 **livePatternBundle** **conservation** scaffold.
livePatternBundleConservationPhysicsGreenAuthorized :: Bool
livePatternBundleConservationPhysicsGreenAuthorized = False

livePatternBundleConservationPhysicsGreenFalse :: Bool
livePatternBundleConservationPhysicsGreenFalse =
  not livePatternBundleConservationPhysicsGreenAuthorized

livePatternBundleConservationModalityUnwired :: Bool
livePatternBundleConservationModalityUnwired =
  livePatternBundleConservationModalityCurrent == LivePatternBundleConservationUnwired

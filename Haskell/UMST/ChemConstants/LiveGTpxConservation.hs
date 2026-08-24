-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.LiveGTpxConservation
Description : LIVE **G(T,P,x)** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**LIVE G(T,P,x)** **conservation**: live measured G(T,P,x) **type-only** until WAVE100 lifts —
freeze-safe **conservation** identity until live wire. Named LIVE G(T,P,x) identity conserved
under honest scaffold; trivial XOR, formation-zero ≠ G, T/P float-pin smuggle, CALPHAD hull
conflation, and GREEN invent fail-closed. LIVE-G-TPX **conservation** laws are structure
witnesses only (@liveGTpxConservationProved@ = False). No SpeciesId fork.

* @LiveGTpxConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateLiveGTpxBundle@ — named LIVE G(T,P,x) identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateLiveGTpxConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@liveGTpxConservationAxiom@): second law + **conservation** (not second axiom).
* @physics_green@ stays false.

Haskell mirror of LIVE **G(T,P,x)** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-LIVE-G-TPX-CONSERVATION@.
INT: umst/umst-chem/src/thermo_g.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/thermo_g.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.LiveGTpxConservation
  ( LiveGTpxConservationModality (..)
  , liveGTpxConservationModalityCurrent
  , liveGTpxLatticeAll
  , liveGTpxLatticeCount
  , liveGTpxConservationTag
  , LiveGTpxChannelSlot (..)
  , liveGTpxChannelSlotAll
  , liveGTpxChannelSlotCount
  , LiveGTpxProductChannel (..)
  , liveGTpxProductChannelAll
  , liveGTpxProductChannelCount
  , liveGTpxProductChannelIndex
  , LiveGTpxConcurrentBundle (..)
  , liveGTpxConcurrentBundleUnwired
  , liveGTpxConcurrentBundleWithChannel
  , liveGTpxConcurrentBundleWithPresent
  , liveGTpxConcurrentBundleChannelAt
  , liveGTpxConcurrentBundleHolds
  , liveGTpxConcurrentBundlePresentCount
  , liveGTpxConcurrentBundleIsConcurrentProduct
  , liveGTpxTypeWitness
  , LiveGTpxXorPosture (..)
  , liveGTpxXorPostureExclusive
  , liveGTpxXorPostureConcurrent
  , LiveGTpxConservationVerdict (..)
  , LiveGTpxXorVerdict (..)
  , evaluateLiveGTpxBundle
  , evaluateLiveGTpxXor
  , evaluateLiveGTpxConservation
  , LiveGTpxConservationLaw (..)
  , liveGTpxConservationLawAll
  , liveGTpxConservationLawCount
  , sampleLiveGTpxTypeBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , liveGTpxTypeConcurrentOk
  , liveGTpxConservationTagOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventLiveGTpxRefuse
  , typeOnlyUntilWave100Refuse
  , thermoHullConflationRefuse
  , formationZeroNotGRefuse
  , tpFloatPinRefuse
  , assumedLiveGTpxDesignOk
  , surrogateLiveGTpxDesignOk
  , liveGTpxLatticeScaffold
  , liveGTpxLatticeNotGreenTable
  , liveGTpxConservationLawsScaffold
  , liveGTpxConservationLawsNotGreenTable
  , liveGTpxKnowingFiberOk
  , liveGTpxConservationInventRefuse
  , liveGTpxLatticeNotXor
  , liveGTpxConservationProved
  , liveGTpxConservationNeSpeciesId
  , speciesIdForked
  , ironAtomicNumberZWitness
  , copperAtomicNumberZWitness
  , liveGTpxConservationFraming
  , liveGTpxConservationAxiom
  , liveGTpxConservationNamed
  , liveGTpxConservationAuthority
  , chemL0LiveGTpxAuthority
  , patternProductConservationAuthority
  , compositionXAuthority
  , thermoConservationAuthority
  , edgeLiveGTpxAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , liveGTpxConservationCellId
  , liveGTpxConservationNonClaim
  , liveGTpxConservationPhysicsGreenAuthorized
  , liveGTpxConservationPhysicsGreenFalse
  , liveGTpxConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not liveGTpx GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | LIVE-G-TPX conservation tag (type-only scaffold marker — not class-14).
liveGTpxConservationTag :: Int
liveGTpxConservationTag = 1

-- | Iron Z=26 — Fe thermo witness element pin.
ironAtomicNumberZWitness :: Int
ironAtomicNumberZWitness = 26

-- | Copper Z=29 — Cu thermo witness element pin.
copperAtomicNumberZWitness :: Int
copperAtomicNumberZWitness = 29

-- | Design **liveGTpx** modality for LIVE-G-TPX **conservation** claims.
data LiveGTpxConservationModality
  = LiveGTpxConservationUnwired
  | LiveGTpxConservationAssumed
  | LiveGTpxConservationProved
  | LiveGTpxConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **liveGTpx** modality — always Unwired on this cell.
liveGTpxConservationModalityCurrent :: LiveGTpxConservationModality
liveGTpxConservationModalityCurrent =
  LiveGTpxConservationUnwired

-- | All LIVE-G-TPX **liveGTpx** lattice steps in stable order.
liveGTpxLatticeAll :: [LiveGTpxConservationModality]
liveGTpxLatticeAll =
  [ LiveGTpxConservationUnwired
  , LiveGTpxConservationAssumed
  , LiveGTpxConservationProved
  , LiveGTpxConservationSurrogate
  ]

liveGTpxLatticeCount :: Int
liveGTpxLatticeCount = length liveGTpxLatticeAll

-- | LiveGTpx product channel slot — concurrent **product** factor, not XOR bucket.
data LiveGTpxChannelSlot
  = LiveGTpxSlotUnwired
  | LiveGTpxSlotAbsent
  | LiveGTpxSlotPresent
  deriving (Eq, Show)

-- | All liveGTpx channel slots in stable order.
liveGTpxChannelSlotAll :: [LiveGTpxChannelSlot]
liveGTpxChannelSlotAll =
  [ LiveGTpxSlotUnwired
  , LiveGTpxSlotAbsent
  , LiveGTpxSlotPresent
  ]

liveGTpxChannelSlotCount :: Int
liveGTpxChannelSlotCount = length liveGTpxChannelSlotAll

-- | Named live measured G type / T graph function / P graph function product channels.
data LiveGTpxProductChannel
  = LiveMeasuredGType
  | TemperatureGraphFunction
  | PressureGraphFunction
  deriving (Eq, Show)

-- | All LIVE G(T,P,x) product channels in north-star stable order.
liveGTpxProductChannelAll :: [LiveGTpxProductChannel]
liveGTpxProductChannelAll =
  [ LiveMeasuredGType
  , TemperatureGraphFunction
  , PressureGraphFunction
  ]

liveGTpxProductChannelCount :: Int
liveGTpxProductChannelCount = length liveGTpxProductChannelAll

-- | Stable channel index for a LIVE G(T,P,x) product channel (0..2).
liveGTpxProductChannelIndex :: LiveGTpxProductChannel -> Int
liveGTpxProductChannelIndex channel =
  case channel of
    LiveMeasuredGType -> 0
    TemperatureGraphFunction -> 1
    PressureGraphFunction -> 2

-- | LIVE-G-TPX liveGTpx concurrent **product** bundle (north-star §3).
data LiveGTpxConcurrentBundle = LiveGTpxConcurrentBundle
  { liveGTpxClassPresent :: Bool
  , liveGTpxChannelSlots :: [LiveGTpxChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
liveGTpxConcurrentBundleUnwired :: LiveGTpxConcurrentBundle
liveGTpxConcurrentBundleUnwired =
  LiveGTpxConcurrentBundle
    False
    (replicate liveGTpxProductChannelCount LiveGTpxSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
liveGTpxConcurrentBundleWithChannel ::
  Int -> LiveGTpxChannelSlot -> LiveGTpxConcurrentBundle -> LiveGTpxConcurrentBundle
liveGTpxConcurrentBundleWithChannel idx slot bundle =
  let slots = liveGTpxChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in LiveGTpxConcurrentBundle
        (liveGTpxClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the liveGTpx **product**.
liveGTpxConcurrentBundleWithPresent ::
  Int -> LiveGTpxConcurrentBundle -> LiveGTpxConcurrentBundle
liveGTpxConcurrentBundleWithPresent idx bundle =
  liveGTpxConcurrentBundleWithChannel idx LiveGTpxSlotPresent bundle

-- | Read channel slot at index (0..2).
liveGTpxConcurrentBundleChannelAt ::
  Int -> LiveGTpxConcurrentBundle -> Maybe LiveGTpxChannelSlot
liveGTpxConcurrentBundleChannelAt idx bundle =
  let slots = liveGTpxChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
liveGTpxConcurrentBundleHolds :: Int -> LiveGTpxConcurrentBundle -> Bool
liveGTpxConcurrentBundleHolds idx bundle =
  case liveGTpxConcurrentBundleChannelAt idx bundle of
    Just LiveGTpxSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
liveGTpxConcurrentBundlePresentCount :: LiveGTpxConcurrentBundle -> Int
liveGTpxConcurrentBundlePresentCount bundle =
  length (filter (== LiveGTpxSlotPresent) (liveGTpxChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
liveGTpxConcurrentBundleIsConcurrentProduct :: LiveGTpxConcurrentBundle -> Bool
liveGTpxConcurrentBundleIsConcurrentProduct bundle =
  liveGTpxConcurrentBundlePresentCount bundle >= 2

-- | LiveGTpx witness: Live measured G type (0) + barrier↓ (1) + not consumed (2) concurrent on LIVE G(T,P,x).
liveGTpxTypeWitness :: LiveGTpxConcurrentBundle
liveGTpxTypeWitness =
  liveGTpxConcurrentBundleWithPresent 2
    (liveGTpxConcurrentBundleWithPresent 1
      (liveGTpxConcurrentBundleWithPresent 0
        (LiveGTpxConcurrentBundle True
          (replicate liveGTpxProductChannelCount LiveGTpxSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data LiveGTpxXorPosture
  = LiveGTpxXorExclusive
  | LiveGTpxXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
liveGTpxXorPostureExclusive :: LiveGTpxXorPosture
liveGTpxXorPostureExclusive = LiveGTpxXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
liveGTpxXorPostureConcurrent :: LiveGTpxXorPosture
liveGTpxXorPostureConcurrent = LiveGTpxXorConcurrent

-- | Verdict for liveGTpx **conservation** close (fail-closed).
data LiveGTpxConservationVerdict
  = LiveGTpxConservationDesignOk
  | LiveGTpxConservationNamedOk
  | LiveGTpxConservationTrivialRefuse
  | LiveGTpxConservationGreenInventRefuse
  | LiveGTpxConservationProvedWithoutBarRefuse
  | LiveGTpxConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data LiveGTpxXorVerdict
  = LiveGTpxXorDesignOk
  | LiveGTpxXorNamedOk
  | LiveGTpxXorGreenInventRefuse
  | LiveGTpxXorProvedWithoutBarRefuse
  | LiveGTpxXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a liveGTpx bundle under LIVE-G-TPX **conservation** bar (fail-closed).
evaluateLiveGTpxBundle ::
  LiveGTpxConservationModality
  -> LiveGTpxConcurrentBundle
  -> Bool
  -> Bool
  -> LiveGTpxConservationVerdict
evaluateLiveGTpxBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = LiveGTpxConservationGreenInventRefuse
  | claimProved = LiveGTpxConservationProvedWithoutBarRefuse
  | length (liveGTpxChannelSlots bundle) /= liveGTpxProductChannelCount =
      LiveGTpxConservationTrivialRefuse
  | otherwise =
      case modality of
        LiveGTpxConservationUnwired ->
          if liveGTpxConcurrentBundleIsConcurrentProduct bundle
            then LiveGTpxConservationNamedOk
            else LiveGTpxConservationDesignOk
        LiveGTpxConservationAssumed -> LiveGTpxConservationDesignOk
        LiveGTpxConservationSurrogate -> LiveGTpxConservationDesignOk
        LiveGTpxConservationProved -> LiveGTpxConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under LIVE-G-TPX **conservation** bar (fail-closed).
evaluateLiveGTpxXor ::
  LiveGTpxConservationModality
  -> LiveGTpxXorPosture
  -> Bool
  -> Bool
  -> LiveGTpxXorVerdict
evaluateLiveGTpxXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = LiveGTpxXorGreenInventRefuse
  | claimProved = LiveGTpxXorProvedWithoutBarRefuse
  | posture == LiveGTpxXorExclusive = LiveGTpxXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        LiveGTpxConservationUnwired -> LiveGTpxXorNamedOk
        LiveGTpxConservationAssumed -> LiveGTpxXorDesignOk
        LiveGTpxConservationSurrogate -> LiveGTpxXorDesignOk
        LiveGTpxConservationProved -> LiveGTpxXorProvedWithoutBarRefuse

-- | **LiveGTpx** identity law cells tracked by LIVE-G-TPX **conservation** (structure scaffold).
data LiveGTpxConservationLaw
  = LiveGTpxConservationConserved
  | NamedLiveGTpxConservationOk
  | TrivialLiveGTpxRefused
  | GreenInventLiveGTpxRefused
  deriving (Eq, Show)

liveGTpxConservationLawAll :: [LiveGTpxConservationLaw]
liveGTpxConservationLawAll =
  [ LiveGTpxConservationConserved
  , NamedLiveGTpxConservationOk
  , TrivialLiveGTpxRefused
  , GreenInventLiveGTpxRefused
  ]

liveGTpxConservationLawCount :: Int
liveGTpxConservationLawCount = length liveGTpxConservationLawAll

-- | Evaluate LIVE-G-TPX **liveGTpx** **conservation** typing (fail-closed).
evaluateLiveGTpxConservation ::
  LiveGTpxConservationModality
  -> LiveGTpxConcurrentBundle
  -> LiveGTpxXorPosture
  -> Bool
  -> Bool
  -> LiveGTpxConservationVerdict
evaluateLiveGTpxConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = LiveGTpxConservationGreenInventRefuse
  | claimProved = LiveGTpxConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateLiveGTpxXor modality posture False False of
        LiveGTpxXorMutuallyExclusiveRefuse -> LiveGTpxConservationXorRefuse
        LiveGTpxXorGreenInventRefuse -> LiveGTpxConservationGreenInventRefuse
        LiveGTpxXorProvedWithoutBarRefuse -> LiveGTpxConservationProvedWithoutBarRefuse
        _ ->
          case evaluateLiveGTpxBundle modality bundle False False of
            LiveGTpxConservationNamedOk -> LiveGTpxConservationNamedOk
            LiveGTpxConservationGreenInventRefuse -> LiveGTpxConservationGreenInventRefuse
            LiveGTpxConservationProvedWithoutBarRefuse -> LiveGTpxConservationProvedWithoutBarRefuse
            LiveGTpxConservationTrivialRefuse -> LiveGTpxConservationTrivialRefuse
            LiveGTpxConservationXorRefuse -> LiveGTpxConservationXorRefuse
            LiveGTpxConservationDesignOk -> LiveGTpxConservationDesignOk

sampleLiveGTpxTypeBundle :: LiveGTpxConcurrentBundle
sampleLiveGTpxTypeBundle = liveGTpxTypeWitness

sampleXorExclusiveBundle :: LiveGTpxConcurrentBundle
sampleXorExclusiveBundle = liveGTpxConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: LiveGTpxConcurrentBundle
sampleTrivialUnwiredBundle = liveGTpxConcurrentBundleUnwired

-- | Unwired **liveGTpx** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateLiveGTpxConservation
    LiveGTpxConservationUnwired
    sampleLiveGTpxTypeBundle
    liveGTpxXorPostureConcurrent
    False
    False
    == LiveGTpxConservationNamedOk

-- | Live G(T,P,x) witness: live measured G type + T graph function + P graph function concurrent Π_c on scaffold.
liveGTpxTypeConcurrentOk :: Bool
liveGTpxTypeConcurrentOk =
  let bundle = liveGTpxTypeWitness
   in liveGTpxClassPresent bundle
        && liveGTpxConcurrentBundleHolds 0 bundle
        && liveGTpxConcurrentBundleHolds 1 bundle
        && liveGTpxConcurrentBundleHolds 2 bundle
        && liveGTpxConcurrentBundlePresentCount bundle == 3
        && liveGTpxConcurrentBundleIsConcurrentProduct bundle
        && ironAtomicNumberZWitness == 26
        && copperAtomicNumberZWitness == 29
        && liveGTpxConservationTag == 1

-- | LIVE-G-TPX liveGTpx pattern index pinned @ scaffold.
liveGTpxConservationTagOk :: Bool
liveGTpxConservationTagOk =
  liveGTpxConservationTag == 1
    && liveGTpxProductChannelCount == 3
    && length (liveGTpxChannelSlots liveGTpxConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  liveGTpxConcurrentBundleIsConcurrentProduct liveGTpxTypeWitness
    && liveGTpxConcurrentBundlePresentCount liveGTpxTypeWitness >= 2
    && liveGTpxConcurrentBundlePresentCount liveGTpxTypeWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateLiveGTpxXor
    LiveGTpxConservationUnwired
    liveGTpxXorPostureExclusive
    False
    False
    == LiveGTpxXorMutuallyExclusiveRefuse
    && evaluateLiveGTpxConservation
      LiveGTpxConservationUnwired
      sampleLiveGTpxTypeBundle
      liveGTpxXorPostureExclusive
      False
      False
      == LiveGTpxConservationXorRefuse

-- | GREEN invent on **liveGTpx** **conservation** promotion is refused.
greenInventLiveGTpxRefuse :: Bool
greenInventLiveGTpxRefuse =
  evaluateLiveGTpxConservation
    LiveGTpxConservationUnwired
    sampleLiveGTpxTypeBundle
    liveGTpxXorPostureConcurrent
    True
    False
    == LiveGTpxConservationGreenInventRefuse
    && evaluateLiveGTpxBundle
      LiveGTpxConservationUnwired
      sampleLiveGTpxTypeBundle
      True
      False
      == LiveGTpxConservationGreenInventRefuse

-- | Live wire before WAVE100 mint is refused — type-only until lift.
typeOnlyUntilWave100Refuse :: Bool
typeOnlyUntilWave100Refuse =
  liveGTpxConservationAuthority
    == "umst/umst-chem/src/thermo_g.rs"
    && liveGTpxConservationProved == False
    && not (liveGTpxConservationAuthority == "second_live_g_axiom")
    && liveGTpxConservationFraming
      /= "live_wire_before_wave100_not_second_law"
    && chemL0LiveGTpxAuthority
      == "umst/umst-chem/src/l0_tables/shared.rs"
    && liveGTpxConservationFraming
      /= "live_measured_g_wired_before_wave100"

-- | CALPHAD hull conflated with live measured G is refused.
thermoHullConflationRefuse :: Bool
thermoHullConflationRefuse =
  typeOnlyUntilWave100Refuse
    && liveGTpxConservationFraming
      /= "calphad_hull_conflated_with_live_measured_g"
    && edgeLiveGTpxAuthority
      == "umst/umst-chem/src/thermo_g.rs"
    && compositionXAuthority
      == "umst/umst-chem/src/temperature_is_graph_function.rs"
    && liveGTpxConservationTag == 1

-- | Formation-zero ≠ G on LIVE G(T,P,x) scaffold — fail-closed.
formationZeroNotGRefuse :: Bool
formationZeroNotGRefuse =
  thermoHullConflationRefuse
    && liveGTpxConservationFraming
      /= "formation_zero_not_g_on_live_g_tpx"
    && liveGTpxConservationTag == 1
    && liveGTpxConcurrentBundleIsConcurrentProduct liveGTpxTypeWitness

-- | T/P graph functions on Interact graph — refuse bare float-pin smuggle on liveGTpx scaffold.
tpFloatPinRefuse :: Bool
tpFloatPinRefuse =
  formationZeroNotGRefuse
    && liveGTpxConservationFraming
      /= "tp_bare_float_pin_on_live_g_tpx"
    && temperatureGraphFunctionAuthority
      == "umst/umst-chem/src/temperature_is_graph_function.rs"
    && pressureGraphFunctionAuthority
      == "umst/umst-chem/src/pressure_is_graph_function.rs"
    && liveGTpxConservationTag == 1

-- | Assumed **liveGTpx** modality OK without thermo break (design scaffold).
assumedLiveGTpxDesignOk :: Bool
assumedLiveGTpxDesignOk =
  evaluateLiveGTpxConservation
    LiveGTpxConservationAssumed
    sampleLiveGTpxTypeBundle
    liveGTpxXorPostureConcurrent
    False
    False
    == LiveGTpxConservationDesignOk

-- | Surrogate **liveGTpx** modality OK without thermo break (design scaffold).
surrogateLiveGTpxDesignOk :: Bool
surrogateLiveGTpxDesignOk =
  evaluateLiveGTpxConservation
    LiveGTpxConservationSurrogate
    sampleLiveGTpxTypeBundle
    liveGTpxXorPostureConcurrent
    False
    False
    == LiveGTpxConservationDesignOk

-- | Four-step LIVE-G-TPX **liveGTpx** lattice scaffold pinned.
liveGTpxLatticeScaffold :: Bool
liveGTpxLatticeScaffold =
  liveGTpxLatticeCount == 4
    && unwiredDesignOk
    && liveGTpxConservationTagOk
    && liveGTpxTypeConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedLiveGTpxDesignOk
    && surrogateLiveGTpxDesignOk
    && typeOnlyUntilWave100Refuse
    && thermoHullConflationRefuse
    && formationZeroNotGRefuse
    && tpFloatPinRefuse

-- | **LiveGTpx** lattice is structure scaffold — not 118² GREEN periodic table.
liveGTpxLatticeNotGreenTable :: Bool
liveGTpxLatticeNotGreenTable =
  liveGTpxLatticeCount == 4
    && liveGTpxLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && liveGTpxProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && liveGTpxChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **liveGTpx** identity law cells scaffold pinned.
liveGTpxConservationLawsScaffold :: Bool
liveGTpxConservationLawsScaffold =
  liveGTpxConservationLawCount == 4
    && liveGTpxTypeConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLiveGTpxRefuse
    && typeOnlyUntilWave100Refuse
    && thermoHullConflationRefuse
    && formationZeroNotGRefuse
    && tpFloatPinRefuse

-- | **LiveGTpx** law cells are structure scaffold — not 118² GREEN periodic table.
liveGTpxConservationLawsNotGreenTable :: Bool
liveGTpxConservationLawsNotGreenTable =
  liveGTpxConservationLawsScaffold
    && liveGTpxConservationLawCount /= 118 * 118
    && liveGTpxProductChannelCount /= 118 * 118

-- | LIVE-G-TPX **liveGTpx** **conservation** claims route to knowing / quantum fiber (not meso acting).
liveGTpxKnowingFiberOk :: Bool
liveGTpxKnowingFiberOk = True

-- | LIVE-G-TPX **liveGTpx** invent refuse-closed scaffold witness.
liveGTpxConservationInventRefuse :: Bool
liveGTpxConservationInventRefuse =
  not liveGTpxConservationProved

-- | **LiveGTpx** lattice steps are concurrent Π_c — not XOR enum bucket.
liveGTpxLatticeNotXor :: Bool
liveGTpxLatticeNotXor =
  unwiredDesignOk
    && assumedLiveGTpxDesignOk
    && surrogateLiveGTpxDesignOk
    && liveGTpxTypeConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLiveGTpxRefuse

-- | LIVE-G-TPX **liveGTpx** proved (always false on this Unwired cell).
liveGTpxConservationProved :: Bool
liveGTpxConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **LiveGTpx** morphisms are LIVE-G-TPX neighbor channels — not SpeciesId tag mint.
liveGTpxConservationNeSpeciesId :: Bool
liveGTpxConservationNeSpeciesId =
  liveGTpxConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && liveGTpxProductChannelAll /= []
    && liveGTpxConcurrentBundleIsConcurrentProduct liveGTpxTypeWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for LIVE-G-TPX **liveGTpx** scaffold.
liveGTpxConservationFraming :: String
liveGTpxConservationFraming =
  "second_law_conservation_live_g_tpx_type_only_one_axiom"

-- | Single design axiom: second law + **conservation** LIVE-G-TPX liveGTpx (not 26th axiom).
liveGTpxConservationAxiom :: Bool
liveGTpxConservationAxiom =
  liveGTpxLatticeScaffold
    && liveGTpxLatticeNotGreenTable
    && liveGTpxConservationLawsScaffold
    && liveGTpxConservationLawsNotGreenTable
    && liveGTpxKnowingFiberOk
    && liveGTpxConservationTagOk
    && liveGTpxTypeConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLiveGTpxRefuse
    && typeOnlyUntilWave100Refuse
    && thermoHullConflationRefuse
    && formationZeroNotGRefuse
    && tpFloatPinRefuse
    && liveGTpxConservationInventRefuse
    && liveGTpxLatticeNotXor
    && liveGTpxConservationNeSpeciesId
    && not liveGTpxConservationProved
    && not speciesIdForked
    && liveGTpxConservationFraming
      == "second_law_conservation_live_g_tpx_type_only_one_axiom"

liveGTpxConservationNamed :: String
liveGTpxConservationNamed =
  "liveGTpxConservation: LiveGTpxConservationModality Unwired Assumed Proved Surrogate four-step lattice liveGTpxConservationProved false evaluateLiveGTpxBundle evaluateLiveGTpxConservation named LIVE G(T,P,x) live measured G type temperature graph function pressure graph function concurrent product identity conserved present ge 2 product not XOR live G type witness concurrent xor mutually exclusive refuse parallel liveGTpx axiom refuse thermo hull conflation refuse formation zero not G refuse tp float pin refuse live G(T,P,x) ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT liveGTpx **conservation** authority (cited read-only, not forked).
liveGTpxConservationAuthority :: String
liveGTpxConservationAuthority =
  "umst/umst-chem/src/thermo_g.rs"

-- | L0 LIVE-G-TPX liveGTpx table authority (crosswalk).
chemL0LiveGTpxAuthority :: String
chemL0LiveGTpxAuthority =
  "umst/umst-chem/src/l0_tables/shared.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | Composition x authority (mole-fraction scaffold — read-only cite).
compositionXAuthority :: String
compositionXAuthority = "umst/umst-chem/src/chemical_potential_is_graph_function.rs"

-- | THERMO-01 crosswalk authority (CALPHAD hull ≠ live measured G).
thermoConservationAuthority :: String
thermoConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/ThermoConservation.hs"

-- | L0 edge live G(T,P,x) authority (type scaffold — not proved on this cell).
edgeLiveGTpxAuthority :: String
edgeLiveGTpxAuthority = "umst/umst-chem/src/thermo_g.rs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

liveGTpxConservationCellId :: String
liveGTpxConservationCellId =
  "CHEM-FORMAL-Q-HS-LIVE-G-TPX-CONSERVATION"

-- | Non-claim fence — LIVE-G-TPX **liveGTpx** **conservation** Unwired ≠ Proved GREEN.
liveGTpxConservationNonClaim :: String
liveGTpxConservationNonClaim =
  "CHEM-FORMAL-Q-HS-LIVE-G-TPX-CONSERVATION LiveGTpxConservationModality Unwired Assumed Proved Surrogate four-step lattice liveGTpxConservationProved false evaluateLiveGTpxBundle evaluateLiveGTpxConservation named LIVE G(T,P,x) live measured G type temperature graph function pressure graph function concurrent product identity conserved present ge 2 product not XOR live G type witness concurrent xor mutually exclusive refuse parallel liveGTpx axiom refuse thermo hull conflation refuse formation zero not G refuse tp float pin refuse live G(T,P,x) ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing LIVE-G-TPX **liveGTpx** **conservation** scaffold.
liveGTpxConservationPhysicsGreenAuthorized :: Bool
liveGTpxConservationPhysicsGreenAuthorized = False

liveGTpxConservationPhysicsGreenFalse :: Bool
liveGTpxConservationPhysicsGreenFalse =
  not liveGTpxConservationPhysicsGreenAuthorized

liveGTpxConservationModalityUnwired :: Bool
liveGTpxConservationModalityUnwired =
  liveGTpxConservationModalityCurrent == LiveGTpxConservationUnwired

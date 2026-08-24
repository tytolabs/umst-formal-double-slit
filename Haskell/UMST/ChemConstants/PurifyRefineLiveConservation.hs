-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.PurifyRefineLiveConservation
Description : LIVE **purify-refine** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**LIVE purify-refine** **conservation**: north-star v48 LIVE purify-refine adjunction
cost (@purify_refine@) — purify-refine is an **Interact** restriction on the same second-law +
**conservation** object, not a 26th axiom. LIVE purify-refine adjunction ⊗ refine adjunction
cost Landauer ⊗ no-free-purification Π_c is **product** not XOR. Named LIVE purify-refine
identity conserved under honest scaffold; trivial XOR, parallel purify-refine axiom,
free purification, T/P float-pin smuggle, and GREEN invent fail-closed. LIVE purify-refine
**conservation** laws are structure witnesses only (@purifyRefineLiveConservationProved@ =
False). No SpeciesId fork.

* @PurifyRefineLiveConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluatePurifyRefineLiveBundle@ — named LIVE purify-refine identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluatePurifyRefineLiveConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@purifyRefineLiveConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of LIVE **purify-refine** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-PURIFY-REFINE-LIVE-CONSERVATION@.
INT: umst/umst-chem/src/impure_pure_adjunction.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/impure_component_morphism.rs (read-only cite).
XROW: umst/umst-chem/src/x_rows/adjunction_cost_landauer.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.PurifyRefineLiveConservation
  ( PurifyRefineLiveConservationModality (..)
  , purifyRefineLiveConservationModalityCurrent
  , purifyRefineLiveLatticeAll
  , purifyRefineLiveLatticeCount
  , cat03PurifyRefineLiveHonestyTag
  , PurifyRefineLiveChannelSlot (..)
  , purifyRefineLiveChannelSlotAll
  , purifyRefineLiveChannelSlotCount
  , PurifyRefineLiveProductChannel (..)
  , purifyRefineLiveProductChannelAll
  , purifyRefineLiveProductChannelCount
  , purifyRefineLiveProductChannelIndex
  , PurifyRefineLiveConcurrentBundle (..)
  , purifyRefineLiveConcurrentBundleUnwired
  , purifyRefineLiveConcurrentBundleWithChannel
  , purifyRefineLiveConcurrentBundleWithPresent
  , purifyRefineLiveConcurrentBundleChannelAt
  , purifyRefineLiveConcurrentBundleHolds
  , purifyRefineLiveConcurrentBundlePresentCount
  , purifyRefineLiveConcurrentBundleIsConcurrentProduct
  , purifyRefineLiveAdjunctionWitness
  , PurifyRefineLiveXorPosture (..)
  , purifyRefineLiveXorPostureExclusive
  , purifyRefineLiveXorPostureConcurrent
  , PurifyRefineLiveConservationVerdict (..)
  , PurifyRefineLiveXorVerdict (..)
  , evaluatePurifyRefineLiveBundle
  , evaluatePurifyRefineLiveXor
  , evaluatePurifyRefineLiveConservation
  , PurifyRefineLiveConservationLaw (..)
  , purifyRefineLiveConservationLawAll
  , purifyRefineLiveConservationLawCount
  , samplePurifyRefineLiveAdjunctionBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , purifyRefineLiveAdjunctionConcurrentOk
  , cat03PurifyRefineLiveHonestyTagOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventPurifyRefineLiveRefuse
  , parallelPurifyRefineAxiomRefuse
  , freePurificationRefuse
  , adjunctionNotAxiomRefuse
  , tpFloatPinRefuse
  , assumedPurifyRefineLiveDesignOk
  , surrogatePurifyRefineLiveDesignOk
  , purifyRefineLiveLatticeScaffold
  , purifyRefineLiveLatticeNotGreenTable
  , purifyRefineLiveConservationLawsScaffold
  , purifyRefineLiveConservationLawsNotGreenTable
  , purifyRefineLiveKnowingFiberOk
  , purifyRefineLiveConservationInventRefuse
  , purifyRefineLiveLatticeNotXor
  , purifyRefineLiveConservationProved
  , purifyRefineLiveConservationNeSpeciesId
  , speciesIdForked
  , copperAtomicNumberZ
  , ironAtomicNumberZ
  , purifyRefineLiveConservationFraming
  , purifyRefineLiveConservationAxiom
  , purifyRefineLiveConservationNamed
  , purifyRefineLiveConservationAuthority
  , chemL0Cat03Authority
  , patternProductConservationAuthority
  , adjunctionCostLandauerAuthority
  , impureComponentMorphismAuthority
  , goldschmidtConservationAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , purifyRefineLiveConservationCellId
  , purifyRefineLiveConservationNonClaim
  , purifyRefineLiveConservationPhysicsGreenAuthorized
  , purifyRefineLiveConservationPhysicsGreenFalse
  , adjunctionCostLandauerHsAuthority
  , purifyRefineLiveConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not purifyRefineLive GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star v48 LIVE purify-refine (`purify_refine`) honesty tag.
cat03PurifyRefineLiveHonestyTag :: String
cat03PurifyRefineLiveHonestyTag = "CAT-03"

-- | Iron Z=26 — ore host witness element pin.
ironAtomicNumberZ :: Int
ironAtomicNumberZ = 26

-- | Copper Z=29 — trace contaminant witness element pin.
copperAtomicNumberZ :: Int
copperAtomicNumberZ = 29

-- | Design **purifyRefineLive** modality for class-14 **conservation** claims.
data PurifyRefineLiveConservationModality
  = PurifyRefineLiveConservationUnwired
  | PurifyRefineLiveConservationAssumed
  | PurifyRefineLiveConservationProved
  | PurifyRefineLiveConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **purifyRefineLive** modality — always Unwired on this cell.
purifyRefineLiveConservationModalityCurrent :: PurifyRefineLiveConservationModality
purifyRefineLiveConservationModalityCurrent =
  PurifyRefineLiveConservationUnwired

-- | All class-14 **purifyRefineLive** lattice steps in stable order.
purifyRefineLiveLatticeAll :: [PurifyRefineLiveConservationModality]
purifyRefineLiveLatticeAll =
  [ PurifyRefineLiveConservationUnwired
  , PurifyRefineLiveConservationAssumed
  , PurifyRefineLiveConservationProved
  , PurifyRefineLiveConservationSurrogate
  ]

purifyRefineLiveLatticeCount :: Int
purifyRefineLiveLatticeCount = length purifyRefineLiveLatticeAll

-- | PurifyRefineLive product channel slot — concurrent **product** factor, not XOR bucket.
data PurifyRefineLiveChannelSlot
  = PurifyRefineLiveSlotUnwired
  | PurifyRefineLiveSlotAbsent
  | PurifyRefineLiveSlotPresent
  deriving (Eq, Show)

-- | All purifyRefineLive channel slots in stable order.
purifyRefineLiveChannelSlotAll :: [PurifyRefineLiveChannelSlot]
purifyRefineLiveChannelSlotAll =
  [ PurifyRefineLiveSlotUnwired
  , PurifyRefineLiveSlotAbsent
  , PurifyRefineLiveSlotPresent
  ]

purifyRefineLiveChannelSlotCount :: Int
purifyRefineLiveChannelSlotCount = length purifyRefineLiveChannelSlotAll

-- | Named Interact restriction / barrier↓ / no-free-purification product channels.
data PurifyRefineLiveProductChannel
  = InteractRestrictionPurifyRefineLive
  | RefineAdjunctionCostLandauer
  | NoFreePurification
  deriving (Eq, Show)

-- | All purifyRefineLive product channels in north-star stable order.
purifyRefineLiveProductChannelAll :: [PurifyRefineLiveProductChannel]
purifyRefineLiveProductChannelAll =
  [ InteractRestrictionPurifyRefineLive
  , RefineAdjunctionCostLandauer
  , NoFreePurification
  ]

purifyRefineLiveProductChannelCount :: Int
purifyRefineLiveProductChannelCount = length purifyRefineLiveProductChannelAll

-- | Stable channel index for a purifyRefineLive product channel (0..2).
purifyRefineLiveProductChannelIndex :: PurifyRefineLiveProductChannel -> Int
purifyRefineLiveProductChannelIndex channel =
  case channel of
    InteractRestrictionPurifyRefineLive -> 0
    RefineAdjunctionCostLandauer -> 1
    NoFreePurification -> 2

-- | Class-14 purifyRefineLive concurrent **product** bundle (north-star §3).
data PurifyRefineLiveConcurrentBundle = PurifyRefineLiveConcurrentBundle
  { purifyRefineLiveClassPresent :: Bool
  , purifyRefineLiveChannelSlots :: [PurifyRefineLiveChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
purifyRefineLiveConcurrentBundleUnwired :: PurifyRefineLiveConcurrentBundle
purifyRefineLiveConcurrentBundleUnwired =
  PurifyRefineLiveConcurrentBundle
    False
    (replicate purifyRefineLiveProductChannelCount PurifyRefineLiveSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
purifyRefineLiveConcurrentBundleWithChannel ::
  Int -> PurifyRefineLiveChannelSlot -> PurifyRefineLiveConcurrentBundle -> PurifyRefineLiveConcurrentBundle
purifyRefineLiveConcurrentBundleWithChannel idx slot bundle =
  let slots = purifyRefineLiveChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in PurifyRefineLiveConcurrentBundle
        (purifyRefineLiveClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the purifyRefineLive **product**.
purifyRefineLiveConcurrentBundleWithPresent ::
  Int -> PurifyRefineLiveConcurrentBundle -> PurifyRefineLiveConcurrentBundle
purifyRefineLiveConcurrentBundleWithPresent idx bundle =
  purifyRefineLiveConcurrentBundleWithChannel idx PurifyRefineLiveSlotPresent bundle

-- | Read channel slot at index (0..2).
purifyRefineLiveConcurrentBundleChannelAt ::
  Int -> PurifyRefineLiveConcurrentBundle -> Maybe PurifyRefineLiveChannelSlot
purifyRefineLiveConcurrentBundleChannelAt idx bundle =
  let slots = purifyRefineLiveChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
purifyRefineLiveConcurrentBundleHolds :: Int -> PurifyRefineLiveConcurrentBundle -> Bool
purifyRefineLiveConcurrentBundleHolds idx bundle =
  case purifyRefineLiveConcurrentBundleChannelAt idx bundle of
    Just PurifyRefineLiveSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
purifyRefineLiveConcurrentBundlePresentCount :: PurifyRefineLiveConcurrentBundle -> Int
purifyRefineLiveConcurrentBundlePresentCount bundle =
  length (filter (== PurifyRefineLiveSlotPresent) (purifyRefineLiveChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
purifyRefineLiveConcurrentBundleIsConcurrentProduct :: PurifyRefineLiveConcurrentBundle -> Bool
purifyRefineLiveConcurrentBundleIsConcurrentProduct bundle =
  purifyRefineLiveConcurrentBundlePresentCount bundle >= 2

-- | LIVE purify-refine witness: adjunction (0) + refine cost Landauer (1) + no free purification (2) concurrent.
purifyRefineLiveAdjunctionWitness :: PurifyRefineLiveConcurrentBundle
purifyRefineLiveAdjunctionWitness =
  purifyRefineLiveConcurrentBundleWithPresent 2
    (purifyRefineLiveConcurrentBundleWithPresent 1
      (purifyRefineLiveConcurrentBundleWithPresent 0
        (PurifyRefineLiveConcurrentBundle True
          (replicate purifyRefineLiveProductChannelCount PurifyRefineLiveSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data PurifyRefineLiveXorPosture
  = PurifyRefineLiveXorExclusive
  | PurifyRefineLiveXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
purifyRefineLiveXorPostureExclusive :: PurifyRefineLiveXorPosture
purifyRefineLiveXorPostureExclusive = PurifyRefineLiveXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
purifyRefineLiveXorPostureConcurrent :: PurifyRefineLiveXorPosture
purifyRefineLiveXorPostureConcurrent = PurifyRefineLiveXorConcurrent

-- | Verdict for purifyRefineLive **conservation** close (fail-closed).
data PurifyRefineLiveConservationVerdict
  = PurifyRefineLiveConservationDesignOk
  | PurifyRefineLiveConservationNamedOk
  | PurifyRefineLiveConservationTrivialRefuse
  | PurifyRefineLiveConservationGreenInventRefuse
  | PurifyRefineLiveConservationProvedWithoutBarRefuse
  | PurifyRefineLiveConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data PurifyRefineLiveXorVerdict
  = PurifyRefineLiveXorDesignOk
  | PurifyRefineLiveXorNamedOk
  | PurifyRefineLiveXorGreenInventRefuse
  | PurifyRefineLiveXorProvedWithoutBarRefuse
  | PurifyRefineLiveXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a purifyRefineLive bundle under class-14 **conservation** bar (fail-closed).
evaluatePurifyRefineLiveBundle ::
  PurifyRefineLiveConservationModality
  -> PurifyRefineLiveConcurrentBundle
  -> Bool
  -> Bool
  -> PurifyRefineLiveConservationVerdict
evaluatePurifyRefineLiveBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = PurifyRefineLiveConservationGreenInventRefuse
  | claimProved = PurifyRefineLiveConservationProvedWithoutBarRefuse
  | length (purifyRefineLiveChannelSlots bundle) /= purifyRefineLiveProductChannelCount =
      PurifyRefineLiveConservationTrivialRefuse
  | otherwise =
      case modality of
        PurifyRefineLiveConservationUnwired ->
          if purifyRefineLiveConcurrentBundleIsConcurrentProduct bundle
            then PurifyRefineLiveConservationNamedOk
            else PurifyRefineLiveConservationDesignOk
        PurifyRefineLiveConservationAssumed -> PurifyRefineLiveConservationDesignOk
        PurifyRefineLiveConservationSurrogate -> PurifyRefineLiveConservationDesignOk
        PurifyRefineLiveConservationProved -> PurifyRefineLiveConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-14 **conservation** bar (fail-closed).
evaluatePurifyRefineLiveXor ::
  PurifyRefineLiveConservationModality
  -> PurifyRefineLiveXorPosture
  -> Bool
  -> Bool
  -> PurifyRefineLiveXorVerdict
evaluatePurifyRefineLiveXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = PurifyRefineLiveXorGreenInventRefuse
  | claimProved = PurifyRefineLiveXorProvedWithoutBarRefuse
  | posture == PurifyRefineLiveXorExclusive = PurifyRefineLiveXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        PurifyRefineLiveConservationUnwired -> PurifyRefineLiveXorNamedOk
        PurifyRefineLiveConservationAssumed -> PurifyRefineLiveXorDesignOk
        PurifyRefineLiveConservationSurrogate -> PurifyRefineLiveXorDesignOk
        PurifyRefineLiveConservationProved -> PurifyRefineLiveXorProvedWithoutBarRefuse

-- | **PurifyRefineLive** identity law cells tracked by class-14 **conservation** (structure scaffold).
data PurifyRefineLiveConservationLaw
  = PurifyRefineLiveConservationConserved
  | NamedPurifyRefineLiveConservationOk
  | TrivialPurifyRefineLiveRefused
  | GreenInventPurifyRefineLiveRefused
  deriving (Eq, Show)

purifyRefineLiveConservationLawAll :: [PurifyRefineLiveConservationLaw]
purifyRefineLiveConservationLawAll =
  [ PurifyRefineLiveConservationConserved
  , NamedPurifyRefineLiveConservationOk
  , TrivialPurifyRefineLiveRefused
  , GreenInventPurifyRefineLiveRefused
  ]

purifyRefineLiveConservationLawCount :: Int
purifyRefineLiveConservationLawCount = length purifyRefineLiveConservationLawAll

-- | Evaluate class-14 **purifyRefineLive** **conservation** typing (fail-closed).
evaluatePurifyRefineLiveConservation ::
  PurifyRefineLiveConservationModality
  -> PurifyRefineLiveConcurrentBundle
  -> PurifyRefineLiveXorPosture
  -> Bool
  -> Bool
  -> PurifyRefineLiveConservationVerdict
evaluatePurifyRefineLiveConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = PurifyRefineLiveConservationGreenInventRefuse
  | claimProved = PurifyRefineLiveConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluatePurifyRefineLiveXor modality posture False False of
        PurifyRefineLiveXorMutuallyExclusiveRefuse -> PurifyRefineLiveConservationXorRefuse
        PurifyRefineLiveXorGreenInventRefuse -> PurifyRefineLiveConservationGreenInventRefuse
        PurifyRefineLiveXorProvedWithoutBarRefuse -> PurifyRefineLiveConservationProvedWithoutBarRefuse
        _ ->
          case evaluatePurifyRefineLiveBundle modality bundle False False of
            PurifyRefineLiveConservationNamedOk -> PurifyRefineLiveConservationNamedOk
            PurifyRefineLiveConservationGreenInventRefuse -> PurifyRefineLiveConservationGreenInventRefuse
            PurifyRefineLiveConservationProvedWithoutBarRefuse -> PurifyRefineLiveConservationProvedWithoutBarRefuse
            PurifyRefineLiveConservationTrivialRefuse -> PurifyRefineLiveConservationTrivialRefuse
            PurifyRefineLiveConservationXorRefuse -> PurifyRefineLiveConservationXorRefuse
            PurifyRefineLiveConservationDesignOk -> PurifyRefineLiveConservationDesignOk

samplePurifyRefineLiveAdjunctionBundle :: PurifyRefineLiveConcurrentBundle
samplePurifyRefineLiveAdjunctionBundle = purifyRefineLiveAdjunctionWitness

sampleXorExclusiveBundle :: PurifyRefineLiveConcurrentBundle
sampleXorExclusiveBundle = purifyRefineLiveConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: PurifyRefineLiveConcurrentBundle
sampleTrivialUnwiredBundle = purifyRefineLiveConcurrentBundleUnwired

-- | Unwired **purifyRefineLive** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluatePurifyRefineLiveConservation
    PurifyRefineLiveConservationUnwired
    samplePurifyRefineLiveAdjunctionBundle
    purifyRefineLiveXorPostureConcurrent
    False
    False
    == PurifyRefineLiveConservationNamedOk

-- | LIVE purify-refine witness: adjunction + refine cost Landauer + no-free-purification concurrent Π_c.
purifyRefineLiveAdjunctionConcurrentOk :: Bool
purifyRefineLiveAdjunctionConcurrentOk =
  let bundle = purifyRefineLiveAdjunctionWitness
   in purifyRefineLiveClassPresent bundle
        && purifyRefineLiveConcurrentBundleHolds 0 bundle
        && purifyRefineLiveConcurrentBundleHolds 1 bundle
        && purifyRefineLiveConcurrentBundleHolds 2 bundle
        && purifyRefineLiveConcurrentBundlePresentCount bundle == 3
        && purifyRefineLiveConcurrentBundleIsConcurrentProduct bundle
        && copperAtomicNumberZ == 29
        && ironAtomicNumberZ == 26
        && cat03PurifyRefineLiveHonestyTag == "CAT-03"

-- | Class-14 purifyRefineLive pattern index pinned @ scaffold.
cat03PurifyRefineLiveHonestyTagOk :: Bool
cat03PurifyRefineLiveHonestyTagOk =
  cat03PurifyRefineLiveHonestyTag == "CAT-03"
    && purifyRefineLiveProductChannelCount == 3
    && length (purifyRefineLiveChannelSlots purifyRefineLiveConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  purifyRefineLiveConcurrentBundleIsConcurrentProduct purifyRefineLiveAdjunctionWitness
    && purifyRefineLiveConcurrentBundlePresentCount purifyRefineLiveAdjunctionWitness >= 2
    && purifyRefineLiveConcurrentBundlePresentCount purifyRefineLiveAdjunctionWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluatePurifyRefineLiveXor
    PurifyRefineLiveConservationUnwired
    purifyRefineLiveXorPostureExclusive
    False
    False
    == PurifyRefineLiveXorMutuallyExclusiveRefuse
    && evaluatePurifyRefineLiveConservation
      PurifyRefineLiveConservationUnwired
      samplePurifyRefineLiveAdjunctionBundle
      purifyRefineLiveXorPostureExclusive
      False
      False
      == PurifyRefineLiveConservationXorRefuse

-- | GREEN invent on **purifyRefineLive** **conservation** promotion is refused.
greenInventPurifyRefineLiveRefuse :: Bool
greenInventPurifyRefineLiveRefuse =
  evaluatePurifyRefineLiveConservation
    PurifyRefineLiveConservationUnwired
    samplePurifyRefineLiveAdjunctionBundle
    purifyRefineLiveXorPostureConcurrent
    True
    False
    == PurifyRefineLiveConservationGreenInventRefuse
    && evaluatePurifyRefineLiveBundle
      PurifyRefineLiveConservationUnwired
      samplePurifyRefineLiveAdjunctionBundle
      True
      False
      == PurifyRefineLiveConservationGreenInventRefuse

-- | Parallel purifyRefineLive axiom (26th law) mint is refused — second law + conservation only.
parallelPurifyRefineAxiomRefuse :: Bool
parallelPurifyRefineAxiomRefuse =
  purifyRefineLiveConservationAuthority
    == "umst/umst-chem/src/impure_pure_adjunction.rs"
    && purifyRefineLiveConservationProved == False
    && not (purifyRefineLiveConservationAuthority == "26th_chemistry_axiom")
    && purifyRefineLiveConservationFraming
      /= "parallel_purify_refine_axiom_not_second_law"
    && chemL0Cat03Authority
      == "CHEM-L0-CAT-03"
    && adjunctionCostLandauerHsAuthority
      == "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/AdjunctionCostLandauer.hs"

-- | Free purification on LIVE purify-refine is refused — pureward cost mandatory.
freePurificationRefuse :: Bool
freePurificationRefuse =
  parallelPurifyRefineAxiomRefuse
    && purifyRefineLiveConservationFraming
      /= "free_purification_reverse_refine"
    && adjunctionCostLandauerAuthority
      == "umst/umst-chem/src/x_rows/adjunction_cost_landauer.rs"
    && impureComponentMorphismAuthority
      == "umst/umst-chem/src/l0_tables/impure_component_morphism.rs"
    && cat03PurifyRefineLiveHonestyTag == "CAT-03"

-- | LIVE purify-refine is adjunction restriction — not a parallel purify-refine axiom.
adjunctionNotAxiomRefuse :: Bool
adjunctionNotAxiomRefuse =
  freePurificationRefuse
    && purifyRefineLiveConservationFraming
      /= "purify_refine_axiom_not_adjunction"
    && cat03PurifyRefineLiveHonestyTag == "CAT-03"
    && purifyRefineLiveConcurrentBundleIsConcurrentProduct purifyRefineLiveAdjunctionWitness

-- | T/P graph functions on Interact graph — refuse bare float-pin smuggle on purifyRefineLive scaffold.
tpFloatPinRefuse :: Bool
tpFloatPinRefuse =
  adjunctionNotAxiomRefuse
    && purifyRefineLiveConservationFraming
      /= "tp_bare_float_pin_on_purify_refine_live"
    && temperatureGraphFunctionAuthority
      == "umst/umst-chem/src/temperature_is_graph_function.rs"
    && pressureGraphFunctionAuthority
      == "umst/umst-chem/src/pressure_is_graph_function.rs"
    && cat03PurifyRefineLiveHonestyTag == "CAT-03"

-- | Assumed **purifyRefineLive** modality OK without thermo break (design scaffold).
assumedPurifyRefineLiveDesignOk :: Bool
assumedPurifyRefineLiveDesignOk =
  evaluatePurifyRefineLiveConservation
    PurifyRefineLiveConservationAssumed
    samplePurifyRefineLiveAdjunctionBundle
    purifyRefineLiveXorPostureConcurrent
    False
    False
    == PurifyRefineLiveConservationDesignOk

-- | Surrogate **purifyRefineLive** modality OK without thermo break (design scaffold).
surrogatePurifyRefineLiveDesignOk :: Bool
surrogatePurifyRefineLiveDesignOk =
  evaluatePurifyRefineLiveConservation
    PurifyRefineLiveConservationSurrogate
    samplePurifyRefineLiveAdjunctionBundle
    purifyRefineLiveXorPostureConcurrent
    False
    False
    == PurifyRefineLiveConservationDesignOk

-- | Four-step class-14 **purifyRefineLive** lattice scaffold pinned.
purifyRefineLiveLatticeScaffold :: Bool
purifyRefineLiveLatticeScaffold =
  purifyRefineLiveLatticeCount == 4
    && unwiredDesignOk
    && cat03PurifyRefineLiveHonestyTagOk
    && purifyRefineLiveAdjunctionConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedPurifyRefineLiveDesignOk
    && surrogatePurifyRefineLiveDesignOk
    && parallelPurifyRefineAxiomRefuse
    && freePurificationRefuse
    && adjunctionNotAxiomRefuse
    && tpFloatPinRefuse

-- | **PurifyRefineLive** lattice is structure scaffold — not 118² GREEN periodic table.
purifyRefineLiveLatticeNotGreenTable :: Bool
purifyRefineLiveLatticeNotGreenTable =
  purifyRefineLiveLatticeCount == 4
    && purifyRefineLiveLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && purifyRefineLiveProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && purifyRefineLiveChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **purifyRefineLive** identity law cells scaffold pinned.
purifyRefineLiveConservationLawsScaffold :: Bool
purifyRefineLiveConservationLawsScaffold =
  purifyRefineLiveConservationLawCount == 4
    && purifyRefineLiveAdjunctionConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventPurifyRefineLiveRefuse
    && parallelPurifyRefineAxiomRefuse
    && freePurificationRefuse
    && adjunctionNotAxiomRefuse
    && tpFloatPinRefuse

-- | **PurifyRefineLive** law cells are structure scaffold — not 118² GREEN periodic table.
purifyRefineLiveConservationLawsNotGreenTable :: Bool
purifyRefineLiveConservationLawsNotGreenTable =
  purifyRefineLiveConservationLawsScaffold
    && purifyRefineLiveConservationLawCount /= 118 * 118
    && purifyRefineLiveProductChannelCount /= 118 * 118

-- | Class-14 **purifyRefineLive** **conservation** claims route to knowing / quantum fiber (not meso acting).
purifyRefineLiveKnowingFiberOk :: Bool
purifyRefineLiveKnowingFiberOk = True

-- | Class-14 **purifyRefineLive** invent refuse-closed scaffold witness.
purifyRefineLiveConservationInventRefuse :: Bool
purifyRefineLiveConservationInventRefuse =
  not purifyRefineLiveConservationProved

-- | **PurifyRefineLive** lattice steps are concurrent Π_c — not XOR enum bucket.
purifyRefineLiveLatticeNotXor :: Bool
purifyRefineLiveLatticeNotXor =
  unwiredDesignOk
    && assumedPurifyRefineLiveDesignOk
    && surrogatePurifyRefineLiveDesignOk
    && purifyRefineLiveAdjunctionConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventPurifyRefineLiveRefuse

-- | Class-14 **purifyRefineLive** proved (always false on this Unwired cell).
purifyRefineLiveConservationProved :: Bool
purifyRefineLiveConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **PurifyRefineLive** morphisms are class-14 neighbor channels — not SpeciesId tag mint.
purifyRefineLiveConservationNeSpeciesId :: Bool
purifyRefineLiveConservationNeSpeciesId =
  purifyRefineLiveConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && purifyRefineLiveProductChannelAll /= []
    && purifyRefineLiveConcurrentBundleIsConcurrentProduct purifyRefineLiveAdjunctionWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-14 **purifyRefineLive** scaffold.
purifyRefineLiveConservationFraming :: String
purifyRefineLiveConservationFraming =
  "second_law_conservation_purify_refine_live_one_axiom"

-- | Single design axiom: second law + **conservation** class-14 purifyRefineLive (not 26th axiom).
purifyRefineLiveConservationAxiom :: Bool
purifyRefineLiveConservationAxiom =
  purifyRefineLiveLatticeScaffold
    && purifyRefineLiveLatticeNotGreenTable
    && purifyRefineLiveConservationLawsScaffold
    && purifyRefineLiveConservationLawsNotGreenTable
    && purifyRefineLiveKnowingFiberOk
    && cat03PurifyRefineLiveHonestyTagOk
    && purifyRefineLiveAdjunctionConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventPurifyRefineLiveRefuse
    && parallelPurifyRefineAxiomRefuse
    && freePurificationRefuse
    && adjunctionNotAxiomRefuse
    && tpFloatPinRefuse
    && purifyRefineLiveConservationInventRefuse
    && purifyRefineLiveLatticeNotXor
    && purifyRefineLiveConservationNeSpeciesId
    && not purifyRefineLiveConservationProved
    && not speciesIdForked
    && purifyRefineLiveConservationFraming
      == "second_law_conservation_purify_refine_live_one_axiom"

purifyRefineLiveConservationNamed :: String
purifyRefineLiveConservationNamed =
  "purifyRefineLiveConservation: PurifyRefineLiveConservationModality Unwired Assumed Proved Surrogate four-step lattice purifyRefineLiveConservationProved false evaluatePurifyRefineLiveBundle evaluatePurifyRefineLiveConservation named LIVE purify refine adjunction refine adjunction cost landauer no free purification concurrent product identity conserved present ge 2 product not XOR adjunction witness concurrent xor mutually exclusive refuse parallel purify refine axiom refuse free purification refuse adjunction not axiom refuse tp float pin refuse purify refine live ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT purify-refine LIVE **conservation** authority (cited read-only, not forked).
purifyRefineLiveConservationAuthority :: String
purifyRefineLiveConservationAuthority =
  "umst/umst-chem/src/impure_pure_adjunction.rs"

-- | L0 CAT-03 table authority (crosswalk).
chemL0Cat03Authority :: String
chemL0Cat03Authority = "CHEM-L0-CAT-03"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | Adjunction-cost Landauer x-row authority (read-only cite).
adjunctionCostLandauerAuthority :: String
adjunctionCostLandauerAuthority =
  "umst/umst-chem/src/x_rows/adjunction_cost_landauer.rs"

-- | Haskell adjunction-cost Landauer crosswalk (read-only cite).
adjunctionCostLandauerHsAuthority :: String
adjunctionCostLandauerHsAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/AdjunctionCostLandauer.hs"

-- | L0 impure-component-morphism authority (refuse_free_purification crosswalk).
impureComponentMorphismAuthority :: String
impureComponentMorphismAuthority =
  "umst/umst-chem/src/l0_tables/impure_component_morphism.rs"

-- | Goldschmidt conservation dependency (read-only cite — not forked).
goldschmidtConservationAuthority :: String
goldschmidtConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/GoldschmidtConservation.hs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

purifyRefineLiveConservationCellId :: String
purifyRefineLiveConservationCellId =
  "CHEM-FORMAL-Q-HS-PURIFY-REFINE-LIVE-CONSERVATION"

-- | Non-claim fence — class-14 **purifyRefineLive** **conservation** Unwired ≠ Proved GREEN.
purifyRefineLiveConservationNonClaim :: String
purifyRefineLiveConservationNonClaim =
  "CHEM-FORMAL-Q-HS-PURIFY-REFINE-LIVE-CONSERVATION PurifyRefineLiveConservationModality Unwired Assumed Proved Surrogate four-step lattice purifyRefineLiveConservationProved false evaluatePurifyRefineLiveBundle evaluatePurifyRefineLiveConservation named LIVE purify refine adjunction refine adjunction cost landauer no free purification concurrent product identity conserved present ge 2 product not XOR adjunction witness concurrent xor mutually exclusive refuse parallel purify refine axiom refuse free purification refuse adjunction not axiom refuse tp float pin refuse purify refine live ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-14 **purifyRefineLive** **conservation** scaffold.
purifyRefineLiveConservationPhysicsGreenAuthorized :: Bool
purifyRefineLiveConservationPhysicsGreenAuthorized = False

purifyRefineLiveConservationPhysicsGreenFalse :: Bool
purifyRefineLiveConservationPhysicsGreenFalse =
  not purifyRefineLiveConservationPhysicsGreenAuthorized

purifyRefineLiveConservationModalityUnwired :: Bool
purifyRefineLiveConservationModalityUnwired =
  purifyRefineLiveConservationModalityCurrent == PurifyRefineLiveConservationUnwired

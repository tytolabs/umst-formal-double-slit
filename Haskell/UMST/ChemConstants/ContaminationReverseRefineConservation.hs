-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ContaminationReverseRefineConservation
Description : Class-20 **contamination-reverse-refine** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Contamination-reverse-refine** **conservation**: north-star §2 class 20
(@contamination_reverse_refine@) — contamination is the **reverse Refine** inverse morphism on
the same second-law + **conservation** object, not a 26th axiom. Reverse contaminate inverse
morphism ⊗ messy Env sample section ⊗ PatternBundle Π_c is **product** not XOR. Named class-20
**contamination-reverse-refine** identity conserved under honest scaffold; trivial XOR, parallel
contamination axiom, free mix-reverse, third chemistry, and GREEN invent fail-closed. Class-20
**conservation** laws are structure witnesses only (@contaminationReverseRefineConservationProved@ =
False). No SpeciesId fork.

* @ContaminationReverseRefineConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateContaminationReverseRefineBundle@ — named class-20 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateContaminationReverseRefineConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@contaminationReverseRefineConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of class-20 **contamination-reverse-refine** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-CONTAMINATION-REVERSE-REFINE-CONSERVATION@.
INT: umst/umst-chem/src/contamination_reverse_refine.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.ContaminationReverseRefineConservation
  ( ContaminationReverseRefineConservationModality (..)
  , contaminationReverseRefineConservationModalityCurrent
  , contaminationReverseRefineLatticeAll
  , contaminationReverseRefineLatticeCount
  , class20ContaminationReverseRefinePatternIndex
  , ContaminationReverseRefineChannelSlot (..)
  , contaminationReverseRefineChannelSlotAll
  , contaminationReverseRefineChannelSlotCount
  , ContaminationReverseRefineProductChannel (..)
  , contaminationReverseRefineProductChannelAll
  , contaminationReverseRefineProductChannelCount
  , contaminationReverseRefineProductChannelIndex
  , ContaminationReverseRefineConcurrentBundle (..)
  , contaminationReverseRefineConcurrentBundleUnwired
  , contaminationReverseRefineConcurrentBundleWithChannel
  , contaminationReverseRefineConcurrentBundleWithPresent
  , contaminationReverseRefineConcurrentBundleChannelAt
  , contaminationReverseRefineConcurrentBundleHolds
  , contaminationReverseRefineConcurrentBundlePresentCount
  , contaminationReverseRefineConcurrentBundleIsConcurrentProduct
  , contaminationReverseRefineWitness
  , ContaminationReverseRefineXorPosture (..)
  , contaminationReverseRefineXorPostureExclusive
  , contaminationReverseRefineXorPostureConcurrent
  , ContaminationReverseRefineConservationVerdict (..)
  , ContaminationReverseRefineXorVerdict (..)
  , evaluateContaminationReverseRefineBundle
  , evaluateContaminationReverseRefineXor
  , evaluateContaminationReverseRefineConservation
  , ContaminationReverseRefineConservationLaw (..)
  , contaminationReverseRefineConservationLawAll
  , contaminationReverseRefineConservationLawCount
  , sampleContaminationReverseRefineBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , contaminationReverseRefineConcurrentOk
  , class20ContaminationReverseRefinePatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventContaminationReverseRefineRefuse
  , parallelContaminationAxiomRefuse
  , freeMixReverseRefuse
  , thirdChemistryRefuse
  , tpFloatPinRefuse
  , assumedContaminationReverseRefineDesignOk
  , surrogateContaminationReverseRefineDesignOk
  , contaminationReverseRefineLatticeScaffold
  , contaminationReverseRefineLatticeNotGreenTable
  , contaminationReverseRefineConservationLawsScaffold
  , contaminationReverseRefineConservationLawsNotGreenTable
  , contaminationReverseRefineKnowingFiberOk
  , contaminationReverseRefineConservationInventRefuse
  , contaminationReverseRefineLatticeNotXor
  , contaminationReverseRefineConservationProved
  , contaminationReverseRefineConservationNeSpeciesId
  , speciesIdForked
  , ironAtomicNumberZ
  , copperAtomicNumberZ
  , contaminationReverseRefineConservationFraming
  , contaminationReverseRefineConservationAxiom
  , contaminationReverseRefineConservationNamed
  , contaminationReverseRefineConservationAuthority
  , chemL0ContaminationReverseRefineAuthority
  , patternProductConservationAuthority
  , contaminationIsMessySectionAuthority
  , refineEffectTypesAuthority
  , messyIsGraphSectionAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , contaminationReverseRefineConservationCellId
  , contaminationReverseRefineConservationNonClaim
  , contaminationReverseRefineConservationPhysicsGreenAuthorized
  , contaminationReverseRefineConservationPhysicsGreenFalse
  , contaminationReverseRefineConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not contamination-reverse-refine GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-20 (`contamination_reverse_refine`) pattern index.
class20ContaminationReverseRefinePatternIndex :: Int
class20ContaminationReverseRefinePatternIndex = 20

-- | Iron Z=26 — ore host witness element pin.
ironAtomicNumberZ :: Int
ironAtomicNumberZ = 26

-- | Copper Z=29 — trace contaminant witness element pin.
copperAtomicNumberZ :: Int
copperAtomicNumberZ = 29

-- | Design **contamination-reverse-refine** modality for class-20 **conservation** claims.
data ContaminationReverseRefineConservationModality
  = ContaminationReverseRefineConservationUnwired
  | ContaminationReverseRefineConservationAssumed
  | ContaminationReverseRefineConservationProved
  | ContaminationReverseRefineConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **contamination-reverse-refine** modality — always Unwired on this cell.
contaminationReverseRefineConservationModalityCurrent :: ContaminationReverseRefineConservationModality
contaminationReverseRefineConservationModalityCurrent =
  ContaminationReverseRefineConservationUnwired

-- | All class-20 **contamination-reverse-refine** lattice steps in stable order.
contaminationReverseRefineLatticeAll :: [ContaminationReverseRefineConservationModality]
contaminationReverseRefineLatticeAll =
  [ ContaminationReverseRefineConservationUnwired
  , ContaminationReverseRefineConservationAssumed
  , ContaminationReverseRefineConservationProved
  , ContaminationReverseRefineConservationSurrogate
  ]

contaminationReverseRefineLatticeCount :: Int
contaminationReverseRefineLatticeCount = length contaminationReverseRefineLatticeAll

-- | Contamination-reverse-refine product channel slot — concurrent **product** factor, not XOR bucket.
data ContaminationReverseRefineChannelSlot
  = ContaminationReverseRefineSlotUnwired
  | ContaminationReverseRefineSlotAbsent
  | ContaminationReverseRefineSlotPresent
  deriving (Eq, Show)

-- | All contamination-reverse-refine channel slots in stable order.
contaminationReverseRefineChannelSlotAll :: [ContaminationReverseRefineChannelSlot]
contaminationReverseRefineChannelSlotAll =
  [ ContaminationReverseRefineSlotUnwired
  , ContaminationReverseRefineSlotAbsent
  , ContaminationReverseRefineSlotPresent
  ]

contaminationReverseRefineChannelSlotCount :: Int
contaminationReverseRefineChannelSlotCount = length contaminationReverseRefineChannelSlotAll

-- | Named reverse-contaminate inverse / messy Env section / PatternBundle product channels.
data ContaminationReverseRefineProductChannel
  = ReverseContaminateInverseMorphism
  | MessyEnvSampleSectionRestriction
  | PatternBundleConcurrentFactor
  deriving (Eq, Show)

-- | All contamination-reverse-refine product channels in north-star stable order.
contaminationReverseRefineProductChannelAll :: [ContaminationReverseRefineProductChannel]
contaminationReverseRefineProductChannelAll =
  [ ReverseContaminateInverseMorphism
  , MessyEnvSampleSectionRestriction
  , PatternBundleConcurrentFactor
  ]

contaminationReverseRefineProductChannelCount :: Int
contaminationReverseRefineProductChannelCount = length contaminationReverseRefineProductChannelAll

-- | Stable channel index for a contamination-reverse-refine product channel (0..2).
contaminationReverseRefineProductChannelIndex :: ContaminationReverseRefineProductChannel -> Int
contaminationReverseRefineProductChannelIndex channel =
  case channel of
    ReverseContaminateInverseMorphism -> 0
    MessyEnvSampleSectionRestriction -> 1
    PatternBundleConcurrentFactor -> 2

-- | Class-20 contamination-reverse-refine concurrent **product** bundle (north-star §3).
data ContaminationReverseRefineConcurrentBundle = ContaminationReverseRefineConcurrentBundle
  { contaminationReverseRefineClassPresent :: Bool
  , contaminationReverseRefineChannelSlots :: [ContaminationReverseRefineChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
contaminationReverseRefineConcurrentBundleUnwired :: ContaminationReverseRefineConcurrentBundle
contaminationReverseRefineConcurrentBundleUnwired =
  ContaminationReverseRefineConcurrentBundle
    False
    (replicate contaminationReverseRefineProductChannelCount ContaminationReverseRefineSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
contaminationReverseRefineConcurrentBundleWithChannel ::
  Int -> ContaminationReverseRefineChannelSlot -> ContaminationReverseRefineConcurrentBundle -> ContaminationReverseRefineConcurrentBundle
contaminationReverseRefineConcurrentBundleWithChannel idx slot bundle =
  let slots = contaminationReverseRefineChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in ContaminationReverseRefineConcurrentBundle
        (contaminationReverseRefineClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the contamination-reverse-refine **product**.
contaminationReverseRefineConcurrentBundleWithPresent ::
  Int -> ContaminationReverseRefineConcurrentBundle -> ContaminationReverseRefineConcurrentBundle
contaminationReverseRefineConcurrentBundleWithPresent idx bundle =
  contaminationReverseRefineConcurrentBundleWithChannel idx ContaminationReverseRefineSlotPresent bundle

-- | Read channel slot at index (0..2).
contaminationReverseRefineConcurrentBundleChannelAt ::
  Int -> ContaminationReverseRefineConcurrentBundle -> Maybe ContaminationReverseRefineChannelSlot
contaminationReverseRefineConcurrentBundleChannelAt idx bundle =
  let slots = contaminationReverseRefineChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
contaminationReverseRefineConcurrentBundleHolds :: Int -> ContaminationReverseRefineConcurrentBundle -> Bool
contaminationReverseRefineConcurrentBundleHolds idx bundle =
  case contaminationReverseRefineConcurrentBundleChannelAt idx bundle of
    Just ContaminationReverseRefineSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
contaminationReverseRefineConcurrentBundlePresentCount :: ContaminationReverseRefineConcurrentBundle -> Int
contaminationReverseRefineConcurrentBundlePresentCount bundle =
  length (filter (== ContaminationReverseRefineSlotPresent) (contaminationReverseRefineChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
contaminationReverseRefineConcurrentBundleIsConcurrentProduct :: ContaminationReverseRefineConcurrentBundle -> Bool
contaminationReverseRefineConcurrentBundleIsConcurrentProduct bundle =
  contaminationReverseRefineConcurrentBundlePresentCount bundle >= 2

-- | Class-20 witness: reverse contaminate (0) + messy Env section (1) + PatternBundle (2) concurrent on class 20.
contaminationReverseRefineWitness :: ContaminationReverseRefineConcurrentBundle
contaminationReverseRefineWitness =
  contaminationReverseRefineConcurrentBundleWithPresent 2
    (contaminationReverseRefineConcurrentBundleWithPresent 1
      (contaminationReverseRefineConcurrentBundleWithPresent 0
        (ContaminationReverseRefineConcurrentBundle True
          (replicate contaminationReverseRefineProductChannelCount ContaminationReverseRefineSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data ContaminationReverseRefineXorPosture
  = ContaminationReverseRefineXorExclusive
  | ContaminationReverseRefineXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
contaminationReverseRefineXorPostureExclusive :: ContaminationReverseRefineXorPosture
contaminationReverseRefineXorPostureExclusive = ContaminationReverseRefineXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
contaminationReverseRefineXorPostureConcurrent :: ContaminationReverseRefineXorPosture
contaminationReverseRefineXorPostureConcurrent = ContaminationReverseRefineXorConcurrent

-- | Verdict for contamination-reverse-refine **conservation** close (fail-closed).
data ContaminationReverseRefineConservationVerdict
  = ContaminationReverseRefineConservationDesignOk
  | ContaminationReverseRefineConservationNamedOk
  | ContaminationReverseRefineConservationTrivialRefuse
  | ContaminationReverseRefineConservationGreenInventRefuse
  | ContaminationReverseRefineConservationProvedWithoutBarRefuse
  | ContaminationReverseRefineConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data ContaminationReverseRefineXorVerdict
  = ContaminationReverseRefineXorDesignOk
  | ContaminationReverseRefineXorNamedOk
  | ContaminationReverseRefineXorGreenInventRefuse
  | ContaminationReverseRefineXorProvedWithoutBarRefuse
  | ContaminationReverseRefineXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a contamination-reverse-refine bundle under class-20 **conservation** bar (fail-closed).
evaluateContaminationReverseRefineBundle ::
  ContaminationReverseRefineConservationModality
  -> ContaminationReverseRefineConcurrentBundle
  -> Bool
  -> Bool
  -> ContaminationReverseRefineConservationVerdict
evaluateContaminationReverseRefineBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = ContaminationReverseRefineConservationGreenInventRefuse
  | claimProved = ContaminationReverseRefineConservationProvedWithoutBarRefuse
  | length (contaminationReverseRefineChannelSlots bundle) /= contaminationReverseRefineProductChannelCount =
      ContaminationReverseRefineConservationTrivialRefuse
  | otherwise =
      case modality of
        ContaminationReverseRefineConservationUnwired ->
          if contaminationReverseRefineConcurrentBundleIsConcurrentProduct bundle
            then ContaminationReverseRefineConservationNamedOk
            else ContaminationReverseRefineConservationDesignOk
        ContaminationReverseRefineConservationAssumed -> ContaminationReverseRefineConservationDesignOk
        ContaminationReverseRefineConservationSurrogate -> ContaminationReverseRefineConservationDesignOk
        ContaminationReverseRefineConservationProved -> ContaminationReverseRefineConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-20 **conservation** bar (fail-closed).
evaluateContaminationReverseRefineXor ::
  ContaminationReverseRefineConservationModality
  -> ContaminationReverseRefineXorPosture
  -> Bool
  -> Bool
  -> ContaminationReverseRefineXorVerdict
evaluateContaminationReverseRefineXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = ContaminationReverseRefineXorGreenInventRefuse
  | claimProved = ContaminationReverseRefineXorProvedWithoutBarRefuse
  | posture == ContaminationReverseRefineXorExclusive = ContaminationReverseRefineXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        ContaminationReverseRefineConservationUnwired -> ContaminationReverseRefineXorNamedOk
        ContaminationReverseRefineConservationAssumed -> ContaminationReverseRefineXorDesignOk
        ContaminationReverseRefineConservationSurrogate -> ContaminationReverseRefineXorDesignOk
        ContaminationReverseRefineConservationProved -> ContaminationReverseRefineXorProvedWithoutBarRefuse

-- | **Contamination-reverse-refine** identity law cells tracked by class-20 **conservation** (structure scaffold).
data ContaminationReverseRefineConservationLaw
  = ContaminationReverseRefineConservationConserved
  | NamedContaminationReverseRefineConservationOk
  | TrivialContaminationReverseRefineRefused
  | GreenInventContaminationReverseRefineRefused
  deriving (Eq, Show)

contaminationReverseRefineConservationLawAll :: [ContaminationReverseRefineConservationLaw]
contaminationReverseRefineConservationLawAll =
  [ ContaminationReverseRefineConservationConserved
  , NamedContaminationReverseRefineConservationOk
  , TrivialContaminationReverseRefineRefused
  , GreenInventContaminationReverseRefineRefused
  ]

contaminationReverseRefineConservationLawCount :: Int
contaminationReverseRefineConservationLawCount = length contaminationReverseRefineConservationLawAll

-- | Evaluate class-20 **contamination-reverse-refine** **conservation** typing (fail-closed).
evaluateContaminationReverseRefineConservation ::
  ContaminationReverseRefineConservationModality
  -> ContaminationReverseRefineConcurrentBundle
  -> ContaminationReverseRefineXorPosture
  -> Bool
  -> Bool
  -> ContaminationReverseRefineConservationVerdict
evaluateContaminationReverseRefineConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = ContaminationReverseRefineConservationGreenInventRefuse
  | claimProved = ContaminationReverseRefineConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateContaminationReverseRefineXor modality posture False False of
        ContaminationReverseRefineXorMutuallyExclusiveRefuse -> ContaminationReverseRefineConservationXorRefuse
        ContaminationReverseRefineXorGreenInventRefuse -> ContaminationReverseRefineConservationGreenInventRefuse
        ContaminationReverseRefineXorProvedWithoutBarRefuse -> ContaminationReverseRefineConservationProvedWithoutBarRefuse
        _ ->
          case evaluateContaminationReverseRefineBundle modality bundle False False of
            ContaminationReverseRefineConservationNamedOk -> ContaminationReverseRefineConservationNamedOk
            ContaminationReverseRefineConservationGreenInventRefuse -> ContaminationReverseRefineConservationGreenInventRefuse
            ContaminationReverseRefineConservationProvedWithoutBarRefuse -> ContaminationReverseRefineConservationProvedWithoutBarRefuse
            ContaminationReverseRefineConservationTrivialRefuse -> ContaminationReverseRefineConservationTrivialRefuse
            ContaminationReverseRefineConservationXorRefuse -> ContaminationReverseRefineConservationXorRefuse
            ContaminationReverseRefineConservationDesignOk -> ContaminationReverseRefineConservationDesignOk

sampleContaminationReverseRefineBundle :: ContaminationReverseRefineConcurrentBundle
sampleContaminationReverseRefineBundle = contaminationReverseRefineWitness

sampleXorExclusiveBundle :: ContaminationReverseRefineConcurrentBundle
sampleXorExclusiveBundle = contaminationReverseRefineConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: ContaminationReverseRefineConcurrentBundle
sampleTrivialUnwiredBundle = contaminationReverseRefineConcurrentBundleUnwired

-- | Unwired **contamination-reverse-refine** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateContaminationReverseRefineConservation
    ContaminationReverseRefineConservationUnwired
    sampleContaminationReverseRefineBundle
    contaminationReverseRefineXorPostureConcurrent
    False
    False
    == ContaminationReverseRefineConservationNamedOk

-- | Class-20 witness: reverse contaminate + messy Env section + PatternBundle concurrent Π_c on class 20.
contaminationReverseRefineConcurrentOk :: Bool
contaminationReverseRefineConcurrentOk =
  let bundle = contaminationReverseRefineWitness
   in contaminationReverseRefineClassPresent bundle
        && contaminationReverseRefineConcurrentBundleHolds 0 bundle
        && contaminationReverseRefineConcurrentBundleHolds 1 bundle
        && contaminationReverseRefineConcurrentBundleHolds 2 bundle
        && contaminationReverseRefineConcurrentBundlePresentCount bundle == 3
        && contaminationReverseRefineConcurrentBundleIsConcurrentProduct bundle
        && ironAtomicNumberZ == 26
        && copperAtomicNumberZ == 29
        && class20ContaminationReverseRefinePatternIndex == 20

-- | Class-20 contamination-reverse-refine pattern index pinned @ scaffold.
class20ContaminationReverseRefinePatternIndexOk :: Bool
class20ContaminationReverseRefinePatternIndexOk =
  class20ContaminationReverseRefinePatternIndex == 20
    && contaminationReverseRefineProductChannelCount == 3
    && length (contaminationReverseRefineChannelSlots contaminationReverseRefineConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  contaminationReverseRefineConcurrentBundleIsConcurrentProduct contaminationReverseRefineWitness
    && contaminationReverseRefineConcurrentBundlePresentCount contaminationReverseRefineWitness >= 2
    && contaminationReverseRefineConcurrentBundlePresentCount contaminationReverseRefineWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateContaminationReverseRefineXor
    ContaminationReverseRefineConservationUnwired
    contaminationReverseRefineXorPostureExclusive
    False
    False
    == ContaminationReverseRefineXorMutuallyExclusiveRefuse
    && evaluateContaminationReverseRefineConservation
      ContaminationReverseRefineConservationUnwired
      sampleContaminationReverseRefineBundle
      contaminationReverseRefineXorPostureExclusive
      False
      False
      == ContaminationReverseRefineConservationXorRefuse

-- | GREEN invent on **contamination-reverse-refine** **conservation** promotion is refused.
greenInventContaminationReverseRefineRefuse :: Bool
greenInventContaminationReverseRefineRefuse =
  evaluateContaminationReverseRefineConservation
    ContaminationReverseRefineConservationUnwired
    sampleContaminationReverseRefineBundle
    contaminationReverseRefineXorPostureConcurrent
    True
    False
    == ContaminationReverseRefineConservationGreenInventRefuse
    && evaluateContaminationReverseRefineBundle
      ContaminationReverseRefineConservationUnwired
      sampleContaminationReverseRefineBundle
      True
      False
      == ContaminationReverseRefineConservationGreenInventRefuse

-- | Parallel contamination axiom (26th law) mint is refused — second law + conservation only.
parallelContaminationAxiomRefuse :: Bool
parallelContaminationAxiomRefuse =
  contaminationReverseRefineConservationAuthority
    == "umst/umst-chem/src/contamination_reverse_refine.rs"
    && contaminationReverseRefineConservationProved == False
    && not (contaminationReverseRefineConservationAuthority == "26th_chemistry_axiom")
    && contaminationReverseRefineConservationFraming
      /= "parallel_contamination_axiom_not_second_law"
    && chemL0ContaminationReverseRefineAuthority
      == "umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs"

-- | Free mix-reverse on reverse Refine morphism is refused — second-law fence mandatory.
freeMixReverseRefuse :: Bool
freeMixReverseRefuse =
  parallelContaminationAxiomRefuse
    && contaminationReverseRefineConservationFraming
      /= "free_mix_reverse_ne_dissipative_refine"
    && refineEffectTypesAuthority
      == "umst/umst-chem/src/refine_effect_types.rs"
    && messyIsGraphSectionAuthority
      == "umst/umst-chem/src/messy_is_graph_section.rs"
    && class20ContaminationReverseRefinePatternIndex == 20

-- | Third chemistry / parallel contamination law mint is refused — sole axiom only.
thirdChemistryRefuse :: Bool
thirdChemistryRefuse =
  freeMixReverseRefuse
    && contaminationReverseRefineConservationFraming
      /= "contamination_third_chemistry_not_env_coordinate"
    && contaminationIsMessySectionAuthority
      == "umst/umst-chem/src/contamination_is_messy_section.rs"
    && class20ContaminationReverseRefinePatternIndex == 20
    && contaminationReverseRefineConcurrentBundleIsConcurrentProduct contaminationReverseRefineWitness

-- | T/P graph functions on Interact graph — refuse bare float-pin smuggle on contamination scaffold.
tpFloatPinRefuse :: Bool
tpFloatPinRefuse =
  thirdChemistryRefuse
    && contaminationReverseRefineConservationFraming
      /= "tp_bare_float_pin_on_contamination_reverse_refine"
    && temperatureGraphFunctionAuthority
      == "umst/umst-chem/src/temperature_is_graph_function.rs"
    && pressureGraphFunctionAuthority
      == "umst/umst-chem/src/pressure_is_graph_function.rs"
    && class20ContaminationReverseRefinePatternIndex == 20

-- | Assumed **contamination-reverse-refine** modality OK without thermo break (design scaffold).
assumedContaminationReverseRefineDesignOk :: Bool
assumedContaminationReverseRefineDesignOk =
  evaluateContaminationReverseRefineConservation
    ContaminationReverseRefineConservationAssumed
    sampleContaminationReverseRefineBundle
    contaminationReverseRefineXorPostureConcurrent
    False
    False
    == ContaminationReverseRefineConservationDesignOk

-- | Surrogate **contamination-reverse-refine** modality OK without thermo break (design scaffold).
surrogateContaminationReverseRefineDesignOk :: Bool
surrogateContaminationReverseRefineDesignOk =
  evaluateContaminationReverseRefineConservation
    ContaminationReverseRefineConservationSurrogate
    sampleContaminationReverseRefineBundle
    contaminationReverseRefineXorPostureConcurrent
    False
    False
    == ContaminationReverseRefineConservationDesignOk

-- | Four-step class-20 **contamination-reverse-refine** lattice scaffold pinned.
contaminationReverseRefineLatticeScaffold :: Bool
contaminationReverseRefineLatticeScaffold =
  contaminationReverseRefineLatticeCount == 4
    && unwiredDesignOk
    && class20ContaminationReverseRefinePatternIndexOk
    && contaminationReverseRefineConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedContaminationReverseRefineDesignOk
    && surrogateContaminationReverseRefineDesignOk
    && parallelContaminationAxiomRefuse
    && freeMixReverseRefuse
    && thirdChemistryRefuse
    && tpFloatPinRefuse

-- | **Contamination-reverse-refine** lattice is structure scaffold — not 118² GREEN periodic table.
contaminationReverseRefineLatticeNotGreenTable :: Bool
contaminationReverseRefineLatticeNotGreenTable =
  contaminationReverseRefineLatticeCount == 4
    && contaminationReverseRefineLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && contaminationReverseRefineProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && contaminationReverseRefineChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **contamination-reverse-refine** identity law cells scaffold pinned.
contaminationReverseRefineConservationLawsScaffold :: Bool
contaminationReverseRefineConservationLawsScaffold =
  contaminationReverseRefineConservationLawCount == 4
    && contaminationReverseRefineConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventContaminationReverseRefineRefuse
    && parallelContaminationAxiomRefuse
    && freeMixReverseRefuse
    && thirdChemistryRefuse
    && tpFloatPinRefuse

-- | **Contamination-reverse-refine** law cells are structure scaffold — not 118² GREEN periodic table.
contaminationReverseRefineConservationLawsNotGreenTable :: Bool
contaminationReverseRefineConservationLawsNotGreenTable =
  contaminationReverseRefineConservationLawsScaffold
    && contaminationReverseRefineConservationLawCount /= 118 * 118
    && contaminationReverseRefineProductChannelCount /= 118 * 118

-- | Class-20 **contamination-reverse-refine** **conservation** claims route to knowing / quantum fiber (not meso acting).
contaminationReverseRefineKnowingFiberOk :: Bool
contaminationReverseRefineKnowingFiberOk = True

-- | Class-20 **contamination-reverse-refine** invent refuse-closed scaffold witness.
contaminationReverseRefineConservationInventRefuse :: Bool
contaminationReverseRefineConservationInventRefuse =
  not contaminationReverseRefineConservationProved

-- | **Contamination-reverse-refine** lattice steps are concurrent Π_c — not XOR enum bucket.
contaminationReverseRefineLatticeNotXor :: Bool
contaminationReverseRefineLatticeNotXor =
  unwiredDesignOk
    && assumedContaminationReverseRefineDesignOk
    && surrogateContaminationReverseRefineDesignOk
    && contaminationReverseRefineConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventContaminationReverseRefineRefuse

-- | Class-20 **contamination-reverse-refine** proved (always false on this Unwired cell).
contaminationReverseRefineConservationProved :: Bool
contaminationReverseRefineConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Contamination-reverse-refine** morphisms are class-20 neighbor channels — not SpeciesId tag mint.
contaminationReverseRefineConservationNeSpeciesId :: Bool
contaminationReverseRefineConservationNeSpeciesId =
  contaminationReverseRefineConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && contaminationReverseRefineProductChannelAll /= []
    && contaminationReverseRefineConcurrentBundleIsConcurrentProduct contaminationReverseRefineWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-20 **contamination-reverse-refine** scaffold.
contaminationReverseRefineConservationFraming :: String
contaminationReverseRefineConservationFraming =
  "second_law_conservation_contamination_reverse_refine_one_axiom"

-- | Single design axiom: second law + **conservation** class-20 contamination-reverse-refine (not 26th axiom).
contaminationReverseRefineConservationAxiom :: Bool
contaminationReverseRefineConservationAxiom =
  contaminationReverseRefineLatticeScaffold
    && contaminationReverseRefineLatticeNotGreenTable
    && contaminationReverseRefineConservationLawsScaffold
    && contaminationReverseRefineConservationLawsNotGreenTable
    && contaminationReverseRefineKnowingFiberOk
    && class20ContaminationReverseRefinePatternIndexOk
    && contaminationReverseRefineConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventContaminationReverseRefineRefuse
    && parallelContaminationAxiomRefuse
    && freeMixReverseRefuse
    && thirdChemistryRefuse
    && tpFloatPinRefuse
    && contaminationReverseRefineConservationInventRefuse
    && contaminationReverseRefineLatticeNotXor
    && contaminationReverseRefineConservationNeSpeciesId
    && not contaminationReverseRefineConservationProved
    && not speciesIdForked
    && contaminationReverseRefineConservationFraming
      == "second_law_conservation_contamination_reverse_refine_one_axiom"

contaminationReverseRefineConservationNamed :: String
contaminationReverseRefineConservationNamed =
  "contaminationReverseRefineConservation: ContaminationReverseRefineConservationModality Unwired Assumed Proved Surrogate four-step lattice contaminationReverseRefineConservationProved false evaluateContaminationReverseRefineBundle evaluateContaminationReverseRefineConservation named class 20 contamination_reverse_refine reverse contaminate inverse morphism messy Env sample section restriction PatternBundle concurrent factor concurrent product identity conserved present ge 2 product not XOR contamination reverse refine witness concurrent xor mutually exclusive refuse parallel contamination axiom refuse free mix reverse refuse third chemistry refuse tp float pin refuse contamination reverse refine ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT contamination-reverse-refine **conservation** authority (cited read-only, not forked).
contaminationReverseRefineConservationAuthority :: String
contaminationReverseRefineConservationAuthority =
  "umst/umst-chem/src/contamination_reverse_refine.rs"

-- | L0 class-20 contamination-reverse-refine table authority (crosswalk).
chemL0ContaminationReverseRefineAuthority :: String
chemL0ContaminationReverseRefineAuthority =
  "umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | Contamination-on-messy-section authority (class 20 Env coordinate — not new law).
contaminationIsMessySectionAuthority :: String
contaminationIsMessySectionAuthority =
  "umst/umst-chem/src/contamination_is_messy_section.rs"

-- | L0 Refine effect-types authority (forward Refine / reverse contaminate typing).
refineEffectTypesAuthority :: String
refineEffectTypesAuthority = "umst/umst-chem/src/refine_effect_types.rs"

-- | Messy graph section authority (free mix-reverse refuse fence).
messyIsGraphSectionAuthority :: String
messyIsGraphSectionAuthority = "umst/umst-chem/src/messy_is_graph_section.rs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

contaminationReverseRefineConservationCellId :: String
contaminationReverseRefineConservationCellId =
  "CHEM-FORMAL-Q-HS-CONTAMINATION-REVERSE-REFINE-CONSERVATION"

-- | Non-claim fence — class-20 **contamination-reverse-refine** **conservation** Unwired ≠ Proved GREEN.
contaminationReverseRefineConservationNonClaim :: String
contaminationReverseRefineConservationNonClaim =
  "CHEM-FORMAL-Q-HS-CONTAMINATION-REVERSE-REFINE-CONSERVATION ContaminationReverseRefineConservationModality Unwired Assumed Proved Surrogate four-step lattice contaminationReverseRefineConservationProved false evaluateContaminationReverseRefineBundle evaluateContaminationReverseRefineConservation named class 20 contamination_reverse_refine reverse contaminate inverse morphism messy Env sample section restriction PatternBundle concurrent factor concurrent product identity conserved present ge 2 product not XOR contamination reverse refine witness concurrent xor mutually exclusive refuse parallel contamination axiom refuse free mix reverse refuse third chemistry refuse tp float pin refuse contamination reverse refine ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-20 **contamination-reverse-refine** **conservation** scaffold.
contaminationReverseRefineConservationPhysicsGreenAuthorized :: Bool
contaminationReverseRefineConservationPhysicsGreenAuthorized = False

contaminationReverseRefineConservationPhysicsGreenFalse :: Bool
contaminationReverseRefineConservationPhysicsGreenFalse =
  not contaminationReverseRefineConservationPhysicsGreenAuthorized

contaminationReverseRefineConservationModalityUnwired :: Bool
contaminationReverseRefineConservationModalityUnwired =
  contaminationReverseRefineConservationModalityCurrent == ContaminationReverseRefineConservationUnwired

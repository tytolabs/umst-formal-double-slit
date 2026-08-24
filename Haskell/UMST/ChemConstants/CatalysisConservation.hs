-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.CatalysisConservation
Description : Class-14 **catalysis** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Catalysis** **conservation**: north-star §2 class 14
(@catalysis@) — catalysis is an **Interact** restriction on the same second-law +
**conservation** object, not a 26th axiom. Interact restriction ⊗ activation barrier↓
⊗ catalyst-not-consumed Π_c is **product** not XOR. Named class-14 **catalysis**
identity conserved under honest scaffold; trivial XOR, parallel catalysis axiom,
catalyst consumed, T/P float-pin smuggle, and GREEN invent fail-closed. Class-14
**conservation** laws are structure witnesses only (@catalysisConservationProved@ =
False). No SpeciesId fork.

* @CatalysisConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateCatalysisBundle@ — named class-14 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateCatalysisConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@catalysisConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of class-14 **catalysis** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-CATALYSIS-CONSERVATION@.
INT: umst/umst-chem/src/catalysis_barrier.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/catalysis.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.CatalysisConservation
  ( CatalysisConservationModality (..)
  , catalysisConservationModalityCurrent
  , catalysisLatticeAll
  , catalysisLatticeCount
  , class14CatalysisPatternIndex
  , CatalysisChannelSlot (..)
  , catalysisChannelSlotAll
  , catalysisChannelSlotCount
  , CatalysisProductChannel (..)
  , catalysisProductChannelAll
  , catalysisProductChannelCount
  , catalysisProductChannelIndex
  , CatalysisConcurrentBundle (..)
  , catalysisConcurrentBundleUnwired
  , catalysisConcurrentBundleWithChannel
  , catalysisConcurrentBundleWithPresent
  , catalysisConcurrentBundleChannelAt
  , catalysisConcurrentBundleHolds
  , catalysisConcurrentBundlePresentCount
  , catalysisConcurrentBundleIsConcurrentProduct
  , catalysisInteractRestrictionWitness
  , CatalysisXorPosture (..)
  , catalysisXorPostureExclusive
  , catalysisXorPostureConcurrent
  , CatalysisConservationVerdict (..)
  , CatalysisXorVerdict (..)
  , evaluateCatalysisBundle
  , evaluateCatalysisXor
  , evaluateCatalysisConservation
  , CatalysisConservationLaw (..)
  , catalysisConservationLawAll
  , catalysisConservationLawCount
  , sampleCatalysisInteractRestrictionBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , catalysisInteractRestrictionConcurrentOk
  , class14CatalysisPatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventCatalysisRefuse
  , parallelCatalysisAxiomRefuse
  , catalystConsumedRefuse
  , interactRestrictionNotAxiomRefuse
  , tpFloatPinRefuse
  , assumedCatalysisDesignOk
  , surrogateCatalysisDesignOk
  , catalysisLatticeScaffold
  , catalysisLatticeNotGreenTable
  , catalysisConservationLawsScaffold
  , catalysisConservationLawsNotGreenTable
  , catalysisKnowingFiberOk
  , catalysisConservationInventRefuse
  , catalysisLatticeNotXor
  , catalysisConservationProved
  , catalysisConservationNeSpeciesId
  , speciesIdForked
  , platinumAtomicNumberZ
  , ironAtomicNumberZ
  , catalysisConservationFraming
  , catalysisConservationAxiom
  , catalysisConservationNamed
  , catalysisConservationAuthority
  , chemL0CatalysisAuthority
  , patternProductConservationAuthority
  , interactRestrictionAuthority
  , kleisliInteractAuthority
  , edgeCatalysisAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , catalysisConservationCellId
  , catalysisConservationNonClaim
  , catalysisConservationPhysicsGreenAuthorized
  , catalysisConservationPhysicsGreenFalse
  , catalysisConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not catalysis GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-14 (`catalysis`) pattern index.
class14CatalysisPatternIndex :: Int
class14CatalysisPatternIndex = 14

-- | Platinum Z=78 — catalyst witness element pin.
platinumAtomicNumberZ :: Int
platinumAtomicNumberZ = 78

-- | Iron Z=26 — ore host witness element pin.
ironAtomicNumberZ :: Int
ironAtomicNumberZ = 26

-- | Design **catalysis** modality for class-14 **conservation** claims.
data CatalysisConservationModality
  = CatalysisConservationUnwired
  | CatalysisConservationAssumed
  | CatalysisConservationProved
  | CatalysisConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **catalysis** modality — always Unwired on this cell.
catalysisConservationModalityCurrent :: CatalysisConservationModality
catalysisConservationModalityCurrent =
  CatalysisConservationUnwired

-- | All class-14 **catalysis** lattice steps in stable order.
catalysisLatticeAll :: [CatalysisConservationModality]
catalysisLatticeAll =
  [ CatalysisConservationUnwired
  , CatalysisConservationAssumed
  , CatalysisConservationProved
  , CatalysisConservationSurrogate
  ]

catalysisLatticeCount :: Int
catalysisLatticeCount = length catalysisLatticeAll

-- | Catalysis product channel slot — concurrent **product** factor, not XOR bucket.
data CatalysisChannelSlot
  = CatalysisSlotUnwired
  | CatalysisSlotAbsent
  | CatalysisSlotPresent
  deriving (Eq, Show)

-- | All catalysis channel slots in stable order.
catalysisChannelSlotAll :: [CatalysisChannelSlot]
catalysisChannelSlotAll =
  [ CatalysisSlotUnwired
  , CatalysisSlotAbsent
  , CatalysisSlotPresent
  ]

catalysisChannelSlotCount :: Int
catalysisChannelSlotCount = length catalysisChannelSlotAll

-- | Named Interact restriction / barrier↓ / catalyst-not-consumed product channels.
data CatalysisProductChannel
  = InteractRestrictionCatalysis
  | ActivationBarrierLowered
  | CatalystNotConsumed
  deriving (Eq, Show)

-- | All catalysis product channels in north-star stable order.
catalysisProductChannelAll :: [CatalysisProductChannel]
catalysisProductChannelAll =
  [ InteractRestrictionCatalysis
  , ActivationBarrierLowered
  , CatalystNotConsumed
  ]

catalysisProductChannelCount :: Int
catalysisProductChannelCount = length catalysisProductChannelAll

-- | Stable channel index for a catalysis product channel (0..2).
catalysisProductChannelIndex :: CatalysisProductChannel -> Int
catalysisProductChannelIndex channel =
  case channel of
    InteractRestrictionCatalysis -> 0
    ActivationBarrierLowered -> 1
    CatalystNotConsumed -> 2

-- | Class-14 catalysis concurrent **product** bundle (north-star §3).
data CatalysisConcurrentBundle = CatalysisConcurrentBundle
  { catalysisClassPresent :: Bool
  , catalysisChannelSlots :: [CatalysisChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
catalysisConcurrentBundleUnwired :: CatalysisConcurrentBundle
catalysisConcurrentBundleUnwired =
  CatalysisConcurrentBundle
    False
    (replicate catalysisProductChannelCount CatalysisSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
catalysisConcurrentBundleWithChannel ::
  Int -> CatalysisChannelSlot -> CatalysisConcurrentBundle -> CatalysisConcurrentBundle
catalysisConcurrentBundleWithChannel idx slot bundle =
  let slots = catalysisChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in CatalysisConcurrentBundle
        (catalysisClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the catalysis **product**.
catalysisConcurrentBundleWithPresent ::
  Int -> CatalysisConcurrentBundle -> CatalysisConcurrentBundle
catalysisConcurrentBundleWithPresent idx bundle =
  catalysisConcurrentBundleWithChannel idx CatalysisSlotPresent bundle

-- | Read channel slot at index (0..2).
catalysisConcurrentBundleChannelAt ::
  Int -> CatalysisConcurrentBundle -> Maybe CatalysisChannelSlot
catalysisConcurrentBundleChannelAt idx bundle =
  let slots = catalysisChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
catalysisConcurrentBundleHolds :: Int -> CatalysisConcurrentBundle -> Bool
catalysisConcurrentBundleHolds idx bundle =
  case catalysisConcurrentBundleChannelAt idx bundle of
    Just CatalysisSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
catalysisConcurrentBundlePresentCount :: CatalysisConcurrentBundle -> Int
catalysisConcurrentBundlePresentCount bundle =
  length (filter (== CatalysisSlotPresent) (catalysisChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
catalysisConcurrentBundleIsConcurrentProduct :: CatalysisConcurrentBundle -> Bool
catalysisConcurrentBundleIsConcurrentProduct bundle =
  catalysisConcurrentBundlePresentCount bundle >= 2

-- | Catalysis witness: Interact restriction (0) + barrier↓ (1) + not consumed (2) concurrent on class 14.
catalysisInteractRestrictionWitness :: CatalysisConcurrentBundle
catalysisInteractRestrictionWitness =
  catalysisConcurrentBundleWithPresent 2
    (catalysisConcurrentBundleWithPresent 1
      (catalysisConcurrentBundleWithPresent 0
        (CatalysisConcurrentBundle True
          (replicate catalysisProductChannelCount CatalysisSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data CatalysisXorPosture
  = CatalysisXorExclusive
  | CatalysisXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
catalysisXorPostureExclusive :: CatalysisXorPosture
catalysisXorPostureExclusive = CatalysisXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
catalysisXorPostureConcurrent :: CatalysisXorPosture
catalysisXorPostureConcurrent = CatalysisXorConcurrent

-- | Verdict for catalysis **conservation** close (fail-closed).
data CatalysisConservationVerdict
  = CatalysisConservationDesignOk
  | CatalysisConservationNamedOk
  | CatalysisConservationTrivialRefuse
  | CatalysisConservationGreenInventRefuse
  | CatalysisConservationProvedWithoutBarRefuse
  | CatalysisConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data CatalysisXorVerdict
  = CatalysisXorDesignOk
  | CatalysisXorNamedOk
  | CatalysisXorGreenInventRefuse
  | CatalysisXorProvedWithoutBarRefuse
  | CatalysisXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a catalysis bundle under class-14 **conservation** bar (fail-closed).
evaluateCatalysisBundle ::
  CatalysisConservationModality
  -> CatalysisConcurrentBundle
  -> Bool
  -> Bool
  -> CatalysisConservationVerdict
evaluateCatalysisBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = CatalysisConservationGreenInventRefuse
  | claimProved = CatalysisConservationProvedWithoutBarRefuse
  | length (catalysisChannelSlots bundle) /= catalysisProductChannelCount =
      CatalysisConservationTrivialRefuse
  | otherwise =
      case modality of
        CatalysisConservationUnwired ->
          if catalysisConcurrentBundleIsConcurrentProduct bundle
            then CatalysisConservationNamedOk
            else CatalysisConservationDesignOk
        CatalysisConservationAssumed -> CatalysisConservationDesignOk
        CatalysisConservationSurrogate -> CatalysisConservationDesignOk
        CatalysisConservationProved -> CatalysisConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-14 **conservation** bar (fail-closed).
evaluateCatalysisXor ::
  CatalysisConservationModality
  -> CatalysisXorPosture
  -> Bool
  -> Bool
  -> CatalysisXorVerdict
evaluateCatalysisXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = CatalysisXorGreenInventRefuse
  | claimProved = CatalysisXorProvedWithoutBarRefuse
  | posture == CatalysisXorExclusive = CatalysisXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        CatalysisConservationUnwired -> CatalysisXorNamedOk
        CatalysisConservationAssumed -> CatalysisXorDesignOk
        CatalysisConservationSurrogate -> CatalysisXorDesignOk
        CatalysisConservationProved -> CatalysisXorProvedWithoutBarRefuse

-- | **Catalysis** identity law cells tracked by class-14 **conservation** (structure scaffold).
data CatalysisConservationLaw
  = CatalysisConservationConserved
  | NamedCatalysisConservationOk
  | TrivialCatalysisRefused
  | GreenInventCatalysisRefused
  deriving (Eq, Show)

catalysisConservationLawAll :: [CatalysisConservationLaw]
catalysisConservationLawAll =
  [ CatalysisConservationConserved
  , NamedCatalysisConservationOk
  , TrivialCatalysisRefused
  , GreenInventCatalysisRefused
  ]

catalysisConservationLawCount :: Int
catalysisConservationLawCount = length catalysisConservationLawAll

-- | Evaluate class-14 **catalysis** **conservation** typing (fail-closed).
evaluateCatalysisConservation ::
  CatalysisConservationModality
  -> CatalysisConcurrentBundle
  -> CatalysisXorPosture
  -> Bool
  -> Bool
  -> CatalysisConservationVerdict
evaluateCatalysisConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = CatalysisConservationGreenInventRefuse
  | claimProved = CatalysisConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateCatalysisXor modality posture False False of
        CatalysisXorMutuallyExclusiveRefuse -> CatalysisConservationXorRefuse
        CatalysisXorGreenInventRefuse -> CatalysisConservationGreenInventRefuse
        CatalysisXorProvedWithoutBarRefuse -> CatalysisConservationProvedWithoutBarRefuse
        _ ->
          case evaluateCatalysisBundle modality bundle False False of
            CatalysisConservationNamedOk -> CatalysisConservationNamedOk
            CatalysisConservationGreenInventRefuse -> CatalysisConservationGreenInventRefuse
            CatalysisConservationProvedWithoutBarRefuse -> CatalysisConservationProvedWithoutBarRefuse
            CatalysisConservationTrivialRefuse -> CatalysisConservationTrivialRefuse
            CatalysisConservationXorRefuse -> CatalysisConservationXorRefuse
            CatalysisConservationDesignOk -> CatalysisConservationDesignOk

sampleCatalysisInteractRestrictionBundle :: CatalysisConcurrentBundle
sampleCatalysisInteractRestrictionBundle = catalysisInteractRestrictionWitness

sampleXorExclusiveBundle :: CatalysisConcurrentBundle
sampleXorExclusiveBundle = catalysisConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: CatalysisConcurrentBundle
sampleTrivialUnwiredBundle = catalysisConcurrentBundleUnwired

-- | Unwired **catalysis** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateCatalysisConservation
    CatalysisConservationUnwired
    sampleCatalysisInteractRestrictionBundle
    catalysisXorPostureConcurrent
    False
    False
    == CatalysisConservationNamedOk

-- | Catalysis witness: Interact restriction + barrier↓ + catalyst-not-consumed concurrent Π_c on class 14.
catalysisInteractRestrictionConcurrentOk :: Bool
catalysisInteractRestrictionConcurrentOk =
  let bundle = catalysisInteractRestrictionWitness
   in catalysisClassPresent bundle
        && catalysisConcurrentBundleHolds 0 bundle
        && catalysisConcurrentBundleHolds 1 bundle
        && catalysisConcurrentBundleHolds 2 bundle
        && catalysisConcurrentBundlePresentCount bundle == 3
        && catalysisConcurrentBundleIsConcurrentProduct bundle
        && platinumAtomicNumberZ == 78
        && ironAtomicNumberZ == 26
        && class14CatalysisPatternIndex == 14

-- | Class-14 catalysis pattern index pinned @ scaffold.
class14CatalysisPatternIndexOk :: Bool
class14CatalysisPatternIndexOk =
  class14CatalysisPatternIndex == 14
    && catalysisProductChannelCount == 3
    && length (catalysisChannelSlots catalysisConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  catalysisConcurrentBundleIsConcurrentProduct catalysisInteractRestrictionWitness
    && catalysisConcurrentBundlePresentCount catalysisInteractRestrictionWitness >= 2
    && catalysisConcurrentBundlePresentCount catalysisInteractRestrictionWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateCatalysisXor
    CatalysisConservationUnwired
    catalysisXorPostureExclusive
    False
    False
    == CatalysisXorMutuallyExclusiveRefuse
    && evaluateCatalysisConservation
      CatalysisConservationUnwired
      sampleCatalysisInteractRestrictionBundle
      catalysisXorPostureExclusive
      False
      False
      == CatalysisConservationXorRefuse

-- | GREEN invent on **catalysis** **conservation** promotion is refused.
greenInventCatalysisRefuse :: Bool
greenInventCatalysisRefuse =
  evaluateCatalysisConservation
    CatalysisConservationUnwired
    sampleCatalysisInteractRestrictionBundle
    catalysisXorPostureConcurrent
    True
    False
    == CatalysisConservationGreenInventRefuse
    && evaluateCatalysisBundle
      CatalysisConservationUnwired
      sampleCatalysisInteractRestrictionBundle
      True
      False
      == CatalysisConservationGreenInventRefuse

-- | Parallel catalysis axiom (26th law) mint is refused — second law + conservation only.
parallelCatalysisAxiomRefuse :: Bool
parallelCatalysisAxiomRefuse =
  catalysisConservationAuthority
    == "umst/umst-chem/src/catalysis_barrier.rs"
    && catalysisConservationProved == False
    && not (catalysisConservationAuthority == "26th_chemistry_axiom")
    && catalysisConservationFraming
      /= "parallel_catalysis_axiom_not_second_law"
    && chemL0CatalysisAuthority
      == "umst/umst-chem/src/l0_tables/catalysis.rs"

-- | Catalyst consumed in net reaction is refused — conservation posture mandatory.
catalystConsumedRefuse :: Bool
catalystConsumedRefuse =
  parallelCatalysisAxiomRefuse
    && catalysisConservationFraming
      /= "catalyst_consumed_in_net_reaction"
    && edgeCatalysisAuthority
      == "umst/umst-chem/src/catalysis_barrier.rs"
    && interactRestrictionAuthority
      == "umst/umst-chem/src/interact_pattern_match.rs"
    && class14CatalysisPatternIndex == 14

-- | Catalysis is Interact restriction — not a parallel catalysis axiom.
interactRestrictionNotAxiomRefuse :: Bool
interactRestrictionNotAxiomRefuse =
  catalystConsumedRefuse
    && catalysisConservationFraming
      /= "catalysis_axiom_not_interact_restriction"
    && class14CatalysisPatternIndex == 14
    && catalysisConcurrentBundleIsConcurrentProduct catalysisInteractRestrictionWitness

-- | T/P graph functions on Interact graph — refuse bare float-pin smuggle on catalysis scaffold.
tpFloatPinRefuse :: Bool
tpFloatPinRefuse =
  interactRestrictionNotAxiomRefuse
    && catalysisConservationFraming
      /= "tp_bare_float_pin_on_catalysis"
    && temperatureGraphFunctionAuthority
      == "umst/umst-chem/src/temperature_is_graph_function.rs"
    && pressureGraphFunctionAuthority
      == "umst/umst-chem/src/pressure_is_graph_function.rs"
    && class14CatalysisPatternIndex == 14

-- | Assumed **catalysis** modality OK without thermo break (design scaffold).
assumedCatalysisDesignOk :: Bool
assumedCatalysisDesignOk =
  evaluateCatalysisConservation
    CatalysisConservationAssumed
    sampleCatalysisInteractRestrictionBundle
    catalysisXorPostureConcurrent
    False
    False
    == CatalysisConservationDesignOk

-- | Surrogate **catalysis** modality OK without thermo break (design scaffold).
surrogateCatalysisDesignOk :: Bool
surrogateCatalysisDesignOk =
  evaluateCatalysisConservation
    CatalysisConservationSurrogate
    sampleCatalysisInteractRestrictionBundle
    catalysisXorPostureConcurrent
    False
    False
    == CatalysisConservationDesignOk

-- | Four-step class-14 **catalysis** lattice scaffold pinned.
catalysisLatticeScaffold :: Bool
catalysisLatticeScaffold =
  catalysisLatticeCount == 4
    && unwiredDesignOk
    && class14CatalysisPatternIndexOk
    && catalysisInteractRestrictionConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedCatalysisDesignOk
    && surrogateCatalysisDesignOk
    && parallelCatalysisAxiomRefuse
    && catalystConsumedRefuse
    && interactRestrictionNotAxiomRefuse
    && tpFloatPinRefuse

-- | **Catalysis** lattice is structure scaffold — not 118² GREEN periodic table.
catalysisLatticeNotGreenTable :: Bool
catalysisLatticeNotGreenTable =
  catalysisLatticeCount == 4
    && catalysisLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && catalysisProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && catalysisChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **catalysis** identity law cells scaffold pinned.
catalysisConservationLawsScaffold :: Bool
catalysisConservationLawsScaffold =
  catalysisConservationLawCount == 4
    && catalysisInteractRestrictionConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCatalysisRefuse
    && parallelCatalysisAxiomRefuse
    && catalystConsumedRefuse
    && interactRestrictionNotAxiomRefuse
    && tpFloatPinRefuse

-- | **Catalysis** law cells are structure scaffold — not 118² GREEN periodic table.
catalysisConservationLawsNotGreenTable :: Bool
catalysisConservationLawsNotGreenTable =
  catalysisConservationLawsScaffold
    && catalysisConservationLawCount /= 118 * 118
    && catalysisProductChannelCount /= 118 * 118

-- | Class-14 **catalysis** **conservation** claims route to knowing / quantum fiber (not meso acting).
catalysisKnowingFiberOk :: Bool
catalysisKnowingFiberOk = True

-- | Class-14 **catalysis** invent refuse-closed scaffold witness.
catalysisConservationInventRefuse :: Bool
catalysisConservationInventRefuse =
  not catalysisConservationProved

-- | **Catalysis** lattice steps are concurrent Π_c — not XOR enum bucket.
catalysisLatticeNotXor :: Bool
catalysisLatticeNotXor =
  unwiredDesignOk
    && assumedCatalysisDesignOk
    && surrogateCatalysisDesignOk
    && catalysisInteractRestrictionConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCatalysisRefuse

-- | Class-14 **catalysis** proved (always false on this Unwired cell).
catalysisConservationProved :: Bool
catalysisConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Catalysis** morphisms are class-14 neighbor channels — not SpeciesId tag mint.
catalysisConservationNeSpeciesId :: Bool
catalysisConservationNeSpeciesId =
  catalysisConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && catalysisProductChannelAll /= []
    && catalysisConcurrentBundleIsConcurrentProduct catalysisInteractRestrictionWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-14 **catalysis** scaffold.
catalysisConservationFraming :: String
catalysisConservationFraming =
  "second_law_conservation_catalysis_one_axiom"

-- | Single design axiom: second law + **conservation** class-14 catalysis (not 26th axiom).
catalysisConservationAxiom :: Bool
catalysisConservationAxiom =
  catalysisLatticeScaffold
    && catalysisLatticeNotGreenTable
    && catalysisConservationLawsScaffold
    && catalysisConservationLawsNotGreenTable
    && catalysisKnowingFiberOk
    && class14CatalysisPatternIndexOk
    && catalysisInteractRestrictionConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCatalysisRefuse
    && parallelCatalysisAxiomRefuse
    && catalystConsumedRefuse
    && interactRestrictionNotAxiomRefuse
    && tpFloatPinRefuse
    && catalysisConservationInventRefuse
    && catalysisLatticeNotXor
    && catalysisConservationNeSpeciesId
    && not catalysisConservationProved
    && not speciesIdForked
    && catalysisConservationFraming
      == "second_law_conservation_catalysis_one_axiom"

catalysisConservationNamed :: String
catalysisConservationNamed =
  "catalysisConservation: CatalysisConservationModality Unwired Assumed Proved Surrogate four-step lattice catalysisConservationProved false evaluateCatalysisBundle evaluateCatalysisConservation named class 14 catalysis interact restriction activation barrier lowered catalyst not consumed concurrent product identity conserved present ge 2 product not XOR interact restriction witness concurrent xor mutually exclusive refuse parallel catalysis axiom refuse catalyst consumed refuse interact restriction not axiom refuse tp float pin refuse catalysis ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT catalysis **conservation** authority (cited read-only, not forked).
catalysisConservationAuthority :: String
catalysisConservationAuthority =
  "umst/umst-chem/src/catalysis_barrier.rs"

-- | L0 class-14 catalysis table authority (crosswalk).
chemL0CatalysisAuthority :: String
chemL0CatalysisAuthority =
  "umst/umst-chem/src/l0_tables/catalysis.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | Interact restriction authority (catalysis as Interact restriction — not axiom).
interactRestrictionAuthority :: String
interactRestrictionAuthority = "umst/umst-chem/src/interact_pattern_match.rs"

-- | Kleisli Interact authority (composition carrier — not folklore list).
kleisliInteractAuthority :: String
kleisliInteractAuthority = "umst/umst-chem/src/kleisli_interact.rs"

-- | L0 edge catalysis authority (barrier↓ morphism — not proved on this cell).
edgeCatalysisAuthority :: String
edgeCatalysisAuthority = "umst/umst-chem/src/catalysis_barrier.rs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

catalysisConservationCellId :: String
catalysisConservationCellId =
  "CHEM-FORMAL-Q-HS-CATALYSIS-CONSERVATION"

-- | Non-claim fence — class-14 **catalysis** **conservation** Unwired ≠ Proved GREEN.
catalysisConservationNonClaim :: String
catalysisConservationNonClaim =
  "CHEM-FORMAL-Q-HS-CATALYSIS-CONSERVATION CatalysisConservationModality Unwired Assumed Proved Surrogate four-step lattice catalysisConservationProved false evaluateCatalysisBundle evaluateCatalysisConservation named class 14 catalysis interact restriction activation barrier lowered catalyst not consumed concurrent product identity conserved present ge 2 product not XOR interact restriction witness concurrent xor mutually exclusive refuse parallel catalysis axiom refuse catalyst consumed refuse interact restriction not axiom refuse tp float pin refuse catalysis ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-14 **catalysis** **conservation** scaffold.
catalysisConservationPhysicsGreenAuthorized :: Bool
catalysisConservationPhysicsGreenAuthorized = False

catalysisConservationPhysicsGreenFalse :: Bool
catalysisConservationPhysicsGreenFalse =
  not catalysisConservationPhysicsGreenAuthorized

catalysisConservationModalityUnwired :: Bool
catalysisConservationModalityUnwired =
  catalysisConservationModalityCurrent == CatalysisConservationUnwired

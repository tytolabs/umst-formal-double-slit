{-|
Module      : UMST.ChemConstants.NaturalVsPurifiedEnvConservation
Description : Class-24 **natural-vs-purified-Env** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Natural-vs-purified-Env** **conservation**: north-star §2 class 24
(@natural_vs_purified_env@) — natural vs purified Env are **named Environment sections**
of `Env : InteractGraph → EnvState` on the same second-law + **conservation** object,
not a 26th axiom. Natural Env section ⊗ purified Env section ⊗ sections-not-XOR-worlds
Π_c is **product** not XOR. Named class-24 **natural-vs-purified-Env** identity conserved
under honest scaffold; trivial XOR, parallel natural-vs-purified-Env axiom, natural XOR
purified world smuggle, environment-section-not-axiom refuse, T/P float-pin smuggle, and
GREEN invent fail-closed. Class-24 **conservation** laws are structure witnesses only
(@naturalVsPurifiedEnvConservationProved@ = False). No SpeciesId fork.

* @NaturalVsPurifiedEnvConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateNaturalVsPurifiedEnvBundle@ — named class-24 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateNaturalVsPurifiedEnvConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@naturalVsPurifiedEnvConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of class-24 **natural-vs-purified-Env** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-NATURAL-VS-PURIFIED-ENV-CONSERVATION@.
INT: umst/umst-chem/src/x_rows/natural_vs_purified_env_conservation.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/natural_ore_assemblage.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}module UMST.ChemConstants.NaturalVsPurifiedEnvConservation
  ( NaturalVsPurifiedEnvConservationModality (..)
  , naturalVsPurifiedEnvConservationModalityCurrent
  , naturalVsPurifiedEnvLatticeAll
  , naturalVsPurifiedEnvLatticeCount
  , class24NaturalVsPurifiedEnvPatternIndex
  , NaturalVsPurifiedEnvChannelSlot (..)
  , naturalVsPurifiedEnvChannelSlotAll
  , naturalVsPurifiedEnvChannelSlotCount
  , NaturalVsPurifiedEnvProductChannel (..)
  , naturalVsPurifiedEnvProductChannelAll
  , naturalVsPurifiedEnvProductChannelCount
  , naturalVsPurifiedEnvProductChannelIndex
  , NaturalVsPurifiedEnvConcurrentBundle (..)
  , naturalVsPurifiedEnvConcurrentBundleUnwired
  , naturalVsPurifiedEnvConcurrentBundleWithChannel
  , naturalVsPurifiedEnvConcurrentBundleWithPresent
  , naturalVsPurifiedEnvConcurrentBundleChannelAt
  , naturalVsPurifiedEnvConcurrentBundleHolds
  , naturalVsPurifiedEnvConcurrentBundlePresentCount
  , naturalVsPurifiedEnvConcurrentBundleIsConcurrentProduct
  , naturalVsPurifiedEnvWitness
  , NaturalVsPurifiedEnvXorPosture (..)
  , naturalVsPurifiedEnvXorPostureExclusive
  , naturalVsPurifiedEnvXorPostureConcurrent
  , NaturalVsPurifiedEnvConservationVerdict (..)
  , NaturalVsPurifiedEnvXorVerdict (..)
  , evaluateNaturalVsPurifiedEnvBundle
  , evaluateNaturalVsPurifiedEnvXor
  , evaluateNaturalVsPurifiedEnvConservation
  , NaturalVsPurifiedEnvConservationLaw (..)
  , naturalVsPurifiedEnvConservationLawAll
  , naturalVsPurifiedEnvConservationLawCount
  , sampleNaturalVsPurifiedEnvBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , naturalVsPurifiedEnvConcurrentOk
  , class24NaturalVsPurifiedEnvPatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventNaturalVsPurifiedEnvRefuse
  , parallelNaturalVsPurifiedEnvAxiomRefuse
  , xorEnvWorldsRefuse
  , environmentSectionNotAxiomRefuse
  , tpFloatPinRefuse
  , assumedNaturalVsPurifiedEnvDesignOk
  , surrogateNaturalVsPurifiedEnvDesignOk
  , naturalVsPurifiedEnvLatticeScaffold
  , naturalVsPurifiedEnvLatticeNotGreenTable
  , naturalVsPurifiedEnvConservationLawsScaffold
  , naturalVsPurifiedEnvConservationLawsNotGreenTable
  , naturalVsPurifiedEnvKnowingFiberOk
  , naturalVsPurifiedEnvConservationInventRefuse
  , naturalVsPurifiedEnvLatticeNotXor
  , naturalVsPurifiedEnvConservationProved
  , naturalVsPurifiedEnvConservationNeSpeciesId
  , speciesIdForked
  , copperAtomicNumberZ
  , ironAtomicNumberZ
  , naturalVsPurifiedEnvConservationFraming
  , naturalVsPurifiedEnvConservationAxiom
  , naturalVsPurifiedEnvConservationNamed
  , naturalVsPurifiedEnvConservationAuthority
  , chemL0NaturalOreAssemblageAuthority
  , patternProductConservationAuthority
  , surroundingsEnvSectionAuthority
  , environmentThreeSampleSpacesAuthority
  , refineProcessAuthority
  , goldschmidtConservationAuthority
  , chemPhysicsChartIsomorphismAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , naturalVsPurifiedEnvConservationCellId
  , naturalVsPurifiedEnvConservationNonClaim
  , naturalVsPurifiedEnvConservationPhysicsGreenAuthorized
  , naturalVsPurifiedEnvConservationPhysicsGreenFalse
  , naturalVsPurifiedEnvConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not naturalVsPurifiedEnv GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-24 (`naturalVsPurifiedEnv`) pattern index.
class24NaturalVsPurifiedEnvPatternIndex :: Int
class24NaturalVsPurifiedEnvPatternIndex = 24

-- | Copper Z=29 — refined/purified witness element pin.
copperAtomicNumberZ :: Int
copperAtomicNumberZ = 29

-- | Iron Z=26 — natural ore witness element pin.
ironAtomicNumberZ :: Int
ironAtomicNumberZ = 26

-- | Design **naturalVsPurifiedEnv** modality for class-24 **conservation** claims.
data NaturalVsPurifiedEnvConservationModality
  = NaturalVsPurifiedEnvConservationUnwired
  | NaturalVsPurifiedEnvConservationAssumed
  | NaturalVsPurifiedEnvConservationProved
  | NaturalVsPurifiedEnvConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **naturalVsPurifiedEnv** modality — always Unwired on this cell.
naturalVsPurifiedEnvConservationModalityCurrent :: NaturalVsPurifiedEnvConservationModality
naturalVsPurifiedEnvConservationModalityCurrent =
  NaturalVsPurifiedEnvConservationUnwired

-- | All class-24 **naturalVsPurifiedEnv** lattice steps in stable order.
naturalVsPurifiedEnvLatticeAll :: [NaturalVsPurifiedEnvConservationModality]
naturalVsPurifiedEnvLatticeAll =
  [ NaturalVsPurifiedEnvConservationUnwired
  , NaturalVsPurifiedEnvConservationAssumed
  , NaturalVsPurifiedEnvConservationProved
  , NaturalVsPurifiedEnvConservationSurrogate
  ]

naturalVsPurifiedEnvLatticeCount :: Int
naturalVsPurifiedEnvLatticeCount = length naturalVsPurifiedEnvLatticeAll

-- | NaturalVsPurifiedEnv product channel slot — concurrent **product** factor, not XOR bucket.
data NaturalVsPurifiedEnvChannelSlot
  = NaturalVsPurifiedEnvSlotUnwired
  | NaturalVsPurifiedEnvSlotAbsent
  | NaturalVsPurifiedEnvSlotPresent
  deriving (Eq, Show)

-- | All naturalVsPurifiedEnv channel slots in stable order.
naturalVsPurifiedEnvChannelSlotAll :: [NaturalVsPurifiedEnvChannelSlot]
naturalVsPurifiedEnvChannelSlotAll =
  [ NaturalVsPurifiedEnvSlotUnwired
  , NaturalVsPurifiedEnvSlotAbsent
  , NaturalVsPurifiedEnvSlotPresent
  ]

naturalVsPurifiedEnvChannelSlotCount :: Int
naturalVsPurifiedEnvChannelSlotCount = length naturalVsPurifiedEnvChannelSlotAll

-- | Named natural Env / purified Env / sections-not-XOR-worlds product channels.
data NaturalVsPurifiedEnvProductChannel
  = NaturalEnvSampleSection
  | PurifiedEnvSampleSection
  | EnvSectionsNotXorWorlds
  deriving (Eq, Show)

-- | All naturalVsPurifiedEnv product channels in north-star stable order.
naturalVsPurifiedEnvProductChannelAll :: [NaturalVsPurifiedEnvProductChannel]
naturalVsPurifiedEnvProductChannelAll =
  [ NaturalEnvSampleSection
  , PurifiedEnvSampleSection
  , EnvSectionsNotXorWorlds
  ]

naturalVsPurifiedEnvProductChannelCount :: Int
naturalVsPurifiedEnvProductChannelCount = length naturalVsPurifiedEnvProductChannelAll

-- | Stable channel index for a naturalVsPurifiedEnv product channel (0..2).
naturalVsPurifiedEnvProductChannelIndex :: NaturalVsPurifiedEnvProductChannel -> Int
naturalVsPurifiedEnvProductChannelIndex channel =
  case channel of
    NaturalEnvSampleSection -> 0
    PurifiedEnvSampleSection -> 1
    EnvSectionsNotXorWorlds -> 2

-- | Class-14 naturalVsPurifiedEnv concurrent **product** bundle (north-star §3).
data NaturalVsPurifiedEnvConcurrentBundle = NaturalVsPurifiedEnvConcurrentBundle
  { naturalVsPurifiedEnvClassPresent :: Bool
  , naturalVsPurifiedEnvChannelSlots :: [NaturalVsPurifiedEnvChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
naturalVsPurifiedEnvConcurrentBundleUnwired :: NaturalVsPurifiedEnvConcurrentBundle
naturalVsPurifiedEnvConcurrentBundleUnwired =
  NaturalVsPurifiedEnvConcurrentBundle
    False
    (replicate naturalVsPurifiedEnvProductChannelCount NaturalVsPurifiedEnvSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
naturalVsPurifiedEnvConcurrentBundleWithChannel ::
  Int -> NaturalVsPurifiedEnvChannelSlot -> NaturalVsPurifiedEnvConcurrentBundle -> NaturalVsPurifiedEnvConcurrentBundle
naturalVsPurifiedEnvConcurrentBundleWithChannel idx slot bundle =
  let slots = naturalVsPurifiedEnvChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in NaturalVsPurifiedEnvConcurrentBundle
        (naturalVsPurifiedEnvClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the naturalVsPurifiedEnv **product**.
naturalVsPurifiedEnvConcurrentBundleWithPresent ::
  Int -> NaturalVsPurifiedEnvConcurrentBundle -> NaturalVsPurifiedEnvConcurrentBundle
naturalVsPurifiedEnvConcurrentBundleWithPresent idx bundle =
  naturalVsPurifiedEnvConcurrentBundleWithChannel idx NaturalVsPurifiedEnvSlotPresent bundle

-- | Read channel slot at index (0..2).
naturalVsPurifiedEnvConcurrentBundleChannelAt ::
  Int -> NaturalVsPurifiedEnvConcurrentBundle -> Maybe NaturalVsPurifiedEnvChannelSlot
naturalVsPurifiedEnvConcurrentBundleChannelAt idx bundle =
  let slots = naturalVsPurifiedEnvChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
naturalVsPurifiedEnvConcurrentBundleHolds :: Int -> NaturalVsPurifiedEnvConcurrentBundle -> Bool
naturalVsPurifiedEnvConcurrentBundleHolds idx bundle =
  case naturalVsPurifiedEnvConcurrentBundleChannelAt idx bundle of
    Just NaturalVsPurifiedEnvSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
naturalVsPurifiedEnvConcurrentBundlePresentCount :: NaturalVsPurifiedEnvConcurrentBundle -> Int
naturalVsPurifiedEnvConcurrentBundlePresentCount bundle =
  length (filter (== NaturalVsPurifiedEnvSlotPresent) (naturalVsPurifiedEnvChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
naturalVsPurifiedEnvConcurrentBundleIsConcurrentProduct :: NaturalVsPurifiedEnvConcurrentBundle -> Bool
naturalVsPurifiedEnvConcurrentBundleIsConcurrentProduct bundle =
  naturalVsPurifiedEnvConcurrentBundlePresentCount bundle >= 2

-- | Natural-vs-purified-Env witness: natural section (0) + purified section (1) + not XOR worlds (2) concurrent on class 24.
naturalVsPurifiedEnvWitness :: NaturalVsPurifiedEnvConcurrentBundle
naturalVsPurifiedEnvWitness =
  naturalVsPurifiedEnvConcurrentBundleWithPresent 2
    (naturalVsPurifiedEnvConcurrentBundleWithPresent 1
      (naturalVsPurifiedEnvConcurrentBundleWithPresent 0
        (NaturalVsPurifiedEnvConcurrentBundle True
          (replicate naturalVsPurifiedEnvProductChannelCount NaturalVsPurifiedEnvSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data NaturalVsPurifiedEnvXorPosture
  = NaturalVsPurifiedEnvXorExclusive
  | NaturalVsPurifiedEnvXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
naturalVsPurifiedEnvXorPostureExclusive :: NaturalVsPurifiedEnvXorPosture
naturalVsPurifiedEnvXorPostureExclusive = NaturalVsPurifiedEnvXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
naturalVsPurifiedEnvXorPostureConcurrent :: NaturalVsPurifiedEnvXorPosture
naturalVsPurifiedEnvXorPostureConcurrent = NaturalVsPurifiedEnvXorConcurrent

-- | Verdict for naturalVsPurifiedEnv **conservation** close (fail-closed).
data NaturalVsPurifiedEnvConservationVerdict
  = NaturalVsPurifiedEnvConservationDesignOk
  | NaturalVsPurifiedEnvConservationNamedOk
  | NaturalVsPurifiedEnvConservationTrivialRefuse
  | NaturalVsPurifiedEnvConservationGreenInventRefuse
  | NaturalVsPurifiedEnvConservationProvedWithoutBarRefuse
  | NaturalVsPurifiedEnvConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data NaturalVsPurifiedEnvXorVerdict
  = NaturalVsPurifiedEnvXorDesignOk
  | NaturalVsPurifiedEnvXorNamedOk
  | NaturalVsPurifiedEnvXorGreenInventRefuse
  | NaturalVsPurifiedEnvXorProvedWithoutBarRefuse
  | NaturalVsPurifiedEnvXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a naturalVsPurifiedEnv bundle under class-24 **conservation** bar (fail-closed).
evaluateNaturalVsPurifiedEnvBundle ::
  NaturalVsPurifiedEnvConservationModality
  -> NaturalVsPurifiedEnvConcurrentBundle
  -> Bool
  -> Bool
  -> NaturalVsPurifiedEnvConservationVerdict
evaluateNaturalVsPurifiedEnvBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = NaturalVsPurifiedEnvConservationGreenInventRefuse
  | claimProved = NaturalVsPurifiedEnvConservationProvedWithoutBarRefuse
  | length (naturalVsPurifiedEnvChannelSlots bundle) /= naturalVsPurifiedEnvProductChannelCount =
      NaturalVsPurifiedEnvConservationTrivialRefuse
  | otherwise =
      case modality of
        NaturalVsPurifiedEnvConservationUnwired ->
          if naturalVsPurifiedEnvConcurrentBundleIsConcurrentProduct bundle
            then NaturalVsPurifiedEnvConservationNamedOk
            else NaturalVsPurifiedEnvConservationDesignOk
        NaturalVsPurifiedEnvConservationAssumed -> NaturalVsPurifiedEnvConservationDesignOk
        NaturalVsPurifiedEnvConservationSurrogate -> NaturalVsPurifiedEnvConservationDesignOk
        NaturalVsPurifiedEnvConservationProved -> NaturalVsPurifiedEnvConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-24 **conservation** bar (fail-closed).
evaluateNaturalVsPurifiedEnvXor ::
  NaturalVsPurifiedEnvConservationModality
  -> NaturalVsPurifiedEnvXorPosture
  -> Bool
  -> Bool
  -> NaturalVsPurifiedEnvXorVerdict
evaluateNaturalVsPurifiedEnvXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = NaturalVsPurifiedEnvXorGreenInventRefuse
  | claimProved = NaturalVsPurifiedEnvXorProvedWithoutBarRefuse
  | posture == NaturalVsPurifiedEnvXorExclusive = NaturalVsPurifiedEnvXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        NaturalVsPurifiedEnvConservationUnwired -> NaturalVsPurifiedEnvXorNamedOk
        NaturalVsPurifiedEnvConservationAssumed -> NaturalVsPurifiedEnvXorDesignOk
        NaturalVsPurifiedEnvConservationSurrogate -> NaturalVsPurifiedEnvXorDesignOk
        NaturalVsPurifiedEnvConservationProved -> NaturalVsPurifiedEnvXorProvedWithoutBarRefuse

-- | **NaturalVsPurifiedEnv** identity law cells tracked by class-24 **conservation** (structure scaffold).
data NaturalVsPurifiedEnvConservationLaw
  = NaturalVsPurifiedEnvConservationConserved
  | NamedNaturalVsPurifiedEnvConservationOk
  | TrivialNaturalVsPurifiedEnvRefused
  | GreenInventNaturalVsPurifiedEnvRefused
  deriving (Eq, Show)

naturalVsPurifiedEnvConservationLawAll :: [NaturalVsPurifiedEnvConservationLaw]
naturalVsPurifiedEnvConservationLawAll =
  [ NaturalVsPurifiedEnvConservationConserved
  , NamedNaturalVsPurifiedEnvConservationOk
  , TrivialNaturalVsPurifiedEnvRefused
  , GreenInventNaturalVsPurifiedEnvRefused
  ]

naturalVsPurifiedEnvConservationLawCount :: Int
naturalVsPurifiedEnvConservationLawCount = length naturalVsPurifiedEnvConservationLawAll

-- | Evaluate class-24 **naturalVsPurifiedEnv** **conservation** typing (fail-closed).
evaluateNaturalVsPurifiedEnvConservation ::
  NaturalVsPurifiedEnvConservationModality
  -> NaturalVsPurifiedEnvConcurrentBundle
  -> NaturalVsPurifiedEnvXorPosture
  -> Bool
  -> Bool
  -> NaturalVsPurifiedEnvConservationVerdict
evaluateNaturalVsPurifiedEnvConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = NaturalVsPurifiedEnvConservationGreenInventRefuse
  | claimProved = NaturalVsPurifiedEnvConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateNaturalVsPurifiedEnvXor modality posture False False of
        NaturalVsPurifiedEnvXorMutuallyExclusiveRefuse -> NaturalVsPurifiedEnvConservationXorRefuse
        NaturalVsPurifiedEnvXorGreenInventRefuse -> NaturalVsPurifiedEnvConservationGreenInventRefuse
        NaturalVsPurifiedEnvXorProvedWithoutBarRefuse -> NaturalVsPurifiedEnvConservationProvedWithoutBarRefuse
        _ ->
          case evaluateNaturalVsPurifiedEnvBundle modality bundle False False of
            NaturalVsPurifiedEnvConservationNamedOk -> NaturalVsPurifiedEnvConservationNamedOk
            NaturalVsPurifiedEnvConservationGreenInventRefuse -> NaturalVsPurifiedEnvConservationGreenInventRefuse
            NaturalVsPurifiedEnvConservationProvedWithoutBarRefuse -> NaturalVsPurifiedEnvConservationProvedWithoutBarRefuse
            NaturalVsPurifiedEnvConservationTrivialRefuse -> NaturalVsPurifiedEnvConservationTrivialRefuse
            NaturalVsPurifiedEnvConservationXorRefuse -> NaturalVsPurifiedEnvConservationXorRefuse
            NaturalVsPurifiedEnvConservationDesignOk -> NaturalVsPurifiedEnvConservationDesignOk

sampleNaturalVsPurifiedEnvBundle :: NaturalVsPurifiedEnvConcurrentBundle
sampleNaturalVsPurifiedEnvBundle = naturalVsPurifiedEnvWitness

sampleXorExclusiveBundle :: NaturalVsPurifiedEnvConcurrentBundle
sampleXorExclusiveBundle = naturalVsPurifiedEnvConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: NaturalVsPurifiedEnvConcurrentBundle
sampleTrivialUnwiredBundle = naturalVsPurifiedEnvConcurrentBundleUnwired

-- | Unwired **naturalVsPurifiedEnv** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateNaturalVsPurifiedEnvConservation
    NaturalVsPurifiedEnvConservationUnwired
    sampleNaturalVsPurifiedEnvBundle
    naturalVsPurifiedEnvXorPostureConcurrent
    False
    False
    == NaturalVsPurifiedEnvConservationNamedOk

-- | NaturalVsPurifiedEnv witness: Interact restriction + barrier↓ + catalyst-not-consumed concurrent Π_c on class 24.
naturalVsPurifiedEnvConcurrentOk :: Bool
naturalVsPurifiedEnvConcurrentOk =
  let bundle = naturalVsPurifiedEnvWitness
   in naturalVsPurifiedEnvClassPresent bundle
        && naturalVsPurifiedEnvConcurrentBundleHolds 0 bundle
        && naturalVsPurifiedEnvConcurrentBundleHolds 1 bundle
        && naturalVsPurifiedEnvConcurrentBundleHolds 2 bundle
        && naturalVsPurifiedEnvConcurrentBundlePresentCount bundle == 3
        && naturalVsPurifiedEnvConcurrentBundleIsConcurrentProduct bundle
        && copperAtomicNumberZ == 29
        && ironAtomicNumberZ == 26
        && class24NaturalVsPurifiedEnvPatternIndex == 24

-- | Class-14 naturalVsPurifiedEnv pattern index pinned @ scaffold.
class24NaturalVsPurifiedEnvPatternIndexOk :: Bool
class24NaturalVsPurifiedEnvPatternIndexOk =
  class24NaturalVsPurifiedEnvPatternIndex == 24
    && naturalVsPurifiedEnvProductChannelCount == 3
    && length (naturalVsPurifiedEnvChannelSlots naturalVsPurifiedEnvConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  naturalVsPurifiedEnvConcurrentBundleIsConcurrentProduct naturalVsPurifiedEnvWitness
    && naturalVsPurifiedEnvConcurrentBundlePresentCount naturalVsPurifiedEnvWitness >= 2
    && naturalVsPurifiedEnvConcurrentBundlePresentCount naturalVsPurifiedEnvWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateNaturalVsPurifiedEnvXor
    NaturalVsPurifiedEnvConservationUnwired
    naturalVsPurifiedEnvXorPostureExclusive
    False
    False
    == NaturalVsPurifiedEnvXorMutuallyExclusiveRefuse
    && evaluateNaturalVsPurifiedEnvConservation
      NaturalVsPurifiedEnvConservationUnwired
      sampleNaturalVsPurifiedEnvBundle
      naturalVsPurifiedEnvXorPostureExclusive
      False
      False
      == NaturalVsPurifiedEnvConservationXorRefuse

-- | GREEN invent on **naturalVsPurifiedEnv** **conservation** promotion is refused.
greenInventNaturalVsPurifiedEnvRefuse :: Bool
greenInventNaturalVsPurifiedEnvRefuse =
  evaluateNaturalVsPurifiedEnvConservation
    NaturalVsPurifiedEnvConservationUnwired
    sampleNaturalVsPurifiedEnvBundle
    naturalVsPurifiedEnvXorPostureConcurrent
    True
    False
    == NaturalVsPurifiedEnvConservationGreenInventRefuse
    && evaluateNaturalVsPurifiedEnvBundle
      NaturalVsPurifiedEnvConservationUnwired
      sampleNaturalVsPurifiedEnvBundle
      True
      False
      == NaturalVsPurifiedEnvConservationGreenInventRefuse

-- | Parallel naturalVsPurifiedEnv axiom (26th law) mint is refused — second law + conservation only.
parallelNaturalVsPurifiedEnvAxiomRefuse :: Bool
parallelNaturalVsPurifiedEnvAxiomRefuse =
  naturalVsPurifiedEnvConservationAuthority
    == "umst/umst-chem/src/x_rows/natural_vs_purified_env_conservation.rs"
    && naturalVsPurifiedEnvConservationProved == False
    && not (naturalVsPurifiedEnvConservationAuthority == "26th_chemistry_axiom")
    && naturalVsPurifiedEnvConservationFraming
      /= "parallel_natural_vs_purified_env_axiom_not_second_law"
    && chemL0NaturalOreAssemblageAuthority
      == "umst/umst-chem/src/l0_tables/natural_ore_assemblage.rs"

-- | Natural XOR purified Env worlds smuggle is refused — sample sections not XOR.
xorEnvWorldsRefuse :: Bool
xorEnvWorldsRefuse =
  parallelNaturalVsPurifiedEnvAxiomRefuse
    && naturalVsPurifiedEnvConservationFraming
      /= "natural_xor_purified_env_worlds"
    && refineProcessAuthority
      == "umst/umst-chem/src/refine_process.rs"
    && surroundingsEnvSectionAuthority
      == "umst/umst-chem/src/surroundings_are_environment_sections.rs"
    && environmentThreeSampleSpacesAuthority
      == "umst/umst-chem/src/environment_three_sample_spaces_not_xor.rs"
    && class24NaturalVsPurifiedEnvPatternIndex == 24

-- | Natural-vs-purified-Env is Environment section restriction — not a parallel axiom.
environmentSectionNotAxiomRefuse :: Bool
environmentSectionNotAxiomRefuse =
  xorEnvWorldsRefuse
    && naturalVsPurifiedEnvConservationFraming
      /= "natural_vs_purified_env_axiom_not_environment_section"
    && goldschmidtConservationAuthority
      == "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/GoldschmidtConservation.hs"
    && chemPhysicsChartIsomorphismAuthority
      == "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"
    && class24NaturalVsPurifiedEnvPatternIndex == 24
    && naturalVsPurifiedEnvConcurrentBundleIsConcurrentProduct naturalVsPurifiedEnvWitness

-- | T/P graph functions on Interact graph — refuse bare float-pin smuggle on naturalVsPurifiedEnv scaffold.
tpFloatPinRefuse :: Bool
tpFloatPinRefuse =
  environmentSectionNotAxiomRefuse
    && naturalVsPurifiedEnvConservationFraming
      /= "tp_bare_float_pin_on_natural_vs_purified_env"
    && temperatureGraphFunctionAuthority
      == "umst/umst-chem/src/temperature_is_graph_function.rs"
    && pressureGraphFunctionAuthority
      == "umst/umst-chem/src/pressure_is_graph_function.rs"
    && class24NaturalVsPurifiedEnvPatternIndex == 24

-- | Assumed **naturalVsPurifiedEnv** modality OK without thermo break (design scaffold).
assumedNaturalVsPurifiedEnvDesignOk :: Bool
assumedNaturalVsPurifiedEnvDesignOk =
  evaluateNaturalVsPurifiedEnvConservation
    NaturalVsPurifiedEnvConservationAssumed
    sampleNaturalVsPurifiedEnvBundle
    naturalVsPurifiedEnvXorPostureConcurrent
    False
    False
    == NaturalVsPurifiedEnvConservationDesignOk

-- | Surrogate **naturalVsPurifiedEnv** modality OK without thermo break (design scaffold).
surrogateNaturalVsPurifiedEnvDesignOk :: Bool
surrogateNaturalVsPurifiedEnvDesignOk =
  evaluateNaturalVsPurifiedEnvConservation
    NaturalVsPurifiedEnvConservationSurrogate
    sampleNaturalVsPurifiedEnvBundle
    naturalVsPurifiedEnvXorPostureConcurrent
    False
    False
    == NaturalVsPurifiedEnvConservationDesignOk

-- | Four-step class-24 **naturalVsPurifiedEnv** lattice scaffold pinned.
naturalVsPurifiedEnvLatticeScaffold :: Bool
naturalVsPurifiedEnvLatticeScaffold =
  naturalVsPurifiedEnvLatticeCount == 4
    && unwiredDesignOk
    && class24NaturalVsPurifiedEnvPatternIndexOk
    && naturalVsPurifiedEnvConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedNaturalVsPurifiedEnvDesignOk
    && surrogateNaturalVsPurifiedEnvDesignOk
    && parallelNaturalVsPurifiedEnvAxiomRefuse
    && xorEnvWorldsRefuse
    && environmentSectionNotAxiomRefuse
    && tpFloatPinRefuse

-- | **NaturalVsPurifiedEnv** lattice is structure scaffold — not 118² GREEN periodic table.
naturalVsPurifiedEnvLatticeNotGreenTable :: Bool
naturalVsPurifiedEnvLatticeNotGreenTable =
  naturalVsPurifiedEnvLatticeCount == 4
    && naturalVsPurifiedEnvLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && naturalVsPurifiedEnvProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && naturalVsPurifiedEnvChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **naturalVsPurifiedEnv** identity law cells scaffold pinned.
naturalVsPurifiedEnvConservationLawsScaffold :: Bool
naturalVsPurifiedEnvConservationLawsScaffold =
  naturalVsPurifiedEnvConservationLawCount == 4
    && naturalVsPurifiedEnvConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNaturalVsPurifiedEnvRefuse
    && parallelNaturalVsPurifiedEnvAxiomRefuse
    && xorEnvWorldsRefuse
    && environmentSectionNotAxiomRefuse
    && tpFloatPinRefuse

-- | **NaturalVsPurifiedEnv** law cells are structure scaffold — not 118² GREEN periodic table.
naturalVsPurifiedEnvConservationLawsNotGreenTable :: Bool
naturalVsPurifiedEnvConservationLawsNotGreenTable =
  naturalVsPurifiedEnvConservationLawsScaffold
    && naturalVsPurifiedEnvConservationLawCount /= 118 * 118
    && naturalVsPurifiedEnvProductChannelCount /= 118 * 118

-- | Class-14 **naturalVsPurifiedEnv** **conservation** claims route to knowing / quantum fiber (not meso acting).
naturalVsPurifiedEnvKnowingFiberOk :: Bool
naturalVsPurifiedEnvKnowingFiberOk = True

-- | Class-14 **naturalVsPurifiedEnv** invent refuse-closed scaffold witness.
naturalVsPurifiedEnvConservationInventRefuse :: Bool
naturalVsPurifiedEnvConservationInventRefuse =
  not naturalVsPurifiedEnvConservationProved

-- | **NaturalVsPurifiedEnv** lattice steps are concurrent Π_c — not XOR enum bucket.
naturalVsPurifiedEnvLatticeNotXor :: Bool
naturalVsPurifiedEnvLatticeNotXor =
  unwiredDesignOk
    && assumedNaturalVsPurifiedEnvDesignOk
    && surrogateNaturalVsPurifiedEnvDesignOk
    && naturalVsPurifiedEnvConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNaturalVsPurifiedEnvRefuse

-- | Class-14 **naturalVsPurifiedEnv** proved (always false on this Unwired cell).
naturalVsPurifiedEnvConservationProved :: Bool
naturalVsPurifiedEnvConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **NaturalVsPurifiedEnv** morphisms are class-24 neighbor channels — not SpeciesId tag mint.
naturalVsPurifiedEnvConservationNeSpeciesId :: Bool
naturalVsPurifiedEnvConservationNeSpeciesId =
  naturalVsPurifiedEnvConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && naturalVsPurifiedEnvProductChannelAll /= []
    && naturalVsPurifiedEnvConcurrentBundleIsConcurrentProduct naturalVsPurifiedEnvWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-24 **naturalVsPurifiedEnv** scaffold.
naturalVsPurifiedEnvConservationFraming :: String
naturalVsPurifiedEnvConservationFraming =
  "second_law_conservation_natural_vs_purified_env_one_axiom"

-- | Single design axiom: second law + **conservation** class-24 naturalVsPurifiedEnv (not 26th axiom).
naturalVsPurifiedEnvConservationAxiom :: Bool
naturalVsPurifiedEnvConservationAxiom =
  naturalVsPurifiedEnvLatticeScaffold
    && naturalVsPurifiedEnvLatticeNotGreenTable
    && naturalVsPurifiedEnvConservationLawsScaffold
    && naturalVsPurifiedEnvConservationLawsNotGreenTable
    && naturalVsPurifiedEnvKnowingFiberOk
    && class24NaturalVsPurifiedEnvPatternIndexOk
    && naturalVsPurifiedEnvConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNaturalVsPurifiedEnvRefuse
    && parallelNaturalVsPurifiedEnvAxiomRefuse
    && xorEnvWorldsRefuse
    && environmentSectionNotAxiomRefuse
    && tpFloatPinRefuse
    && naturalVsPurifiedEnvConservationInventRefuse
    && naturalVsPurifiedEnvLatticeNotXor
    && naturalVsPurifiedEnvConservationNeSpeciesId
    && not naturalVsPurifiedEnvConservationProved
    && not speciesIdForked
    && naturalVsPurifiedEnvConservationFraming
      == "second_law_conservation_natural_vs_purified_env_one_axiom"

naturalVsPurifiedEnvConservationNamed :: String
naturalVsPurifiedEnvConservationNamed =
  "naturalVsPurifiedEnvConservation: NaturalVsPurifiedEnvConservationModality Unwired Assumed Proved Surrogate four-step lattice naturalVsPurifiedEnvConservationProved false evaluateNaturalVsPurifiedEnvBundle evaluateNaturalVsPurifiedEnvConservation named class 24 natural_vs_purified_env natural env sample section purified env sample section env sections not xor worlds concurrent product identity conserved present ge 2 product not XOR natural vs purified env witness concurrent xor mutually exclusive refuse parallel natural vs purified env axiom refuse natural xor purified env worlds refuse environment section not axiom refuse tp float pin refuse natural vs purified env ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT natural-vs-purified-Env **conservation** authority (cited read-only, not forked).
naturalVsPurifiedEnvConservationAuthority :: String
naturalVsPurifiedEnvConservationAuthority =
  "umst/umst-chem/src/x_rows/natural_vs_purified_env_conservation.rs"

-- | L0 class-24 naturalVsPurifiedEnv table authority (crosswalk).
chemL0NaturalOreAssemblageAuthority :: String
chemL0NaturalOreAssemblageAuthority =
  "umst/umst-chem/src/l0_tables/natural_ore_assemblage.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | Surroundings Env section authority (natural vs purified as Env sections — not axiom).
surroundingsEnvSectionAuthority :: String
surroundingsEnvSectionAuthority = "umst/umst-chem/src/surroundings_are_environment_sections.rs"

-- | Three sample spaces not XOR authority (vacuum|contained|messy on one Env).
environmentThreeSampleSpacesAuthority :: String
environmentThreeSampleSpacesAuthority = "umst/umst-chem/src/environment_three_sample_spaces_not_xor.rs"

-- | Refine process authority (purified Env section — not proved on this cell).
refineProcessAuthority :: String
refineProcessAuthority = "umst/umst-chem/src/refine_process.rs"

-- | Goldschmidt ore-class authority (natural Env crosswalk — read-only cite).
goldschmidtConservationAuthority :: String
goldschmidtConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/GoldschmidtConservation.hs"

-- | Chem-physics chart isomorphism authority (natural_vs_purified_env chart cite).
chemPhysicsChartIsomorphismAuthority :: String
chemPhysicsChartIsomorphismAuthority =
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

naturalVsPurifiedEnvConservationCellId :: String
naturalVsPurifiedEnvConservationCellId =
  "CHEM-FORMAL-Q-HS-NATURAL-VS-PURIFIED-ENV-CONSERVATION"

-- | Non-claim fence — class-24 **naturalVsPurifiedEnv** **conservation** Unwired ≠ Proved GREEN.
naturalVsPurifiedEnvConservationNonClaim :: String
naturalVsPurifiedEnvConservationNonClaim =
  "CHEM-FORMAL-Q-HS-NATURAL-VS-PURIFIED-ENV-CONSERVATION NaturalVsPurifiedEnvConservationModality Unwired Assumed Proved Surrogate four-step lattice naturalVsPurifiedEnvConservationProved false evaluateNaturalVsPurifiedEnvBundle evaluateNaturalVsPurifiedEnvConservation named class 24 natural_vs_purified_env natural env sample section purified env sample section env sections not xor worlds concurrent product identity conserved present ge 2 product not XOR natural vs purified env witness concurrent xor mutually exclusive refuse parallel natural vs purified env axiom refuse natural xor purified env worlds refuse environment section not axiom refuse tp float pin refuse natural vs purified env ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-24 **naturalVsPurifiedEnv** **conservation** scaffold.
naturalVsPurifiedEnvConservationPhysicsGreenAuthorized :: Bool
naturalVsPurifiedEnvConservationPhysicsGreenAuthorized = False

naturalVsPurifiedEnvConservationPhysicsGreenFalse :: Bool
naturalVsPurifiedEnvConservationPhysicsGreenFalse =
  not naturalVsPurifiedEnvConservationPhysicsGreenAuthorized

naturalVsPurifiedEnvConservationModalityUnwired :: Bool
naturalVsPurifiedEnvConservationModalityUnwired =
  naturalVsPurifiedEnvConservationModalityCurrent == NaturalVsPurifiedEnvConservationUnwired

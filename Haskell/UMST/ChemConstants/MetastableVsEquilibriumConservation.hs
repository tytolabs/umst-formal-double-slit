-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.MetastableVsEquilibriumConservation
Description : Class-12 **metastable-vs-equilibrium** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Metastable-vs-equilibrium** **conservation**: north-star §2 class 12
(@metastable_vs_equilibrium@) — G hull equilibrium basin and process kinetics remainder are
concurrent PatternBundle factors on the same second-law + **conservation** object, not a 26th
axiom. G hull equilibrium ⊗ ReactionKinetics remainder ⊗ PatternBundle Π_c is **product** not XOR.
Named class-12 **metastable-vs-equilibrium** identity conserved under honest scaffold; trivial XOR,
parallel metastability axiom, CALPHAD equilibrium≠kinetics remainder, G hull≠fast kinetics, and
GREEN invent fail-closed. Class-12 **conservation** laws are structure witnesses only
(@metastableVsEquilibriumConservationProved@ = False). No SpeciesId fork.

* @MetastableVsEquilibriumConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateMetastableVsEquilibriumBundle@ — named class-12 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateMetastableVsEquilibriumConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@metastableVsEquilibriumConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of class-12 **metastable-vs-equilibrium** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-METASTABLE-VS-EQUILIBRIUM-CONSERVATION@.
INT: umst/umst-chem/src/metastable_equilibrium.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.MetastableVsEquilibriumConservation
  ( MetastableVsEquilibriumConservationModality (..)
  , metastableVsEquilibriumConservationModalityCurrent
  , metastableVsEquilibriumLatticeAll
  , metastableVsEquilibriumLatticeCount
  , class12MetastableVsEquilibriumPatternIndex
  , MetastableVsEquilibriumChannelSlot (..)
  , metastableVsEquilibriumChannelSlotAll
  , metastableVsEquilibriumChannelSlotCount
  , MetastableVsEquilibriumProductChannel (..)
  , metastableVsEquilibriumProductChannelAll
  , metastableVsEquilibriumProductChannelCount
  , metastableVsEquilibriumProductChannelIndex
  , MetastableVsEquilibriumConcurrentBundle (..)
  , metastableVsEquilibriumConcurrentBundleUnwired
  , metastableVsEquilibriumConcurrentBundleWithChannel
  , metastableVsEquilibriumConcurrentBundleWithPresent
  , metastableVsEquilibriumConcurrentBundleChannelAt
  , metastableVsEquilibriumConcurrentBundleHolds
  , metastableVsEquilibriumConcurrentBundlePresentCount
  , metastableVsEquilibriumConcurrentBundleIsConcurrentProduct
  , metastableVsEquilibriumGHullKineticsWitness
  , MetastableVsEquilibriumXorPosture (..)
  , metastableVsEquilibriumXorPostureExclusive
  , metastableVsEquilibriumXorPostureConcurrent
  , MetastableVsEquilibriumConservationVerdict (..)
  , MetastableVsEquilibriumXorVerdict (..)
  , evaluateMetastableVsEquilibriumBundle
  , evaluateMetastableVsEquilibriumXor
  , evaluateMetastableVsEquilibriumConservation
  , MetastableVsEquilibriumConservationLaw (..)
  , metastableVsEquilibriumConservationLawAll
  , metastableVsEquilibriumConservationLawCount
  , sampleMetastableVsEquilibriumGHullKineticsBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , metastableVsEquilibriumGHullKineticsConcurrentOk
  , class12MetastableVsEquilibriumPatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventMetastableVsEquilibriumRefuse
  , parallelMetastabilityAxiomRefuse
  , calphadEquilibriumNeKineticsRemainderRefuse
  , kineticsVsGHullRemainderRefuse
  , assumedMetastableVsEquilibriumDesignOk
  , surrogateMetastableVsEquilibriumDesignOk
  , metastableVsEquilibriumLatticeScaffold
  , metastableVsEquilibriumLatticeNotGreenTable
  , metastableVsEquilibriumConservationLawsScaffold
  , metastableVsEquilibriumConservationLawsNotGreenTable
  , metastableVsEquilibriumKnowingFiberOk
  , metastableVsEquilibriumConservationInventRefuse
  , metastableVsEquilibriumLatticeNotXor
  , metastableVsEquilibriumConservationProved
  , metastableVsEquilibriumConservationNeSpeciesId
  , speciesIdForked
  , carbonAtomicNumberZ
  , calciumAtomicNumberZ
  , metastableVsEquilibriumConservationFraming
  , metastableVsEquilibriumConservationAxiom
  , metastableVsEquilibriumConservationNamed
  , metastableVsEquilibriumConservationAuthority
  , chemL0MetastableVsEquilibriumAuthority
  , patternProductConservationAuthority
  , edgeMetastableAuthority
  , calphadEquilibriumIsNotKineticsAuthority
  , scale02RemainderAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , metastableVsEquilibriumConservationCellId
  , metastableVsEquilibriumConservationNonClaim
  , metastableVsEquilibriumConservationPhysicsGreenAuthorized
  , metastableVsEquilibriumConservationPhysicsGreenFalse
  , metastableVsEquilibriumConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not metastable-vs-equilibrium GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-12 (`metastable_vs_equilibrium`) pattern index.
class12MetastableVsEquilibriumPatternIndex :: Int
class12MetastableVsEquilibriumPatternIndex = 12

-- | Carbon Z=6 — diamond metastable trap witness pin.
carbonAtomicNumberZ :: Int
carbonAtomicNumberZ = 6

-- | Calcium Z=20 — aragonite metastable trap witness pin.
calciumAtomicNumberZ :: Int
calciumAtomicNumberZ = 20

-- | Design **metastable-vs-equilibrium** modality for class-12 **conservation** claims.
data MetastableVsEquilibriumConservationModality
  = MetastableVsEquilibriumConservationUnwired
  | MetastableVsEquilibriumConservationAssumed
  | MetastableVsEquilibriumConservationProved
  | MetastableVsEquilibriumConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **metastable-vs-equilibrium** modality — always Unwired on this cell.
metastableVsEquilibriumConservationModalityCurrent :: MetastableVsEquilibriumConservationModality
metastableVsEquilibriumConservationModalityCurrent =
  MetastableVsEquilibriumConservationUnwired

-- | All class-12 **metastable-vs-equilibrium** lattice steps in stable order.
metastableVsEquilibriumLatticeAll :: [MetastableVsEquilibriumConservationModality]
metastableVsEquilibriumLatticeAll =
  [ MetastableVsEquilibriumConservationUnwired
  , MetastableVsEquilibriumConservationAssumed
  , MetastableVsEquilibriumConservationProved
  , MetastableVsEquilibriumConservationSurrogate
  ]

metastableVsEquilibriumLatticeCount :: Int
metastableVsEquilibriumLatticeCount = length metastableVsEquilibriumLatticeAll

-- | Metastable-vs-equilibrium product channel slot — concurrent **product** factor, not XOR bucket.
data MetastableVsEquilibriumChannelSlot
  = MetastableVsEquilibriumSlotUnwired
  | MetastableVsEquilibriumSlotAbsent
  | MetastableVsEquilibriumSlotPresent
  deriving (Eq, Show)

-- | All metastable-vs-equilibrium channel slots in stable order.
metastableVsEquilibriumChannelSlotAll :: [MetastableVsEquilibriumChannelSlot]
metastableVsEquilibriumChannelSlotAll =
  [ MetastableVsEquilibriumSlotUnwired
  , MetastableVsEquilibriumSlotAbsent
  , MetastableVsEquilibriumSlotPresent
  ]

metastableVsEquilibriumChannelSlotCount :: Int
metastableVsEquilibriumChannelSlotCount = length metastableVsEquilibriumChannelSlotAll

-- | Named G hull equilibrium / kinetics remainder / PatternBundle product channels.
data MetastableVsEquilibriumProductChannel
  = GHullEquilibriumBasin
  | ReactionKineticsRemainder
  | PatternBundleConcurrentFactor
  deriving (Eq, Show)

-- | All metastable-vs-equilibrium product channels in north-star stable order.
metastableVsEquilibriumProductChannelAll :: [MetastableVsEquilibriumProductChannel]
metastableVsEquilibriumProductChannelAll =
  [ GHullEquilibriumBasin
  , ReactionKineticsRemainder
  , PatternBundleConcurrentFactor
  ]

metastableVsEquilibriumProductChannelCount :: Int
metastableVsEquilibriumProductChannelCount = length metastableVsEquilibriumProductChannelAll

-- | Stable channel index for a metastable-vs-equilibrium product channel (0..2).
metastableVsEquilibriumProductChannelIndex :: MetastableVsEquilibriumProductChannel -> Int
metastableVsEquilibriumProductChannelIndex channel =
  case channel of
    GHullEquilibriumBasin -> 0
    ReactionKineticsRemainder -> 1
    PatternBundleConcurrentFactor -> 2

-- | Class-12 metastable-vs-equilibrium concurrent **product** bundle (north-star §3).
data MetastableVsEquilibriumConcurrentBundle = MetastableVsEquilibriumConcurrentBundle
  { metastableVsEquilibriumClassPresent :: Bool
  , metastableVsEquilibriumChannelSlots :: [MetastableVsEquilibriumChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
metastableVsEquilibriumConcurrentBundleUnwired :: MetastableVsEquilibriumConcurrentBundle
metastableVsEquilibriumConcurrentBundleUnwired =
  MetastableVsEquilibriumConcurrentBundle
    False
    (replicate metastableVsEquilibriumProductChannelCount MetastableVsEquilibriumSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
metastableVsEquilibriumConcurrentBundleWithChannel ::
  Int -> MetastableVsEquilibriumChannelSlot -> MetastableVsEquilibriumConcurrentBundle -> MetastableVsEquilibriumConcurrentBundle
metastableVsEquilibriumConcurrentBundleWithChannel idx slot bundle =
  let slots = metastableVsEquilibriumChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in MetastableVsEquilibriumConcurrentBundle
        (metastableVsEquilibriumClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the metastable-vs-equilibrium **product**.
metastableVsEquilibriumConcurrentBundleWithPresent ::
  Int -> MetastableVsEquilibriumConcurrentBundle -> MetastableVsEquilibriumConcurrentBundle
metastableVsEquilibriumConcurrentBundleWithPresent idx bundle =
  metastableVsEquilibriumConcurrentBundleWithChannel idx MetastableVsEquilibriumSlotPresent bundle

-- | Read channel slot at index (0..2).
metastableVsEquilibriumConcurrentBundleChannelAt ::
  Int -> MetastableVsEquilibriumConcurrentBundle -> Maybe MetastableVsEquilibriumChannelSlot
metastableVsEquilibriumConcurrentBundleChannelAt idx bundle =
  let slots = metastableVsEquilibriumChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
metastableVsEquilibriumConcurrentBundleHolds :: Int -> MetastableVsEquilibriumConcurrentBundle -> Bool
metastableVsEquilibriumConcurrentBundleHolds idx bundle =
  case metastableVsEquilibriumConcurrentBundleChannelAt idx bundle of
    Just MetastableVsEquilibriumSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
metastableVsEquilibriumConcurrentBundlePresentCount :: MetastableVsEquilibriumConcurrentBundle -> Int
metastableVsEquilibriumConcurrentBundlePresentCount bundle =
  length (filter (== MetastableVsEquilibriumSlotPresent) (metastableVsEquilibriumChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
metastableVsEquilibriumConcurrentBundleIsConcurrentProduct :: MetastableVsEquilibriumConcurrentBundle -> Bool
metastableVsEquilibriumConcurrentBundleIsConcurrentProduct bundle =
  metastableVsEquilibriumConcurrentBundlePresentCount bundle >= 2

-- | Metastable-vs-equilibrium witness: G hull (0) + kinetics remainder (1) + PatternBundle (2) concurrent on class 12.
metastableVsEquilibriumGHullKineticsWitness :: MetastableVsEquilibriumConcurrentBundle
metastableVsEquilibriumGHullKineticsWitness =
  metastableVsEquilibriumConcurrentBundleWithPresent 2
    (metastableVsEquilibriumConcurrentBundleWithPresent 1
      (metastableVsEquilibriumConcurrentBundleWithPresent 0
        (MetastableVsEquilibriumConcurrentBundle True
          (replicate metastableVsEquilibriumProductChannelCount MetastableVsEquilibriumSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data MetastableVsEquilibriumXorPosture
  = MetastableVsEquilibriumXorExclusive
  | MetastableVsEquilibriumXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
metastableVsEquilibriumXorPostureExclusive :: MetastableVsEquilibriumXorPosture
metastableVsEquilibriumXorPostureExclusive = MetastableVsEquilibriumXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
metastableVsEquilibriumXorPostureConcurrent :: MetastableVsEquilibriumXorPosture
metastableVsEquilibriumXorPostureConcurrent = MetastableVsEquilibriumXorConcurrent

-- | Verdict for metastable-vs-equilibrium **conservation** close (fail-closed).
data MetastableVsEquilibriumConservationVerdict
  = MetastableVsEquilibriumConservationDesignOk
  | MetastableVsEquilibriumConservationNamedOk
  | MetastableVsEquilibriumConservationTrivialRefuse
  | MetastableVsEquilibriumConservationGreenInventRefuse
  | MetastableVsEquilibriumConservationProvedWithoutBarRefuse
  | MetastableVsEquilibriumConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data MetastableVsEquilibriumXorVerdict
  = MetastableVsEquilibriumXorDesignOk
  | MetastableVsEquilibriumXorNamedOk
  | MetastableVsEquilibriumXorGreenInventRefuse
  | MetastableVsEquilibriumXorProvedWithoutBarRefuse
  | MetastableVsEquilibriumXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a metastable-vs-equilibrium bundle under class-12 **conservation** bar (fail-closed).
evaluateMetastableVsEquilibriumBundle ::
  MetastableVsEquilibriumConservationModality
  -> MetastableVsEquilibriumConcurrentBundle
  -> Bool
  -> Bool
  -> MetastableVsEquilibriumConservationVerdict
evaluateMetastableVsEquilibriumBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = MetastableVsEquilibriumConservationGreenInventRefuse
  | claimProved = MetastableVsEquilibriumConservationProvedWithoutBarRefuse
  | length (metastableVsEquilibriumChannelSlots bundle) /= metastableVsEquilibriumProductChannelCount =
      MetastableVsEquilibriumConservationTrivialRefuse
  | otherwise =
      case modality of
        MetastableVsEquilibriumConservationUnwired ->
          if metastableVsEquilibriumConcurrentBundleIsConcurrentProduct bundle
            then MetastableVsEquilibriumConservationNamedOk
            else MetastableVsEquilibriumConservationDesignOk
        MetastableVsEquilibriumConservationAssumed -> MetastableVsEquilibriumConservationDesignOk
        MetastableVsEquilibriumConservationSurrogate -> MetastableVsEquilibriumConservationDesignOk
        MetastableVsEquilibriumConservationProved -> MetastableVsEquilibriumConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-12 **conservation** bar (fail-closed).
evaluateMetastableVsEquilibriumXor ::
  MetastableVsEquilibriumConservationModality
  -> MetastableVsEquilibriumXorPosture
  -> Bool
  -> Bool
  -> MetastableVsEquilibriumXorVerdict
evaluateMetastableVsEquilibriumXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = MetastableVsEquilibriumXorGreenInventRefuse
  | claimProved = MetastableVsEquilibriumXorProvedWithoutBarRefuse
  | posture == MetastableVsEquilibriumXorExclusive = MetastableVsEquilibriumXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        MetastableVsEquilibriumConservationUnwired -> MetastableVsEquilibriumXorNamedOk
        MetastableVsEquilibriumConservationAssumed -> MetastableVsEquilibriumXorDesignOk
        MetastableVsEquilibriumConservationSurrogate -> MetastableVsEquilibriumXorDesignOk
        MetastableVsEquilibriumConservationProved -> MetastableVsEquilibriumXorProvedWithoutBarRefuse

-- | **Metastable-vs-equilibrium** identity law cells tracked by class-12 **conservation** (structure scaffold).
data MetastableVsEquilibriumConservationLaw
  = MetastableVsEquilibriumConservationConserved
  | NamedMetastableVsEquilibriumConservationOk
  | TrivialMetastableVsEquilibriumRefused
  | GreenInventMetastableVsEquilibriumRefused
  deriving (Eq, Show)

metastableVsEquilibriumConservationLawAll :: [MetastableVsEquilibriumConservationLaw]
metastableVsEquilibriumConservationLawAll =
  [ MetastableVsEquilibriumConservationConserved
  , NamedMetastableVsEquilibriumConservationOk
  , TrivialMetastableVsEquilibriumRefused
  , GreenInventMetastableVsEquilibriumRefused
  ]

metastableVsEquilibriumConservationLawCount :: Int
metastableVsEquilibriumConservationLawCount = length metastableVsEquilibriumConservationLawAll

-- | Evaluate class-12 **metastable-vs-equilibrium** **conservation** typing (fail-closed).
evaluateMetastableVsEquilibriumConservation ::
  MetastableVsEquilibriumConservationModality
  -> MetastableVsEquilibriumConcurrentBundle
  -> MetastableVsEquilibriumXorPosture
  -> Bool
  -> Bool
  -> MetastableVsEquilibriumConservationVerdict
evaluateMetastableVsEquilibriumConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = MetastableVsEquilibriumConservationGreenInventRefuse
  | claimProved = MetastableVsEquilibriumConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateMetastableVsEquilibriumXor modality posture False False of
        MetastableVsEquilibriumXorMutuallyExclusiveRefuse -> MetastableVsEquilibriumConservationXorRefuse
        MetastableVsEquilibriumXorGreenInventRefuse -> MetastableVsEquilibriumConservationGreenInventRefuse
        MetastableVsEquilibriumXorProvedWithoutBarRefuse -> MetastableVsEquilibriumConservationProvedWithoutBarRefuse
        _ ->
          case evaluateMetastableVsEquilibriumBundle modality bundle False False of
            MetastableVsEquilibriumConservationNamedOk -> MetastableVsEquilibriumConservationNamedOk
            MetastableVsEquilibriumConservationGreenInventRefuse -> MetastableVsEquilibriumConservationGreenInventRefuse
            MetastableVsEquilibriumConservationProvedWithoutBarRefuse -> MetastableVsEquilibriumConservationProvedWithoutBarRefuse
            MetastableVsEquilibriumConservationTrivialRefuse -> MetastableVsEquilibriumConservationTrivialRefuse
            MetastableVsEquilibriumConservationXorRefuse -> MetastableVsEquilibriumConservationXorRefuse
            MetastableVsEquilibriumConservationDesignOk -> MetastableVsEquilibriumConservationDesignOk

sampleMetastableVsEquilibriumGHullKineticsBundle :: MetastableVsEquilibriumConcurrentBundle
sampleMetastableVsEquilibriumGHullKineticsBundle = metastableVsEquilibriumGHullKineticsWitness

sampleXorExclusiveBundle :: MetastableVsEquilibriumConcurrentBundle
sampleXorExclusiveBundle = metastableVsEquilibriumConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: MetastableVsEquilibriumConcurrentBundle
sampleTrivialUnwiredBundle = metastableVsEquilibriumConcurrentBundleUnwired

-- | Unwired **metastable-vs-equilibrium** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateMetastableVsEquilibriumConservation
    MetastableVsEquilibriumConservationUnwired
    sampleMetastableVsEquilibriumGHullKineticsBundle
    metastableVsEquilibriumXorPostureConcurrent
    False
    False
    == MetastableVsEquilibriumConservationNamedOk

-- | Metastable-vs-equilibrium witness: G hull + kinetics remainder + PatternBundle concurrent Π_c on class 12.
metastableVsEquilibriumGHullKineticsConcurrentOk :: Bool
metastableVsEquilibriumGHullKineticsConcurrentOk =
  let bundle = metastableVsEquilibriumGHullKineticsWitness
   in metastableVsEquilibriumClassPresent bundle
        && metastableVsEquilibriumConcurrentBundleHolds 0 bundle
        && metastableVsEquilibriumConcurrentBundleHolds 1 bundle
        && metastableVsEquilibriumConcurrentBundleHolds 2 bundle
        && metastableVsEquilibriumConcurrentBundlePresentCount bundle == 3
        && metastableVsEquilibriumConcurrentBundleIsConcurrentProduct bundle
        && carbonAtomicNumberZ == 6
        && calciumAtomicNumberZ == 20
        && class12MetastableVsEquilibriumPatternIndex == 12

-- | Class-12 metastable-vs-equilibrium pattern index pinned @ scaffold.
class12MetastableVsEquilibriumPatternIndexOk :: Bool
class12MetastableVsEquilibriumPatternIndexOk =
  class12MetastableVsEquilibriumPatternIndex == 12
    && metastableVsEquilibriumProductChannelCount == 3
    && length (metastableVsEquilibriumChannelSlots metastableVsEquilibriumConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  metastableVsEquilibriumConcurrentBundleIsConcurrentProduct metastableVsEquilibriumGHullKineticsWitness
    && metastableVsEquilibriumConcurrentBundlePresentCount metastableVsEquilibriumGHullKineticsWitness >= 2
    && metastableVsEquilibriumConcurrentBundlePresentCount metastableVsEquilibriumGHullKineticsWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateMetastableVsEquilibriumXor
    MetastableVsEquilibriumConservationUnwired
    metastableVsEquilibriumXorPostureExclusive
    False
    False
    == MetastableVsEquilibriumXorMutuallyExclusiveRefuse
    && evaluateMetastableVsEquilibriumConservation
      MetastableVsEquilibriumConservationUnwired
      sampleMetastableVsEquilibriumGHullKineticsBundle
      metastableVsEquilibriumXorPostureExclusive
      False
      False
      == MetastableVsEquilibriumConservationXorRefuse

-- | GREEN invent on **metastable-vs-equilibrium** **conservation** promotion is refused.
greenInventMetastableVsEquilibriumRefuse :: Bool
greenInventMetastableVsEquilibriumRefuse =
  evaluateMetastableVsEquilibriumConservation
    MetastableVsEquilibriumConservationUnwired
    sampleMetastableVsEquilibriumGHullKineticsBundle
    metastableVsEquilibriumXorPostureConcurrent
    True
    False
    == MetastableVsEquilibriumConservationGreenInventRefuse
    && evaluateMetastableVsEquilibriumBundle
      MetastableVsEquilibriumConservationUnwired
      sampleMetastableVsEquilibriumGHullKineticsBundle
      True
      False
      == MetastableVsEquilibriumConservationGreenInventRefuse

-- | Parallel metastability axiom (26th law) mint is refused — second law + conservation only.
parallelMetastabilityAxiomRefuse :: Bool
parallelMetastabilityAxiomRefuse =
  metastableVsEquilibriumConservationAuthority
    == "umst/umst-chem/src/metastable_equilibrium.rs"
    && metastableVsEquilibriumConservationProved == False
    && not (metastableVsEquilibriumConservationAuthority == "26th_chemistry_axiom")
    && metastableVsEquilibriumConservationFraming
      /= "parallel_metastability_axiom_not_second_law"
    && chemL0MetastableVsEquilibriumAuthority
      == "umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs"

-- | CALPHAD equilibrium hull ≠ process kinetics remainder — refuse folklore collision.
calphadEquilibriumNeKineticsRemainderRefuse :: Bool
calphadEquilibriumNeKineticsRemainderRefuse =
  parallelMetastabilityAxiomRefuse
    && metastableVsEquilibriumConservationFraming
      /= "calphad_equilibrium_equals_kinetics_remainder"
    && calphadEquilibriumIsNotKineticsAuthority
      == "umst/umst-chem/src/cross_classifier/calphad_equilibrium_is_not_kinetics.rs"
    && scale02RemainderAuthority
      == "umst/umst-chem/src/timescale_separation_remainders.rs"
    && class12MetastableVsEquilibriumPatternIndex == 12

-- | G hull equilibrium basin ≠ fast kinetics remainder — refuse folklore collision.
kineticsVsGHullRemainderRefuse :: Bool
kineticsVsGHullRemainderRefuse =
  calphadEquilibriumNeKineticsRemainderRefuse
    && metastableVsEquilibriumConservationFraming
      /= "g_hull_equilibrium_equals_fast_kinetics"
    && class12MetastableVsEquilibriumPatternIndex == 12
    && metastableVsEquilibriumConcurrentBundleIsConcurrentProduct metastableVsEquilibriumGHullKineticsWitness

-- | Assumed **metastable-vs-equilibrium** modality OK without thermo break (design scaffold).
assumedMetastableVsEquilibriumDesignOk :: Bool
assumedMetastableVsEquilibriumDesignOk =
  evaluateMetastableVsEquilibriumConservation
    MetastableVsEquilibriumConservationAssumed
    sampleMetastableVsEquilibriumGHullKineticsBundle
    metastableVsEquilibriumXorPostureConcurrent
    False
    False
    == MetastableVsEquilibriumConservationDesignOk

-- | Surrogate **metastable-vs-equilibrium** modality OK without thermo break (design scaffold).
surrogateMetastableVsEquilibriumDesignOk :: Bool
surrogateMetastableVsEquilibriumDesignOk =
  evaluateMetastableVsEquilibriumConservation
    MetastableVsEquilibriumConservationSurrogate
    sampleMetastableVsEquilibriumGHullKineticsBundle
    metastableVsEquilibriumXorPostureConcurrent
    False
    False
    == MetastableVsEquilibriumConservationDesignOk

-- | Four-step class-12 **metastable-vs-equilibrium** lattice scaffold pinned.
metastableVsEquilibriumLatticeScaffold :: Bool
metastableVsEquilibriumLatticeScaffold =
  metastableVsEquilibriumLatticeCount == 4
    && unwiredDesignOk
    && class12MetastableVsEquilibriumPatternIndexOk
    && metastableVsEquilibriumGHullKineticsConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedMetastableVsEquilibriumDesignOk
    && surrogateMetastableVsEquilibriumDesignOk
    && parallelMetastabilityAxiomRefuse
    && calphadEquilibriumNeKineticsRemainderRefuse
    && kineticsVsGHullRemainderRefuse

-- | **Metastable-vs-equilibrium** lattice is structure scaffold — not 118² GREEN periodic table.
metastableVsEquilibriumLatticeNotGreenTable :: Bool
metastableVsEquilibriumLatticeNotGreenTable =
  metastableVsEquilibriumLatticeCount == 4
    && metastableVsEquilibriumLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && metastableVsEquilibriumProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && metastableVsEquilibriumChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **metastable-vs-equilibrium** identity law cells scaffold pinned.
metastableVsEquilibriumConservationLawsScaffold :: Bool
metastableVsEquilibriumConservationLawsScaffold =
  metastableVsEquilibriumConservationLawCount == 4
    && metastableVsEquilibriumGHullKineticsConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventMetastableVsEquilibriumRefuse
    && parallelMetastabilityAxiomRefuse
    && calphadEquilibriumNeKineticsRemainderRefuse
    && kineticsVsGHullRemainderRefuse

-- | **Metastable-vs-equilibrium** law cells are structure scaffold — not 118² GREEN periodic table.
metastableVsEquilibriumConservationLawsNotGreenTable :: Bool
metastableVsEquilibriumConservationLawsNotGreenTable =
  metastableVsEquilibriumConservationLawsScaffold
    && metastableVsEquilibriumConservationLawCount /= 118 * 118
    && metastableVsEquilibriumProductChannelCount /= 118 * 118

-- | Class-12 **metastable-vs-equilibrium** **conservation** claims route to knowing / quantum fiber (not meso acting).
metastableVsEquilibriumKnowingFiberOk :: Bool
metastableVsEquilibriumKnowingFiberOk = True

-- | Class-12 **metastable-vs-equilibrium** invent refuse-closed scaffold witness.
metastableVsEquilibriumConservationInventRefuse :: Bool
metastableVsEquilibriumConservationInventRefuse =
  not metastableVsEquilibriumConservationProved

-- | **Metastable-vs-equilibrium** lattice steps are concurrent Π_c — not XOR enum bucket.
metastableVsEquilibriumLatticeNotXor :: Bool
metastableVsEquilibriumLatticeNotXor =
  unwiredDesignOk
    && assumedMetastableVsEquilibriumDesignOk
    && surrogateMetastableVsEquilibriumDesignOk
    && metastableVsEquilibriumGHullKineticsConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventMetastableVsEquilibriumRefuse

-- | Class-12 **metastable-vs-equilibrium** proved (always false on this Unwired cell).
metastableVsEquilibriumConservationProved :: Bool
metastableVsEquilibriumConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Metastable-vs-equilibrium** morphisms are class-12 neighbor channels — not SpeciesId tag mint.
metastableVsEquilibriumConservationNeSpeciesId :: Bool
metastableVsEquilibriumConservationNeSpeciesId =
  metastableVsEquilibriumConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && metastableVsEquilibriumProductChannelAll /= []
    && metastableVsEquilibriumConcurrentBundleIsConcurrentProduct metastableVsEquilibriumGHullKineticsWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-12 **metastable-vs-equilibrium** scaffold.
metastableVsEquilibriumConservationFraming :: String
metastableVsEquilibriumConservationFraming =
  "second_law_conservation_metastable_vs_equilibrium_one_axiom"

-- | Single design axiom: second law + **conservation** class-12 metastable-vs-equilibrium (not 26th axiom).
metastableVsEquilibriumConservationAxiom :: Bool
metastableVsEquilibriumConservationAxiom =
  metastableVsEquilibriumLatticeScaffold
    && metastableVsEquilibriumLatticeNotGreenTable
    && metastableVsEquilibriumConservationLawsScaffold
    && metastableVsEquilibriumConservationLawsNotGreenTable
    && metastableVsEquilibriumKnowingFiberOk
    && class12MetastableVsEquilibriumPatternIndexOk
    && metastableVsEquilibriumGHullKineticsConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventMetastableVsEquilibriumRefuse
    && parallelMetastabilityAxiomRefuse
    && calphadEquilibriumNeKineticsRemainderRefuse
    && kineticsVsGHullRemainderRefuse
    && metastableVsEquilibriumConservationInventRefuse
    && metastableVsEquilibriumLatticeNotXor
    && metastableVsEquilibriumConservationNeSpeciesId
    && not metastableVsEquilibriumConservationProved
    && not speciesIdForked
    && metastableVsEquilibriumConservationFraming
      == "second_law_conservation_metastable_vs_equilibrium_one_axiom"

metastableVsEquilibriumConservationNamed :: String
metastableVsEquilibriumConservationNamed =
  "metastableVsEquilibriumConservation: MetastableVsEquilibriumConservationModality Unwired Assumed Proved Surrogate four-step lattice metastableVsEquilibriumConservationProved false evaluateMetastableVsEquilibriumBundle evaluateMetastableVsEquilibriumConservation named class 12 metastable_vs_equilibrium G hull equilibrium basin reaction kinetics remainder PatternBundle concurrent factor concurrent product identity conserved present ge 2 product not XOR G hull kinetics witness concurrent xor mutually exclusive refuse parallel metastability axiom refuse calphad equilibrium ne kinetics remainder refuse kinetics vs G hull remainder refuse metastable vs equilibrium ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT metastable-vs-equilibrium **conservation** authority (cited read-only, not forked).
metastableVsEquilibriumConservationAuthority :: String
metastableVsEquilibriumConservationAuthority =
  "umst/umst-chem/src/metastable_equilibrium.rs"

-- | L0 class-12 metastable-vs-equilibrium table authority (crosswalk).
chemL0MetastableVsEquilibriumAuthority :: String
chemL0MetastableVsEquilibriumAuthority =
  "umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | L0 edge metastable/equilibrium morphism authority (single axiom — no parallel law).
edgeMetastableAuthority :: String
edgeMetastableAuthority = "umst/umst-chem/src/metastable_equilibrium.rs"

-- | CALPHAD equilibrium ≠ kinetics cross-classifier authority (prove-now crosswalk).
calphadEquilibriumIsNotKineticsAuthority :: String
calphadEquilibriumIsNotKineticsAuthority =
  "umst/umst-chem/src/cross_classifier/calphad_equilibrium_is_not_kinetics.rs"

-- | SCALE-02 time-scale separation remainder authority (kinetics ≠ G-min).
scale02RemainderAuthority :: String
scale02RemainderAuthority =
  "umst/umst-chem/src/timescale_separation_remainders.rs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

metastableVsEquilibriumConservationCellId :: String
metastableVsEquilibriumConservationCellId =
  "CHEM-FORMAL-Q-HS-METASTABLE-VS-EQUILIBRIUM-CONSERVATION"

-- | Non-claim fence — class-12 **metastable-vs-equilibrium** **conservation** Unwired ≠ Proved GREEN.
metastableVsEquilibriumConservationNonClaim :: String
metastableVsEquilibriumConservationNonClaim =
  "CHEM-FORMAL-Q-HS-METASTABLE-VS-EQUILIBRIUM-CONSERVATION MetastableVsEquilibriumConservationModality Unwired Assumed Proved Surrogate four-step lattice metastableVsEquilibriumConservationProved false evaluateMetastableVsEquilibriumBundle evaluateMetastableVsEquilibriumConservation named class 12 metastable_vs_equilibrium G hull equilibrium basin reaction kinetics remainder PatternBundle concurrent factor concurrent product identity conserved present ge 2 product not XOR G hull kinetics witness concurrent xor mutually exclusive refuse parallel metastability axiom refuse calphad equilibrium ne kinetics remainder refuse kinetics vs G hull remainder refuse metastable vs equilibrium ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-12 **metastable-vs-equilibrium** **conservation** scaffold.
metastableVsEquilibriumConservationPhysicsGreenAuthorized :: Bool
metastableVsEquilibriumConservationPhysicsGreenAuthorized = False

metastableVsEquilibriumConservationPhysicsGreenFalse :: Bool
metastableVsEquilibriumConservationPhysicsGreenFalse =
  not metastableVsEquilibriumConservationPhysicsGreenAuthorized

metastableVsEquilibriumConservationModalityUnwired :: Bool
metastableVsEquilibriumConservationModalityUnwired =
  metastableVsEquilibriumConservationModalityCurrent == MetastableVsEquilibriumConservationUnwired

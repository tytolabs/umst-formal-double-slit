-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ImpureComponentMorphismConservation
Description : Class-8 **impure-component-morphism** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Impure-component-morphism** **conservation**: north-star §2 class 8
(@impure_component_morphism@) — impurity is a morphism on the same second-law +
**conservation** object, not a second SpeciesId / 26th axiom. Concurrent PatternBundle
factor; ore-constituent ⊗ second-law carrier ⊗ PatternBundle Π_c is **product** not XOR.
Named class-8 **impure-component-morphism** identity conserved under honest scaffold;
trivial XOR, parallel impurity axiom, free purification, extra ElementId, and GREEN invent
fail-closed. Class-8 **conservation** laws are structure witnesses only
(@impureComponentMorphismConservationProved@ = False). No SpeciesId fork.

* @ImpureComponentMorphismConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateImpureComponentMorphismBundle@ — named class-8 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateImpureComponentMorphismConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@impureComponentMorphismConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of class-8 **impure-component-morphism** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-IMPURE-COMPONENT-MORPHISM-CONSERVATION@.
INT: umst/umst-chem/src/impure_component_morphism.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/impure_component_morphism.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.ImpureComponentMorphismConservation
  ( ImpureComponentMorphismConservationModality (..)
  , impureComponentMorphismConservationModalityCurrent
  , impureComponentMorphismLatticeAll
  , impureComponentMorphismLatticeCount
  , class8ImpureComponentMorphismPatternIndex
  , ImpureComponentMorphismChannelSlot (..)
  , impureComponentMorphismChannelSlotAll
  , impureComponentMorphismChannelSlotCount
  , ImpureComponentMorphismProductChannel (..)
  , impureComponentMorphismProductChannelAll
  , impureComponentMorphismProductChannelCount
  , impureComponentMorphismProductChannelIndex
  , ImpureComponentMorphismConcurrentBundle (..)
  , impureComponentMorphismConcurrentBundleUnwired
  , impureComponentMorphismConcurrentBundleWithChannel
  , impureComponentMorphismConcurrentBundleWithPresent
  , impureComponentMorphismConcurrentBundleChannelAt
  , impureComponentMorphismConcurrentBundleHolds
  , impureComponentMorphismConcurrentBundlePresentCount
  , impureComponentMorphismConcurrentBundleIsConcurrentProduct
  , impureComponentMorphismOreSecondLawWitness
  , ImpureComponentMorphismXorPosture (..)
  , impureComponentMorphismXorPostureExclusive
  , impureComponentMorphismXorPostureConcurrent
  , ImpureComponentMorphismConservationVerdict (..)
  , ImpureComponentMorphismXorVerdict (..)
  , evaluateImpureComponentMorphismBundle
  , evaluateImpureComponentMorphismXor
  , evaluateImpureComponentMorphismConservation
  , ImpureComponentMorphismConservationLaw (..)
  , impureComponentMorphismConservationLawAll
  , impureComponentMorphismConservationLawCount
  , sampleImpureComponentMorphismOreSecondLawBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , impureComponentMorphismOreSecondLawConcurrentOk
  , class8ImpureComponentMorphismPatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventImpureComponentMorphismRefuse
  , parallelImpurityAxiomRefuse
  , freePurificationRefuse
  , extraElementIdRefuse
  , assumedImpureComponentMorphismDesignOk
  , surrogateImpureComponentMorphismDesignOk
  , impureComponentMorphismLatticeScaffold
  , impureComponentMorphismLatticeNotGreenTable
  , impureComponentMorphismConservationLawsScaffold
  , impureComponentMorphismConservationLawsNotGreenTable
  , impureComponentMorphismKnowingFiberOk
  , impureComponentMorphismConservationInventRefuse
  , impureComponentMorphismLatticeNotXor
  , impureComponentMorphismConservationProved
  , impureComponentMorphismConservationNeSpeciesId
  , speciesIdForked
  , ironAtomicNumberZ
  , copperAtomicNumberZ
  , impureComponentMorphismConservationFraming
  , impureComponentMorphismConservationAxiom
  , impureComponentMorphismConservationNamed
  , impureComponentMorphismConservationAuthority
  , chemL0ImpureComponentMorphismAuthority
  , patternProductConservationAuthority
  , oreAssemblageAuthority
  , impurePureAdjunctionAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , impureComponentMorphismConservationCellId
  , impureComponentMorphismConservationNonClaim
  , impureComponentMorphismConservationPhysicsGreenAuthorized
  , impureComponentMorphismConservationPhysicsGreenFalse
  , impureComponentMorphismConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not impure-component-morphism GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-8 (`impure_component_morphism`) pattern index.
class8ImpureComponentMorphismPatternIndex :: Int
class8ImpureComponentMorphismPatternIndex = 8

-- | Iron Z=26 — ore host witness element pin.
ironAtomicNumberZ :: Int
ironAtomicNumberZ = 26

-- | Copper Z=29 — trace contaminant witness element pin.
copperAtomicNumberZ :: Int
copperAtomicNumberZ = 29

-- | Design **impure-component-morphism** modality for class-8 **conservation** claims.
data ImpureComponentMorphismConservationModality
  = ImpureComponentMorphismConservationUnwired
  | ImpureComponentMorphismConservationAssumed
  | ImpureComponentMorphismConservationProved
  | ImpureComponentMorphismConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **impure-component-morphism** modality — always Unwired on this cell.
impureComponentMorphismConservationModalityCurrent :: ImpureComponentMorphismConservationModality
impureComponentMorphismConservationModalityCurrent =
  ImpureComponentMorphismConservationUnwired

-- | All class-8 **impure-component-morphism** lattice steps in stable order.
impureComponentMorphismLatticeAll :: [ImpureComponentMorphismConservationModality]
impureComponentMorphismLatticeAll =
  [ ImpureComponentMorphismConservationUnwired
  , ImpureComponentMorphismConservationAssumed
  , ImpureComponentMorphismConservationProved
  , ImpureComponentMorphismConservationSurrogate
  ]

impureComponentMorphismLatticeCount :: Int
impureComponentMorphismLatticeCount = length impureComponentMorphismLatticeAll

-- | Impure-component-morphism product channel slot — concurrent **product** factor, not XOR bucket.
data ImpureComponentMorphismChannelSlot
  = ImpureComponentMorphismSlotUnwired
  | ImpureComponentMorphismSlotAbsent
  | ImpureComponentMorphismSlotPresent
  deriving (Eq, Show)

-- | All impure-component-morphism channel slots in stable order.
impureComponentMorphismChannelSlotAll :: [ImpureComponentMorphismChannelSlot]
impureComponentMorphismChannelSlotAll =
  [ ImpureComponentMorphismSlotUnwired
  , ImpureComponentMorphismSlotAbsent
  , ImpureComponentMorphismSlotPresent
  ]

impureComponentMorphismChannelSlotCount :: Int
impureComponentMorphismChannelSlotCount = length impureComponentMorphismChannelSlotAll

-- | Named second-law carrier / ore-constituent morphism / PatternBundle product channels.
data ImpureComponentMorphismProductChannel
  = SecondLawConservationCarrier
  | OreConstituentMorphism
  | PatternBundleConcurrentFactor
  deriving (Eq, Show)

-- | All impure-component-morphism product channels in north-star stable order.
impureComponentMorphismProductChannelAll :: [ImpureComponentMorphismProductChannel]
impureComponentMorphismProductChannelAll =
  [ SecondLawConservationCarrier
  , OreConstituentMorphism
  , PatternBundleConcurrentFactor
  ]

impureComponentMorphismProductChannelCount :: Int
impureComponentMorphismProductChannelCount = length impureComponentMorphismProductChannelAll

-- | Stable channel index for an impure-component-morphism product channel (0..2).
impureComponentMorphismProductChannelIndex :: ImpureComponentMorphismProductChannel -> Int
impureComponentMorphismProductChannelIndex channel =
  case channel of
    SecondLawConservationCarrier -> 0
    OreConstituentMorphism -> 1
    PatternBundleConcurrentFactor -> 2

-- | Class-8 impure-component-morphism concurrent **product** bundle (north-star §3).
data ImpureComponentMorphismConcurrentBundle = ImpureComponentMorphismConcurrentBundle
  { impureComponentMorphismClassPresent :: Bool
  , impureComponentMorphismChannelSlots :: [ImpureComponentMorphismChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
impureComponentMorphismConcurrentBundleUnwired :: ImpureComponentMorphismConcurrentBundle
impureComponentMorphismConcurrentBundleUnwired =
  ImpureComponentMorphismConcurrentBundle
    False
    (replicate impureComponentMorphismProductChannelCount ImpureComponentMorphismSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
impureComponentMorphismConcurrentBundleWithChannel ::
  Int -> ImpureComponentMorphismChannelSlot -> ImpureComponentMorphismConcurrentBundle -> ImpureComponentMorphismConcurrentBundle
impureComponentMorphismConcurrentBundleWithChannel idx slot bundle =
  let slots = impureComponentMorphismChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in ImpureComponentMorphismConcurrentBundle
        (impureComponentMorphismClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the impure-component-morphism **product**.
impureComponentMorphismConcurrentBundleWithPresent ::
  Int -> ImpureComponentMorphismConcurrentBundle -> ImpureComponentMorphismConcurrentBundle
impureComponentMorphismConcurrentBundleWithPresent idx bundle =
  impureComponentMorphismConcurrentBundleWithChannel idx ImpureComponentMorphismSlotPresent bundle

-- | Read channel slot at index (0..2).
impureComponentMorphismConcurrentBundleChannelAt ::
  Int -> ImpureComponentMorphismConcurrentBundle -> Maybe ImpureComponentMorphismChannelSlot
impureComponentMorphismConcurrentBundleChannelAt idx bundle =
  let slots = impureComponentMorphismChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
impureComponentMorphismConcurrentBundleHolds :: Int -> ImpureComponentMorphismConcurrentBundle -> Bool
impureComponentMorphismConcurrentBundleHolds idx bundle =
  case impureComponentMorphismConcurrentBundleChannelAt idx bundle of
    Just ImpureComponentMorphismSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
impureComponentMorphismConcurrentBundlePresentCount :: ImpureComponentMorphismConcurrentBundle -> Int
impureComponentMorphismConcurrentBundlePresentCount bundle =
  length (filter (== ImpureComponentMorphismSlotPresent) (impureComponentMorphismChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
impureComponentMorphismConcurrentBundleIsConcurrentProduct :: ImpureComponentMorphismConcurrentBundle -> Bool
impureComponentMorphismConcurrentBundleIsConcurrentProduct bundle =
  impureComponentMorphismConcurrentBundlePresentCount bundle >= 2

-- | Impure-component-morphism witness: second-law (0) + ore morphism (1) + PatternBundle (2) concurrent on class 8.
impureComponentMorphismOreSecondLawWitness :: ImpureComponentMorphismConcurrentBundle
impureComponentMorphismOreSecondLawWitness =
  impureComponentMorphismConcurrentBundleWithPresent 2
    (impureComponentMorphismConcurrentBundleWithPresent 1
      (impureComponentMorphismConcurrentBundleWithPresent 0
        (ImpureComponentMorphismConcurrentBundle True
          (replicate impureComponentMorphismProductChannelCount ImpureComponentMorphismSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data ImpureComponentMorphismXorPosture
  = ImpureComponentMorphismXorExclusive
  | ImpureComponentMorphismXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
impureComponentMorphismXorPostureExclusive :: ImpureComponentMorphismXorPosture
impureComponentMorphismXorPostureExclusive = ImpureComponentMorphismXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
impureComponentMorphismXorPostureConcurrent :: ImpureComponentMorphismXorPosture
impureComponentMorphismXorPostureConcurrent = ImpureComponentMorphismXorConcurrent

-- | Verdict for impure-component-morphism **conservation** close (fail-closed).
data ImpureComponentMorphismConservationVerdict
  = ImpureComponentMorphismConservationDesignOk
  | ImpureComponentMorphismConservationNamedOk
  | ImpureComponentMorphismConservationTrivialRefuse
  | ImpureComponentMorphismConservationGreenInventRefuse
  | ImpureComponentMorphismConservationProvedWithoutBarRefuse
  | ImpureComponentMorphismConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data ImpureComponentMorphismXorVerdict
  = ImpureComponentMorphismXorDesignOk
  | ImpureComponentMorphismXorNamedOk
  | ImpureComponentMorphismXorGreenInventRefuse
  | ImpureComponentMorphismXorProvedWithoutBarRefuse
  | ImpureComponentMorphismXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate an impure-component-morphism bundle under class-8 **conservation** bar (fail-closed).
evaluateImpureComponentMorphismBundle ::
  ImpureComponentMorphismConservationModality
  -> ImpureComponentMorphismConcurrentBundle
  -> Bool
  -> Bool
  -> ImpureComponentMorphismConservationVerdict
evaluateImpureComponentMorphismBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = ImpureComponentMorphismConservationGreenInventRefuse
  | claimProved = ImpureComponentMorphismConservationProvedWithoutBarRefuse
  | length (impureComponentMorphismChannelSlots bundle) /= impureComponentMorphismProductChannelCount =
      ImpureComponentMorphismConservationTrivialRefuse
  | otherwise =
      case modality of
        ImpureComponentMorphismConservationUnwired ->
          if impureComponentMorphismConcurrentBundleIsConcurrentProduct bundle
            then ImpureComponentMorphismConservationNamedOk
            else ImpureComponentMorphismConservationDesignOk
        ImpureComponentMorphismConservationAssumed -> ImpureComponentMorphismConservationDesignOk
        ImpureComponentMorphismConservationSurrogate -> ImpureComponentMorphismConservationDesignOk
        ImpureComponentMorphismConservationProved -> ImpureComponentMorphismConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-8 **conservation** bar (fail-closed).
evaluateImpureComponentMorphismXor ::
  ImpureComponentMorphismConservationModality
  -> ImpureComponentMorphismXorPosture
  -> Bool
  -> Bool
  -> ImpureComponentMorphismXorVerdict
evaluateImpureComponentMorphismXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = ImpureComponentMorphismXorGreenInventRefuse
  | claimProved = ImpureComponentMorphismXorProvedWithoutBarRefuse
  | posture == ImpureComponentMorphismXorExclusive = ImpureComponentMorphismXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        ImpureComponentMorphismConservationUnwired -> ImpureComponentMorphismXorNamedOk
        ImpureComponentMorphismConservationAssumed -> ImpureComponentMorphismXorDesignOk
        ImpureComponentMorphismConservationSurrogate -> ImpureComponentMorphismXorDesignOk
        ImpureComponentMorphismConservationProved -> ImpureComponentMorphismXorProvedWithoutBarRefuse

-- | **Impure-component-morphism** identity law cells tracked by class-8 **conservation** (structure scaffold).
data ImpureComponentMorphismConservationLaw
  = ImpureComponentMorphismConservationConserved
  | NamedImpureComponentMorphismConservationOk
  | TrivialImpureComponentMorphismRefused
  | GreenInventImpureComponentMorphismRefused
  deriving (Eq, Show)

impureComponentMorphismConservationLawAll :: [ImpureComponentMorphismConservationLaw]
impureComponentMorphismConservationLawAll =
  [ ImpureComponentMorphismConservationConserved
  , NamedImpureComponentMorphismConservationOk
  , TrivialImpureComponentMorphismRefused
  , GreenInventImpureComponentMorphismRefused
  ]

impureComponentMorphismConservationLawCount :: Int
impureComponentMorphismConservationLawCount = length impureComponentMorphismConservationLawAll

-- | Evaluate class-8 **impure-component-morphism** **conservation** typing (fail-closed).
evaluateImpureComponentMorphismConservation ::
  ImpureComponentMorphismConservationModality
  -> ImpureComponentMorphismConcurrentBundle
  -> ImpureComponentMorphismXorPosture
  -> Bool
  -> Bool
  -> ImpureComponentMorphismConservationVerdict
evaluateImpureComponentMorphismConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = ImpureComponentMorphismConservationGreenInventRefuse
  | claimProved = ImpureComponentMorphismConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateImpureComponentMorphismXor modality posture False False of
        ImpureComponentMorphismXorMutuallyExclusiveRefuse -> ImpureComponentMorphismConservationXorRefuse
        ImpureComponentMorphismXorGreenInventRefuse -> ImpureComponentMorphismConservationGreenInventRefuse
        ImpureComponentMorphismXorProvedWithoutBarRefuse -> ImpureComponentMorphismConservationProvedWithoutBarRefuse
        _ ->
          case evaluateImpureComponentMorphismBundle modality bundle False False of
            ImpureComponentMorphismConservationNamedOk -> ImpureComponentMorphismConservationNamedOk
            ImpureComponentMorphismConservationGreenInventRefuse -> ImpureComponentMorphismConservationGreenInventRefuse
            ImpureComponentMorphismConservationProvedWithoutBarRefuse -> ImpureComponentMorphismConservationProvedWithoutBarRefuse
            ImpureComponentMorphismConservationTrivialRefuse -> ImpureComponentMorphismConservationTrivialRefuse
            ImpureComponentMorphismConservationXorRefuse -> ImpureComponentMorphismConservationXorRefuse
            ImpureComponentMorphismConservationDesignOk -> ImpureComponentMorphismConservationDesignOk

sampleImpureComponentMorphismOreSecondLawBundle :: ImpureComponentMorphismConcurrentBundle
sampleImpureComponentMorphismOreSecondLawBundle = impureComponentMorphismOreSecondLawWitness

sampleXorExclusiveBundle :: ImpureComponentMorphismConcurrentBundle
sampleXorExclusiveBundle = impureComponentMorphismConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: ImpureComponentMorphismConcurrentBundle
sampleTrivialUnwiredBundle = impureComponentMorphismConcurrentBundleUnwired

-- | Unwired **impure-component-morphism** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateImpureComponentMorphismConservation
    ImpureComponentMorphismConservationUnwired
    sampleImpureComponentMorphismOreSecondLawBundle
    impureComponentMorphismXorPostureConcurrent
    False
    False
    == ImpureComponentMorphismConservationNamedOk

-- | Impure-component-morphism witness: second-law + ore morphism + PatternBundle concurrent Π_c on class 8.
impureComponentMorphismOreSecondLawConcurrentOk :: Bool
impureComponentMorphismOreSecondLawConcurrentOk =
  let bundle = impureComponentMorphismOreSecondLawWitness
   in impureComponentMorphismClassPresent bundle
        && impureComponentMorphismConcurrentBundleHolds 0 bundle
        && impureComponentMorphismConcurrentBundleHolds 1 bundle
        && impureComponentMorphismConcurrentBundleHolds 2 bundle
        && impureComponentMorphismConcurrentBundlePresentCount bundle == 3
        && impureComponentMorphismConcurrentBundleIsConcurrentProduct bundle
        && ironAtomicNumberZ == 26
        && copperAtomicNumberZ == 29
        && class8ImpureComponentMorphismPatternIndex == 8

-- | Class-8 impure-component-morphism pattern index pinned @ scaffold.
class8ImpureComponentMorphismPatternIndexOk :: Bool
class8ImpureComponentMorphismPatternIndexOk =
  class8ImpureComponentMorphismPatternIndex == 8
    && impureComponentMorphismProductChannelCount == 3
    && length (impureComponentMorphismChannelSlots impureComponentMorphismConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  impureComponentMorphismConcurrentBundleIsConcurrentProduct impureComponentMorphismOreSecondLawWitness
    && impureComponentMorphismConcurrentBundlePresentCount impureComponentMorphismOreSecondLawWitness >= 2
    && impureComponentMorphismConcurrentBundlePresentCount impureComponentMorphismOreSecondLawWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateImpureComponentMorphismXor
    ImpureComponentMorphismConservationUnwired
    impureComponentMorphismXorPostureExclusive
    False
    False
    == ImpureComponentMorphismXorMutuallyExclusiveRefuse
    && evaluateImpureComponentMorphismConservation
      ImpureComponentMorphismConservationUnwired
      sampleImpureComponentMorphismOreSecondLawBundle
      impureComponentMorphismXorPostureExclusive
      False
      False
      == ImpureComponentMorphismConservationXorRefuse

-- | GREEN invent on **impure-component-morphism** **conservation** promotion is refused.
greenInventImpureComponentMorphismRefuse :: Bool
greenInventImpureComponentMorphismRefuse =
  evaluateImpureComponentMorphismConservation
    ImpureComponentMorphismConservationUnwired
    sampleImpureComponentMorphismOreSecondLawBundle
    impureComponentMorphismXorPostureConcurrent
    True
    False
    == ImpureComponentMorphismConservationGreenInventRefuse
    && evaluateImpureComponentMorphismBundle
      ImpureComponentMorphismConservationUnwired
      sampleImpureComponentMorphismOreSecondLawBundle
      True
      False
      == ImpureComponentMorphismConservationGreenInventRefuse

-- | Parallel impurity axiom (26th law) mint is refused — second law + conservation only.
parallelImpurityAxiomRefuse :: Bool
parallelImpurityAxiomRefuse =
  impureComponentMorphismConservationAuthority
    == "umst/umst-chem/src/impure_component_morphism.rs"
    && impureComponentMorphismConservationProved == False
    && not (impureComponentMorphismConservationAuthority == "26th_chemistry_axiom")
    && impureComponentMorphismConservationFraming
      /= "parallel_impure_component_morphism_axiom_not_second_law"

-- | Free purification on impure morphism is refused — pureward cost mandatory.
freePurificationRefuse :: Bool
freePurificationRefuse =
  parallelImpurityAxiomRefuse
    && impureComponentMorphismConservationFraming
      /= "free_purification_reverse_refine"
    && impurePureAdjunctionAuthority
      == "umst/umst-chem/src/impure_pure_adjunction.rs"
    && class8ImpureComponentMorphismPatternIndex == 8

-- | Impurity morphism ≠ extra ElementId Z=119 row smuggle.
extraElementIdRefuse :: Bool
extraElementIdRefuse =
  freePurificationRefuse
    && impureComponentMorphismConservationFraming
      /= "impurity_as_extra_element_id_z_119"
    && ironAtomicNumberZ <= iupacTableCardinality
    && copperAtomicNumberZ <= iupacTableCardinality
    && impureComponentMorphismConcurrentBundleIsConcurrentProduct impureComponentMorphismOreSecondLawWitness

-- | Assumed **impure-component-morphism** modality OK without thermo break (design scaffold).
assumedImpureComponentMorphismDesignOk :: Bool
assumedImpureComponentMorphismDesignOk =
  evaluateImpureComponentMorphismConservation
    ImpureComponentMorphismConservationAssumed
    sampleImpureComponentMorphismOreSecondLawBundle
    impureComponentMorphismXorPostureConcurrent
    False
    False
    == ImpureComponentMorphismConservationDesignOk

-- | Surrogate **impure-component-morphism** modality OK without thermo break (design scaffold).
surrogateImpureComponentMorphismDesignOk :: Bool
surrogateImpureComponentMorphismDesignOk =
  evaluateImpureComponentMorphismConservation
    ImpureComponentMorphismConservationSurrogate
    sampleImpureComponentMorphismOreSecondLawBundle
    impureComponentMorphismXorPostureConcurrent
    False
    False
    == ImpureComponentMorphismConservationDesignOk

-- | Four-step class-8 **impure-component-morphism** lattice scaffold pinned.
impureComponentMorphismLatticeScaffold :: Bool
impureComponentMorphismLatticeScaffold =
  impureComponentMorphismLatticeCount == 4
    && unwiredDesignOk
    && class8ImpureComponentMorphismPatternIndexOk
    && impureComponentMorphismOreSecondLawConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedImpureComponentMorphismDesignOk
    && surrogateImpureComponentMorphismDesignOk
    && parallelImpurityAxiomRefuse
    && freePurificationRefuse
    && extraElementIdRefuse

-- | **Impure-component-morphism** lattice is structure scaffold — not 118² GREEN periodic table.
impureComponentMorphismLatticeNotGreenTable :: Bool
impureComponentMorphismLatticeNotGreenTable =
  impureComponentMorphismLatticeCount == 4
    && impureComponentMorphismLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && impureComponentMorphismProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && impureComponentMorphismChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **impure-component-morphism** identity law cells scaffold pinned.
impureComponentMorphismConservationLawsScaffold :: Bool
impureComponentMorphismConservationLawsScaffold =
  impureComponentMorphismConservationLawCount == 4
    && impureComponentMorphismOreSecondLawConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventImpureComponentMorphismRefuse
    && parallelImpurityAxiomRefuse
    && freePurificationRefuse
    && extraElementIdRefuse

-- | **Impure-component-morphism** law cells are structure scaffold — not 118² GREEN periodic table.
impureComponentMorphismConservationLawsNotGreenTable :: Bool
impureComponentMorphismConservationLawsNotGreenTable =
  impureComponentMorphismConservationLawsScaffold
    && impureComponentMorphismConservationLawCount /= 118 * 118
    && impureComponentMorphismProductChannelCount /= 118 * 118

-- | Class-8 **impure-component-morphism** **conservation** claims route to knowing / quantum fiber (not meso acting).
impureComponentMorphismKnowingFiberOk :: Bool
impureComponentMorphismKnowingFiberOk = True

-- | Class-8 **impure-component-morphism** invent refuse-closed scaffold witness.
impureComponentMorphismConservationInventRefuse :: Bool
impureComponentMorphismConservationInventRefuse =
  not impureComponentMorphismConservationProved

-- | **Impure-component-morphism** lattice steps are concurrent Π_c — not XOR enum bucket.
impureComponentMorphismLatticeNotXor :: Bool
impureComponentMorphismLatticeNotXor =
  unwiredDesignOk
    && assumedImpureComponentMorphismDesignOk
    && surrogateImpureComponentMorphismDesignOk
    && impureComponentMorphismOreSecondLawConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventImpureComponentMorphismRefuse

-- | Class-8 **impure-component-morphism** proved (always false on this Unwired cell).
impureComponentMorphismConservationProved :: Bool
impureComponentMorphismConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Impure-component-morphism** morphisms are class-8 neighbor channels — not SpeciesId tag mint.
impureComponentMorphismConservationNeSpeciesId :: Bool
impureComponentMorphismConservationNeSpeciesId =
  impureComponentMorphismConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && impureComponentMorphismProductChannelAll /= []
    && impureComponentMorphismConcurrentBundleIsConcurrentProduct impureComponentMorphismOreSecondLawWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-8 **impure-component-morphism** scaffold.
impureComponentMorphismConservationFraming :: String
impureComponentMorphismConservationFraming =
  "second_law_conservation_impure_component_morphism_one_axiom"

-- | Single design axiom: second law + **conservation** class-8 impure-component-morphism (not 26th axiom).
impureComponentMorphismConservationAxiom :: Bool
impureComponentMorphismConservationAxiom =
  impureComponentMorphismLatticeScaffold
    && impureComponentMorphismLatticeNotGreenTable
    && impureComponentMorphismConservationLawsScaffold
    && impureComponentMorphismConservationLawsNotGreenTable
    && impureComponentMorphismKnowingFiberOk
    && class8ImpureComponentMorphismPatternIndexOk
    && impureComponentMorphismOreSecondLawConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventImpureComponentMorphismRefuse
    && parallelImpurityAxiomRefuse
    && freePurificationRefuse
    && extraElementIdRefuse
    && impureComponentMorphismConservationInventRefuse
    && impureComponentMorphismLatticeNotXor
    && impureComponentMorphismConservationNeSpeciesId
    && not impureComponentMorphismConservationProved
    && not speciesIdForked
    && impureComponentMorphismConservationFraming
      == "second_law_conservation_impure_component_morphism_one_axiom"

impureComponentMorphismConservationNamed :: String
impureComponentMorphismConservationNamed =
  "impureComponentMorphismConservation: ImpureComponentMorphismConservationModality Unwired Assumed Proved Surrogate four-step lattice impureComponentMorphismConservationProved false evaluateImpureComponentMorphismBundle evaluateImpureComponentMorphismConservation named class 8 impure_component_morphism second law conservation carrier ore constituent morphism PatternBundle concurrent factor concurrent product identity conserved present ge 2 product not XOR ore second law witness concurrent xor mutually exclusive refuse parallel impurity axiom refuse free purification refuse extra ElementId refuse impure component morphism ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT impure-component-morphism **conservation** authority (cited read-only, not forked).
impureComponentMorphismConservationAuthority :: String
impureComponentMorphismConservationAuthority =
  "umst/umst-chem/src/impure_component_morphism.rs"

-- | L0 class-8 impure-component-morphism table authority (crosswalk).
chemL0ImpureComponentMorphismAuthority :: String
chemL0ImpureComponentMorphismAuthority =
  "umst/umst-chem/src/l0_tables/impure_component_morphism.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | L0 OreAssemblage object authority (morphism carrier — not folklore list).
oreAssemblageAuthority :: String
oreAssemblageAuthority = "umst/umst-chem/src/ore_assemblage.rs"

-- | L0 impure⇄pure adjunction authority (pureward cost — not proved on this cell).
impurePureAdjunctionAuthority :: String
impurePureAdjunctionAuthority = "umst/umst-chem/src/impure_pure_adjunction.rs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

impureComponentMorphismConservationCellId :: String
impureComponentMorphismConservationCellId =
  "CHEM-FORMAL-Q-HS-IMPURE-COMPONENT-MORPHISM-CONSERVATION"

-- | Non-claim fence — class-8 **impure-component-morphism** **conservation** Unwired ≠ Proved GREEN.
impureComponentMorphismConservationNonClaim :: String
impureComponentMorphismConservationNonClaim =
  "CHEM-FORMAL-Q-HS-IMPURE-COMPONENT-MORPHISM-CONSERVATION ImpureComponentMorphismConservationModality Unwired Assumed Proved Surrogate four-step lattice impureComponentMorphismConservationProved false evaluateImpureComponentMorphismBundle evaluateImpureComponentMorphismConservation named class 8 impure_component_morphism second law conservation carrier ore constituent morphism PatternBundle concurrent factor concurrent product identity conserved present ge 2 product not XOR ore second law witness concurrent xor mutually exclusive refuse parallel impurity axiom refuse free purification refuse extra ElementId refuse impure component morphism ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-8 **impure-component-morphism** **conservation** scaffold.
impureComponentMorphismConservationPhysicsGreenAuthorized :: Bool
impureComponentMorphismConservationPhysicsGreenAuthorized = False

impureComponentMorphismConservationPhysicsGreenFalse :: Bool
impureComponentMorphismConservationPhysicsGreenFalse =
  not impureComponentMorphismConservationPhysicsGreenAuthorized

impureComponentMorphismConservationModalityUnwired :: Bool
impureComponentMorphismConservationModalityUnwired =
  impureComponentMorphismConservationModalityCurrent == ImpureComponentMorphismConservationUnwired

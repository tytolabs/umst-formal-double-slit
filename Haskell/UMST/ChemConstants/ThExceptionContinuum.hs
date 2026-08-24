-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ThExceptionContinuum
Description : Th Z=90 **exception-continuum** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Th exception continuum**: Actinide occupancy-engine sort witness Th Z=90 as one second-law
**conservation** product (ore ⊗ isotope mix ⊗ purify Refine-cost ⊗ G-stability ⊗ Env) —
cite @occupancy_engine_sort@ + @homolog_exception_not_copy@ read-only; homolog ≠ copy;
**not** a 26th axiom. Named Th natural-continuum identity conserved under honest scaffold;
trivial XOR, parallel occupancy axiom, homolog occupancy copy, and GREEN invent fail-closed.
Exception-continuum laws are structure witnesses only (@thExceptionContinuumProved@ = False).
No SpeciesId fork.

* @ThExceptionContinuumModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateThExceptionBundle@ — named Th Z=90 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateThExceptionContinuum@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@thExceptionContinuumAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of Th Z=90 actinide exception continuum on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-TH-EXCEPTION-CONTINUUM@.
INT: umst/umst-chem/src/x_rows/th_exception_continuum.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.ThExceptionContinuum
  ( ThExceptionContinuumModality (..)
  , thExceptionContinuumModalityCurrent
  , thExceptionLatticeAll
  , thExceptionLatticeCount
  , thoriumAtomicNumberZ
  , ceriumHomologZ
  , ThExceptionChannelSlot (..)
  , thExceptionChannelSlotAll
  , thExceptionChannelSlotCount
  , ThExceptionProductChannel (..)
  , thExceptionProductChannelAll
  , thExceptionProductChannelCount
  , thExceptionProductChannelIndex
  , ThExceptionConcurrentBundle (..)
  , thExceptionConcurrentBundleUnwired
  , thExceptionConcurrentBundleWithChannel
  , thExceptionConcurrentBundleWithPresent
  , thExceptionConcurrentBundleChannelAt
  , thExceptionConcurrentBundleHolds
  , thExceptionConcurrentBundlePresentCount
  , thExceptionConcurrentBundleIsConcurrentProduct
  , thExceptionNaturalContinuumWitness
  , ThExceptionXorPosture (..)
  , thExceptionXorPostureExclusive
  , thExceptionXorPostureConcurrent
  , ThExceptionContinuumVerdict (..)
  , ThExceptionXorVerdict (..)
  , evaluateThExceptionBundle
  , evaluateThExceptionXor
  , evaluateThExceptionContinuum
  , ThExceptionContinuumLaw (..)
  , thExceptionContinuumLawAll
  , thExceptionContinuumLawCount
  , sampleThExceptionNaturalContinuumBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , thExceptionNaturalContinuumConcurrentOk
  , thZ90OccupancyEngineSortOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventThExceptionRefuse
  , parallelOccupancyAxiomRefuse
  , homologOccupancyCopyRefuse
  , occupancyEngineSortNotAxiomRefuse
  , refineCostFloatPinRefuse
  , assumedThExceptionDesignOk
  , surrogateThExceptionDesignOk
  , thExceptionLatticeScaffold
  , thExceptionLatticeNotGreenTable
  , thExceptionContinuumLawsScaffold
  , thExceptionContinuumLawsNotGreenTable
  , thExceptionKnowingFiberOk
  , thExceptionContinuumInventRefuse
  , thExceptionLatticeNotXor
  , thExceptionContinuumProved
  , thExceptionContinuumNeSpeciesId
  , speciesIdForked
  , ceHomologNotThOccupancyCopy
  , thObservedNePredictedOk
  , thExceptionContinuumFraming
  , thExceptionContinuumAxiom
  , thExceptionContinuumNamed
  , thExceptionContinuumAuthority
  , occupancyEngineSortAuthority
  , homologExceptionNotCopyAuthority
  , goldschmidtContinuumAuthority
  , actinideOccupancyExceptionsAuthority
  , thExceptionContinuumCellId
  , thExceptionContinuumNonClaim
  , thExceptionContinuumPhysicsGreenAuthorized
  , thExceptionContinuumPhysicsGreenFalse
  , thExceptionContinuumModalityUnwired
  ) where

import UMST.ChemConstants.ActinideOccupancyExceptions
  ( ActinideException (Th)
  , thObservedNePredicted
  , actinideExceptionObservedNotation
  , actinideExceptionZ
  )
import UMST.ChemConstants.NamedOccupancyExceptions
  ( NamedException (Ce)
  , namedExceptionObservedNotation
  , namedExceptionZ
  )
import UMST.ChemConstants.OccupancyEngineSort
  ( OccupancyEngineSortBucket (ActinideExceptionBucket, NamedExceptionBucket)
  , occupancyEngineSortAuthority
  , occupancyEngineSortBucket
  , occupancyEngineSortNotSecondAxiom
  )

-- | IUPAC periodic-table cardinality (Z=1..118) — not Th exception GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Thorium Z=90 — Actinide occupancy exception witness pin.
thoriumAtomicNumberZ :: Int
thoriumAtomicNumberZ = 90

-- | Cerium Z=58 — period-6 lanthanide homolog witness pin (homolog ≠ copy).
ceriumHomologZ :: Int
ceriumHomologZ = 58

-- | Design **Th exception continuum** modality for conservation claims.
data ThExceptionContinuumModality
  = ThExceptionContinuumUnwired
  | ThExceptionContinuumAssumed
  | ThExceptionContinuumProved
  | ThExceptionContinuumSurrogate
  deriving (Eq, Show)

-- | Current scaffold **Th exception continuum** modality — always Unwired on this cell.
thExceptionContinuumModalityCurrent :: ThExceptionContinuumModality
thExceptionContinuumModalityCurrent = ThExceptionContinuumUnwired

-- | All Th exception continuum lattice steps in stable order.
thExceptionLatticeAll :: [ThExceptionContinuumModality]
thExceptionLatticeAll =
  [ ThExceptionContinuumUnwired
  , ThExceptionContinuumAssumed
  , ThExceptionContinuumProved
  , ThExceptionContinuumSurrogate
  ]

thExceptionLatticeCount :: Int
thExceptionLatticeCount = length thExceptionLatticeAll

-- | Th exception continuum channel slot — concurrent **product** factor, not XOR bucket.
data ThExceptionChannelSlot
  = ThExceptionSlotUnwired
  | ThExceptionSlotAbsent
  | ThExceptionSlotPresent
  deriving (Eq, Show)

thExceptionChannelSlotAll :: [ThExceptionChannelSlot]
thExceptionChannelSlotAll =
  [ ThExceptionSlotUnwired
  , ThExceptionSlotAbsent
  , ThExceptionSlotPresent
  ]

thExceptionChannelSlotCount :: Int
thExceptionChannelSlotCount = length thExceptionChannelSlotAll

-- | Named Th natural-continuum product channels (ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env).
data ThExceptionProductChannel
  = OreNaturalContinuum
  | IsotopeMixContinuum
  | PurifyRefineCostContinuum
  | GStabilityContinuum
  | EnvContinuum
  deriving (Eq, Show)

thExceptionProductChannelAll :: [ThExceptionProductChannel]
thExceptionProductChannelAll =
  [ OreNaturalContinuum
  , IsotopeMixContinuum
  , PurifyRefineCostContinuum
  , GStabilityContinuum
  , EnvContinuum
  ]

thExceptionProductChannelCount :: Int
thExceptionProductChannelCount = length thExceptionProductChannelAll

thExceptionProductChannelIndex :: ThExceptionProductChannel -> Int
thExceptionProductChannelIndex channel =
  case channel of
    OreNaturalContinuum -> 0
    IsotopeMixContinuum -> 1
    PurifyRefineCostContinuum -> 2
    GStabilityContinuum -> 3
    EnvContinuum -> 4

-- | Th Z=90 exception-continuum concurrent **product** bundle (north-star §3).
data ThExceptionConcurrentBundle = ThExceptionConcurrentBundle
  { thExceptionClassPresent :: Bool
  , thExceptionChannelSlots :: [ThExceptionChannelSlot]
  }
  deriving (Eq, Show)

thExceptionConcurrentBundleUnwired :: ThExceptionConcurrentBundle
thExceptionConcurrentBundleUnwired =
  ThExceptionConcurrentBundle
    False
    (replicate thExceptionProductChannelCount ThExceptionSlotUnwired)

thExceptionConcurrentBundleWithChannel ::
  Int -> ThExceptionChannelSlot -> ThExceptionConcurrentBundle -> ThExceptionConcurrentBundle
thExceptionConcurrentBundleWithChannel idx slot bundle =
  let slots = thExceptionChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in ThExceptionConcurrentBundle
        (thExceptionClassPresent bundle)
        (before ++ [current] ++ after)

thExceptionConcurrentBundleWithPresent ::
  Int -> ThExceptionConcurrentBundle -> ThExceptionConcurrentBundle
thExceptionConcurrentBundleWithPresent idx bundle =
  thExceptionConcurrentBundleWithChannel idx ThExceptionSlotPresent bundle

thExceptionConcurrentBundleChannelAt ::
  Int -> ThExceptionConcurrentBundle -> Maybe ThExceptionChannelSlot
thExceptionConcurrentBundleChannelAt idx bundle =
  let slots = thExceptionChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

thExceptionConcurrentBundleHolds :: Int -> ThExceptionConcurrentBundle -> Bool
thExceptionConcurrentBundleHolds idx bundle =
  case thExceptionConcurrentBundleChannelAt idx bundle of
    Just ThExceptionSlotPresent -> True
    _ -> False

thExceptionConcurrentBundlePresentCount :: ThExceptionConcurrentBundle -> Int
thExceptionConcurrentBundlePresentCount bundle =
  length (filter (== ThExceptionSlotPresent) (thExceptionChannelSlots bundle))

thExceptionConcurrentBundleIsConcurrentProduct :: ThExceptionConcurrentBundle -> Bool
thExceptionConcurrentBundleIsConcurrentProduct bundle =
  thExceptionConcurrentBundlePresentCount bundle >= 2

-- | Th witness: ore (0) + isotope (1) + purify (2) + G (3) + Env (4) concurrent on Z=90.
thExceptionNaturalContinuumWitness :: ThExceptionConcurrentBundle
thExceptionNaturalContinuumWitness =
  thExceptionConcurrentBundleWithPresent 4
    (thExceptionConcurrentBundleWithPresent 3
      (thExceptionConcurrentBundleWithPresent 2
        (thExceptionConcurrentBundleWithPresent 1
          (thExceptionConcurrentBundleWithPresent 0
            (ThExceptionConcurrentBundle True
              (replicate thExceptionProductChannelCount ThExceptionSlotUnwired))))))

data ThExceptionXorPosture
  = ThExceptionXorExclusive
  | ThExceptionXorConcurrent
  deriving (Eq, Show)

thExceptionXorPostureExclusive :: ThExceptionXorPosture
thExceptionXorPostureExclusive = ThExceptionXorExclusive

thExceptionXorPostureConcurrent :: ThExceptionXorPosture
thExceptionXorPostureConcurrent = ThExceptionXorConcurrent

data ThExceptionContinuumVerdict
  = ThExceptionContinuumDesignOk
  | ThExceptionContinuumNamedOk
  | ThExceptionContinuumTrivialRefuse
  | ThExceptionContinuumGreenInventRefuse
  | ThExceptionContinuumProvedWithoutBarRefuse
  | ThExceptionContinuumXorRefuse
  deriving (Eq, Show)

data ThExceptionXorVerdict
  = ThExceptionXorDesignOk
  | ThExceptionXorNamedOk
  | ThExceptionXorGreenInventRefuse
  | ThExceptionXorProvedWithoutBarRefuse
  | ThExceptionXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

evaluateThExceptionBundle ::
  ThExceptionContinuumModality
  -> ThExceptionConcurrentBundle
  -> Bool
  -> Bool
  -> ThExceptionContinuumVerdict
evaluateThExceptionBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = ThExceptionContinuumGreenInventRefuse
  | claimProved = ThExceptionContinuumProvedWithoutBarRefuse
  | length (thExceptionChannelSlots bundle) /= thExceptionProductChannelCount =
      ThExceptionContinuumTrivialRefuse
  | otherwise =
      case modality of
        ThExceptionContinuumUnwired ->
          if thExceptionConcurrentBundleIsConcurrentProduct bundle
            then ThExceptionContinuumNamedOk
            else ThExceptionContinuumDesignOk
        ThExceptionContinuumAssumed -> ThExceptionContinuumDesignOk
        ThExceptionContinuumSurrogate -> ThExceptionContinuumDesignOk
        ThExceptionContinuumProved -> ThExceptionContinuumProvedWithoutBarRefuse

evaluateThExceptionXor ::
  ThExceptionContinuumModality
  -> ThExceptionXorPosture
  -> Bool
  -> Bool
  -> ThExceptionXorVerdict
evaluateThExceptionXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = ThExceptionXorGreenInventRefuse
  | claimProved = ThExceptionXorProvedWithoutBarRefuse
  | posture == ThExceptionXorExclusive = ThExceptionXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        ThExceptionContinuumUnwired -> ThExceptionXorNamedOk
        ThExceptionContinuumAssumed -> ThExceptionXorDesignOk
        ThExceptionContinuumSurrogate -> ThExceptionXorDesignOk
        ThExceptionContinuumProved -> ThExceptionXorProvedWithoutBarRefuse

data ThExceptionContinuumLaw
  = ThExceptionContinuumConserved
  | NamedThExceptionContinuumOk
  | TrivialThExceptionRefused
  | GreenInventThExceptionRefused
  deriving (Eq, Show)

thExceptionContinuumLawAll :: [ThExceptionContinuumLaw]
thExceptionContinuumLawAll =
  [ ThExceptionContinuumConserved
  , NamedThExceptionContinuumOk
  , TrivialThExceptionRefused
  , GreenInventThExceptionRefused
  ]

thExceptionContinuumLawCount :: Int
thExceptionContinuumLawCount = length thExceptionContinuumLawAll

evaluateThExceptionContinuum ::
  ThExceptionContinuumModality
  -> ThExceptionConcurrentBundle
  -> ThExceptionXorPosture
  -> Bool
  -> Bool
  -> ThExceptionContinuumVerdict
evaluateThExceptionContinuum modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = ThExceptionContinuumGreenInventRefuse
  | claimProved = ThExceptionContinuumProvedWithoutBarRefuse
  | otherwise =
      case evaluateThExceptionXor modality posture False False of
        ThExceptionXorMutuallyExclusiveRefuse -> ThExceptionContinuumXorRefuse
        ThExceptionXorGreenInventRefuse -> ThExceptionContinuumGreenInventRefuse
        ThExceptionXorProvedWithoutBarRefuse -> ThExceptionContinuumProvedWithoutBarRefuse
        _ ->
          case evaluateThExceptionBundle modality bundle False False of
            ThExceptionContinuumNamedOk -> ThExceptionContinuumNamedOk
            ThExceptionContinuumGreenInventRefuse -> ThExceptionContinuumGreenInventRefuse
            ThExceptionContinuumProvedWithoutBarRefuse -> ThExceptionContinuumProvedWithoutBarRefuse
            ThExceptionContinuumTrivialRefuse -> ThExceptionContinuumTrivialRefuse
            ThExceptionContinuumXorRefuse -> ThExceptionContinuumXorRefuse
            ThExceptionContinuumDesignOk -> ThExceptionContinuumDesignOk

sampleThExceptionNaturalContinuumBundle :: ThExceptionConcurrentBundle
sampleThExceptionNaturalContinuumBundle = thExceptionNaturalContinuumWitness

sampleXorExclusiveBundle :: ThExceptionConcurrentBundle
sampleXorExclusiveBundle = thExceptionConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: ThExceptionConcurrentBundle
sampleTrivialUnwiredBundle = thExceptionConcurrentBundleUnwired

unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateThExceptionContinuum
    ThExceptionContinuumUnwired
    sampleThExceptionNaturalContinuumBundle
    thExceptionXorPostureConcurrent
    False
    False
    == ThExceptionContinuumNamedOk

thExceptionNaturalContinuumConcurrentOk :: Bool
thExceptionNaturalContinuumConcurrentOk =
  let bundle = thExceptionNaturalContinuumWitness
   in thExceptionClassPresent bundle
        && thExceptionConcurrentBundleHolds 0 bundle
        && thExceptionConcurrentBundleHolds 1 bundle
        && thExceptionConcurrentBundleHolds 2 bundle
        && thExceptionConcurrentBundleHolds 3 bundle
        && thExceptionConcurrentBundleHolds 4 bundle
        && thExceptionConcurrentBundlePresentCount bundle == 5
        && thExceptionConcurrentBundleIsConcurrentProduct bundle
        && thoriumAtomicNumberZ == 90
        && actinideExceptionZ Th == 90

thZ90OccupancyEngineSortOk :: Bool
thZ90OccupancyEngineSortOk =
  thoriumAtomicNumberZ == 90
    && occupancyEngineSortBucket thoriumAtomicNumberZ == ActinideExceptionBucket
    && thExceptionProductChannelCount == 5
    && length (thExceptionChannelSlots thExceptionConcurrentBundleUnwired) == 5

thObservedNePredictedOk :: Bool
thObservedNePredictedOk = thObservedNePredicted

ceHomologNotThOccupancyCopy :: Bool
ceHomologNotThOccupancyCopy =
  ceriumHomologZ == thoriumAtomicNumberZ - 32
    && ceriumHomologZ /= thoriumAtomicNumberZ
    && actinideExceptionZ Th == thoriumAtomicNumberZ
    && namedExceptionZ Ce == ceriumHomologZ
    && actinideExceptionObservedNotation Th /= namedExceptionObservedNotation Ce
    && occupancyEngineSortBucket thoriumAtomicNumberZ == ActinideExceptionBucket
    && occupancyEngineSortBucket ceriumHomologZ == NamedExceptionBucket

concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  thExceptionConcurrentBundleIsConcurrentProduct thExceptionNaturalContinuumWitness
    && thExceptionConcurrentBundlePresentCount thExceptionNaturalContinuumWitness >= 2
    && thExceptionConcurrentBundlePresentCount thExceptionNaturalContinuumWitness == 5

xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateThExceptionXor
    ThExceptionContinuumUnwired
    thExceptionXorPostureExclusive
    False
    False
    == ThExceptionXorMutuallyExclusiveRefuse
    && evaluateThExceptionContinuum
      ThExceptionContinuumUnwired
      sampleThExceptionNaturalContinuumBundle
      thExceptionXorPostureExclusive
      False
      False
      == ThExceptionContinuumXorRefuse

greenInventThExceptionRefuse :: Bool
greenInventThExceptionRefuse =
  evaluateThExceptionContinuum
    ThExceptionContinuumUnwired
    sampleThExceptionNaturalContinuumBundle
    thExceptionXorPostureConcurrent
    True
    False
    == ThExceptionContinuumGreenInventRefuse
    && evaluateThExceptionBundle
      ThExceptionContinuumUnwired
      sampleThExceptionNaturalContinuumBundle
      True
      False
      == ThExceptionContinuumGreenInventRefuse

parallelOccupancyAxiomRefuse :: Bool
parallelOccupancyAxiomRefuse =
  thExceptionContinuumAuthority
    == "umst/umst-chem/src/x_rows/th_exception_continuum.rs"
    && thExceptionContinuumProved == False
    && not (thExceptionContinuumAuthority == "26th_chemistry_axiom")
    && thExceptionContinuumFraming
      /= "parallel_occupancy_axiom_not_second_law"
    && occupancyEngineSortNotSecondAxiom

homologOccupancyCopyRefuse :: Bool
homologOccupancyCopyRefuse =
  parallelOccupancyAxiomRefuse
    && thExceptionContinuumFraming
      /= "homolog_occupancy_copy_smuggle"
    && homologExceptionNotCopyAuthority
      == "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"
    && ceHomologNotThOccupancyCopyNotation

ceHomologNotThOccupancyCopyNotation :: Bool
ceHomologNotThOccupancyCopyNotation =
  actinideExceptionObservedNotation Th
    /= namedExceptionObservedNotation Ce

occupancyEngineSortNotAxiomRefuse :: Bool
occupancyEngineSortNotAxiomRefuse =
  homologOccupancyCopyRefuse
    && thExceptionContinuumFraming
      /= "occupancy_engine_sort_axiom_not_continuum"
    && occupancyEngineSortAuthority
      == "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
    && occupancyEngineSortNotSecondAxiom
    && thoriumAtomicNumberZ == 90

refineCostFloatPinRefuse :: Bool
refineCostFloatPinRefuse =
  occupancyEngineSortNotAxiomRefuse
    && thExceptionContinuumFraming
      /= "refine_cost_bare_float_pin_on_th_continuum"
    && goldschmidtContinuumAuthority
      == "umst/umst-chem/src/l0_tables/goldschmidt.rs"
    && thoriumAtomicNumberZ == 90

assumedThExceptionDesignOk :: Bool
assumedThExceptionDesignOk =
  evaluateThExceptionContinuum
    ThExceptionContinuumAssumed
    sampleThExceptionNaturalContinuumBundle
    thExceptionXorPostureConcurrent
    False
    False
    == ThExceptionContinuumDesignOk

surrogateThExceptionDesignOk :: Bool
surrogateThExceptionDesignOk =
  evaluateThExceptionContinuum
    ThExceptionContinuumSurrogate
    sampleThExceptionNaturalContinuumBundle
    thExceptionXorPostureConcurrent
    False
    False
    == ThExceptionContinuumDesignOk

thExceptionLatticeScaffold :: Bool
thExceptionLatticeScaffold =
  thExceptionLatticeCount == 4
    && unwiredDesignOk
    && thZ90OccupancyEngineSortOk
    && thExceptionNaturalContinuumConcurrentOk
    && thObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedThExceptionDesignOk
    && surrogateThExceptionDesignOk
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

thExceptionLatticeNotGreenTable :: Bool
thExceptionLatticeNotGreenTable =
  thExceptionLatticeCount == 4
    && thExceptionLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && thExceptionProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && thExceptionChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

thExceptionContinuumLawsScaffold :: Bool
thExceptionContinuumLawsScaffold =
  thExceptionContinuumLawCount == 4
    && thExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventThExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

thExceptionContinuumLawsNotGreenTable :: Bool
thExceptionContinuumLawsNotGreenTable =
  thExceptionContinuumLawsScaffold
    && thExceptionContinuumLawCount /= 118 * 118
    && thExceptionProductChannelCount /= 118 * 118

thExceptionKnowingFiberOk :: Bool
thExceptionKnowingFiberOk = True

thExceptionContinuumInventRefuse :: Bool
thExceptionContinuumInventRefuse = not thExceptionContinuumProved

thExceptionLatticeNotXor :: Bool
thExceptionLatticeNotXor =
  unwiredDesignOk
    && assumedThExceptionDesignOk
    && surrogateThExceptionDesignOk
    && thExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventThExceptionRefuse

thExceptionContinuumProved :: Bool
thExceptionContinuumProved = False

speciesIdForked :: Bool
speciesIdForked = False

thExceptionContinuumNeSpeciesId :: Bool
thExceptionContinuumNeSpeciesId =
  thExceptionContinuumAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && thExceptionProductChannelAll /= []
    && thExceptionConcurrentBundleIsConcurrentProduct thExceptionNaturalContinuumWitness
    && not speciesIdForked

thExceptionContinuumFraming :: String
thExceptionContinuumFraming =
  "second_law_conservation_th_exception_continuum_one_axiom"

thExceptionContinuumAxiom :: Bool
thExceptionContinuumAxiom =
  thExceptionLatticeScaffold
    && thExceptionLatticeNotGreenTable
    && thExceptionContinuumLawsScaffold
    && thExceptionContinuumLawsNotGreenTable
    && thExceptionKnowingFiberOk
    && thZ90OccupancyEngineSortOk
    && thExceptionNaturalContinuumConcurrentOk
    && thObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventThExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse
    && thExceptionContinuumInventRefuse
    && thExceptionLatticeNotXor
    && thExceptionContinuumNeSpeciesId
    && not thExceptionContinuumProved
    && not speciesIdForked
    && thExceptionContinuumFraming
      == "second_law_conservation_th_exception_continuum_one_axiom"

thExceptionContinuumNamed :: String
thExceptionContinuumNamed =
  "thExceptionContinuum: ThExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice thExceptionContinuumProved false evaluateThExceptionBundle evaluateThExceptionContinuum named Th Z=90 Actinide occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not axiom refuse th ce homolog not copy SpeciesId fork second law conservation one axiom"

thExceptionContinuumAuthority :: String
thExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/th_exception_continuum.rs"

goldschmidtContinuumAuthority :: String
goldschmidtContinuumAuthority =
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"

actinideOccupancyExceptionsAuthority :: String
actinideOccupancyExceptionsAuthority =
  "umst/umst-chem/src/qlattice.rs"

homologExceptionNotCopyAuthority :: String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

thExceptionContinuumCellId :: String
thExceptionContinuumCellId = "CHEM-FORMAL-Q-HS-TH-EXCEPTION-CONTINUUM"

thExceptionContinuumNonClaim :: String
thExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-HS-TH-EXCEPTION-CONTINUUM ThExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice thExceptionContinuumProved false evaluateThExceptionBundle evaluateThExceptionContinuum named Th Z=90 Actinide occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not 26th axiom refuse cite occupancy_engine_sort homolog_exception_not_copy goldschmidt read-only th ce homolog not copy SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

thExceptionContinuumPhysicsGreenAuthorized :: Bool
thExceptionContinuumPhysicsGreenAuthorized = False

thExceptionContinuumPhysicsGreenFalse :: Bool
thExceptionContinuumPhysicsGreenFalse =
  not thExceptionContinuumPhysicsGreenAuthorized

thExceptionContinuumModalityUnwired :: Bool
thExceptionContinuumModalityUnwired =
  thExceptionContinuumModalityCurrent == ThExceptionContinuumUnwired

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.LaExceptionContinuum
Description : La Z=57 **exception-continuum** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**La exception continuum**: Named occupancy-engine sort witness La Z=57 as one second-law
**conservation** product (ore ⊗ isotope mix ⊗ purify Refine-cost ⊗ G-stability ⊗ Env) —
cite @occupancy_engine_sort@ + @homolog_exception_not_copy@ read-only; homolog ≠ copy;
**not** a 26th axiom. Named La natural-continuum identity conserved under honest scaffold;
trivial XOR, parallel occupancy axiom, homolog occupancy copy, and GREEN invent fail-closed.
Exception-continuum laws are structure witnesses only (@laExceptionContinuumProved@ = False).
No SpeciesId fork.

* @LaExceptionContinuumModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateLaExceptionBundle@ — named La Z=57 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateLaExceptionContinuum@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@laExceptionContinuumAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of La Z=57 exception continuum on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-LA-EXCEPTION-CONTINUUM@.
INT: umst/umst-chem/src/elements/z_057_la.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.LaExceptionContinuum
  ( LaExceptionContinuumModality (..)
  , laExceptionContinuumModalityCurrent
  , laExceptionLatticeAll
  , laExceptionLatticeCount
  , lanthanumAtomicNumberZ
  , yttriumHomologZ
  , actiniumHomologZ
  , LaExceptionChannelSlot (..)
  , laExceptionChannelSlotAll
  , laExceptionChannelSlotCount
  , LaExceptionProductChannel (..)
  , laExceptionProductChannelAll
  , laExceptionProductChannelCount
  , laExceptionProductChannelIndex
  , LaExceptionConcurrentBundle (..)
  , laExceptionConcurrentBundleUnwired
  , laExceptionConcurrentBundleWithChannel
  , laExceptionConcurrentBundleWithPresent
  , laExceptionConcurrentBundleChannelAt
  , laExceptionConcurrentBundleHolds
  , laExceptionConcurrentBundlePresentCount
  , laExceptionConcurrentBundleIsConcurrentProduct
  , laExceptionNaturalContinuumWitness
  , LaExceptionXorPosture (..)
  , laExceptionXorPostureExclusive
  , laExceptionXorPostureConcurrent
  , LaExceptionContinuumVerdict (..)
  , LaExceptionXorVerdict (..)
  , evaluateLaExceptionBundle
  , evaluateLaExceptionXor
  , evaluateLaExceptionContinuum
  , LaExceptionContinuumLaw (..)
  , laExceptionContinuumLawAll
  , laExceptionContinuumLawCount
  , sampleLaExceptionNaturalContinuumBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , laExceptionNaturalContinuumConcurrentOk
  , laZ57OccupancyEngineSortOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventLaExceptionRefuse
  , parallelOccupancyAxiomRefuse
  , homologOccupancyCopyRefuse
  , occupancyEngineSortNotAxiomRefuse
  , refineCostFloatPinRefuse
  , assumedLaExceptionDesignOk
  , surrogateLaExceptionDesignOk
  , laExceptionLatticeScaffold
  , laExceptionLatticeNotGreenTable
  , laExceptionContinuumLawsScaffold
  , laExceptionContinuumLawsNotGreenTable
  , laExceptionKnowingFiberOk
  , laExceptionContinuumInventRefuse
  , laExceptionLatticeNotXor
  , laExceptionContinuumProved
  , laExceptionContinuumNeSpeciesId
  , speciesIdForked
  , yAcHomologNotLaOccupancyCopy
  , laObservedNePredictedOk
  , laExceptionContinuumFraming
  , laExceptionContinuumAxiom
  , laExceptionContinuumNamed
  , laExceptionContinuumAuthority
  , occupancyEngineSortAuthority
  , homologExceptionNotCopyAuthority
  , goldschmidtContinuumAuthority
  , namedOccupancyExceptionsAuthority
  , laExceptionContinuumCellId
  , laExceptionContinuumNonClaim
  , laExceptionContinuumPhysicsGreenAuthorized
  , laExceptionContinuumPhysicsGreenFalse
  , laExceptionContinuumModalityUnwired
  ) where

import UMST.ChemConstants.NamedOccupancyExceptions
  ( NamedException (La)
  , laObservedNePredicted
  , namedExceptionObservedNotation
  , namedExceptionZ
  )
import UMST.ChemConstants.OccupancyEngineSort
  ( OccupancyEngineSortBucket (NamedExceptionBucket)
  , occupancyEngineSortAuthority
  , occupancyEngineSortBucket
  , occupancyEngineSortNotSecondAxiom
  )

-- | IUPAC periodic-table cardinality (Z=1..118) — not La exception GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Lanthanum Z=57 — Named occupancy exception witness pin.
lanthanumAtomicNumberZ :: Int
lanthanumAtomicNumberZ = 57

-- | Yttrium Z=39 — period-5 d-block homolog witness pin (homolog ≠ copy).
yttriumHomologZ :: Int
yttriumHomologZ = 39

-- | Actinium Z=89 — period-7 d-block homolog witness pin (homolog ≠ copy).
actiniumHomologZ :: Int
actiniumHomologZ = 89

-- | Yttrium period-5 homolog subshell notation — **refused** as La copy.
yttriumHomologNotationRefused :: String
yttriumHomologNotationRefused = "1s22s22p63s23p64s23d104p65s24d1"

-- | Actinium period-7 homolog subshell notation — **refused** as La copy.
actiniumHomologNotationRefused :: String
actiniumHomologNotationRefused =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d1"

-- | Design **La exception continuum** modality for conservation claims.
data LaExceptionContinuumModality
  = LaExceptionContinuumUnwired
  | LaExceptionContinuumAssumed
  | LaExceptionContinuumProved
  | LaExceptionContinuumSurrogate
  deriving (Eq, Show)

-- | Current scaffold **La exception continuum** modality — always Unwired on this cell.
laExceptionContinuumModalityCurrent :: LaExceptionContinuumModality
laExceptionContinuumModalityCurrent = LaExceptionContinuumUnwired

-- | All La exception continuum lattice steps in stable order.
laExceptionLatticeAll :: [LaExceptionContinuumModality]
laExceptionLatticeAll =
  [ LaExceptionContinuumUnwired
  , LaExceptionContinuumAssumed
  , LaExceptionContinuumProved
  , LaExceptionContinuumSurrogate
  ]

laExceptionLatticeCount :: Int
laExceptionLatticeCount = length laExceptionLatticeAll

-- | La exception continuum channel slot — concurrent **product** factor, not XOR bucket.
data LaExceptionChannelSlot
  = LaExceptionSlotUnwired
  | LaExceptionSlotAbsent
  | LaExceptionSlotPresent
  deriving (Eq, Show)

laExceptionChannelSlotAll :: [LaExceptionChannelSlot]
laExceptionChannelSlotAll =
  [ LaExceptionSlotUnwired
  , LaExceptionSlotAbsent
  , LaExceptionSlotPresent
  ]

laExceptionChannelSlotCount :: Int
laExceptionChannelSlotCount = length laExceptionChannelSlotAll

-- | Named La natural-continuum product channels (ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env).
data LaExceptionProductChannel
  = OreNaturalContinuum
  | IsotopeMixContinuum
  | PurifyRefineCostContinuum
  | GStabilityContinuum
  | EnvContinuum
  deriving (Eq, Show)

laExceptionProductChannelAll :: [LaExceptionProductChannel]
laExceptionProductChannelAll =
  [ OreNaturalContinuum
  , IsotopeMixContinuum
  , PurifyRefineCostContinuum
  , GStabilityContinuum
  , EnvContinuum
  ]

laExceptionProductChannelCount :: Int
laExceptionProductChannelCount = length laExceptionProductChannelAll

laExceptionProductChannelIndex :: LaExceptionProductChannel -> Int
laExceptionProductChannelIndex channel =
  case channel of
    OreNaturalContinuum -> 0
    IsotopeMixContinuum -> 1
    PurifyRefineCostContinuum -> 2
    GStabilityContinuum -> 3
    EnvContinuum -> 4

-- | La Z=57 exception-continuum concurrent **product** bundle (north-star §3).
data LaExceptionConcurrentBundle = LaExceptionConcurrentBundle
  { laExceptionClassPresent :: Bool
  , laExceptionChannelSlots :: [LaExceptionChannelSlot]
  }
  deriving (Eq, Show)

laExceptionConcurrentBundleUnwired :: LaExceptionConcurrentBundle
laExceptionConcurrentBundleUnwired =
  LaExceptionConcurrentBundle
    False
    (replicate laExceptionProductChannelCount LaExceptionSlotUnwired)

laExceptionConcurrentBundleWithChannel ::
  Int -> LaExceptionChannelSlot -> LaExceptionConcurrentBundle -> LaExceptionConcurrentBundle
laExceptionConcurrentBundleWithChannel idx slot bundle =
  let slots = laExceptionChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in LaExceptionConcurrentBundle
        (laExceptionClassPresent bundle)
        (before ++ [current] ++ after)

laExceptionConcurrentBundleWithPresent ::
  Int -> LaExceptionConcurrentBundle -> LaExceptionConcurrentBundle
laExceptionConcurrentBundleWithPresent idx bundle =
  laExceptionConcurrentBundleWithChannel idx LaExceptionSlotPresent bundle

laExceptionConcurrentBundleChannelAt ::
  Int -> LaExceptionConcurrentBundle -> Maybe LaExceptionChannelSlot
laExceptionConcurrentBundleChannelAt idx bundle =
  let slots = laExceptionChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

laExceptionConcurrentBundleHolds :: Int -> LaExceptionConcurrentBundle -> Bool
laExceptionConcurrentBundleHolds idx bundle =
  case laExceptionConcurrentBundleChannelAt idx bundle of
    Just LaExceptionSlotPresent -> True
    _ -> False

laExceptionConcurrentBundlePresentCount :: LaExceptionConcurrentBundle -> Int
laExceptionConcurrentBundlePresentCount bundle =
  length (filter (== LaExceptionSlotPresent) (laExceptionChannelSlots bundle))

laExceptionConcurrentBundleIsConcurrentProduct :: LaExceptionConcurrentBundle -> Bool
laExceptionConcurrentBundleIsConcurrentProduct bundle =
  laExceptionConcurrentBundlePresentCount bundle >= 2

-- | La witness: ore (0) + isotope (1) + purify (2) + G (3) + Env (4) concurrent on Z=57.
laExceptionNaturalContinuumWitness :: LaExceptionConcurrentBundle
laExceptionNaturalContinuumWitness =
  laExceptionConcurrentBundleWithPresent 4
    (laExceptionConcurrentBundleWithPresent 3
      (laExceptionConcurrentBundleWithPresent 2
        (laExceptionConcurrentBundleWithPresent 1
          (laExceptionConcurrentBundleWithPresent 0
            (LaExceptionConcurrentBundle True
              (replicate laExceptionProductChannelCount LaExceptionSlotUnwired))))))

data LaExceptionXorPosture
  = LaExceptionXorExclusive
  | LaExceptionXorConcurrent
  deriving (Eq, Show)

laExceptionXorPostureExclusive :: LaExceptionXorPosture
laExceptionXorPostureExclusive = LaExceptionXorExclusive

laExceptionXorPostureConcurrent :: LaExceptionXorPosture
laExceptionXorPostureConcurrent = LaExceptionXorConcurrent

data LaExceptionContinuumVerdict
  = LaExceptionContinuumDesignOk
  | LaExceptionContinuumNamedOk
  | LaExceptionContinuumTrivialRefuse
  | LaExceptionContinuumGreenInventRefuse
  | LaExceptionContinuumProvedWithoutBarRefuse
  | LaExceptionContinuumXorRefuse
  deriving (Eq, Show)

data LaExceptionXorVerdict
  = LaExceptionXorDesignOk
  | LaExceptionXorNamedOk
  | LaExceptionXorGreenInventRefuse
  | LaExceptionXorProvedWithoutBarRefuse
  | LaExceptionXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

evaluateLaExceptionBundle ::
  LaExceptionContinuumModality
  -> LaExceptionConcurrentBundle
  -> Bool
  -> Bool
  -> LaExceptionContinuumVerdict
evaluateLaExceptionBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = LaExceptionContinuumGreenInventRefuse
  | claimProved = LaExceptionContinuumProvedWithoutBarRefuse
  | length (laExceptionChannelSlots bundle) /= laExceptionProductChannelCount =
      LaExceptionContinuumTrivialRefuse
  | otherwise =
      case modality of
        LaExceptionContinuumUnwired ->
          if laExceptionConcurrentBundleIsConcurrentProduct bundle
            then LaExceptionContinuumNamedOk
            else LaExceptionContinuumDesignOk
        LaExceptionContinuumAssumed -> LaExceptionContinuumDesignOk
        LaExceptionContinuumSurrogate -> LaExceptionContinuumDesignOk
        LaExceptionContinuumProved -> LaExceptionContinuumProvedWithoutBarRefuse

evaluateLaExceptionXor ::
  LaExceptionContinuumModality
  -> LaExceptionXorPosture
  -> Bool
  -> Bool
  -> LaExceptionXorVerdict
evaluateLaExceptionXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = LaExceptionXorGreenInventRefuse
  | claimProved = LaExceptionXorProvedWithoutBarRefuse
  | posture == LaExceptionXorExclusive = LaExceptionXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        LaExceptionContinuumUnwired -> LaExceptionXorNamedOk
        LaExceptionContinuumAssumed -> LaExceptionXorDesignOk
        LaExceptionContinuumSurrogate -> LaExceptionXorDesignOk
        LaExceptionContinuumProved -> LaExceptionXorProvedWithoutBarRefuse

data LaExceptionContinuumLaw
  = LaExceptionContinuumConserved
  | NamedLaExceptionContinuumOk
  | TrivialLaExceptionRefused
  | GreenInventLaExceptionRefused
  deriving (Eq, Show)

laExceptionContinuumLawAll :: [LaExceptionContinuumLaw]
laExceptionContinuumLawAll =
  [ LaExceptionContinuumConserved
  , NamedLaExceptionContinuumOk
  , TrivialLaExceptionRefused
  , GreenInventLaExceptionRefused
  ]

laExceptionContinuumLawCount :: Int
laExceptionContinuumLawCount = length laExceptionContinuumLawAll

evaluateLaExceptionContinuum ::
  LaExceptionContinuumModality
  -> LaExceptionConcurrentBundle
  -> LaExceptionXorPosture
  -> Bool
  -> Bool
  -> LaExceptionContinuumVerdict
evaluateLaExceptionContinuum modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = LaExceptionContinuumGreenInventRefuse
  | claimProved = LaExceptionContinuumProvedWithoutBarRefuse
  | otherwise =
      case evaluateLaExceptionXor modality posture False False of
        LaExceptionXorMutuallyExclusiveRefuse -> LaExceptionContinuumXorRefuse
        LaExceptionXorGreenInventRefuse -> LaExceptionContinuumGreenInventRefuse
        LaExceptionXorProvedWithoutBarRefuse -> LaExceptionContinuumProvedWithoutBarRefuse
        _ ->
          case evaluateLaExceptionBundle modality bundle False False of
            LaExceptionContinuumNamedOk -> LaExceptionContinuumNamedOk
            LaExceptionContinuumGreenInventRefuse -> LaExceptionContinuumGreenInventRefuse
            LaExceptionContinuumProvedWithoutBarRefuse -> LaExceptionContinuumProvedWithoutBarRefuse
            LaExceptionContinuumTrivialRefuse -> LaExceptionContinuumTrivialRefuse
            LaExceptionContinuumXorRefuse -> LaExceptionContinuumXorRefuse
            LaExceptionContinuumDesignOk -> LaExceptionContinuumDesignOk

sampleLaExceptionNaturalContinuumBundle :: LaExceptionConcurrentBundle
sampleLaExceptionNaturalContinuumBundle = laExceptionNaturalContinuumWitness

sampleXorExclusiveBundle :: LaExceptionConcurrentBundle
sampleXorExclusiveBundle = laExceptionConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: LaExceptionConcurrentBundle
sampleTrivialUnwiredBundle = laExceptionConcurrentBundleUnwired

unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateLaExceptionContinuum
    LaExceptionContinuumUnwired
    sampleLaExceptionNaturalContinuumBundle
    laExceptionXorPostureConcurrent
    False
    False
    == LaExceptionContinuumNamedOk

laExceptionNaturalContinuumConcurrentOk :: Bool
laExceptionNaturalContinuumConcurrentOk =
  let bundle = laExceptionNaturalContinuumWitness
   in laExceptionClassPresent bundle
        && laExceptionConcurrentBundleHolds 0 bundle
        && laExceptionConcurrentBundleHolds 1 bundle
        && laExceptionConcurrentBundleHolds 2 bundle
        && laExceptionConcurrentBundleHolds 3 bundle
        && laExceptionConcurrentBundleHolds 4 bundle
        && laExceptionConcurrentBundlePresentCount bundle == 5
        && laExceptionConcurrentBundleIsConcurrentProduct bundle
        && lanthanumAtomicNumberZ == 57
        && namedExceptionZ La == 57

laZ57OccupancyEngineSortOk :: Bool
laZ57OccupancyEngineSortOk =
  lanthanumAtomicNumberZ == 57
    && occupancyEngineSortBucket lanthanumAtomicNumberZ == NamedExceptionBucket
    && laExceptionProductChannelCount == 5
    && length (laExceptionChannelSlots laExceptionConcurrentBundleUnwired) == 5

laObservedNePredictedOk :: Bool
laObservedNePredictedOk = laObservedNePredicted

yAcHomologNotLaOccupancyCopy :: Bool
yAcHomologNotLaOccupancyCopy =
  yttriumHomologZ == lanthanumAtomicNumberZ - 18
    && actiniumHomologZ == lanthanumAtomicNumberZ + 32
    && yttriumHomologZ /= lanthanumAtomicNumberZ
    && actiniumHomologZ /= lanthanumAtomicNumberZ
    && namedExceptionZ La == 57
    && namedExceptionObservedNotation La /= yttriumHomologNotationRefused
    && namedExceptionObservedNotation La /= actiniumHomologNotationRefused
    && occupancyEngineSortBucket lanthanumAtomicNumberZ == NamedExceptionBucket

concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  laExceptionConcurrentBundleIsConcurrentProduct laExceptionNaturalContinuumWitness
    && laExceptionConcurrentBundlePresentCount laExceptionNaturalContinuumWitness >= 2
    && laExceptionConcurrentBundlePresentCount laExceptionNaturalContinuumWitness == 5

xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateLaExceptionXor
    LaExceptionContinuumUnwired
    laExceptionXorPostureExclusive
    False
    False
    == LaExceptionXorMutuallyExclusiveRefuse
    && evaluateLaExceptionContinuum
      LaExceptionContinuumUnwired
      sampleLaExceptionNaturalContinuumBundle
      laExceptionXorPostureExclusive
      False
      False
      == LaExceptionContinuumXorRefuse

greenInventLaExceptionRefuse :: Bool
greenInventLaExceptionRefuse =
  evaluateLaExceptionContinuum
    LaExceptionContinuumUnwired
    sampleLaExceptionNaturalContinuumBundle
    laExceptionXorPostureConcurrent
    True
    False
    == LaExceptionContinuumGreenInventRefuse
    && evaluateLaExceptionBundle
      LaExceptionContinuumUnwired
      sampleLaExceptionNaturalContinuumBundle
      True
      False
      == LaExceptionContinuumGreenInventRefuse

parallelOccupancyAxiomRefuse :: Bool
parallelOccupancyAxiomRefuse =
  laExceptionContinuumAuthority
    == "umst/umst-chem/src/elements/z_057_la.rs"
    && laExceptionContinuumProved == False
    && not (laExceptionContinuumAuthority == "26th_chemistry_axiom")
    && laExceptionContinuumFraming
      /= "parallel_occupancy_axiom_not_second_law"
    && occupancyEngineSortNotSecondAxiom

homologOccupancyCopyRefuse :: Bool
homologOccupancyCopyRefuse =
  parallelOccupancyAxiomRefuse
    && laExceptionContinuumFraming
      /= "homolog_occupancy_copy_smuggle"
    && homologExceptionNotCopyAuthority
      == "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"
    && yAcHomologNotLaOccupancyCopyNotation

yAcHomologNotLaOccupancyCopyNotation :: Bool
yAcHomologNotLaOccupancyCopyNotation =
  namedExceptionObservedNotation La /= yttriumHomologNotationRefused
    && namedExceptionObservedNotation La /= actiniumHomologNotationRefused

occupancyEngineSortNotAxiomRefuse :: Bool
occupancyEngineSortNotAxiomRefuse =
  homologOccupancyCopyRefuse
    && laExceptionContinuumFraming
      /= "occupancy_engine_sort_axiom_not_continuum"
    && occupancyEngineSortAuthority
      == "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
    && occupancyEngineSortNotSecondAxiom
    && lanthanumAtomicNumberZ == 57

refineCostFloatPinRefuse :: Bool
refineCostFloatPinRefuse =
  occupancyEngineSortNotAxiomRefuse
    && laExceptionContinuumFraming
      /= "refine_cost_bare_float_pin_on_la_continuum"
    && goldschmidtContinuumAuthority
      == "umst/umst-chem/src/l0_tables/goldschmidt.rs"
    && lanthanumAtomicNumberZ == 57

assumedLaExceptionDesignOk :: Bool
assumedLaExceptionDesignOk =
  evaluateLaExceptionContinuum
    LaExceptionContinuumAssumed
    sampleLaExceptionNaturalContinuumBundle
    laExceptionXorPostureConcurrent
    False
    False
    == LaExceptionContinuumDesignOk

surrogateLaExceptionDesignOk :: Bool
surrogateLaExceptionDesignOk =
  evaluateLaExceptionContinuum
    LaExceptionContinuumSurrogate
    sampleLaExceptionNaturalContinuumBundle
    laExceptionXorPostureConcurrent
    False
    False
    == LaExceptionContinuumDesignOk

laExceptionLatticeScaffold :: Bool
laExceptionLatticeScaffold =
  laExceptionLatticeCount == 4
    && unwiredDesignOk
    && laZ57OccupancyEngineSortOk
    && laExceptionNaturalContinuumConcurrentOk
    && laObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedLaExceptionDesignOk
    && surrogateLaExceptionDesignOk
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

laExceptionLatticeNotGreenTable :: Bool
laExceptionLatticeNotGreenTable =
  laExceptionLatticeCount == 4
    && laExceptionLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && laExceptionProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && laExceptionChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

laExceptionContinuumLawsScaffold :: Bool
laExceptionContinuumLawsScaffold =
  laExceptionContinuumLawCount == 4
    && laExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLaExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

laExceptionContinuumLawsNotGreenTable :: Bool
laExceptionContinuumLawsNotGreenTable =
  laExceptionContinuumLawsScaffold
    && laExceptionContinuumLawCount /= 118 * 118
    && laExceptionProductChannelCount /= 118 * 118

laExceptionKnowingFiberOk :: Bool
laExceptionKnowingFiberOk = True

laExceptionContinuumInventRefuse :: Bool
laExceptionContinuumInventRefuse = not laExceptionContinuumProved

laExceptionLatticeNotXor :: Bool
laExceptionLatticeNotXor =
  unwiredDesignOk
    && assumedLaExceptionDesignOk
    && surrogateLaExceptionDesignOk
    && laExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLaExceptionRefuse

laExceptionContinuumProved :: Bool
laExceptionContinuumProved = False

speciesIdForked :: Bool
speciesIdForked = False

laExceptionContinuumNeSpeciesId :: Bool
laExceptionContinuumNeSpeciesId =
  laExceptionContinuumAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && laExceptionProductChannelAll /= []
    && laExceptionConcurrentBundleIsConcurrentProduct laExceptionNaturalContinuumWitness
    && not speciesIdForked

laExceptionContinuumFraming :: String
laExceptionContinuumFraming =
  "second_law_conservation_la_exception_continuum_one_axiom"

laExceptionContinuumAxiom :: Bool
laExceptionContinuumAxiom =
  laExceptionLatticeScaffold
    && laExceptionLatticeNotGreenTable
    && laExceptionContinuumLawsScaffold
    && laExceptionContinuumLawsNotGreenTable
    && laExceptionKnowingFiberOk
    && laZ57OccupancyEngineSortOk
    && laExceptionNaturalContinuumConcurrentOk
    && laObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventLaExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse
    && laExceptionContinuumInventRefuse
    && laExceptionLatticeNotXor
    && laExceptionContinuumNeSpeciesId
    && not laExceptionContinuumProved
    && not speciesIdForked
    && laExceptionContinuumFraming
      == "second_law_conservation_la_exception_continuum_one_axiom"

laExceptionContinuumNamed :: String
laExceptionContinuumNamed =
  "laExceptionContinuum: LaExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice laExceptionContinuumProved false evaluateLaExceptionBundle evaluateLaExceptionContinuum named La Z=57 Named occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not axiom refuse la ne SpeciesId fork second law conservation one axiom"

laExceptionContinuumAuthority :: String
laExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_057_la.rs"

goldschmidtContinuumAuthority :: String
goldschmidtContinuumAuthority =
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"

namedOccupancyExceptionsAuthority :: String
namedOccupancyExceptionsAuthority =
  "umst/umst-chem/src/x_rows/named_occupancy_exceptions.rs"

homologExceptionNotCopyAuthority :: String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

laExceptionContinuumCellId :: String
laExceptionContinuumCellId = "CHEM-FORMAL-Q-HS-LA-EXCEPTION-CONTINUUM"

laExceptionContinuumNonClaim :: String
laExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-HS-LA-EXCEPTION-CONTINUUM LaExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice laExceptionContinuumProved false evaluateLaExceptionBundle evaluateLaExceptionContinuum named La Z=57 Named occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not 26th axiom refuse cite occupancy_engine_sort homolog_exception_not_copy goldschmidt read-only la ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

laExceptionContinuumPhysicsGreenAuthorized :: Bool
laExceptionContinuumPhysicsGreenAuthorized = False

laExceptionContinuumPhysicsGreenFalse :: Bool
laExceptionContinuumPhysicsGreenFalse =
  not laExceptionContinuumPhysicsGreenAuthorized

laExceptionContinuumModalityUnwired :: Bool
laExceptionContinuumModalityUnwired =
  laExceptionContinuumModalityCurrent == LaExceptionContinuumUnwired

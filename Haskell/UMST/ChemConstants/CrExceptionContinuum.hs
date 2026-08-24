-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.CrExceptionContinuum
Description : Cr Z=24 **exception-continuum** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Cr exception continuum**: D-block occupancy-engine sort witness Cr Z=24 as one second-law
**conservation** product (ore ⊗ isotope mix ⊗ purify Refine-cost ⊗ G-stability ⊗ Env) —
cite @occupancy_engine_sort@ + @homolog_exception_not_copy@ read-only; homolog ≠ copy;
**not** a 26th axiom. Named Cr natural-continuum identity conserved under honest scaffold;
trivial XOR, parallel occupancy axiom, homolog occupancy copy, and GREEN invent fail-closed.
Exception-continuum laws are structure witnesses only (@crExceptionContinuumProved@ = False).
No SpeciesId fork.

* @CrExceptionContinuumModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateCrExceptionBundle@ — named Cr Z=24 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateCrExceptionContinuum@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@crExceptionContinuumAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of Cr Z=24 exception continuum on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-CR-EXCEPTION-CONTINUUM@.
INT: umst/umst-chem/src/x_rows/cr_exception_continuum.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.CrExceptionContinuum
  ( CrExceptionContinuumModality (..)
  , crExceptionContinuumModalityCurrent
  , crExceptionLatticeAll
  , crExceptionLatticeCount
  , chromiumAtomicNumberZ
  , molybdenumHomologZ
  , CrExceptionChannelSlot (..)
  , crExceptionChannelSlotAll
  , crExceptionChannelSlotCount
  , CrExceptionProductChannel (..)
  , crExceptionProductChannelAll
  , crExceptionProductChannelCount
  , crExceptionProductChannelIndex
  , CrExceptionConcurrentBundle (..)
  , crExceptionConcurrentBundleUnwired
  , crExceptionConcurrentBundleWithChannel
  , crExceptionConcurrentBundleWithPresent
  , crExceptionConcurrentBundleChannelAt
  , crExceptionConcurrentBundleHolds
  , crExceptionConcurrentBundlePresentCount
  , crExceptionConcurrentBundleIsConcurrentProduct
  , crExceptionNaturalContinuumWitness
  , CrExceptionXorPosture (..)
  , crExceptionXorPostureExclusive
  , crExceptionXorPostureConcurrent
  , CrExceptionContinuumVerdict (..)
  , CrExceptionXorVerdict (..)
  , evaluateCrExceptionBundle
  , evaluateCrExceptionXor
  , evaluateCrExceptionContinuum
  , CrExceptionContinuumLaw (..)
  , crExceptionContinuumLawAll
  , crExceptionContinuumLawCount
  , sampleCrExceptionNaturalContinuumBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , crExceptionNaturalContinuumConcurrentOk
  , crZ24OccupancyEngineSortOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventCrExceptionRefuse
  , parallelOccupancyAxiomRefuse
  , homologOccupancyCopyRefuse
  , occupancyEngineSortNotAxiomRefuse
  , refineCostFloatPinRefuse
  , assumedCrExceptionDesignOk
  , surrogateCrExceptionDesignOk
  , crExceptionLatticeScaffold
  , crExceptionLatticeNotGreenTable
  , crExceptionContinuumLawsScaffold
  , crExceptionContinuumLawsNotGreenTable
  , crExceptionKnowingFiberOk
  , crExceptionContinuumInventRefuse
  , crExceptionLatticeNotXor
  , crExceptionContinuumProved
  , crExceptionContinuumNeSpeciesId
  , speciesIdForked
  , moHomologNotCrOccupancyCopy
  , crObservedNePredictedOk
  , crExceptionContinuumFraming
  , crExceptionContinuumAxiom
  , crExceptionContinuumNamed
  , crExceptionContinuumAuthority
  , occupancyEngineSortAuthority
  , homologExceptionNotCopyAuthority
  , goldschmidtContinuumAuthority
  , dBlockOccupancyExceptionsAuthority
  , crExceptionContinuumCellId
  , crExceptionContinuumNonClaim
  , crExceptionContinuumPhysicsGreenAuthorized
  , crExceptionContinuumPhysicsGreenFalse
  , crExceptionContinuumModalityUnwired
  ) where

import UMST.ChemConstants.DBlockOccupancyExceptions
  ( DBlockException (Cr, Mo)
  , crObservedNePredicted
  , dBlockExceptionObservedNotation
  , dBlockExceptionZ
  )
import UMST.ChemConstants.OccupancyEngineSort
  ( OccupancyEngineSortBucket (DBlockExceptionBucket)
  , occupancyEngineSortAuthority
  , occupancyEngineSortBucket
  , occupancyEngineSortNotSecondAxiom
  )

-- | IUPAC periodic-table cardinality (Z=1..118) — not Cr exception GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Chromium Z=24 — D-block occupancy exception witness pin.
chromiumAtomicNumberZ :: Int
chromiumAtomicNumberZ = 24

-- | Molybdenum Z=42 — group-6 homolog witness pin (homolog ≠ copy).
molybdenumHomologZ :: Int
molybdenumHomologZ = 42

-- | Design **Cr exception continuum** modality for conservation claims.
data CrExceptionContinuumModality
  = CrExceptionContinuumUnwired
  | CrExceptionContinuumAssumed
  | CrExceptionContinuumProved
  | CrExceptionContinuumSurrogate
  deriving (Eq, Show)

-- | Current scaffold **Cr exception continuum** modality — always Unwired on this cell.
crExceptionContinuumModalityCurrent :: CrExceptionContinuumModality
crExceptionContinuumModalityCurrent = CrExceptionContinuumUnwired

-- | All Cr exception continuum lattice steps in stable order.
crExceptionLatticeAll :: [CrExceptionContinuumModality]
crExceptionLatticeAll =
  [ CrExceptionContinuumUnwired
  , CrExceptionContinuumAssumed
  , CrExceptionContinuumProved
  , CrExceptionContinuumSurrogate
  ]

crExceptionLatticeCount :: Int
crExceptionLatticeCount = length crExceptionLatticeAll

-- | Cr exception continuum channel slot — concurrent **product** factor, not XOR bucket.
data CrExceptionChannelSlot
  = CrExceptionSlotUnwired
  | CrExceptionSlotAbsent
  | CrExceptionSlotPresent
  deriving (Eq, Show)

crExceptionChannelSlotAll :: [CrExceptionChannelSlot]
crExceptionChannelSlotAll =
  [ CrExceptionSlotUnwired
  , CrExceptionSlotAbsent
  , CrExceptionSlotPresent
  ]

crExceptionChannelSlotCount :: Int
crExceptionChannelSlotCount = length crExceptionChannelSlotAll

-- | Named Cr natural-continuum product channels (ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env).
data CrExceptionProductChannel
  = OreNaturalContinuum
  | IsotopeMixContinuum
  | PurifyRefineCostContinuum
  | GStabilityContinuum
  | EnvContinuum
  deriving (Eq, Show)

crExceptionProductChannelAll :: [CrExceptionProductChannel]
crExceptionProductChannelAll =
  [ OreNaturalContinuum
  , IsotopeMixContinuum
  , PurifyRefineCostContinuum
  , GStabilityContinuum
  , EnvContinuum
  ]

crExceptionProductChannelCount :: Int
crExceptionProductChannelCount = length crExceptionProductChannelAll

crExceptionProductChannelIndex :: CrExceptionProductChannel -> Int
crExceptionProductChannelIndex channel =
  case channel of
    OreNaturalContinuum -> 0
    IsotopeMixContinuum -> 1
    PurifyRefineCostContinuum -> 2
    GStabilityContinuum -> 3
    EnvContinuum -> 4

-- | Cr Z=24 exception-continuum concurrent **product** bundle (north-star §3).
data CrExceptionConcurrentBundle = CrExceptionConcurrentBundle
  { crExceptionClassPresent :: Bool
  , crExceptionChannelSlots :: [CrExceptionChannelSlot]
  }
  deriving (Eq, Show)

crExceptionConcurrentBundleUnwired :: CrExceptionConcurrentBundle
crExceptionConcurrentBundleUnwired =
  CrExceptionConcurrentBundle
    False
    (replicate crExceptionProductChannelCount CrExceptionSlotUnwired)

crExceptionConcurrentBundleWithChannel ::
  Int -> CrExceptionChannelSlot -> CrExceptionConcurrentBundle -> CrExceptionConcurrentBundle
crExceptionConcurrentBundleWithChannel idx slot bundle =
  let slots = crExceptionChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in CrExceptionConcurrentBundle
        (crExceptionClassPresent bundle)
        (before ++ [current] ++ after)

crExceptionConcurrentBundleWithPresent ::
  Int -> CrExceptionConcurrentBundle -> CrExceptionConcurrentBundle
crExceptionConcurrentBundleWithPresent idx bundle =
  crExceptionConcurrentBundleWithChannel idx CrExceptionSlotPresent bundle

crExceptionConcurrentBundleChannelAt ::
  Int -> CrExceptionConcurrentBundle -> Maybe CrExceptionChannelSlot
crExceptionConcurrentBundleChannelAt idx bundle =
  let slots = crExceptionChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

crExceptionConcurrentBundleHolds :: Int -> CrExceptionConcurrentBundle -> Bool
crExceptionConcurrentBundleHolds idx bundle =
  case crExceptionConcurrentBundleChannelAt idx bundle of
    Just CrExceptionSlotPresent -> True
    _ -> False

crExceptionConcurrentBundlePresentCount :: CrExceptionConcurrentBundle -> Int
crExceptionConcurrentBundlePresentCount bundle =
  length (filter (== CrExceptionSlotPresent) (crExceptionChannelSlots bundle))

crExceptionConcurrentBundleIsConcurrentProduct :: CrExceptionConcurrentBundle -> Bool
crExceptionConcurrentBundleIsConcurrentProduct bundle =
  crExceptionConcurrentBundlePresentCount bundle >= 2

-- | Cr witness: ore (0) + isotope (1) + purify (2) + G (3) + Env (4) concurrent on Z=24.
crExceptionNaturalContinuumWitness :: CrExceptionConcurrentBundle
crExceptionNaturalContinuumWitness =
  crExceptionConcurrentBundleWithPresent 4
    (crExceptionConcurrentBundleWithPresent 3
      (crExceptionConcurrentBundleWithPresent 2
        (crExceptionConcurrentBundleWithPresent 1
          (crExceptionConcurrentBundleWithPresent 0
            (CrExceptionConcurrentBundle True
              (replicate crExceptionProductChannelCount CrExceptionSlotUnwired))))))

data CrExceptionXorPosture
  = CrExceptionXorExclusive
  | CrExceptionXorConcurrent
  deriving (Eq, Show)

crExceptionXorPostureExclusive :: CrExceptionXorPosture
crExceptionXorPostureExclusive = CrExceptionXorExclusive

crExceptionXorPostureConcurrent :: CrExceptionXorPosture
crExceptionXorPostureConcurrent = CrExceptionXorConcurrent

data CrExceptionContinuumVerdict
  = CrExceptionContinuumDesignOk
  | CrExceptionContinuumNamedOk
  | CrExceptionContinuumTrivialRefuse
  | CrExceptionContinuumGreenInventRefuse
  | CrExceptionContinuumProvedWithoutBarRefuse
  | CrExceptionContinuumXorRefuse
  deriving (Eq, Show)

data CrExceptionXorVerdict
  = CrExceptionXorDesignOk
  | CrExceptionXorNamedOk
  | CrExceptionXorGreenInventRefuse
  | CrExceptionXorProvedWithoutBarRefuse
  | CrExceptionXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

evaluateCrExceptionBundle ::
  CrExceptionContinuumModality
  -> CrExceptionConcurrentBundle
  -> Bool
  -> Bool
  -> CrExceptionContinuumVerdict
evaluateCrExceptionBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = CrExceptionContinuumGreenInventRefuse
  | claimProved = CrExceptionContinuumProvedWithoutBarRefuse
  | length (crExceptionChannelSlots bundle) /= crExceptionProductChannelCount =
      CrExceptionContinuumTrivialRefuse
  | otherwise =
      case modality of
        CrExceptionContinuumUnwired ->
          if crExceptionConcurrentBundleIsConcurrentProduct bundle
            then CrExceptionContinuumNamedOk
            else CrExceptionContinuumDesignOk
        CrExceptionContinuumAssumed -> CrExceptionContinuumDesignOk
        CrExceptionContinuumSurrogate -> CrExceptionContinuumDesignOk
        CrExceptionContinuumProved -> CrExceptionContinuumProvedWithoutBarRefuse

evaluateCrExceptionXor ::
  CrExceptionContinuumModality
  -> CrExceptionXorPosture
  -> Bool
  -> Bool
  -> CrExceptionXorVerdict
evaluateCrExceptionXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = CrExceptionXorGreenInventRefuse
  | claimProved = CrExceptionXorProvedWithoutBarRefuse
  | posture == CrExceptionXorExclusive = CrExceptionXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        CrExceptionContinuumUnwired -> CrExceptionXorNamedOk
        CrExceptionContinuumAssumed -> CrExceptionXorDesignOk
        CrExceptionContinuumSurrogate -> CrExceptionXorDesignOk
        CrExceptionContinuumProved -> CrExceptionXorProvedWithoutBarRefuse

data CrExceptionContinuumLaw
  = CrExceptionContinuumConserved
  | NamedCrExceptionContinuumOk
  | TrivialCrExceptionRefused
  | GreenInventCrExceptionRefused
  deriving (Eq, Show)

crExceptionContinuumLawAll :: [CrExceptionContinuumLaw]
crExceptionContinuumLawAll =
  [ CrExceptionContinuumConserved
  , NamedCrExceptionContinuumOk
  , TrivialCrExceptionRefused
  , GreenInventCrExceptionRefused
  ]

crExceptionContinuumLawCount :: Int
crExceptionContinuumLawCount = length crExceptionContinuumLawAll

evaluateCrExceptionContinuum ::
  CrExceptionContinuumModality
  -> CrExceptionConcurrentBundle
  -> CrExceptionXorPosture
  -> Bool
  -> Bool
  -> CrExceptionContinuumVerdict
evaluateCrExceptionContinuum modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = CrExceptionContinuumGreenInventRefuse
  | claimProved = CrExceptionContinuumProvedWithoutBarRefuse
  | otherwise =
      case evaluateCrExceptionXor modality posture False False of
        CrExceptionXorMutuallyExclusiveRefuse -> CrExceptionContinuumXorRefuse
        CrExceptionXorGreenInventRefuse -> CrExceptionContinuumGreenInventRefuse
        CrExceptionXorProvedWithoutBarRefuse -> CrExceptionContinuumProvedWithoutBarRefuse
        _ ->
          case evaluateCrExceptionBundle modality bundle False False of
            CrExceptionContinuumNamedOk -> CrExceptionContinuumNamedOk
            CrExceptionContinuumGreenInventRefuse -> CrExceptionContinuumGreenInventRefuse
            CrExceptionContinuumProvedWithoutBarRefuse -> CrExceptionContinuumProvedWithoutBarRefuse
            CrExceptionContinuumTrivialRefuse -> CrExceptionContinuumTrivialRefuse
            CrExceptionContinuumXorRefuse -> CrExceptionContinuumXorRefuse
            CrExceptionContinuumDesignOk -> CrExceptionContinuumDesignOk

sampleCrExceptionNaturalContinuumBundle :: CrExceptionConcurrentBundle
sampleCrExceptionNaturalContinuumBundle = crExceptionNaturalContinuumWitness

sampleXorExclusiveBundle :: CrExceptionConcurrentBundle
sampleXorExclusiveBundle = crExceptionConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: CrExceptionConcurrentBundle
sampleTrivialUnwiredBundle = crExceptionConcurrentBundleUnwired

unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateCrExceptionContinuum
    CrExceptionContinuumUnwired
    sampleCrExceptionNaturalContinuumBundle
    crExceptionXorPostureConcurrent
    False
    False
    == CrExceptionContinuumNamedOk

crExceptionNaturalContinuumConcurrentOk :: Bool
crExceptionNaturalContinuumConcurrentOk =
  let bundle = crExceptionNaturalContinuumWitness
   in crExceptionClassPresent bundle
        && crExceptionConcurrentBundleHolds 0 bundle
        && crExceptionConcurrentBundleHolds 1 bundle
        && crExceptionConcurrentBundleHolds 2 bundle
        && crExceptionConcurrentBundleHolds 3 bundle
        && crExceptionConcurrentBundleHolds 4 bundle
        && crExceptionConcurrentBundlePresentCount bundle == 5
        && crExceptionConcurrentBundleIsConcurrentProduct bundle
        && chromiumAtomicNumberZ == 24
        && dBlockExceptionZ Cr == 24

crZ24OccupancyEngineSortOk :: Bool
crZ24OccupancyEngineSortOk =
  chromiumAtomicNumberZ == 24
    && occupancyEngineSortBucket chromiumAtomicNumberZ == DBlockExceptionBucket
    && crExceptionProductChannelCount == 5
    && length (crExceptionChannelSlots crExceptionConcurrentBundleUnwired) == 5

crObservedNePredictedOk :: Bool
crObservedNePredictedOk = crObservedNePredicted

moHomologNotCrOccupancyCopy :: Bool
moHomologNotCrOccupancyCopy =
  molybdenumHomologZ == chromiumAtomicNumberZ + 18
    && molybdenumHomologZ /= chromiumAtomicNumberZ
    && dBlockExceptionZ Mo == molybdenumHomologZ
    && dBlockExceptionObservedNotation Cr /= dBlockExceptionObservedNotation Mo
    && occupancyEngineSortBucket molybdenumHomologZ == DBlockExceptionBucket

concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  crExceptionConcurrentBundleIsConcurrentProduct crExceptionNaturalContinuumWitness
    && crExceptionConcurrentBundlePresentCount crExceptionNaturalContinuumWitness >= 2
    && crExceptionConcurrentBundlePresentCount crExceptionNaturalContinuumWitness == 5

xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateCrExceptionXor
    CrExceptionContinuumUnwired
    crExceptionXorPostureExclusive
    False
    False
    == CrExceptionXorMutuallyExclusiveRefuse
    && evaluateCrExceptionContinuum
      CrExceptionContinuumUnwired
      sampleCrExceptionNaturalContinuumBundle
      crExceptionXorPostureExclusive
      False
      False
      == CrExceptionContinuumXorRefuse

greenInventCrExceptionRefuse :: Bool
greenInventCrExceptionRefuse =
  evaluateCrExceptionContinuum
    CrExceptionContinuumUnwired
    sampleCrExceptionNaturalContinuumBundle
    crExceptionXorPostureConcurrent
    True
    False
    == CrExceptionContinuumGreenInventRefuse
    && evaluateCrExceptionBundle
      CrExceptionContinuumUnwired
      sampleCrExceptionNaturalContinuumBundle
      True
      False
      == CrExceptionContinuumGreenInventRefuse

parallelOccupancyAxiomRefuse :: Bool
parallelOccupancyAxiomRefuse =
  crExceptionContinuumAuthority
    == "umst/umst-chem/src/x_rows/cr_exception_continuum.rs"
    && crExceptionContinuumProved == False
    && not (crExceptionContinuumAuthority == "26th_chemistry_axiom")
    && crExceptionContinuumFraming
      /= "parallel_occupancy_axiom_not_second_law"
    && occupancyEngineSortNotSecondAxiom

homologOccupancyCopyRefuse :: Bool
homologOccupancyCopyRefuse =
  parallelOccupancyAxiomRefuse
    && crExceptionContinuumFraming
      /= "homolog_occupancy_copy_smuggle"
    && homologExceptionNotCopyAuthority
      == "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"
    && moHomologNotCrOccupancyCopyNotation

moHomologNotCrOccupancyCopyNotation :: Bool
moHomologNotCrOccupancyCopyNotation =
  dBlockExceptionObservedNotation Cr
    /= "1s22s22p63s23p64s23d104p65s14d5"

occupancyEngineSortNotAxiomRefuse :: Bool
occupancyEngineSortNotAxiomRefuse =
  homologOccupancyCopyRefuse
    && crExceptionContinuumFraming
      /= "occupancy_engine_sort_axiom_not_continuum"
    && occupancyEngineSortAuthority
      == "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
    && occupancyEngineSortNotSecondAxiom
    && chromiumAtomicNumberZ == 24

refineCostFloatPinRefuse :: Bool
refineCostFloatPinRefuse =
  occupancyEngineSortNotAxiomRefuse
    && crExceptionContinuumFraming
      /= "refine_cost_bare_float_pin_on_cr_continuum"
    && goldschmidtContinuumAuthority
      == "umst/umst-chem/src/l0_tables/goldschmidt.rs"
    && chromiumAtomicNumberZ == 24

assumedCrExceptionDesignOk :: Bool
assumedCrExceptionDesignOk =
  evaluateCrExceptionContinuum
    CrExceptionContinuumAssumed
    sampleCrExceptionNaturalContinuumBundle
    crExceptionXorPostureConcurrent
    False
    False
    == CrExceptionContinuumDesignOk

surrogateCrExceptionDesignOk :: Bool
surrogateCrExceptionDesignOk =
  evaluateCrExceptionContinuum
    CrExceptionContinuumSurrogate
    sampleCrExceptionNaturalContinuumBundle
    crExceptionXorPostureConcurrent
    False
    False
    == CrExceptionContinuumDesignOk

crExceptionLatticeScaffold :: Bool
crExceptionLatticeScaffold =
  crExceptionLatticeCount == 4
    && unwiredDesignOk
    && crZ24OccupancyEngineSortOk
    && crExceptionNaturalContinuumConcurrentOk
    && crObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedCrExceptionDesignOk
    && surrogateCrExceptionDesignOk
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

crExceptionLatticeNotGreenTable :: Bool
crExceptionLatticeNotGreenTable =
  crExceptionLatticeCount == 4
    && crExceptionLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && crExceptionProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && crExceptionChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

crExceptionContinuumLawsScaffold :: Bool
crExceptionContinuumLawsScaffold =
  crExceptionContinuumLawCount == 4
    && crExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCrExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

crExceptionContinuumLawsNotGreenTable :: Bool
crExceptionContinuumLawsNotGreenTable =
  crExceptionContinuumLawsScaffold
    && crExceptionContinuumLawCount /= 118 * 118
    && crExceptionProductChannelCount /= 118 * 118

crExceptionKnowingFiberOk :: Bool
crExceptionKnowingFiberOk = True

crExceptionContinuumInventRefuse :: Bool
crExceptionContinuumInventRefuse = not crExceptionContinuumProved

crExceptionLatticeNotXor :: Bool
crExceptionLatticeNotXor =
  unwiredDesignOk
    && assumedCrExceptionDesignOk
    && surrogateCrExceptionDesignOk
    && crExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCrExceptionRefuse

crExceptionContinuumProved :: Bool
crExceptionContinuumProved = False

speciesIdForked :: Bool
speciesIdForked = False

crExceptionContinuumNeSpeciesId :: Bool
crExceptionContinuumNeSpeciesId =
  crExceptionContinuumAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && crExceptionProductChannelAll /= []
    && crExceptionConcurrentBundleIsConcurrentProduct crExceptionNaturalContinuumWitness
    && not speciesIdForked

crExceptionContinuumFraming :: String
crExceptionContinuumFraming =
  "second_law_conservation_cr_exception_continuum_one_axiom"

crExceptionContinuumAxiom :: Bool
crExceptionContinuumAxiom =
  crExceptionLatticeScaffold
    && crExceptionLatticeNotGreenTable
    && crExceptionContinuumLawsScaffold
    && crExceptionContinuumLawsNotGreenTable
    && crExceptionKnowingFiberOk
    && crZ24OccupancyEngineSortOk
    && crExceptionNaturalContinuumConcurrentOk
    && crObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCrExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse
    && crExceptionContinuumInventRefuse
    && crExceptionLatticeNotXor
    && crExceptionContinuumNeSpeciesId
    && not crExceptionContinuumProved
    && not speciesIdForked
    && crExceptionContinuumFraming
      == "second_law_conservation_cr_exception_continuum_one_axiom"

crExceptionContinuumNamed :: String
crExceptionContinuumNamed =
  "crExceptionContinuum: CrExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice crExceptionContinuumProved false evaluateCrExceptionBundle evaluateCrExceptionContinuum named Cr Z=24 DBlock occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not axiom refuse cr ne SpeciesId fork second law conservation one axiom"

crExceptionContinuumAuthority :: String
crExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/cr_exception_continuum.rs"

goldschmidtContinuumAuthority :: String
goldschmidtContinuumAuthority =
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"

dBlockOccupancyExceptionsAuthority :: String
dBlockOccupancyExceptionsAuthority =
  "umst/umst-chem/src/qlattice.rs"

homologExceptionNotCopyAuthority :: String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

crExceptionContinuumCellId :: String
crExceptionContinuumCellId = "CHEM-FORMAL-Q-HS-CR-EXCEPTION-CONTINUUM"

crExceptionContinuumNonClaim :: String
crExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-HS-CR-EXCEPTION-CONTINUUM CrExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice crExceptionContinuumProved false evaluateCrExceptionBundle evaluateCrExceptionContinuum named Cr Z=24 DBlock occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not 26th axiom refuse cite occupancy_engine_sort homolog_exception_not_copy goldschmidt read-only cr ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

crExceptionContinuumPhysicsGreenAuthorized :: Bool
crExceptionContinuumPhysicsGreenAuthorized = False

crExceptionContinuumPhysicsGreenFalse :: Bool
crExceptionContinuumPhysicsGreenFalse =
  not crExceptionContinuumPhysicsGreenAuthorized

crExceptionContinuumModalityUnwired :: Bool
crExceptionContinuumModalityUnwired =
  crExceptionContinuumModalityCurrent == CrExceptionContinuumUnwired

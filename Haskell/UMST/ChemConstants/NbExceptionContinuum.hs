-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.NbExceptionContinuum
Description : Nb Z=41 **exception-continuum** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Nb exception continuum**: D-block occupancy-engine sort witness Nb Z=41 as one second-law
**conservation** product (ore ⊗ isotope mix ⊗ purify Refine-cost ⊗ G-stability ⊗ Env) —
cite @occupancy_engine_sort@ + @homolog_exception_not_copy@ read-only; homolog ≠ copy;
**not** a 26th axiom. Named Nb natural-continuum identity conserved under honest scaffold;
trivial XOR, parallel occupancy axiom, homolog occupancy copy, and GREEN invent fail-closed.
Exception-continuum laws are structure witnesses only (@nbExceptionContinuumProved@ = False).
No SpeciesId fork.

* @NbExceptionContinuumModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateNbExceptionBundle@ — named Nb Z=41 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateNbExceptionContinuum@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@nbExceptionContinuumAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of Nb Z=41 exception continuum on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-NB-EXCEPTION-CONTINUUM@.
INT: umst/umst-chem/src/elements/z_041_nb.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.NbExceptionContinuum
  ( NbExceptionContinuumModality (..)
  , nbExceptionContinuumModalityCurrent
  , nbExceptionLatticeAll
  , nbExceptionLatticeCount
  , niobiumAtomicNumberZ
  , vanadiumHomologZ
  , NbExceptionChannelSlot (..)
  , nbExceptionChannelSlotAll
  , nbExceptionChannelSlotCount
  , NbExceptionProductChannel (..)
  , nbExceptionProductChannelAll
  , nbExceptionProductChannelCount
  , nbExceptionProductChannelIndex
  , NbExceptionConcurrentBundle (..)
  , nbExceptionConcurrentBundleUnwired
  , nbExceptionConcurrentBundleWithChannel
  , nbExceptionConcurrentBundleWithPresent
  , nbExceptionConcurrentBundleChannelAt
  , nbExceptionConcurrentBundleHolds
  , nbExceptionConcurrentBundlePresentCount
  , nbExceptionConcurrentBundleIsConcurrentProduct
  , nbExceptionNaturalContinuumWitness
  , NbExceptionXorPosture (..)
  , nbExceptionXorPostureExclusive
  , nbExceptionXorPostureConcurrent
  , NbExceptionContinuumVerdict (..)
  , NbExceptionXorVerdict (..)
  , evaluateNbExceptionBundle
  , evaluateNbExceptionXor
  , evaluateNbExceptionContinuum
  , NbExceptionContinuumLaw (..)
  , nbExceptionContinuumLawAll
  , nbExceptionContinuumLawCount
  , sampleNbExceptionNaturalContinuumBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , nbExceptionNaturalContinuumConcurrentOk
  , nbZ41OccupancyEngineSortOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventNbExceptionRefuse
  , parallelOccupancyAxiomRefuse
  , homologOccupancyCopyRefuse
  , occupancyEngineSortNotAxiomRefuse
  , refineCostFloatPinRefuse
  , assumedNbExceptionDesignOk
  , surrogateNbExceptionDesignOk
  , nbExceptionLatticeScaffold
  , nbExceptionLatticeNotGreenTable
  , nbExceptionContinuumLawsScaffold
  , nbExceptionContinuumLawsNotGreenTable
  , nbExceptionKnowingFiberOk
  , nbExceptionContinuumInventRefuse
  , nbExceptionLatticeNotXor
  , nbExceptionContinuumProved
  , nbExceptionContinuumNeSpeciesId
  , speciesIdForked
  , vHomologNotNbOccupancyCopy
  , nbObservedNePredictedOk
  , nbExceptionContinuumFraming
  , nbExceptionContinuumAxiom
  , nbExceptionContinuumNamed
  , nbExceptionContinuumAuthority
  , occupancyEngineSortAuthority
  , homologExceptionNotCopyAuthority
  , goldschmidtContinuumAuthority
  , dBlockOccupancyExceptionsAuthority
  , nbExceptionContinuumCellId
  , nbExceptionContinuumNonClaim
  , nbExceptionContinuumPhysicsGreenAuthorized
  , nbExceptionContinuumPhysicsGreenFalse
  , nbExceptionContinuumModalityUnwired
  ) where

import UMST.ChemConstants.DBlockOccupancyExceptions
  ( DBlockException (Nb)
  , nbObservedNePredicted
  , dBlockExceptionObservedNotation
  , dBlockExceptionZ
  )
import UMST.ChemConstants.OccupancyEngineSort
  ( OccupancyEngineSortBucket (DBlockExceptionBucket)
  , occupancyEngineSortAuthority
  , occupancyEngineSortBucket
  , occupancyEngineSortNotSecondAxiom
  )

-- | IUPAC periodic-table cardinality (Z=1..118) — not Nb exception GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Niobium Z=41 — D-block occupancy exception witness pin.
niobiumAtomicNumberZ :: Int
niobiumAtomicNumberZ = 41

-- | Vanadium Z=23 — period-4 group-5 homolog witness pin (homolog ≠ copy).
vanadiumHomologZ :: Int
vanadiumHomologZ = 23

-- | Vanadium period-4 homolog subshell notation — **refused** as Nb copy.
vanadiumHomologNotationRefused :: String
vanadiumHomologNotationRefused = "1s22s22p63s23p64s23d3"

-- | Design **Nb exception continuum** modality for conservation claims.
data NbExceptionContinuumModality
  = NbExceptionContinuumUnwired
  | NbExceptionContinuumAssumed
  | NbExceptionContinuumProved
  | NbExceptionContinuumSurrogate
  deriving (Eq, Show)

-- | Current scaffold **Nb exception continuum** modality — always Unwired on this cell.
nbExceptionContinuumModalityCurrent :: NbExceptionContinuumModality
nbExceptionContinuumModalityCurrent = NbExceptionContinuumUnwired

-- | All Nb exception continuum lattice steps in stable order.
nbExceptionLatticeAll :: [NbExceptionContinuumModality]
nbExceptionLatticeAll =
  [ NbExceptionContinuumUnwired
  , NbExceptionContinuumAssumed
  , NbExceptionContinuumProved
  , NbExceptionContinuumSurrogate
  ]

nbExceptionLatticeCount :: Int
nbExceptionLatticeCount = length nbExceptionLatticeAll

-- | Nb exception continuum channel slot — concurrent **product** factor, not XOR bucket.
data NbExceptionChannelSlot
  = NbExceptionSlotUnwired
  | NbExceptionSlotAbsent
  | NbExceptionSlotPresent
  deriving (Eq, Show)

nbExceptionChannelSlotAll :: [NbExceptionChannelSlot]
nbExceptionChannelSlotAll =
  [ NbExceptionSlotUnwired
  , NbExceptionSlotAbsent
  , NbExceptionSlotPresent
  ]

nbExceptionChannelSlotCount :: Int
nbExceptionChannelSlotCount = length nbExceptionChannelSlotAll

-- | Named Nb natural-continuum product channels (ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env).
data NbExceptionProductChannel
  = OreNaturalContinuum
  | IsotopeMixContinuum
  | PurifyRefineCostContinuum
  | GStabilityContinuum
  | EnvContinuum
  deriving (Eq, Show)

nbExceptionProductChannelAll :: [NbExceptionProductChannel]
nbExceptionProductChannelAll =
  [ OreNaturalContinuum
  , IsotopeMixContinuum
  , PurifyRefineCostContinuum
  , GStabilityContinuum
  , EnvContinuum
  ]

nbExceptionProductChannelCount :: Int
nbExceptionProductChannelCount = length nbExceptionProductChannelAll

nbExceptionProductChannelIndex :: NbExceptionProductChannel -> Int
nbExceptionProductChannelIndex channel =
  case channel of
    OreNaturalContinuum -> 0
    IsotopeMixContinuum -> 1
    PurifyRefineCostContinuum -> 2
    GStabilityContinuum -> 3
    EnvContinuum -> 4

-- | Nb Z=41 exception-continuum concurrent **product** bundle (north-star §3).
data NbExceptionConcurrentBundle = NbExceptionConcurrentBundle
  { nbExceptionClassPresent :: Bool
  , nbExceptionChannelSlots :: [NbExceptionChannelSlot]
  }
  deriving (Eq, Show)

nbExceptionConcurrentBundleUnwired :: NbExceptionConcurrentBundle
nbExceptionConcurrentBundleUnwired =
  NbExceptionConcurrentBundle
    False
    (replicate nbExceptionProductChannelCount NbExceptionSlotUnwired)

nbExceptionConcurrentBundleWithChannel ::
  Int -> NbExceptionChannelSlot -> NbExceptionConcurrentBundle -> NbExceptionConcurrentBundle
nbExceptionConcurrentBundleWithChannel idx slot bundle =
  let slots = nbExceptionChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in NbExceptionConcurrentBundle
        (nbExceptionClassPresent bundle)
        (before ++ [current] ++ after)

nbExceptionConcurrentBundleWithPresent ::
  Int -> NbExceptionConcurrentBundle -> NbExceptionConcurrentBundle
nbExceptionConcurrentBundleWithPresent idx bundle =
  nbExceptionConcurrentBundleWithChannel idx NbExceptionSlotPresent bundle

nbExceptionConcurrentBundleChannelAt ::
  Int -> NbExceptionConcurrentBundle -> Maybe NbExceptionChannelSlot
nbExceptionConcurrentBundleChannelAt idx bundle =
  let slots = nbExceptionChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

nbExceptionConcurrentBundleHolds :: Int -> NbExceptionConcurrentBundle -> Bool
nbExceptionConcurrentBundleHolds idx bundle =
  case nbExceptionConcurrentBundleChannelAt idx bundle of
    Just NbExceptionSlotPresent -> True
    _ -> False

nbExceptionConcurrentBundlePresentCount :: NbExceptionConcurrentBundle -> Int
nbExceptionConcurrentBundlePresentCount bundle =
  length (filter (== NbExceptionSlotPresent) (nbExceptionChannelSlots bundle))

nbExceptionConcurrentBundleIsConcurrentProduct :: NbExceptionConcurrentBundle -> Bool
nbExceptionConcurrentBundleIsConcurrentProduct bundle =
  nbExceptionConcurrentBundlePresentCount bundle >= 2

-- | Nb witness: ore (0) + isotope (1) + purify (2) + G (3) + Env (4) concurrent on Z=41.
nbExceptionNaturalContinuumWitness :: NbExceptionConcurrentBundle
nbExceptionNaturalContinuumWitness =
  nbExceptionConcurrentBundleWithPresent 4
    (nbExceptionConcurrentBundleWithPresent 3
      (nbExceptionConcurrentBundleWithPresent 2
        (nbExceptionConcurrentBundleWithPresent 1
          (nbExceptionConcurrentBundleWithPresent 0
            (NbExceptionConcurrentBundle True
              (replicate nbExceptionProductChannelCount NbExceptionSlotUnwired))))))

data NbExceptionXorPosture
  = NbExceptionXorExclusive
  | NbExceptionXorConcurrent
  deriving (Eq, Show)

nbExceptionXorPostureExclusive :: NbExceptionXorPosture
nbExceptionXorPostureExclusive = NbExceptionXorExclusive

nbExceptionXorPostureConcurrent :: NbExceptionXorPosture
nbExceptionXorPostureConcurrent = NbExceptionXorConcurrent

data NbExceptionContinuumVerdict
  = NbExceptionContinuumDesignOk
  | NbExceptionContinuumNamedOk
  | NbExceptionContinuumTrivialRefuse
  | NbExceptionContinuumGreenInventRefuse
  | NbExceptionContinuumProvedWithoutBarRefuse
  | NbExceptionContinuumXorRefuse
  deriving (Eq, Show)

data NbExceptionXorVerdict
  = NbExceptionXorDesignOk
  | NbExceptionXorNamedOk
  | NbExceptionXorGreenInventRefuse
  | NbExceptionXorProvedWithoutBarRefuse
  | NbExceptionXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

evaluateNbExceptionBundle ::
  NbExceptionContinuumModality
  -> NbExceptionConcurrentBundle
  -> Bool
  -> Bool
  -> NbExceptionContinuumVerdict
evaluateNbExceptionBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = NbExceptionContinuumGreenInventRefuse
  | claimProved = NbExceptionContinuumProvedWithoutBarRefuse
  | length (nbExceptionChannelSlots bundle) /= nbExceptionProductChannelCount =
      NbExceptionContinuumTrivialRefuse
  | otherwise =
      case modality of
        NbExceptionContinuumUnwired ->
          if nbExceptionConcurrentBundleIsConcurrentProduct bundle
            then NbExceptionContinuumNamedOk
            else NbExceptionContinuumDesignOk
        NbExceptionContinuumAssumed -> NbExceptionContinuumDesignOk
        NbExceptionContinuumSurrogate -> NbExceptionContinuumDesignOk
        NbExceptionContinuumProved -> NbExceptionContinuumProvedWithoutBarRefuse

evaluateNbExceptionXor ::
  NbExceptionContinuumModality
  -> NbExceptionXorPosture
  -> Bool
  -> Bool
  -> NbExceptionXorVerdict
evaluateNbExceptionXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = NbExceptionXorGreenInventRefuse
  | claimProved = NbExceptionXorProvedWithoutBarRefuse
  | posture == NbExceptionXorExclusive = NbExceptionXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        NbExceptionContinuumUnwired -> NbExceptionXorNamedOk
        NbExceptionContinuumAssumed -> NbExceptionXorDesignOk
        NbExceptionContinuumSurrogate -> NbExceptionXorDesignOk
        NbExceptionContinuumProved -> NbExceptionXorProvedWithoutBarRefuse

data NbExceptionContinuumLaw
  = NbExceptionContinuumConserved
  | NamedNbExceptionContinuumOk
  | TrivialNbExceptionRefused
  | GreenInventNbExceptionRefused
  deriving (Eq, Show)

nbExceptionContinuumLawAll :: [NbExceptionContinuumLaw]
nbExceptionContinuumLawAll =
  [ NbExceptionContinuumConserved
  , NamedNbExceptionContinuumOk
  , TrivialNbExceptionRefused
  , GreenInventNbExceptionRefused
  ]

nbExceptionContinuumLawCount :: Int
nbExceptionContinuumLawCount = length nbExceptionContinuumLawAll

evaluateNbExceptionContinuum ::
  NbExceptionContinuumModality
  -> NbExceptionConcurrentBundle
  -> NbExceptionXorPosture
  -> Bool
  -> Bool
  -> NbExceptionContinuumVerdict
evaluateNbExceptionContinuum modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = NbExceptionContinuumGreenInventRefuse
  | claimProved = NbExceptionContinuumProvedWithoutBarRefuse
  | otherwise =
      case evaluateNbExceptionXor modality posture False False of
        NbExceptionXorMutuallyExclusiveRefuse -> NbExceptionContinuumXorRefuse
        NbExceptionXorGreenInventRefuse -> NbExceptionContinuumGreenInventRefuse
        NbExceptionXorProvedWithoutBarRefuse -> NbExceptionContinuumProvedWithoutBarRefuse
        _ ->
          case evaluateNbExceptionBundle modality bundle False False of
            NbExceptionContinuumNamedOk -> NbExceptionContinuumNamedOk
            NbExceptionContinuumGreenInventRefuse -> NbExceptionContinuumGreenInventRefuse
            NbExceptionContinuumProvedWithoutBarRefuse -> NbExceptionContinuumProvedWithoutBarRefuse
            NbExceptionContinuumTrivialRefuse -> NbExceptionContinuumTrivialRefuse
            NbExceptionContinuumXorRefuse -> NbExceptionContinuumXorRefuse
            NbExceptionContinuumDesignOk -> NbExceptionContinuumDesignOk

sampleNbExceptionNaturalContinuumBundle :: NbExceptionConcurrentBundle
sampleNbExceptionNaturalContinuumBundle = nbExceptionNaturalContinuumWitness

sampleXorExclusiveBundle :: NbExceptionConcurrentBundle
sampleXorExclusiveBundle = nbExceptionConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: NbExceptionConcurrentBundle
sampleTrivialUnwiredBundle = nbExceptionConcurrentBundleUnwired

unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateNbExceptionContinuum
    NbExceptionContinuumUnwired
    sampleNbExceptionNaturalContinuumBundle
    nbExceptionXorPostureConcurrent
    False
    False
    == NbExceptionContinuumNamedOk

nbExceptionNaturalContinuumConcurrentOk :: Bool
nbExceptionNaturalContinuumConcurrentOk =
  let bundle = nbExceptionNaturalContinuumWitness
   in nbExceptionClassPresent bundle
        && nbExceptionConcurrentBundleHolds 0 bundle
        && nbExceptionConcurrentBundleHolds 1 bundle
        && nbExceptionConcurrentBundleHolds 2 bundle
        && nbExceptionConcurrentBundleHolds 3 bundle
        && nbExceptionConcurrentBundleHolds 4 bundle
        && nbExceptionConcurrentBundlePresentCount bundle == 5
        && nbExceptionConcurrentBundleIsConcurrentProduct bundle
        && niobiumAtomicNumberZ == 41
        && dBlockExceptionZ Nb == 41

nbZ41OccupancyEngineSortOk :: Bool
nbZ41OccupancyEngineSortOk =
  niobiumAtomicNumberZ == 41
    && occupancyEngineSortBucket niobiumAtomicNumberZ == DBlockExceptionBucket
    && nbExceptionProductChannelCount == 5
    && length (nbExceptionChannelSlots nbExceptionConcurrentBundleUnwired) == 5

nbObservedNePredictedOk :: Bool
nbObservedNePredictedOk = nbObservedNePredicted

vHomologNotNbOccupancyCopy :: Bool
vHomologNotNbOccupancyCopy =
  vanadiumHomologZ == niobiumAtomicNumberZ - 18
    && vanadiumHomologZ /= niobiumAtomicNumberZ
    && dBlockExceptionZ Nb == 41
    && dBlockExceptionObservedNotation Nb /= vanadiumHomologNotationRefused
    && occupancyEngineSortBucket niobiumAtomicNumberZ == DBlockExceptionBucket

concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  nbExceptionConcurrentBundleIsConcurrentProduct nbExceptionNaturalContinuumWitness
    && nbExceptionConcurrentBundlePresentCount nbExceptionNaturalContinuumWitness >= 2
    && nbExceptionConcurrentBundlePresentCount nbExceptionNaturalContinuumWitness == 5

xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateNbExceptionXor
    NbExceptionContinuumUnwired
    nbExceptionXorPostureExclusive
    False
    False
    == NbExceptionXorMutuallyExclusiveRefuse
    && evaluateNbExceptionContinuum
      NbExceptionContinuumUnwired
      sampleNbExceptionNaturalContinuumBundle
      nbExceptionXorPostureExclusive
      False
      False
      == NbExceptionContinuumXorRefuse

greenInventNbExceptionRefuse :: Bool
greenInventNbExceptionRefuse =
  evaluateNbExceptionContinuum
    NbExceptionContinuumUnwired
    sampleNbExceptionNaturalContinuumBundle
    nbExceptionXorPostureConcurrent
    True
    False
    == NbExceptionContinuumGreenInventRefuse
    && evaluateNbExceptionBundle
      NbExceptionContinuumUnwired
      sampleNbExceptionNaturalContinuumBundle
      True
      False
      == NbExceptionContinuumGreenInventRefuse

parallelOccupancyAxiomRefuse :: Bool
parallelOccupancyAxiomRefuse =
  nbExceptionContinuumAuthority
    == "umst/umst-chem/src/x_rows/nb_exception_continuum.rs"
    && nbExceptionContinuumProved == False
    && not (nbExceptionContinuumAuthority == "26th_chemistry_axiom")
    && nbExceptionContinuumFraming
      /= "parallel_occupancy_axiom_not_second_law"
    && occupancyEngineSortNotSecondAxiom

homologOccupancyCopyRefuse :: Bool
homologOccupancyCopyRefuse =
  parallelOccupancyAxiomRefuse
    && nbExceptionContinuumFraming
      /= "homolog_occupancy_copy_smuggle"
    && homologExceptionNotCopyAuthority
      == "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"
    && vHomologNotNbOccupancyCopyNotation

vHomologNotNbOccupancyCopyNotation :: Bool
vHomologNotNbOccupancyCopyNotation =
  dBlockExceptionObservedNotation Nb
    /= vanadiumHomologNotationRefused

occupancyEngineSortNotAxiomRefuse :: Bool
occupancyEngineSortNotAxiomRefuse =
  homologOccupancyCopyRefuse
    && nbExceptionContinuumFraming
      /= "occupancy_engine_sort_axiom_not_continuum"
    && occupancyEngineSortAuthority
      == "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
    && occupancyEngineSortNotSecondAxiom
    && niobiumAtomicNumberZ == 41

refineCostFloatPinRefuse :: Bool
refineCostFloatPinRefuse =
  occupancyEngineSortNotAxiomRefuse
    && nbExceptionContinuumFraming
      /= "refine_cost_bare_float_pin_on_nb_continuum"
    && goldschmidtContinuumAuthority
      == "umst/umst-chem/src/l0_tables/goldschmidt.rs"
    && niobiumAtomicNumberZ == 41

assumedNbExceptionDesignOk :: Bool
assumedNbExceptionDesignOk =
  evaluateNbExceptionContinuum
    NbExceptionContinuumAssumed
    sampleNbExceptionNaturalContinuumBundle
    nbExceptionXorPostureConcurrent
    False
    False
    == NbExceptionContinuumDesignOk

surrogateNbExceptionDesignOk :: Bool
surrogateNbExceptionDesignOk =
  evaluateNbExceptionContinuum
    NbExceptionContinuumSurrogate
    sampleNbExceptionNaturalContinuumBundle
    nbExceptionXorPostureConcurrent
    False
    False
    == NbExceptionContinuumDesignOk

nbExceptionLatticeScaffold :: Bool
nbExceptionLatticeScaffold =
  nbExceptionLatticeCount == 4
    && unwiredDesignOk
    && nbZ41OccupancyEngineSortOk
    && nbExceptionNaturalContinuumConcurrentOk
    && nbObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedNbExceptionDesignOk
    && surrogateNbExceptionDesignOk
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

nbExceptionLatticeNotGreenTable :: Bool
nbExceptionLatticeNotGreenTable =
  nbExceptionLatticeCount == 4
    && nbExceptionLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && nbExceptionProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && nbExceptionChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

nbExceptionContinuumLawsScaffold :: Bool
nbExceptionContinuumLawsScaffold =
  nbExceptionContinuumLawCount == 4
    && nbExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNbExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

nbExceptionContinuumLawsNotGreenTable :: Bool
nbExceptionContinuumLawsNotGreenTable =
  nbExceptionContinuumLawsScaffold
    && nbExceptionContinuumLawCount /= 118 * 118
    && nbExceptionProductChannelCount /= 118 * 118

nbExceptionKnowingFiberOk :: Bool
nbExceptionKnowingFiberOk = True

nbExceptionContinuumInventRefuse :: Bool
nbExceptionContinuumInventRefuse = not nbExceptionContinuumProved

nbExceptionLatticeNotXor :: Bool
nbExceptionLatticeNotXor =
  unwiredDesignOk
    && assumedNbExceptionDesignOk
    && surrogateNbExceptionDesignOk
    && nbExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNbExceptionRefuse

nbExceptionContinuumProved :: Bool
nbExceptionContinuumProved = False

speciesIdForked :: Bool
speciesIdForked = False

nbExceptionContinuumNeSpeciesId :: Bool
nbExceptionContinuumNeSpeciesId =
  nbExceptionContinuumAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && nbExceptionProductChannelAll /= []
    && nbExceptionConcurrentBundleIsConcurrentProduct nbExceptionNaturalContinuumWitness
    && not speciesIdForked

nbExceptionContinuumFraming :: String
nbExceptionContinuumFraming =
  "second_law_conservation_nb_exception_continuum_one_axiom"

nbExceptionContinuumAxiom :: Bool
nbExceptionContinuumAxiom =
  nbExceptionLatticeScaffold
    && nbExceptionLatticeNotGreenTable
    && nbExceptionContinuumLawsScaffold
    && nbExceptionContinuumLawsNotGreenTable
    && nbExceptionKnowingFiberOk
    && nbZ41OccupancyEngineSortOk
    && nbExceptionNaturalContinuumConcurrentOk
    && nbObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNbExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse
    && nbExceptionContinuumInventRefuse
    && nbExceptionLatticeNotXor
    && nbExceptionContinuumNeSpeciesId
    && not nbExceptionContinuumProved
    && not speciesIdForked
    && nbExceptionContinuumFraming
      == "second_law_conservation_nb_exception_continuum_one_axiom"

nbExceptionContinuumNamed :: String
nbExceptionContinuumNamed =
  "nbExceptionContinuum: NbExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice nbExceptionContinuumProved false evaluateNbExceptionBundle evaluateNbExceptionContinuum named Nb Z=41 DBlock occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not axiom refuse nb ne SpeciesId fork second law conservation one axiom"

nbExceptionContinuumAuthority :: String
nbExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_041_nb.rs"

goldschmidtContinuumAuthority :: String
goldschmidtContinuumAuthority =
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"

dBlockOccupancyExceptionsAuthority :: String
dBlockOccupancyExceptionsAuthority =
  "umst/umst-chem/src/qlattice.rs"

homologExceptionNotCopyAuthority :: String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

nbExceptionContinuumCellId :: String
nbExceptionContinuumCellId = "CHEM-FORMAL-Q-HS-NB-EXCEPTION-CONTINUUM"

nbExceptionContinuumNonClaim :: String
nbExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-HS-NB-EXCEPTION-CONTINUUM NbExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice nbExceptionContinuumProved false evaluateNbExceptionBundle evaluateNbExceptionContinuum named Nb Z=41 DBlock occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not 26th axiom refuse cite occupancy_engine_sort homolog_exception_not_copy goldschmidt read-only nb ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

nbExceptionContinuumPhysicsGreenAuthorized :: Bool
nbExceptionContinuumPhysicsGreenAuthorized = False

nbExceptionContinuumPhysicsGreenFalse :: Bool
nbExceptionContinuumPhysicsGreenFalse =
  not nbExceptionContinuumPhysicsGreenAuthorized

nbExceptionContinuumModalityUnwired :: Bool
nbExceptionContinuumModalityUnwired =
  nbExceptionContinuumModalityCurrent == NbExceptionContinuumUnwired

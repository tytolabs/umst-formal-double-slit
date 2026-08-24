-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.NpExceptionContinuum
Description : Np Z=93 **exception-continuum** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Np exception continuum**: Actinide occupancy-engine sort witness Np Z=93 as one second-law
**conservation** product (ore ⊗ isotope mix ⊗ purify Refine-cost ⊗ G-stability ⊗ Env) —
cite @occupancy_engine_sort@ + @homolog_exception_not_copy@ read-only; homolog ≠ copy;
**not** a 26th axiom. Named Np natural-continuum identity conserved under honest scaffold;
trivial XOR, parallel occupancy axiom, homolog occupancy copy, and GREEN invent fail-closed.
Exception-continuum laws are structure witnesses only (@npExceptionContinuumProved@ = False).
No SpeciesId fork.

* @NpExceptionContinuumModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateNpExceptionBundle@ — named Np Z=93 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateNpExceptionContinuum@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@npExceptionContinuumAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of Np Z=93 exception continuum on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-NP-EXCEPTION-CONTINUUM@.
INT: umst/umst-chem/src/elements/z_093_np.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.NpExceptionContinuum
  ( NpExceptionContinuumModality (..)
  , npExceptionContinuumModalityCurrent
  , npExceptionLatticeAll
  , npExceptionLatticeCount
  , neptuniumAtomicNumberZ
  , uraniumHomologZ
  , NpExceptionChannelSlot (..)
  , npExceptionChannelSlotAll
  , npExceptionChannelSlotCount
  , NpExceptionProductChannel (..)
  , npExceptionProductChannelAll
  , npExceptionProductChannelCount
  , npExceptionProductChannelIndex
  , NpExceptionConcurrentBundle (..)
  , npExceptionConcurrentBundleUnwired
  , npExceptionConcurrentBundleWithChannel
  , npExceptionConcurrentBundleWithPresent
  , npExceptionConcurrentBundleChannelAt
  , npExceptionConcurrentBundleHolds
  , npExceptionConcurrentBundlePresentCount
  , npExceptionConcurrentBundleIsConcurrentProduct
  , npExceptionNaturalContinuumWitness
  , NpExceptionXorPosture (..)
  , npExceptionXorPostureExclusive
  , npExceptionXorPostureConcurrent
  , NpExceptionContinuumVerdict (..)
  , NpExceptionXorVerdict (..)
  , evaluateNpExceptionBundle
  , evaluateNpExceptionXor
  , evaluateNpExceptionContinuum
  , NpExceptionContinuumLaw (..)
  , npExceptionContinuumLawAll
  , npExceptionContinuumLawCount
  , sampleNpExceptionNaturalContinuumBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , npExceptionNaturalContinuumConcurrentOk
  , npZ93OccupancyEngineSortOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventNpExceptionRefuse
  , parallelOccupancyAxiomRefuse
  , homologOccupancyCopyRefuse
  , occupancyEngineSortNotAxiomRefuse
  , refineCostFloatPinRefuse
  , assumedNpExceptionDesignOk
  , surrogateNpExceptionDesignOk
  , npExceptionLatticeScaffold
  , npExceptionLatticeNotGreenTable
  , npExceptionContinuumLawsScaffold
  , npExceptionContinuumLawsNotGreenTable
  , npExceptionKnowingFiberOk
  , npExceptionContinuumInventRefuse
  , npExceptionLatticeNotXor
  , npExceptionContinuumProved
  , npExceptionContinuumNeSpeciesId
  , speciesIdForked
  , uHomologNotNpOccupancyCopy
  , npObservedNePredictedOk
  , npExceptionContinuumFraming
  , npExceptionContinuumAxiom
  , npExceptionContinuumNamed
  , npExceptionContinuumAuthority
  , occupancyEngineSortAuthority
  , homologExceptionNotCopyAuthority
  , goldschmidtContinuumAuthority
  , actinideOccupancyExceptionsAuthority
  , npExceptionContinuumCellId
  , npExceptionContinuumNonClaim
  , npExceptionContinuumPhysicsGreenAuthorized
  , npExceptionContinuumPhysicsGreenFalse
  , npExceptionContinuumModalityUnwired
  ) where

import UMST.ChemConstants.ActinideOccupancyExceptions
  ( ActinideException (Np, U)
  , npObservedNePredicted
  , actinideExceptionObservedNotation
  , actinideExceptionZ
  )
import UMST.ChemConstants.OccupancyEngineSort
  ( OccupancyEngineSortBucket (ActinideExceptionBucket)
  , occupancyEngineSortAuthority
  , occupancyEngineSortBucket
  , occupancyEngineSortNotSecondAxiom
  )

-- | IUPAC periodic-table cardinality (Z=1..118) — not Np exception GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Neptunium Z=93 — Actinide occupancy exception witness pin.
neptuniumAtomicNumberZ :: Int
neptuniumAtomicNumberZ = 93

-- | Uranium Z=92 — period-7 actinide sibling homolog witness pin (homolog ≠ copy).
uraniumHomologZ :: Int
uraniumHomologZ = 92

-- | Uranium period-7 sibling subshell notation — **refused** as Np copy.
uraniumHomologNotationRefused :: String
uraniumHomologNotationRefused =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f36d1"

-- | Design **Np exception continuum** modality for conservation claims.
data NpExceptionContinuumModality
  = NpExceptionContinuumUnwired
  | NpExceptionContinuumAssumed
  | NpExceptionContinuumProved
  | NpExceptionContinuumSurrogate
  deriving (Eq, Show)

-- | Current scaffold **Np exception continuum** modality — always Unwired on this cell.
npExceptionContinuumModalityCurrent :: NpExceptionContinuumModality
npExceptionContinuumModalityCurrent = NpExceptionContinuumUnwired

-- | All Np exception continuum lattice steps in stable order.
npExceptionLatticeAll :: [NpExceptionContinuumModality]
npExceptionLatticeAll =
  [ NpExceptionContinuumUnwired
  , NpExceptionContinuumAssumed
  , NpExceptionContinuumProved
  , NpExceptionContinuumSurrogate
  ]

npExceptionLatticeCount :: Int
npExceptionLatticeCount = length npExceptionLatticeAll

-- | Np exception continuum channel slot — concurrent **product** factor, not XOR bucket.
data NpExceptionChannelSlot
  = NpExceptionSlotUnwired
  | NpExceptionSlotAbsent
  | NpExceptionSlotPresent
  deriving (Eq, Show)

npExceptionChannelSlotAll :: [NpExceptionChannelSlot]
npExceptionChannelSlotAll =
  [ NpExceptionSlotUnwired
  , NpExceptionSlotAbsent
  , NpExceptionSlotPresent
  ]

npExceptionChannelSlotCount :: Int
npExceptionChannelSlotCount = length npExceptionChannelSlotAll

-- | Named Np natural-continuum product channels (ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env).
data NpExceptionProductChannel
  = OreNaturalContinuum
  | IsotopeMixContinuum
  | PurifyRefineCostContinuum
  | GStabilityContinuum
  | EnvContinuum
  deriving (Eq, Show)

npExceptionProductChannelAll :: [NpExceptionProductChannel]
npExceptionProductChannelAll =
  [ OreNaturalContinuum
  , IsotopeMixContinuum
  , PurifyRefineCostContinuum
  , GStabilityContinuum
  , EnvContinuum
  ]

npExceptionProductChannelCount :: Int
npExceptionProductChannelCount = length npExceptionProductChannelAll

npExceptionProductChannelIndex :: NpExceptionProductChannel -> Int
npExceptionProductChannelIndex channel =
  case channel of
    OreNaturalContinuum -> 0
    IsotopeMixContinuum -> 1
    PurifyRefineCostContinuum -> 2
    GStabilityContinuum -> 3
    EnvContinuum -> 4

-- | Np Z=93 exception-continuum concurrent **product** bundle (north-star §3).
data NpExceptionConcurrentBundle = NpExceptionConcurrentBundle
  { npExceptionClassPresent :: Bool
  , npExceptionChannelSlots :: [NpExceptionChannelSlot]
  }
  deriving (Eq, Show)

npExceptionConcurrentBundleUnwired :: NpExceptionConcurrentBundle
npExceptionConcurrentBundleUnwired =
  NpExceptionConcurrentBundle
    False
    (replicate npExceptionProductChannelCount NpExceptionSlotUnwired)

npExceptionConcurrentBundleWithChannel ::
  Int -> NpExceptionChannelSlot -> NpExceptionConcurrentBundle -> NpExceptionConcurrentBundle
npExceptionConcurrentBundleWithChannel idx slot bundle =
  let slots = npExceptionChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in NpExceptionConcurrentBundle
        (npExceptionClassPresent bundle)
        (before ++ [current] ++ after)

npExceptionConcurrentBundleWithPresent ::
  Int -> NpExceptionConcurrentBundle -> NpExceptionConcurrentBundle
npExceptionConcurrentBundleWithPresent idx bundle =
  npExceptionConcurrentBundleWithChannel idx NpExceptionSlotPresent bundle

npExceptionConcurrentBundleChannelAt ::
  Int -> NpExceptionConcurrentBundle -> Maybe NpExceptionChannelSlot
npExceptionConcurrentBundleChannelAt idx bundle =
  let slots = npExceptionChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

npExceptionConcurrentBundleHolds :: Int -> NpExceptionConcurrentBundle -> Bool
npExceptionConcurrentBundleHolds idx bundle =
  case npExceptionConcurrentBundleChannelAt idx bundle of
    Just NpExceptionSlotPresent -> True
    _ -> False

npExceptionConcurrentBundlePresentCount :: NpExceptionConcurrentBundle -> Int
npExceptionConcurrentBundlePresentCount bundle =
  length (filter (== NpExceptionSlotPresent) (npExceptionChannelSlots bundle))

npExceptionConcurrentBundleIsConcurrentProduct :: NpExceptionConcurrentBundle -> Bool
npExceptionConcurrentBundleIsConcurrentProduct bundle =
  npExceptionConcurrentBundlePresentCount bundle >= 2

-- | Np witness: ore (0) + isotope (1) + purify (2) + G (3) + Env (4) concurrent on Z=93.
npExceptionNaturalContinuumWitness :: NpExceptionConcurrentBundle
npExceptionNaturalContinuumWitness =
  npExceptionConcurrentBundleWithPresent 4
    (npExceptionConcurrentBundleWithPresent 3
      (npExceptionConcurrentBundleWithPresent 2
        (npExceptionConcurrentBundleWithPresent 1
          (npExceptionConcurrentBundleWithPresent 0
            (NpExceptionConcurrentBundle True
              (replicate npExceptionProductChannelCount NpExceptionSlotUnwired))))))

data NpExceptionXorPosture
  = NpExceptionXorExclusive
  | NpExceptionXorConcurrent
  deriving (Eq, Show)

npExceptionXorPostureExclusive :: NpExceptionXorPosture
npExceptionXorPostureExclusive = NpExceptionXorExclusive

npExceptionXorPostureConcurrent :: NpExceptionXorPosture
npExceptionXorPostureConcurrent = NpExceptionXorConcurrent

data NpExceptionContinuumVerdict
  = NpExceptionContinuumDesignOk
  | NpExceptionContinuumNamedOk
  | NpExceptionContinuumTrivialRefuse
  | NpExceptionContinuumGreenInventRefuse
  | NpExceptionContinuumProvedWithoutBarRefuse
  | NpExceptionContinuumXorRefuse
  deriving (Eq, Show)

data NpExceptionXorVerdict
  = NpExceptionXorDesignOk
  | NpExceptionXorNamedOk
  | NpExceptionXorGreenInventRefuse
  | NpExceptionXorProvedWithoutBarRefuse
  | NpExceptionXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

evaluateNpExceptionBundle ::
  NpExceptionContinuumModality
  -> NpExceptionConcurrentBundle
  -> Bool
  -> Bool
  -> NpExceptionContinuumVerdict
evaluateNpExceptionBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = NpExceptionContinuumGreenInventRefuse
  | claimProved = NpExceptionContinuumProvedWithoutBarRefuse
  | length (npExceptionChannelSlots bundle) /= npExceptionProductChannelCount =
      NpExceptionContinuumTrivialRefuse
  | otherwise =
      case modality of
        NpExceptionContinuumUnwired ->
          if npExceptionConcurrentBundleIsConcurrentProduct bundle
            then NpExceptionContinuumNamedOk
            else NpExceptionContinuumDesignOk
        NpExceptionContinuumAssumed -> NpExceptionContinuumDesignOk
        NpExceptionContinuumSurrogate -> NpExceptionContinuumDesignOk
        NpExceptionContinuumProved -> NpExceptionContinuumProvedWithoutBarRefuse

evaluateNpExceptionXor ::
  NpExceptionContinuumModality
  -> NpExceptionXorPosture
  -> Bool
  -> Bool
  -> NpExceptionXorVerdict
evaluateNpExceptionXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = NpExceptionXorGreenInventRefuse
  | claimProved = NpExceptionXorProvedWithoutBarRefuse
  | posture == NpExceptionXorExclusive = NpExceptionXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        NpExceptionContinuumUnwired -> NpExceptionXorNamedOk
        NpExceptionContinuumAssumed -> NpExceptionXorDesignOk
        NpExceptionContinuumSurrogate -> NpExceptionXorDesignOk
        NpExceptionContinuumProved -> NpExceptionXorProvedWithoutBarRefuse

data NpExceptionContinuumLaw
  = NpExceptionContinuumConserved
  | NamedNpExceptionContinuumOk
  | TrivialNpExceptionRefused
  | GreenInventNpExceptionRefused
  deriving (Eq, Show)

npExceptionContinuumLawAll :: [NpExceptionContinuumLaw]
npExceptionContinuumLawAll =
  [ NpExceptionContinuumConserved
  , NamedNpExceptionContinuumOk
  , TrivialNpExceptionRefused
  , GreenInventNpExceptionRefused
  ]

npExceptionContinuumLawCount :: Int
npExceptionContinuumLawCount = length npExceptionContinuumLawAll

evaluateNpExceptionContinuum ::
  NpExceptionContinuumModality
  -> NpExceptionConcurrentBundle
  -> NpExceptionXorPosture
  -> Bool
  -> Bool
  -> NpExceptionContinuumVerdict
evaluateNpExceptionContinuum modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = NpExceptionContinuumGreenInventRefuse
  | claimProved = NpExceptionContinuumProvedWithoutBarRefuse
  | otherwise =
      case evaluateNpExceptionXor modality posture False False of
        NpExceptionXorMutuallyExclusiveRefuse -> NpExceptionContinuumXorRefuse
        NpExceptionXorGreenInventRefuse -> NpExceptionContinuumGreenInventRefuse
        NpExceptionXorProvedWithoutBarRefuse -> NpExceptionContinuumProvedWithoutBarRefuse
        _ ->
          case evaluateNpExceptionBundle modality bundle False False of
            NpExceptionContinuumNamedOk -> NpExceptionContinuumNamedOk
            NpExceptionContinuumGreenInventRefuse -> NpExceptionContinuumGreenInventRefuse
            NpExceptionContinuumProvedWithoutBarRefuse -> NpExceptionContinuumProvedWithoutBarRefuse
            NpExceptionContinuumTrivialRefuse -> NpExceptionContinuumTrivialRefuse
            NpExceptionContinuumXorRefuse -> NpExceptionContinuumXorRefuse
            NpExceptionContinuumDesignOk -> NpExceptionContinuumDesignOk

sampleNpExceptionNaturalContinuumBundle :: NpExceptionConcurrentBundle
sampleNpExceptionNaturalContinuumBundle = npExceptionNaturalContinuumWitness

sampleXorExclusiveBundle :: NpExceptionConcurrentBundle
sampleXorExclusiveBundle = npExceptionConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: NpExceptionConcurrentBundle
sampleTrivialUnwiredBundle = npExceptionConcurrentBundleUnwired

unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateNpExceptionContinuum
    NpExceptionContinuumUnwired
    sampleNpExceptionNaturalContinuumBundle
    npExceptionXorPostureConcurrent
    False
    False
    == NpExceptionContinuumNamedOk

npExceptionNaturalContinuumConcurrentOk :: Bool
npExceptionNaturalContinuumConcurrentOk =
  let bundle = npExceptionNaturalContinuumWitness
   in npExceptionClassPresent bundle
        && npExceptionConcurrentBundleHolds 0 bundle
        && npExceptionConcurrentBundleHolds 1 bundle
        && npExceptionConcurrentBundleHolds 2 bundle
        && npExceptionConcurrentBundleHolds 3 bundle
        && npExceptionConcurrentBundleHolds 4 bundle
        && npExceptionConcurrentBundlePresentCount bundle == 5
        && npExceptionConcurrentBundleIsConcurrentProduct bundle
        && neptuniumAtomicNumberZ == 93
        && actinideExceptionZ Np == 93

npZ93OccupancyEngineSortOk :: Bool
npZ93OccupancyEngineSortOk =
  neptuniumAtomicNumberZ == 93
    && occupancyEngineSortBucket neptuniumAtomicNumberZ == ActinideExceptionBucket
    && npExceptionProductChannelCount == 5
    && length (npExceptionChannelSlots npExceptionConcurrentBundleUnwired) == 5

npObservedNePredictedOk :: Bool
npObservedNePredictedOk = npObservedNePredicted

uHomologNotNpOccupancyCopy :: Bool
uHomologNotNpOccupancyCopy =
  uraniumHomologZ == neptuniumAtomicNumberZ - 1
    && uraniumHomologZ /= neptuniumAtomicNumberZ
    && actinideExceptionZ U == uraniumHomologZ
    && actinideExceptionObservedNotation Np /= uraniumHomologNotationRefused
    && occupancyEngineSortBucket neptuniumAtomicNumberZ == ActinideExceptionBucket

concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  npExceptionConcurrentBundleIsConcurrentProduct npExceptionNaturalContinuumWitness
    && npExceptionConcurrentBundlePresentCount npExceptionNaturalContinuumWitness >= 2
    && npExceptionConcurrentBundlePresentCount npExceptionNaturalContinuumWitness == 5

xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateNpExceptionXor
    NpExceptionContinuumUnwired
    npExceptionXorPostureExclusive
    False
    False
    == NpExceptionXorMutuallyExclusiveRefuse
    && evaluateNpExceptionContinuum
      NpExceptionContinuumUnwired
      sampleNpExceptionNaturalContinuumBundle
      npExceptionXorPostureExclusive
      False
      False
      == NpExceptionContinuumXorRefuse

greenInventNpExceptionRefuse :: Bool
greenInventNpExceptionRefuse =
  evaluateNpExceptionContinuum
    NpExceptionContinuumUnwired
    sampleNpExceptionNaturalContinuumBundle
    npExceptionXorPostureConcurrent
    True
    False
    == NpExceptionContinuumGreenInventRefuse
    && evaluateNpExceptionBundle
      NpExceptionContinuumUnwired
      sampleNpExceptionNaturalContinuumBundle
      True
      False
      == NpExceptionContinuumGreenInventRefuse

parallelOccupancyAxiomRefuse :: Bool
parallelOccupancyAxiomRefuse =
  npExceptionContinuumAuthority
    == "umst/umst-chem/src/elements/z_093_np.rs"
    && npExceptionContinuumProved == False
    && not (npExceptionContinuumAuthority == "26th_chemistry_axiom")
    && npExceptionContinuumFraming
      /= "parallel_occupancy_axiom_not_second_law"
    && occupancyEngineSortNotSecondAxiom

homologOccupancyCopyRefuse :: Bool
homologOccupancyCopyRefuse =
  parallelOccupancyAxiomRefuse
    && npExceptionContinuumFraming
      /= "homolog_occupancy_copy_smuggle"
    && homologExceptionNotCopyAuthority
      == "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"
    && uHomologNotNpOccupancyCopyNotation

uHomologNotNpOccupancyCopyNotation :: Bool
uHomologNotNpOccupancyCopyNotation =
  actinideExceptionObservedNotation Np
    /= uraniumHomologNotationRefused

occupancyEngineSortNotAxiomRefuse :: Bool
occupancyEngineSortNotAxiomRefuse =
  homologOccupancyCopyRefuse
    && npExceptionContinuumFraming
      /= "occupancy_engine_sort_axiom_not_continuum"
    && occupancyEngineSortAuthority
      == "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
    && occupancyEngineSortNotSecondAxiom
    && neptuniumAtomicNumberZ == 93

refineCostFloatPinRefuse :: Bool
refineCostFloatPinRefuse =
  occupancyEngineSortNotAxiomRefuse
    && npExceptionContinuumFraming
      /= "refine_cost_bare_float_pin_on_np_continuum"
    && goldschmidtContinuumAuthority
      == "umst/umst-chem/src/l0_tables/goldschmidt.rs"
    && neptuniumAtomicNumberZ == 93

assumedNpExceptionDesignOk :: Bool
assumedNpExceptionDesignOk =
  evaluateNpExceptionContinuum
    NpExceptionContinuumAssumed
    sampleNpExceptionNaturalContinuumBundle
    npExceptionXorPostureConcurrent
    False
    False
    == NpExceptionContinuumDesignOk

surrogateNpExceptionDesignOk :: Bool
surrogateNpExceptionDesignOk =
  evaluateNpExceptionContinuum
    NpExceptionContinuumSurrogate
    sampleNpExceptionNaturalContinuumBundle
    npExceptionXorPostureConcurrent
    False
    False
    == NpExceptionContinuumDesignOk

npExceptionLatticeScaffold :: Bool
npExceptionLatticeScaffold =
  npExceptionLatticeCount == 4
    && unwiredDesignOk
    && npZ93OccupancyEngineSortOk
    && npExceptionNaturalContinuumConcurrentOk
    && npObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedNpExceptionDesignOk
    && surrogateNpExceptionDesignOk
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

npExceptionLatticeNotGreenTable :: Bool
npExceptionLatticeNotGreenTable =
  npExceptionLatticeCount == 4
    && npExceptionLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && npExceptionProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && npExceptionChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

npExceptionContinuumLawsScaffold :: Bool
npExceptionContinuumLawsScaffold =
  npExceptionContinuumLawCount == 4
    && npExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNpExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

npExceptionContinuumLawsNotGreenTable :: Bool
npExceptionContinuumLawsNotGreenTable =
  npExceptionContinuumLawsScaffold
    && npExceptionContinuumLawCount /= 118 * 118
    && npExceptionProductChannelCount /= 118 * 118

npExceptionKnowingFiberOk :: Bool
npExceptionKnowingFiberOk = True

npExceptionContinuumInventRefuse :: Bool
npExceptionContinuumInventRefuse = not npExceptionContinuumProved

npExceptionLatticeNotXor :: Bool
npExceptionLatticeNotXor =
  unwiredDesignOk
    && assumedNpExceptionDesignOk
    && surrogateNpExceptionDesignOk
    && npExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNpExceptionRefuse

npExceptionContinuumProved :: Bool
npExceptionContinuumProved = False

speciesIdForked :: Bool
speciesIdForked = False

npExceptionContinuumNeSpeciesId :: Bool
npExceptionContinuumNeSpeciesId =
  npExceptionContinuumAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && npExceptionProductChannelAll /= []
    && npExceptionConcurrentBundleIsConcurrentProduct npExceptionNaturalContinuumWitness
    && not speciesIdForked

npExceptionContinuumFraming :: String
npExceptionContinuumFraming =
  "second_law_conservation_np_exception_continuum_one_axiom"

npExceptionContinuumAxiom :: Bool
npExceptionContinuumAxiom =
  npExceptionLatticeScaffold
    && npExceptionLatticeNotGreenTable
    && npExceptionContinuumLawsScaffold
    && npExceptionContinuumLawsNotGreenTable
    && npExceptionKnowingFiberOk
    && npZ93OccupancyEngineSortOk
    && npExceptionNaturalContinuumConcurrentOk
    && npObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventNpExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse
    && npExceptionContinuumInventRefuse
    && npExceptionLatticeNotXor
    && npExceptionContinuumNeSpeciesId
    && not npExceptionContinuumProved
    && not speciesIdForked
    && npExceptionContinuumFraming
      == "second_law_conservation_np_exception_continuum_one_axiom"

npExceptionContinuumNamed :: String
npExceptionContinuumNamed =
  "npExceptionContinuum: NpExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice npExceptionContinuumProved false evaluateNpExceptionBundle evaluateNpExceptionContinuum named Np Z=93 actinide occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not axiom refuse np ne SpeciesId fork second law conservation one axiom"

npExceptionContinuumAuthority :: String
npExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_093_np.rs"

goldschmidtContinuumAuthority :: String
goldschmidtContinuumAuthority =
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"

actinideOccupancyExceptionsAuthority :: String
actinideOccupancyExceptionsAuthority =
  "umst/umst-chem/src/qlattice.rs"

homologExceptionNotCopyAuthority :: String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

npExceptionContinuumCellId :: String
npExceptionContinuumCellId = "CHEM-FORMAL-Q-HS-NP-EXCEPTION-CONTINUUM"

npExceptionContinuumNonClaim :: String
npExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-HS-NP-EXCEPTION-CONTINUUM NpExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice npExceptionContinuumProved false evaluateNpExceptionBundle evaluateNpExceptionContinuum named Np Z=93 actinide occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not 26th axiom refuse cite occupancy_engine_sort homolog_exception_not_copy goldschmidt read-only np ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

npExceptionContinuumPhysicsGreenAuthorized :: Bool
npExceptionContinuumPhysicsGreenAuthorized = False

npExceptionContinuumPhysicsGreenFalse :: Bool
npExceptionContinuumPhysicsGreenFalse =
  not npExceptionContinuumPhysicsGreenAuthorized

npExceptionContinuumModalityUnwired :: Bool
npExceptionContinuumModalityUnwired =
  npExceptionContinuumModalityCurrent == NpExceptionContinuumUnwired

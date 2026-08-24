-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.CmExceptionContinuum
Description : Cm Z=96 **exception-continuum** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Cm exception continuum**: Actinide occupancy-engine sort witness Cm Z=96 as one second-law
**conservation** product (ore ⊗ isotope mix ⊗ purify Refine-cost ⊗ G-stability ⊗ Env) —
cite @occupancy_engine_sort@ + @homolog_exception_not_copy@ read-only; homolog ≠ copy;
**not** a 26th axiom. Named Cm natural-continuum identity conserved under honest scaffold;
trivial XOR, parallel occupancy axiom, homolog occupancy copy, and GREEN invent fail-closed.
Exception-continuum laws are structure witnesses only (@cmExceptionContinuumProved@ = False).
No SpeciesId fork.

* @CmExceptionContinuumModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateCmExceptionBundle@ — named Cm Z=96 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateCmExceptionContinuum@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@cmExceptionContinuumAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of Cm Z=96 exception continuum on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-CM-EXCEPTION-CONTINUUM@.
INT: umst/umst-chem/src/x_rows/cm_exception_continuum.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.CmExceptionContinuum
  ( CmExceptionContinuumModality (..)
  , cmExceptionContinuumModalityCurrent
  , cmExceptionLatticeAll
  , cmExceptionLatticeCount
  , curiumAtomicNumberZ
  , gadoliniumHomologZ
  , CmExceptionChannelSlot (..)
  , cmExceptionChannelSlotAll
  , cmExceptionChannelSlotCount
  , CmExceptionProductChannel (..)
  , cmExceptionProductChannelAll
  , cmExceptionProductChannelCount
  , cmExceptionProductChannelIndex
  , CmExceptionConcurrentBundle (..)
  , cmExceptionConcurrentBundleUnwired
  , cmExceptionConcurrentBundleWithChannel
  , cmExceptionConcurrentBundleWithPresent
  , cmExceptionConcurrentBundleChannelAt
  , cmExceptionConcurrentBundleHolds
  , cmExceptionConcurrentBundlePresentCount
  , cmExceptionConcurrentBundleIsConcurrentProduct
  , cmExceptionNaturalContinuumWitness
  , CmExceptionXorPosture (..)
  , cmExceptionXorPostureExclusive
  , cmExceptionXorPostureConcurrent
  , CmExceptionContinuumVerdict (..)
  , CmExceptionXorVerdict (..)
  , evaluateCmExceptionBundle
  , evaluateCmExceptionXor
  , evaluateCmExceptionContinuum
  , CmExceptionContinuumLaw (..)
  , cmExceptionContinuumLawAll
  , cmExceptionContinuumLawCount
  , sampleCmExceptionNaturalContinuumBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , cmExceptionNaturalContinuumConcurrentOk
  , cmZ96OccupancyEngineSortOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventCmExceptionRefuse
  , parallelOccupancyAxiomRefuse
  , homologOccupancyCopyRefuse
  , occupancyEngineSortNotAxiomRefuse
  , refineCostFloatPinRefuse
  , assumedCmExceptionDesignOk
  , surrogateCmExceptionDesignOk
  , cmExceptionLatticeScaffold
  , cmExceptionLatticeNotGreenTable
  , cmExceptionContinuumLawsScaffold
  , cmExceptionContinuumLawsNotGreenTable
  , cmExceptionKnowingFiberOk
  , cmExceptionContinuumInventRefuse
  , cmExceptionLatticeNotXor
  , cmExceptionContinuumProved
  , cmExceptionContinuumNeSpeciesId
  , speciesIdForked
  , gdHomologNotCmOccupancyCopy
  , cmObservedNePredictedOk
  , cmExceptionContinuumFraming
  , cmExceptionContinuumAxiom
  , cmExceptionContinuumNamed
  , cmExceptionContinuumAuthority
  , occupancyEngineSortAuthority
  , homologExceptionNotCopyAuthority
  , goldschmidtContinuumAuthority
  , actinideOccupancyExceptionsAuthority
  , cmExceptionContinuumCellId
  , cmExceptionContinuumNonClaim
  , cmExceptionContinuumPhysicsGreenAuthorized
  , cmExceptionContinuumPhysicsGreenFalse
  , cmExceptionContinuumModalityUnwired
  ) where

import UMST.ChemConstants.ActinideOccupancyExceptions
  ( ActinideException (Cm)
  , cmObservedNePredicted
  , actinideExceptionObservedNotation
  , actinideExceptionZ
  )
import UMST.ChemConstants.NamedOccupancyExceptions
  ( NamedException (Gd)
  , namedExceptionObservedNotation
  , namedExceptionZ
  )
import UMST.ChemConstants.OccupancyEngineSort
  ( OccupancyEngineSortBucket (ActinideExceptionBucket, NamedExceptionBucket)
  , occupancyEngineSortAuthority
  , occupancyEngineSortBucket
  , occupancyEngineSortNotSecondAxiom
  )

-- | IUPAC periodic-table cardinality (Z=1..118) — not Cm exception GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Curium Z=96 — Actinide occupancy exception witness pin.
curiumAtomicNumberZ :: Int
curiumAtomicNumberZ = 96

-- | Gadolinium Z=64 — lanthanide homolog witness pin (homolog ≠ copy).
gadoliniumHomologZ :: Int
gadoliniumHomologZ = 64

-- | Design **Cm exception continuum** modality for conservation claims.
data CmExceptionContinuumModality
  = CmExceptionContinuumUnwired
  | CmExceptionContinuumAssumed
  | CmExceptionContinuumProved
  | CmExceptionContinuumSurrogate
  deriving (Eq, Show)

-- | Current scaffold **Cm exception continuum** modality — always Unwired on this cell.
cmExceptionContinuumModalityCurrent :: CmExceptionContinuumModality
cmExceptionContinuumModalityCurrent = CmExceptionContinuumUnwired

-- | All Cm exception continuum lattice steps in stable order.
cmExceptionLatticeAll :: [CmExceptionContinuumModality]
cmExceptionLatticeAll =
  [ CmExceptionContinuumUnwired
  , CmExceptionContinuumAssumed
  , CmExceptionContinuumProved
  , CmExceptionContinuumSurrogate
  ]

cmExceptionLatticeCount :: Int
cmExceptionLatticeCount = length cmExceptionLatticeAll

-- | Cm exception continuum channel slot — concurrent **product** factor, not XOR bucket.
data CmExceptionChannelSlot
  = CmExceptionSlotUnwired
  | CmExceptionSlotAbsent
  | CmExceptionSlotPresent
  deriving (Eq, Show)

cmExceptionChannelSlotAll :: [CmExceptionChannelSlot]
cmExceptionChannelSlotAll =
  [ CmExceptionSlotUnwired
  , CmExceptionSlotAbsent
  , CmExceptionSlotPresent
  ]

cmExceptionChannelSlotCount :: Int
cmExceptionChannelSlotCount = length cmExceptionChannelSlotAll

-- | Named Cm natural-continuum product channels (ore ⊗ isotope ⊗ purify ⊗ G ⊗ Env).
data CmExceptionProductChannel
  = OreNaturalContinuum
  | IsotopeMixContinuum
  | PurifyRefineCostContinuum
  | GStabilityContinuum
  | EnvContinuum
  deriving (Eq, Show)

cmExceptionProductChannelAll :: [CmExceptionProductChannel]
cmExceptionProductChannelAll =
  [ OreNaturalContinuum
  , IsotopeMixContinuum
  , PurifyRefineCostContinuum
  , GStabilityContinuum
  , EnvContinuum
  ]

cmExceptionProductChannelCount :: Int
cmExceptionProductChannelCount = length cmExceptionProductChannelAll

cmExceptionProductChannelIndex :: CmExceptionProductChannel -> Int
cmExceptionProductChannelIndex channel =
  case channel of
    OreNaturalContinuum -> 0
    IsotopeMixContinuum -> 1
    PurifyRefineCostContinuum -> 2
    GStabilityContinuum -> 3
    EnvContinuum -> 4

-- | Cm Z=96 exception-continuum concurrent **product** bundle (north-star §3).
data CmExceptionConcurrentBundle = CmExceptionConcurrentBundle
  { cmExceptionClassPresent :: Bool
  , cmExceptionChannelSlots :: [CmExceptionChannelSlot]
  }
  deriving (Eq, Show)

cmExceptionConcurrentBundleUnwired :: CmExceptionConcurrentBundle
cmExceptionConcurrentBundleUnwired =
  CmExceptionConcurrentBundle
    False
    (replicate cmExceptionProductChannelCount CmExceptionSlotUnwired)

cmExceptionConcurrentBundleWithChannel ::
  Int -> CmExceptionChannelSlot -> CmExceptionConcurrentBundle -> CmExceptionConcurrentBundle
cmExceptionConcurrentBundleWithChannel idx slot bundle =
  let slots = cmExceptionChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in CmExceptionConcurrentBundle
        (cmExceptionClassPresent bundle)
        (before ++ [current] ++ after)

cmExceptionConcurrentBundleWithPresent ::
  Int -> CmExceptionConcurrentBundle -> CmExceptionConcurrentBundle
cmExceptionConcurrentBundleWithPresent idx bundle =
  cmExceptionConcurrentBundleWithChannel idx CmExceptionSlotPresent bundle

cmExceptionConcurrentBundleChannelAt ::
  Int -> CmExceptionConcurrentBundle -> Maybe CmExceptionChannelSlot
cmExceptionConcurrentBundleChannelAt idx bundle =
  let slots = cmExceptionChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

cmExceptionConcurrentBundleHolds :: Int -> CmExceptionConcurrentBundle -> Bool
cmExceptionConcurrentBundleHolds idx bundle =
  case cmExceptionConcurrentBundleChannelAt idx bundle of
    Just CmExceptionSlotPresent -> True
    _ -> False

cmExceptionConcurrentBundlePresentCount :: CmExceptionConcurrentBundle -> Int
cmExceptionConcurrentBundlePresentCount bundle =
  length (filter (== CmExceptionSlotPresent) (cmExceptionChannelSlots bundle))

cmExceptionConcurrentBundleIsConcurrentProduct :: CmExceptionConcurrentBundle -> Bool
cmExceptionConcurrentBundleIsConcurrentProduct bundle =
  cmExceptionConcurrentBundlePresentCount bundle >= 2

-- | Cm witness: ore (0) + isotope (1) + purify (2) + G (3) + Env (4) concurrent on Z=96.
cmExceptionNaturalContinuumWitness :: CmExceptionConcurrentBundle
cmExceptionNaturalContinuumWitness =
  cmExceptionConcurrentBundleWithPresent 4
    (cmExceptionConcurrentBundleWithPresent 3
      (cmExceptionConcurrentBundleWithPresent 2
        (cmExceptionConcurrentBundleWithPresent 1
          (cmExceptionConcurrentBundleWithPresent 0
            (CmExceptionConcurrentBundle True
              (replicate cmExceptionProductChannelCount CmExceptionSlotUnwired))))))

data CmExceptionXorPosture
  = CmExceptionXorExclusive
  | CmExceptionXorConcurrent
  deriving (Eq, Show)

cmExceptionXorPostureExclusive :: CmExceptionXorPosture
cmExceptionXorPostureExclusive = CmExceptionXorExclusive

cmExceptionXorPostureConcurrent :: CmExceptionXorPosture
cmExceptionXorPostureConcurrent = CmExceptionXorConcurrent

data CmExceptionContinuumVerdict
  = CmExceptionContinuumDesignOk
  | CmExceptionContinuumNamedOk
  | CmExceptionContinuumTrivialRefuse
  | CmExceptionContinuumGreenInventRefuse
  | CmExceptionContinuumProvedWithoutBarRefuse
  | CmExceptionContinuumXorRefuse
  deriving (Eq, Show)

data CmExceptionXorVerdict
  = CmExceptionXorDesignOk
  | CmExceptionXorNamedOk
  | CmExceptionXorGreenInventRefuse
  | CmExceptionXorProvedWithoutBarRefuse
  | CmExceptionXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

evaluateCmExceptionBundle ::
  CmExceptionContinuumModality
  -> CmExceptionConcurrentBundle
  -> Bool
  -> Bool
  -> CmExceptionContinuumVerdict
evaluateCmExceptionBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = CmExceptionContinuumGreenInventRefuse
  | claimProved = CmExceptionContinuumProvedWithoutBarRefuse
  | length (cmExceptionChannelSlots bundle) /= cmExceptionProductChannelCount =
      CmExceptionContinuumTrivialRefuse
  | otherwise =
      case modality of
        CmExceptionContinuumUnwired ->
          if cmExceptionConcurrentBundleIsConcurrentProduct bundle
            then CmExceptionContinuumNamedOk
            else CmExceptionContinuumDesignOk
        CmExceptionContinuumAssumed -> CmExceptionContinuumDesignOk
        CmExceptionContinuumSurrogate -> CmExceptionContinuumDesignOk
        CmExceptionContinuumProved -> CmExceptionContinuumProvedWithoutBarRefuse

evaluateCmExceptionXor ::
  CmExceptionContinuumModality
  -> CmExceptionXorPosture
  -> Bool
  -> Bool
  -> CmExceptionXorVerdict
evaluateCmExceptionXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = CmExceptionXorGreenInventRefuse
  | claimProved = CmExceptionXorProvedWithoutBarRefuse
  | posture == CmExceptionXorExclusive = CmExceptionXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        CmExceptionContinuumUnwired -> CmExceptionXorNamedOk
        CmExceptionContinuumAssumed -> CmExceptionXorDesignOk
        CmExceptionContinuumSurrogate -> CmExceptionXorDesignOk
        CmExceptionContinuumProved -> CmExceptionXorProvedWithoutBarRefuse

data CmExceptionContinuumLaw
  = CmExceptionContinuumConserved
  | NamedCmExceptionContinuumOk
  | TrivialCmExceptionRefused
  | GreenInventCmExceptionRefused
  deriving (Eq, Show)

cmExceptionContinuumLawAll :: [CmExceptionContinuumLaw]
cmExceptionContinuumLawAll =
  [ CmExceptionContinuumConserved
  , NamedCmExceptionContinuumOk
  , TrivialCmExceptionRefused
  , GreenInventCmExceptionRefused
  ]

cmExceptionContinuumLawCount :: Int
cmExceptionContinuumLawCount = length cmExceptionContinuumLawAll

evaluateCmExceptionContinuum ::
  CmExceptionContinuumModality
  -> CmExceptionConcurrentBundle
  -> CmExceptionXorPosture
  -> Bool
  -> Bool
  -> CmExceptionContinuumVerdict
evaluateCmExceptionContinuum modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = CmExceptionContinuumGreenInventRefuse
  | claimProved = CmExceptionContinuumProvedWithoutBarRefuse
  | otherwise =
      case evaluateCmExceptionXor modality posture False False of
        CmExceptionXorMutuallyExclusiveRefuse -> CmExceptionContinuumXorRefuse
        CmExceptionXorGreenInventRefuse -> CmExceptionContinuumGreenInventRefuse
        CmExceptionXorProvedWithoutBarRefuse -> CmExceptionContinuumProvedWithoutBarRefuse
        _ ->
          case evaluateCmExceptionBundle modality bundle False False of
            CmExceptionContinuumNamedOk -> CmExceptionContinuumNamedOk
            CmExceptionContinuumGreenInventRefuse -> CmExceptionContinuumGreenInventRefuse
            CmExceptionContinuumProvedWithoutBarRefuse -> CmExceptionContinuumProvedWithoutBarRefuse
            CmExceptionContinuumTrivialRefuse -> CmExceptionContinuumTrivialRefuse
            CmExceptionContinuumXorRefuse -> CmExceptionContinuumXorRefuse
            CmExceptionContinuumDesignOk -> CmExceptionContinuumDesignOk

sampleCmExceptionNaturalContinuumBundle :: CmExceptionConcurrentBundle
sampleCmExceptionNaturalContinuumBundle = cmExceptionNaturalContinuumWitness

sampleXorExclusiveBundle :: CmExceptionConcurrentBundle
sampleXorExclusiveBundle = cmExceptionConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: CmExceptionConcurrentBundle
sampleTrivialUnwiredBundle = cmExceptionConcurrentBundleUnwired

unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateCmExceptionContinuum
    CmExceptionContinuumUnwired
    sampleCmExceptionNaturalContinuumBundle
    cmExceptionXorPostureConcurrent
    False
    False
    == CmExceptionContinuumNamedOk

cmExceptionNaturalContinuumConcurrentOk :: Bool
cmExceptionNaturalContinuumConcurrentOk =
  let bundle = cmExceptionNaturalContinuumWitness
   in cmExceptionClassPresent bundle
        && cmExceptionConcurrentBundleHolds 0 bundle
        && cmExceptionConcurrentBundleHolds 1 bundle
        && cmExceptionConcurrentBundleHolds 2 bundle
        && cmExceptionConcurrentBundleHolds 3 bundle
        && cmExceptionConcurrentBundleHolds 4 bundle
        && cmExceptionConcurrentBundlePresentCount bundle == 5
        && cmExceptionConcurrentBundleIsConcurrentProduct bundle
        && curiumAtomicNumberZ == 96
        && actinideExceptionZ Cm == 96

cmZ96OccupancyEngineSortOk :: Bool
cmZ96OccupancyEngineSortOk =
  curiumAtomicNumberZ == 96
    && occupancyEngineSortBucket curiumAtomicNumberZ == ActinideExceptionBucket
    && cmExceptionProductChannelCount == 5
    && length (cmExceptionChannelSlots cmExceptionConcurrentBundleUnwired) == 5

cmObservedNePredictedOk :: Bool
cmObservedNePredictedOk = cmObservedNePredicted

gdHomologNotCmOccupancyCopy :: Bool
gdHomologNotCmOccupancyCopy =
  gadoliniumHomologZ == curiumAtomicNumberZ - 32
    && gadoliniumHomologZ /= curiumAtomicNumberZ
    && namedExceptionZ Gd == gadoliniumHomologZ
    && actinideExceptionObservedNotation Cm /= namedExceptionObservedNotation Gd
    && occupancyEngineSortBucket gadoliniumHomologZ == NamedExceptionBucket
    && occupancyEngineSortBucket curiumAtomicNumberZ == ActinideExceptionBucket

concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  cmExceptionConcurrentBundleIsConcurrentProduct cmExceptionNaturalContinuumWitness
    && cmExceptionConcurrentBundlePresentCount cmExceptionNaturalContinuumWitness >= 2
    && cmExceptionConcurrentBundlePresentCount cmExceptionNaturalContinuumWitness == 5

xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateCmExceptionXor
    CmExceptionContinuumUnwired
    cmExceptionXorPostureExclusive
    False
    False
    == CmExceptionXorMutuallyExclusiveRefuse
    && evaluateCmExceptionContinuum
      CmExceptionContinuumUnwired
      sampleCmExceptionNaturalContinuumBundle
      cmExceptionXorPostureExclusive
      False
      False
      == CmExceptionContinuumXorRefuse

greenInventCmExceptionRefuse :: Bool
greenInventCmExceptionRefuse =
  evaluateCmExceptionContinuum
    CmExceptionContinuumUnwired
    sampleCmExceptionNaturalContinuumBundle
    cmExceptionXorPostureConcurrent
    True
    False
    == CmExceptionContinuumGreenInventRefuse
    && evaluateCmExceptionBundle
      CmExceptionContinuumUnwired
      sampleCmExceptionNaturalContinuumBundle
      True
      False
      == CmExceptionContinuumGreenInventRefuse

parallelOccupancyAxiomRefuse :: Bool
parallelOccupancyAxiomRefuse =
  cmExceptionContinuumAuthority
    == "umst/umst-chem/src/x_rows/cm_exception_continuum.rs"
    && cmExceptionContinuumProved == False
    && not (cmExceptionContinuumAuthority == "26th_chemistry_axiom")
    && cmExceptionContinuumFraming
      /= "parallel_occupancy_axiom_not_second_law"
    && occupancyEngineSortNotSecondAxiom

homologOccupancyCopyRefuse :: Bool
homologOccupancyCopyRefuse =
  parallelOccupancyAxiomRefuse
    && cmExceptionContinuumFraming
      /= "homolog_occupancy_copy_smuggle"
    && homologExceptionNotCopyAuthority
      == "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"
    && gdHomologNotCmOccupancyCopyNotation

gdHomologNotCmOccupancyCopyNotation :: Bool
gdHomologNotCmOccupancyCopyNotation =
  actinideExceptionObservedNotation Cm
    /= namedExceptionObservedNotation Gd

occupancyEngineSortNotAxiomRefuse :: Bool
occupancyEngineSortNotAxiomRefuse =
  homologOccupancyCopyRefuse
    && cmExceptionContinuumFraming
      /= "occupancy_engine_sort_axiom_not_continuum"
    && occupancyEngineSortAuthority
      == "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
    && occupancyEngineSortNotSecondAxiom
    && curiumAtomicNumberZ == 96

refineCostFloatPinRefuse :: Bool
refineCostFloatPinRefuse =
  occupancyEngineSortNotAxiomRefuse
    && cmExceptionContinuumFraming
      /= "refine_cost_bare_float_pin_on_cm_continuum"
    && goldschmidtContinuumAuthority
      == "umst/umst-chem/src/l0_tables/goldschmidt.rs"
    && curiumAtomicNumberZ == 96

assumedCmExceptionDesignOk :: Bool
assumedCmExceptionDesignOk =
  evaluateCmExceptionContinuum
    CmExceptionContinuumAssumed
    sampleCmExceptionNaturalContinuumBundle
    cmExceptionXorPostureConcurrent
    False
    False
    == CmExceptionContinuumDesignOk

surrogateCmExceptionDesignOk :: Bool
surrogateCmExceptionDesignOk =
  evaluateCmExceptionContinuum
    CmExceptionContinuumSurrogate
    sampleCmExceptionNaturalContinuumBundle
    cmExceptionXorPostureConcurrent
    False
    False
    == CmExceptionContinuumDesignOk

cmExceptionLatticeScaffold :: Bool
cmExceptionLatticeScaffold =
  cmExceptionLatticeCount == 4
    && unwiredDesignOk
    && cmZ96OccupancyEngineSortOk
    && cmExceptionNaturalContinuumConcurrentOk
    && cmObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedCmExceptionDesignOk
    && surrogateCmExceptionDesignOk
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

cmExceptionLatticeNotGreenTable :: Bool
cmExceptionLatticeNotGreenTable =
  cmExceptionLatticeCount == 4
    && cmExceptionLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && cmExceptionProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && cmExceptionChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

cmExceptionContinuumLawsScaffold :: Bool
cmExceptionContinuumLawsScaffold =
  cmExceptionContinuumLawCount == 4
    && cmExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCmExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse

cmExceptionContinuumLawsNotGreenTable :: Bool
cmExceptionContinuumLawsNotGreenTable =
  cmExceptionContinuumLawsScaffold
    && cmExceptionContinuumLawCount /= 118 * 118
    && cmExceptionProductChannelCount /= 118 * 118

cmExceptionKnowingFiberOk :: Bool
cmExceptionKnowingFiberOk = True

cmExceptionContinuumInventRefuse :: Bool
cmExceptionContinuumInventRefuse = not cmExceptionContinuumProved

cmExceptionLatticeNotXor :: Bool
cmExceptionLatticeNotXor =
  unwiredDesignOk
    && assumedCmExceptionDesignOk
    && surrogateCmExceptionDesignOk
    && cmExceptionNaturalContinuumConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCmExceptionRefuse

cmExceptionContinuumProved :: Bool
cmExceptionContinuumProved = False

speciesIdForked :: Bool
speciesIdForked = False

cmExceptionContinuumNeSpeciesId :: Bool
cmExceptionContinuumNeSpeciesId =
  cmExceptionContinuumAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && cmExceptionProductChannelAll /= []
    && cmExceptionConcurrentBundleIsConcurrentProduct cmExceptionNaturalContinuumWitness
    && not speciesIdForked

cmExceptionContinuumFraming :: String
cmExceptionContinuumFraming =
  "second_law_conservation_cm_exception_continuum_one_axiom"

cmExceptionContinuumAxiom :: Bool
cmExceptionContinuumAxiom =
  cmExceptionLatticeScaffold
    && cmExceptionLatticeNotGreenTable
    && cmExceptionContinuumLawsScaffold
    && cmExceptionContinuumLawsNotGreenTable
    && cmExceptionKnowingFiberOk
    && cmZ96OccupancyEngineSortOk
    && cmExceptionNaturalContinuumConcurrentOk
    && cmObservedNePredictedOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventCmExceptionRefuse
    && parallelOccupancyAxiomRefuse
    && homologOccupancyCopyRefuse
    && occupancyEngineSortNotAxiomRefuse
    && refineCostFloatPinRefuse
    && cmExceptionContinuumInventRefuse
    && cmExceptionLatticeNotXor
    && cmExceptionContinuumNeSpeciesId
    && not cmExceptionContinuumProved
    && not speciesIdForked
    && cmExceptionContinuumFraming
      == "second_law_conservation_cm_exception_continuum_one_axiom"

cmExceptionContinuumNamed :: String
cmExceptionContinuumNamed =
  "cmExceptionContinuum: CmExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice cmExceptionContinuumProved false evaluateCmExceptionBundle evaluateCmExceptionContinuum named Cm Z=96 Actinide occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not axiom refuse cm ne SpeciesId fork second law conservation one axiom"

cmExceptionContinuumAuthority :: String
cmExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/cm_exception_continuum.rs"

goldschmidtContinuumAuthority :: String
goldschmidtContinuumAuthority =
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"

actinideOccupancyExceptionsAuthority :: String
actinideOccupancyExceptionsAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/ActinideOccupancyExceptions.hs"

homologExceptionNotCopyAuthority :: String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

cmExceptionContinuumCellId :: String
cmExceptionContinuumCellId = "CHEM-FORMAL-Q-HS-CM-EXCEPTION-CONTINUUM"

cmExceptionContinuumNonClaim :: String
cmExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-HS-CM-EXCEPTION-CONTINUUM CmExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice cmExceptionContinuumProved false evaluateCmExceptionBundle evaluateCmExceptionContinuum named Cm Z=96 Actinide occupancy engine sort ore isotope mix purify refine cost G stability Env concurrent product identity conserved present ge 2 product not XOR natural continuum witness concurrent xor mutually exclusive refuse parallel occupancy axiom refuse homolog occupancy copy refuse occupancy engine sort not 26th axiom refuse cite occupancy_engine_sort homolog_exception_not_copy goldschmidt read-only cm ne SpeciesId homolog Gd Z=64 not copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

cmExceptionContinuumPhysicsGreenAuthorized :: Bool
cmExceptionContinuumPhysicsGreenAuthorized = False

cmExceptionContinuumPhysicsGreenFalse :: Bool
cmExceptionContinuumPhysicsGreenFalse =
  not cmExceptionContinuumPhysicsGreenAuthorized

cmExceptionContinuumModalityUnwired :: Bool
cmExceptionContinuumModalityUnwired =
  cmExceptionContinuumModalityCurrent == CmExceptionContinuumUnwired

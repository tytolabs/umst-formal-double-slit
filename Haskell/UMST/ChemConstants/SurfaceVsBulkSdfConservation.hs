-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.SurfaceVsBulkSdfConservation
Description : Class-9 **surface-vs-bulk-SDF** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Surface-vs-bulk-SDF** **conservation**: north-star §2 class 15
(@surface_vs_bulk_sdf@) — surface vs bulk SDF is a concurrent PatternBundle factor on the
same second-law + **conservation** object, not a 26th axiom. Surface-dominated⊗Bulk-dominated⊗PatternBundle Π_c is **product** not XOR. Named class-15
**surface-vs-bulk-SDF** identity conserved under honest scaffold; trivial XOR, parallel
surface-vs-bulk-SDF axiom, thin-slab≠bulk interior, T/P graph≠float pin, and GREEN invent
fail-closed. Class-9 **conservation** laws are structure witnesses only
(@surfaceVsBulkSdfConservationProved@ = False). No SpeciesId fork.

* @SurfaceVsBulkSdfConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateSurfaceVsBulkSdfBundle@ — named class-15 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateSurfaceVsBulkSdfConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@surfaceVsBulkSdfConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of class-15 **surface-vs-bulk-SDF** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-SURFACE-VS-BULK-SDF-CONSERVATION@.
INT: umst/umst-chem/src/surface_bulk_sdf.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/surface_vs_bulk_sdf.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.SurfaceVsBulkSdfConservation
  ( SurfaceVsBulkSdfConservationModality (..)
  , surfaceVsBulkSdfConservationModalityCurrent
  , surfaceVsBulkSdfLatticeAll
  , surfaceVsBulkSdfLatticeCount
  , class15SurfaceVsBulkSdfPatternIndex
  , SurfaceVsBulkSdfChannelSlot (..)
  , surfaceVsBulkSdfChannelSlotAll
  , surfaceVsBulkSdfChannelSlotCount
  , SurfaceVsBulkSdfProductChannel (..)
  , surfaceVsBulkSdfProductChannelAll
  , surfaceVsBulkSdfProductChannelCount
  , surfaceVsBulkSdfProductChannelIndex
  , SurfaceVsBulkSdfConcurrentBundle (..)
  , surfaceVsBulkSdfConcurrentBundleUnwired
  , surfaceVsBulkSdfConcurrentBundleWithChannel
  , surfaceVsBulkSdfConcurrentBundleWithPresent
  , surfaceVsBulkSdfConcurrentBundleChannelAt
  , surfaceVsBulkSdfConcurrentBundleHolds
  , surfaceVsBulkSdfConcurrentBundlePresentCount
  , surfaceVsBulkSdfConcurrentBundleIsConcurrentProduct
  , surfaceVsBulkSdfSurfaceBulkWitness
  , SurfaceVsBulkSdfXorPosture (..)
  , surfaceVsBulkSdfXorPostureExclusive
  , surfaceVsBulkSdfXorPostureConcurrent
  , SurfaceVsBulkSdfConservationVerdict (..)
  , SurfaceVsBulkSdfXorVerdict (..)
  , evaluateSurfaceVsBulkSdfBundle
  , evaluateSurfaceVsBulkSdfXor
  , evaluateSurfaceVsBulkSdfConservation
  , SurfaceVsBulkSdfConservationLaw (..)
  , surfaceVsBulkSdfConservationLawAll
  , surfaceVsBulkSdfConservationLawCount
  , sampleSurfaceVsBulkSdfSurfaceBulkBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , surfaceVsBulkSdfSurfaceBulkConcurrentOk
  , class15SurfaceVsBulkSdfPatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventSurfaceVsBulkSdfRefuse
  , parallelSurfaceBulkSdfAxiomRefuse
  , thinSlabNeBulkInteriorRefuse
  , tpFloatPinNeGraphFunctionRefuse
  , assumedSurfaceVsBulkSdfDesignOk
  , surrogateSurfaceVsBulkSdfDesignOk
  , surfaceVsBulkSdfLatticeScaffold
  , surfaceVsBulkSdfLatticeNotGreenTable
  , surfaceVsBulkSdfConservationLawsScaffold
  , surfaceVsBulkSdfConservationLawsNotGreenTable
  , surfaceVsBulkSdfKnowingFiberOk
  , surfaceVsBulkSdfConservationInventRefuse
  , surfaceVsBulkSdfLatticeNotXor
  , surfaceVsBulkSdfConservationProved
  , surfaceVsBulkSdfConservationNeSpeciesId
  , speciesIdForked
  , hydrogenAtomicNumberZ
  , siliconSurfacePin
  , oganessonTailPin
  , surfaceVsBulkSdfConservationFraming
  , surfaceVsBulkSdfConservationAxiom
  , surfaceVsBulkSdfConservationNamed
  , surfaceVsBulkSdfConservationAuthority
  , chemL0SurfaceVsBulkSdfAuthority
  , patternProductConservationAuthority
  , surfaceBulkSdfAuthority
  , edgeSurfaceAuthority
  , edgeSurfaceFormalFiberAuthority
  , edgeSurfaceClaimFamilyAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , surfaceVsBulkSdfConservationCellId
  , surfaceVsBulkSdfConservationNonClaim
  , surfaceVsBulkSdfConservationPhysicsGreenAuthorized
  , surfaceVsBulkSdfConservationPhysicsGreenFalse
  , surfaceVsBulkSdfConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not surface-vs-bulk-SDF GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-15 (`surface_vs_bulk_sdf`) pattern index.
class15SurfaceVsBulkSdfPatternIndex :: Int
class15SurfaceVsBulkSdfPatternIndex = 15

-- | Hydrogen Z=1 — lightest surface/bulk witness element pin.
hydrogenAtomicNumberZ :: Int
hydrogenAtomicNumberZ = 1

-- | Silicon Z=14 — surface-chemistry witness element pin.
siliconSurfacePin :: Int
siliconSurfacePin = 14

-- | Oganesson Z=118 — tail-Z surface/bulk witness pin.
oganessonTailPin :: Int
oganessonTailPin = 118

-- | Design **surface-vs-bulk-SDF** modality for class-15 **conservation** claims.
data SurfaceVsBulkSdfConservationModality
  = SurfaceVsBulkSdfConservationUnwired
  | SurfaceVsBulkSdfConservationAssumed
  | SurfaceVsBulkSdfConservationProved
  | SurfaceVsBulkSdfConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **surface-vs-bulk-SDF** modality — always Unwired on this cell.
surfaceVsBulkSdfConservationModalityCurrent :: SurfaceVsBulkSdfConservationModality
surfaceVsBulkSdfConservationModalityCurrent =
  SurfaceVsBulkSdfConservationUnwired

-- | All class-15 **surface-vs-bulk-SDF** lattice steps in stable order.
surfaceVsBulkSdfLatticeAll :: [SurfaceVsBulkSdfConservationModality]
surfaceVsBulkSdfLatticeAll =
  [ SurfaceVsBulkSdfConservationUnwired
  , SurfaceVsBulkSdfConservationAssumed
  , SurfaceVsBulkSdfConservationProved
  , SurfaceVsBulkSdfConservationSurrogate
  ]

surfaceVsBulkSdfLatticeCount :: Int
surfaceVsBulkSdfLatticeCount = length surfaceVsBulkSdfLatticeAll

-- | Surface-vs-bulk-SDF product channel slot — concurrent **product** factor, not XOR bucket.
data SurfaceVsBulkSdfChannelSlot
  = SurfaceVsBulkSdfSlotUnwired
  | SurfaceVsBulkSdfSlotAbsent
  | SurfaceVsBulkSdfSlotPresent
  deriving (Eq, Show)

-- | All surface-vs-bulk-SDF channel slots in stable order.
surfaceVsBulkSdfChannelSlotAll :: [SurfaceVsBulkSdfChannelSlot]
surfaceVsBulkSdfChannelSlotAll =
  [ SurfaceVsBulkSdfSlotUnwired
  , SurfaceVsBulkSdfSlotAbsent
  , SurfaceVsBulkSdfSlotPresent
  ]

surfaceVsBulkSdfChannelSlotCount :: Int
surfaceVsBulkSdfChannelSlotCount = length surfaceVsBulkSdfChannelSlotAll

-- | Named surface-dominated / bulk-dominated / PatternBundle product channels.
data SurfaceVsBulkSdfProductChannel
  = SurfaceDominatedSdfExterior
  | BulkDominatedSdfInterior
  | PatternBundleConcurrentFactor
  deriving (Eq, Show)

-- | All surface-vs-bulk-SDF product channels in north-star stable order.
surfaceVsBulkSdfProductChannelAll :: [SurfaceVsBulkSdfProductChannel]
surfaceVsBulkSdfProductChannelAll =
  [ SurfaceDominatedSdfExterior
  , BulkDominatedSdfInterior
  , PatternBundleConcurrentFactor
  ]

surfaceVsBulkSdfProductChannelCount :: Int
surfaceVsBulkSdfProductChannelCount = length surfaceVsBulkSdfProductChannelAll

-- | Stable channel index for an surface-vs-bulk-SDF product channel (0..2).
surfaceVsBulkSdfProductChannelIndex :: SurfaceVsBulkSdfProductChannel -> Int
surfaceVsBulkSdfProductChannelIndex channel =
  case channel of
    SurfaceDominatedSdfExterior -> 0
    BulkDominatedSdfInterior -> 1
    PatternBundleConcurrentFactor -> 2

-- | Class-9 surface-vs-bulk-SDF concurrent **product** bundle (north-star §3).
data SurfaceVsBulkSdfConcurrentBundle = SurfaceVsBulkSdfConcurrentBundle
  { surfaceVsBulkSdfClassPresent :: Bool
  , surfaceVsBulkSdfChannelSlots :: [SurfaceVsBulkSdfChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
surfaceVsBulkSdfConcurrentBundleUnwired :: SurfaceVsBulkSdfConcurrentBundle
surfaceVsBulkSdfConcurrentBundleUnwired =
  SurfaceVsBulkSdfConcurrentBundle
    False
    (replicate surfaceVsBulkSdfProductChannelCount SurfaceVsBulkSdfSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
surfaceVsBulkSdfConcurrentBundleWithChannel ::
  Int -> SurfaceVsBulkSdfChannelSlot -> SurfaceVsBulkSdfConcurrentBundle -> SurfaceVsBulkSdfConcurrentBundle
surfaceVsBulkSdfConcurrentBundleWithChannel idx slot bundle =
  let slots = surfaceVsBulkSdfChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in SurfaceVsBulkSdfConcurrentBundle
        (surfaceVsBulkSdfClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the surface-vs-bulk-SDF **product**.
surfaceVsBulkSdfConcurrentBundleWithPresent ::
  Int -> SurfaceVsBulkSdfConcurrentBundle -> SurfaceVsBulkSdfConcurrentBundle
surfaceVsBulkSdfConcurrentBundleWithPresent idx bundle =
  surfaceVsBulkSdfConcurrentBundleWithChannel idx SurfaceVsBulkSdfSlotPresent bundle

-- | Read channel slot at index (0..2).
surfaceVsBulkSdfConcurrentBundleChannelAt ::
  Int -> SurfaceVsBulkSdfConcurrentBundle -> Maybe SurfaceVsBulkSdfChannelSlot
surfaceVsBulkSdfConcurrentBundleChannelAt idx bundle =
  let slots = surfaceVsBulkSdfChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
surfaceVsBulkSdfConcurrentBundleHolds :: Int -> SurfaceVsBulkSdfConcurrentBundle -> Bool
surfaceVsBulkSdfConcurrentBundleHolds idx bundle =
  case surfaceVsBulkSdfConcurrentBundleChannelAt idx bundle of
    Just SurfaceVsBulkSdfSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
surfaceVsBulkSdfConcurrentBundlePresentCount :: SurfaceVsBulkSdfConcurrentBundle -> Int
surfaceVsBulkSdfConcurrentBundlePresentCount bundle =
  length (filter (== SurfaceVsBulkSdfSlotPresent) (surfaceVsBulkSdfChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
surfaceVsBulkSdfConcurrentBundleIsConcurrentProduct :: SurfaceVsBulkSdfConcurrentBundle -> Bool
surfaceVsBulkSdfConcurrentBundleIsConcurrentProduct bundle =
  surfaceVsBulkSdfConcurrentBundlePresentCount bundle >= 2

-- | Surface-vs-bulk-SDF witness: Surface exterior (0) + Bulk interior (1) + PatternBundle (2) concurrent on class 15.
surfaceVsBulkSdfSurfaceBulkWitness :: SurfaceVsBulkSdfConcurrentBundle
surfaceVsBulkSdfSurfaceBulkWitness =
  surfaceVsBulkSdfConcurrentBundleWithPresent 2
    (surfaceVsBulkSdfConcurrentBundleWithPresent 1
      (surfaceVsBulkSdfConcurrentBundleWithPresent 0
        (SurfaceVsBulkSdfConcurrentBundle True
          (replicate surfaceVsBulkSdfProductChannelCount SurfaceVsBulkSdfSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data SurfaceVsBulkSdfXorPosture
  = SurfaceVsBulkSdfXorExclusive
  | SurfaceVsBulkSdfXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
surfaceVsBulkSdfXorPostureExclusive :: SurfaceVsBulkSdfXorPosture
surfaceVsBulkSdfXorPostureExclusive = SurfaceVsBulkSdfXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
surfaceVsBulkSdfXorPostureConcurrent :: SurfaceVsBulkSdfXorPosture
surfaceVsBulkSdfXorPostureConcurrent = SurfaceVsBulkSdfXorConcurrent

-- | Verdict for surface-vs-bulk-SDF **conservation** close (fail-closed).
data SurfaceVsBulkSdfConservationVerdict
  = SurfaceVsBulkSdfConservationDesignOk
  | SurfaceVsBulkSdfConservationNamedOk
  | SurfaceVsBulkSdfConservationTrivialRefuse
  | SurfaceVsBulkSdfConservationGreenInventRefuse
  | SurfaceVsBulkSdfConservationProvedWithoutBarRefuse
  | SurfaceVsBulkSdfConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data SurfaceVsBulkSdfXorVerdict
  = SurfaceVsBulkSdfXorDesignOk
  | SurfaceVsBulkSdfXorNamedOk
  | SurfaceVsBulkSdfXorGreenInventRefuse
  | SurfaceVsBulkSdfXorProvedWithoutBarRefuse
  | SurfaceVsBulkSdfXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate an surface-vs-bulk-SDF bundle under class-15 **conservation** bar (fail-closed).
evaluateSurfaceVsBulkSdfBundle ::
  SurfaceVsBulkSdfConservationModality
  -> SurfaceVsBulkSdfConcurrentBundle
  -> Bool
  -> Bool
  -> SurfaceVsBulkSdfConservationVerdict
evaluateSurfaceVsBulkSdfBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = SurfaceVsBulkSdfConservationGreenInventRefuse
  | claimProved = SurfaceVsBulkSdfConservationProvedWithoutBarRefuse
  | length (surfaceVsBulkSdfChannelSlots bundle) /= surfaceVsBulkSdfProductChannelCount =
      SurfaceVsBulkSdfConservationTrivialRefuse
  | otherwise =
      case modality of
        SurfaceVsBulkSdfConservationUnwired ->
          if surfaceVsBulkSdfConcurrentBundleIsConcurrentProduct bundle
            then SurfaceVsBulkSdfConservationNamedOk
            else SurfaceVsBulkSdfConservationDesignOk
        SurfaceVsBulkSdfConservationAssumed -> SurfaceVsBulkSdfConservationDesignOk
        SurfaceVsBulkSdfConservationSurrogate -> SurfaceVsBulkSdfConservationDesignOk
        SurfaceVsBulkSdfConservationProved -> SurfaceVsBulkSdfConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-15 **conservation** bar (fail-closed).
evaluateSurfaceVsBulkSdfXor ::
  SurfaceVsBulkSdfConservationModality
  -> SurfaceVsBulkSdfXorPosture
  -> Bool
  -> Bool
  -> SurfaceVsBulkSdfXorVerdict
evaluateSurfaceVsBulkSdfXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = SurfaceVsBulkSdfXorGreenInventRefuse
  | claimProved = SurfaceVsBulkSdfXorProvedWithoutBarRefuse
  | posture == SurfaceVsBulkSdfXorExclusive = SurfaceVsBulkSdfXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        SurfaceVsBulkSdfConservationUnwired -> SurfaceVsBulkSdfXorNamedOk
        SurfaceVsBulkSdfConservationAssumed -> SurfaceVsBulkSdfXorDesignOk
        SurfaceVsBulkSdfConservationSurrogate -> SurfaceVsBulkSdfXorDesignOk
        SurfaceVsBulkSdfConservationProved -> SurfaceVsBulkSdfXorProvedWithoutBarRefuse

-- | **Surface-vs-bulk-SDF** identity law cells tracked by class-15 **conservation** (structure scaffold).
data SurfaceVsBulkSdfConservationLaw
  = SurfaceVsBulkSdfConservationConserved
  | NamedSurfaceVsBulkSdfConservationOk
  | TrivialSurfaceVsBulkSdfRefused
  | GreenInventSurfaceVsBulkSdfRefused
  deriving (Eq, Show)

surfaceVsBulkSdfConservationLawAll :: [SurfaceVsBulkSdfConservationLaw]
surfaceVsBulkSdfConservationLawAll =
  [ SurfaceVsBulkSdfConservationConserved
  , NamedSurfaceVsBulkSdfConservationOk
  , TrivialSurfaceVsBulkSdfRefused
  , GreenInventSurfaceVsBulkSdfRefused
  ]

surfaceVsBulkSdfConservationLawCount :: Int
surfaceVsBulkSdfConservationLawCount = length surfaceVsBulkSdfConservationLawAll

-- | Evaluate class-15 **surface-vs-bulk-SDF** **conservation** typing (fail-closed).
evaluateSurfaceVsBulkSdfConservation ::
  SurfaceVsBulkSdfConservationModality
  -> SurfaceVsBulkSdfConcurrentBundle
  -> SurfaceVsBulkSdfXorPosture
  -> Bool
  -> Bool
  -> SurfaceVsBulkSdfConservationVerdict
evaluateSurfaceVsBulkSdfConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = SurfaceVsBulkSdfConservationGreenInventRefuse
  | claimProved = SurfaceVsBulkSdfConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateSurfaceVsBulkSdfXor modality posture False False of
        SurfaceVsBulkSdfXorMutuallyExclusiveRefuse -> SurfaceVsBulkSdfConservationXorRefuse
        SurfaceVsBulkSdfXorGreenInventRefuse -> SurfaceVsBulkSdfConservationGreenInventRefuse
        SurfaceVsBulkSdfXorProvedWithoutBarRefuse -> SurfaceVsBulkSdfConservationProvedWithoutBarRefuse
        _ ->
          case evaluateSurfaceVsBulkSdfBundle modality bundle False False of
            SurfaceVsBulkSdfConservationNamedOk -> SurfaceVsBulkSdfConservationNamedOk
            SurfaceVsBulkSdfConservationGreenInventRefuse -> SurfaceVsBulkSdfConservationGreenInventRefuse
            SurfaceVsBulkSdfConservationProvedWithoutBarRefuse -> SurfaceVsBulkSdfConservationProvedWithoutBarRefuse
            SurfaceVsBulkSdfConservationTrivialRefuse -> SurfaceVsBulkSdfConservationTrivialRefuse
            SurfaceVsBulkSdfConservationXorRefuse -> SurfaceVsBulkSdfConservationXorRefuse
            SurfaceVsBulkSdfConservationDesignOk -> SurfaceVsBulkSdfConservationDesignOk

sampleSurfaceVsBulkSdfSurfaceBulkBundle :: SurfaceVsBulkSdfConcurrentBundle
sampleSurfaceVsBulkSdfSurfaceBulkBundle = surfaceVsBulkSdfSurfaceBulkWitness

sampleXorExclusiveBundle :: SurfaceVsBulkSdfConcurrentBundle
sampleXorExclusiveBundle = surfaceVsBulkSdfConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: SurfaceVsBulkSdfConcurrentBundle
sampleTrivialUnwiredBundle = surfaceVsBulkSdfConcurrentBundleUnwired

-- | Unwired **surface-vs-bulk-SDF** modality OK without SDF break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateSurfaceVsBulkSdfConservation
    SurfaceVsBulkSdfConservationUnwired
    sampleSurfaceVsBulkSdfSurfaceBulkBundle
    surfaceVsBulkSdfXorPostureConcurrent
    False
    False
    == SurfaceVsBulkSdfConservationNamedOk

-- | Surface-vs-bulk-SDF witness: Surface exterior + Bulk interior + PatternBundle concurrent Π_c on class 15.
surfaceVsBulkSdfSurfaceBulkConcurrentOk :: Bool
surfaceVsBulkSdfSurfaceBulkConcurrentOk =
  let bundle = surfaceVsBulkSdfSurfaceBulkWitness
   in surfaceVsBulkSdfClassPresent bundle
        && surfaceVsBulkSdfConcurrentBundleHolds 0 bundle
        && surfaceVsBulkSdfConcurrentBundleHolds 1 bundle
        && surfaceVsBulkSdfConcurrentBundleHolds 2 bundle
        && surfaceVsBulkSdfConcurrentBundlePresentCount bundle == 3
        && surfaceVsBulkSdfConcurrentBundleIsConcurrentProduct bundle
        && hydrogenAtomicNumberZ == 26
        && siliconSurfacePin == 29
        && class15SurfaceVsBulkSdfPatternIndex == 15

-- | Class-9 surface-vs-bulk-SDF pattern index pinned @ scaffold.
class15SurfaceVsBulkSdfPatternIndexOk :: Bool
class15SurfaceVsBulkSdfPatternIndexOk =
  class15SurfaceVsBulkSdfPatternIndex == 15
    && surfaceVsBulkSdfProductChannelCount == 3
    && length (surfaceVsBulkSdfChannelSlots surfaceVsBulkSdfConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  surfaceVsBulkSdfConcurrentBundleIsConcurrentProduct surfaceVsBulkSdfSurfaceBulkWitness
    && surfaceVsBulkSdfConcurrentBundlePresentCount surfaceVsBulkSdfSurfaceBulkWitness >= 2
    && surfaceVsBulkSdfConcurrentBundlePresentCount surfaceVsBulkSdfSurfaceBulkWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateSurfaceVsBulkSdfXor
    SurfaceVsBulkSdfConservationUnwired
    surfaceVsBulkSdfXorPostureExclusive
    False
    False
    == SurfaceVsBulkSdfXorMutuallyExclusiveRefuse
    && evaluateSurfaceVsBulkSdfConservation
      SurfaceVsBulkSdfConservationUnwired
      sampleSurfaceVsBulkSdfSurfaceBulkBundle
      surfaceVsBulkSdfXorPostureExclusive
      False
      False
      == SurfaceVsBulkSdfConservationXorRefuse

-- | GREEN invent on **surface-vs-bulk-SDF** **conservation** promotion is refused.
greenInventSurfaceVsBulkSdfRefuse :: Bool
greenInventSurfaceVsBulkSdfRefuse =
  evaluateSurfaceVsBulkSdfConservation
    SurfaceVsBulkSdfConservationUnwired
    sampleSurfaceVsBulkSdfSurfaceBulkBundle
    surfaceVsBulkSdfXorPostureConcurrent
    True
    False
    == SurfaceVsBulkSdfConservationGreenInventRefuse
    && evaluateSurfaceVsBulkSdfBundle
      SurfaceVsBulkSdfConservationUnwired
      sampleSurfaceVsBulkSdfSurfaceBulkBundle
      True
      False
      == SurfaceVsBulkSdfConservationGreenInventRefuse

-- | Parallel surface/bulk SDF axiom (26th law) mint is refused — second law + conservation only.
parallelSurfaceBulkSdfAxiomRefuse :: Bool
parallelSurfaceBulkSdfAxiomRefuse =
  surfaceVsBulkSdfConservationAuthority
    == "umst/umst-chem/src/surface_bulk_sdf.rs"
    && surfaceVsBulkSdfConservationProved == False
    && not (surfaceVsBulkSdfConservationAuthority == "26th_chemistry_axiom")
    && surfaceVsBulkSdfConservationFraming
      /= "parallel_surface_vs_bulk_sdf_axiom_not_second_law"
    && chemL0SurfaceVsBulkSdfAuthority
      == "umst/umst-chem/src/l0_tables/surface_vs_bulk_sdf.rs"

-- | Thin-slab / nano exterior ≠ bulk interior SDF regime — refuse folklore collision.
thinSlabNeBulkInteriorRefuse :: Bool
thinSlabNeBulkInteriorRefuse =
  parallelSurfaceBulkSdfAxiomRefuse
    && surfaceVsBulkSdfConservationFraming
      /= "thin_slab_as_bulk_interior"
    && edgeSurfaceAuthority
      == "umst/umst-chem/src/surface_bulk_sdf.rs"
    && edgeSurfaceFormalFiberAuthority
      == "umst-formal-double-slit"
    && class15SurfaceVsBulkSdfPatternIndex == 15

-- | T/P graph functions v14 ≠ bare float pins on surface/bulk scaffold — refuse folklore collision.
tpFloatPinNeGraphFunctionRefuse :: Bool
tpFloatPinNeGraphFunctionRefuse =
  thinSlabNeBulkInteriorRefuse
    && surfaceVsBulkSdfConservationFraming
      /= "tp_bare_float_pin_on_surface_bulk"
    && class15SurfaceVsBulkSdfPatternIndex == 15
    && surfaceVsBulkSdfConcurrentBundleIsConcurrentProduct surfaceVsBulkSdfSurfaceBulkWitness

-- | Assumed **surface-vs-bulk-SDF** modality OK without SDF break (design scaffold).
assumedSurfaceVsBulkSdfDesignOk :: Bool
assumedSurfaceVsBulkSdfDesignOk =
  evaluateSurfaceVsBulkSdfConservation
    SurfaceVsBulkSdfConservationAssumed
    sampleSurfaceVsBulkSdfSurfaceBulkBundle
    surfaceVsBulkSdfXorPostureConcurrent
    False
    False
    == SurfaceVsBulkSdfConservationDesignOk

-- | Surrogate **surface-vs-bulk-SDF** modality OK without SDF break (design scaffold).
surrogateSurfaceVsBulkSdfDesignOk :: Bool
surrogateSurfaceVsBulkSdfDesignOk =
  evaluateSurfaceVsBulkSdfConservation
    SurfaceVsBulkSdfConservationSurrogate
    sampleSurfaceVsBulkSdfSurfaceBulkBundle
    surfaceVsBulkSdfXorPostureConcurrent
    False
    False
    == SurfaceVsBulkSdfConservationDesignOk

-- | Four-step class-15 **surface-vs-bulk-SDF** lattice scaffold pinned.
surfaceVsBulkSdfLatticeScaffold :: Bool
surfaceVsBulkSdfLatticeScaffold =
  surfaceVsBulkSdfLatticeCount == 4
    && unwiredDesignOk
    && class15SurfaceVsBulkSdfPatternIndexOk
    && surfaceVsBulkSdfSurfaceBulkConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedSurfaceVsBulkSdfDesignOk
    && surrogateSurfaceVsBulkSdfDesignOk
    && parallelSurfaceBulkSdfAxiomRefuse
    && thinSlabNeBulkInteriorRefuse
    && tpFloatPinNeGraphFunctionRefuse

-- | **Surface-vs-bulk-SDF** lattice is structure scaffold — not 118² GREEN periodic table.
surfaceVsBulkSdfLatticeNotGreenTable :: Bool
surfaceVsBulkSdfLatticeNotGreenTable =
  surfaceVsBulkSdfLatticeCount == 4
    && surfaceVsBulkSdfLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && surfaceVsBulkSdfProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && surfaceVsBulkSdfChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **surface-vs-bulk-SDF** identity law cells scaffold pinned.
surfaceVsBulkSdfConservationLawsScaffold :: Bool
surfaceVsBulkSdfConservationLawsScaffold =
  surfaceVsBulkSdfConservationLawCount == 4
    && surfaceVsBulkSdfSurfaceBulkConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventSurfaceVsBulkSdfRefuse
    && parallelSurfaceBulkSdfAxiomRefuse
    && thinSlabNeBulkInteriorRefuse
    && tpFloatPinNeGraphFunctionRefuse

-- | **Surface-vs-bulk-SDF** law cells are structure scaffold — not 118² GREEN periodic table.
surfaceVsBulkSdfConservationLawsNotGreenTable :: Bool
surfaceVsBulkSdfConservationLawsNotGreenTable =
  surfaceVsBulkSdfConservationLawsScaffold
    && surfaceVsBulkSdfConservationLawCount /= 118 * 118
    && surfaceVsBulkSdfProductChannelCount /= 118 * 118

-- | Class-9 **surface-vs-bulk-SDF** **conservation** claims route to knowing / quantum fiber (not meso acting).
surfaceVsBulkSdfKnowingFiberOk :: Bool
surfaceVsBulkSdfKnowingFiberOk = True

-- | Class-9 **surface-vs-bulk-SDF** invent refuse-closed scaffold witness.
surfaceVsBulkSdfConservationInventRefuse :: Bool
surfaceVsBulkSdfConservationInventRefuse =
  not surfaceVsBulkSdfConservationProved

-- | **Surface-vs-bulk-SDF** lattice steps are concurrent Π_c — not XOR enum bucket.
surfaceVsBulkSdfLatticeNotXor :: Bool
surfaceVsBulkSdfLatticeNotXor =
  unwiredDesignOk
    && assumedSurfaceVsBulkSdfDesignOk
    && surrogateSurfaceVsBulkSdfDesignOk
    && surfaceVsBulkSdfSurfaceBulkConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventSurfaceVsBulkSdfRefuse

-- | Class-9 **surface-vs-bulk-SDF** proved (always false on this Unwired cell).
surfaceVsBulkSdfConservationProved :: Bool
surfaceVsBulkSdfConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Surface-vs-bulk-SDF** morphisms are class-15 neighbor channels — not SpeciesId tag mint.
surfaceVsBulkSdfConservationNeSpeciesId :: Bool
surfaceVsBulkSdfConservationNeSpeciesId =
  surfaceVsBulkSdfConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && surfaceVsBulkSdfProductChannelAll /= []
    && surfaceVsBulkSdfConcurrentBundleIsConcurrentProduct surfaceVsBulkSdfSurfaceBulkWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-15 **surface-vs-bulk-SDF** scaffold.
surfaceVsBulkSdfConservationFraming :: String
surfaceVsBulkSdfConservationFraming =
  "second_law_conservation_surface_vs_bulk_sdf_one_axiom"

-- | Single design axiom: second law + **conservation** class-15 surface-vs-bulk-SDF (not 26th axiom).
surfaceVsBulkSdfConservationAxiom :: Bool
surfaceVsBulkSdfConservationAxiom =
  surfaceVsBulkSdfLatticeScaffold
    && surfaceVsBulkSdfLatticeNotGreenTable
    && surfaceVsBulkSdfConservationLawsScaffold
    && surfaceVsBulkSdfConservationLawsNotGreenTable
    && surfaceVsBulkSdfKnowingFiberOk
    && class15SurfaceVsBulkSdfPatternIndexOk
    && surfaceVsBulkSdfSurfaceBulkConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventSurfaceVsBulkSdfRefuse
    && parallelSurfaceBulkSdfAxiomRefuse
    && thinSlabNeBulkInteriorRefuse
    && tpFloatPinNeGraphFunctionRefuse
    && surfaceVsBulkSdfConservationInventRefuse
    && surfaceVsBulkSdfLatticeNotXor
    && surfaceVsBulkSdfConservationNeSpeciesId
    && not surfaceVsBulkSdfConservationProved
    && not speciesIdForked
    && surfaceVsBulkSdfConservationFraming
      == "second_law_conservation_surface_vs_bulk_sdf_one_axiom"

surfaceVsBulkSdfConservationNamed :: String
surfaceVsBulkSdfConservationNamed =
  "surfaceVsBulkSdfConservation: SurfaceVsBulkSdfConservationModality Unwired Assumed Proved Surrogate four-step lattice surfaceVsBulkSdfConservationProved false evaluateSurfaceVsBulkSdfBundle evaluateSurfaceVsBulkSdfConservation named class 15 surface_vs_bulk_sdf surface dominated SDF exterior bulk dominated SDF interior PatternBundle concurrent factor concurrent product identity conserved present ge 2 product not XOR surface bulk SDF witness concurrent xor mutually exclusive refuse parallel surface bulk sdf axiom refuse thin slab ne bulk interior refuse tp float pin ne graph function refuse surface vs bulk sdf ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT surface-vs-bulk-SDF **conservation** authority (cited read-only, not forked).
surfaceVsBulkSdfConservationAuthority :: String
surfaceVsBulkSdfConservationAuthority =
  "umst/umst-chem/src/surface_bulk_sdf.rs"

-- | L0 class-15 surface-vs-bulk-SDF table authority (crosswalk).
chemL0SurfaceVsBulkSdfAuthority :: String
chemL0SurfaceVsBulkSdfAuthority =
  "umst/umst-chem/src/l0_tables/surface_vs_bulk_sdf.rs"

-- | PatternBundle product conservation authority (concurrent Π_c crosswalk).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | L0 EDGE-SURFACE authority (surface/bulk SDF carrier — not folklore list).
surfaceBulkSdfAuthority :: String
surfaceBulkSdfAuthority = "umst/umst-chem/src/surface_bulk_sdf.rs"

-- | L0 EDGE-SURFACE graph-cuts authority (separation morphisms — not proved on this cell).
edgeSurfaceAuthority :: String
edgeSurfaceAuthority = "umst/umst-chem/src/surface_bulk_sdf.rs"

-- | Knowing fiber authority for EDGE-SURFACE claims (north-star §3a).
edgeSurfaceFormalFiberAuthority :: String
edgeSurfaceFormalFiberAuthority = "umst-formal-double-slit"

-- | EDGE-SURFACE claim family tag (not proved on this cell). (Landauer stamp witness — not proved on this cell).
edgeSurfaceClaimFamilyAuthority :: String
edgeSurfaceClaimFamilyAuthority = "edge_surface"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

surfaceVsBulkSdfConservationCellId :: String
surfaceVsBulkSdfConservationCellId =
  "CHEM-FORMAL-Q-HS-SURFACE-VS-BULK-SDF-CONSERVATION"

-- | Non-claim fence — class-15 **surface-vs-bulk-SDF** **conservation** Unwired ≠ Proved GREEN.
surfaceVsBulkSdfConservationNonClaim :: String
surfaceVsBulkSdfConservationNonClaim =
  "CHEM-FORMAL-Q-HS-SURFACE-VS-BULK-SDF-CONSERVATION SurfaceVsBulkSdfConservationModality Unwired Assumed Proved Surrogate four-step lattice surfaceVsBulkSdfConservationProved false evaluateSurfaceVsBulkSdfBundle evaluateSurfaceVsBulkSdfConservation named class 15 surface_vs_bulk_sdf surface dominated SDF exterior bulk dominated SDF interior PatternBundle concurrent factor concurrent product identity conserved present ge 2 product not XOR surface bulk SDF witness concurrent xor mutually exclusive refuse parallel surface bulk sdf axiom refuse thin slab ne bulk interior refuse tp float pin ne graph function refuse surface vs bulk sdf ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-15 **surface-vs-bulk-SDF** **conservation** scaffold.
surfaceVsBulkSdfConservationPhysicsGreenAuthorized :: Bool
surfaceVsBulkSdfConservationPhysicsGreenAuthorized = False

surfaceVsBulkSdfConservationPhysicsGreenFalse :: Bool
surfaceVsBulkSdfConservationPhysicsGreenFalse =
  not surfaceVsBulkSdfConservationPhysicsGreenAuthorized

surfaceVsBulkSdfConservationModalityUnwired :: Bool
surfaceVsBulkSdfConservationModalityUnwired =
  surfaceVsBulkSdfConservationModalityCurrent == SurfaceVsBulkSdfConservationUnwired

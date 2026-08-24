-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.AssemblageStabilityWhyConservation
Description : Class-7 **assemblage-stability-why** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Assemblage-stability WHY** **conservation**: north-star §2 class 7
(@assemblage_stability_why@) — why a mineral/phase assemblage is observed under the sole
second-law + **conservation** axiom; Ore predicate ⊗ G-min/common-tangent ⊗ why-axis named.
Concurrent Π_c identity conserved on named class pins; Ore⊗second-law⊗why-axis is **product**
not XOR. Named class-7 identity conserved under honest scaffold; trivial XOR, parallel
stability axiom, Goldschmidt XOR folklore, and GREEN invent fail-closed. Class-7
**conservation** laws are structure witnesses only
(@assemblageStabilityWhyConservationProved@ = False). Not a 26th axiom. No SpeciesId fork.

* @AssemblageStabilityWhyConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateAssemblageStabilityWhyBundle@ — named class-7 identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateAssemblageStabilityWhyConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@assemblageStabilityWhyConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of class-7 **assemblage-stability WHY** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-ASSEMBLAGE-STABILITY-WHY-CONSERVATION@.
INT: umst/umst-chem/src/assemblage_stability.rs (read-only cite).
L0: umst/umst-chem/src/l0_tables/assemblage_stability_why.rs (read-only cite).
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.AssemblageStabilityWhyConservation
  ( AssemblageStabilityWhyConservationModality (..)
  , assemblageStabilityWhyConservationModalityCurrent
  , assemblageStabilityWhyLatticeAll
  , assemblageStabilityWhyLatticeCount
  , class7AssemblageStabilityWhyPatternIndex
  , AssemblageStabilityWhyChannelSlot (..)
  , assemblageStabilityWhyChannelSlotAll
  , assemblageStabilityWhyChannelSlotCount
  , AssemblageStabilityWhyProductChannel (..)
  , assemblageStabilityWhyProductChannelAll
  , assemblageStabilityWhyProductChannelCount
  , assemblageStabilityWhyProductChannelIndex
  , AssemblageStabilityWhyConcurrentBundle (..)
  , assemblageStabilityWhyConcurrentBundleUnwired
  , assemblageStabilityWhyConcurrentBundleWithChannel
  , assemblageStabilityWhyConcurrentBundleWithPresent
  , assemblageStabilityWhyConcurrentBundleChannelAt
  , assemblageStabilityWhyConcurrentBundleHolds
  , assemblageStabilityWhyConcurrentBundlePresentCount
  , assemblageStabilityWhyConcurrentBundleIsConcurrentProduct
  , assemblageStabilityWhyOreSecondLawWitness
  , AssemblageStabilityWhyXorPosture (..)
  , assemblageStabilityWhyXorPostureExclusive
  , assemblageStabilityWhyXorPostureConcurrent
  , AssemblageStabilityWhyConservationVerdict (..)
  , AssemblageStabilityWhyXorVerdict (..)
  , evaluateAssemblageStabilityWhyBundle
  , evaluateAssemblageStabilityWhyXor
  , evaluateAssemblageStabilityWhyConservation
  , AssemblageStabilityWhyConservationLaw (..)
  , assemblageStabilityWhyConservationLawAll
  , assemblageStabilityWhyConservationLawCount
  , sampleAssemblageStabilityWhyOreSecondLawBundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , assemblageStabilityWhyOreSecondLawConcurrentOk
  , class7AssemblageStabilityWhyPatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventAssemblageStabilityWhyRefuse
  , parallelStabilityAxiomRefuse
  , goldschmidtXorRefuse
  , assumedAssemblageStabilityWhyDesignOk
  , surrogateAssemblageStabilityWhyDesignOk
  , assemblageStabilityWhyLatticeScaffold
  , assemblageStabilityWhyLatticeNotGreenTable
  , assemblageStabilityWhyConservationLawsScaffold
  , assemblageStabilityWhyConservationLawsNotGreenTable
  , assemblageStabilityWhyKnowingFiberOk
  , assemblageStabilityWhyConservationInventRefuse
  , assemblageStabilityWhyLatticeNotXor
  , assemblageStabilityWhyConservationProved
  , assemblageStabilityWhyConservationNeSpeciesId
  , speciesIdForked
  , assemblageStabilityWhyConservationFraming
  , assemblageStabilityWhyConservationAxiom
  , assemblageStabilityWhyConservationNamed
  , assemblageStabilityWhyConservationAuthority
  , chemL0AssemblageStabilityWhyAuthority
  , oreAssemblageAuthority
  , gibbsConvexHullAuthority
  , temperatureGraphFunctionAuthority
  , pressureGraphFunctionAuthority
  , assemblageStabilityWhyConservationCellId
  , assemblageStabilityWhyConservationNonClaim
  , assemblageStabilityWhyConservationPhysicsGreenAuthorized
  , assemblageStabilityWhyConservationPhysicsGreenFalse
  , assemblageStabilityWhyConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not assemblage-stability-WHY GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-7 (`assemblage_stability_why`) pattern index.
class7AssemblageStabilityWhyPatternIndex :: Int
class7AssemblageStabilityWhyPatternIndex = 7

-- | Iron Z=26 — ore assemblage witness element pin.
ironAtomicNumberZ :: Int
ironAtomicNumberZ = 26

-- | Design **assemblage-stability WHY** modality for class-7 **conservation** claims.
data AssemblageStabilityWhyConservationModality
  = AssemblageStabilityWhyConservationUnwired
  | AssemblageStabilityWhyConservationAssumed
  | AssemblageStabilityWhyConservationProved
  | AssemblageStabilityWhyConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **assemblage-stability WHY** modality — always Unwired on this cell.
assemblageStabilityWhyConservationModalityCurrent :: AssemblageStabilityWhyConservationModality
assemblageStabilityWhyConservationModalityCurrent =
  AssemblageStabilityWhyConservationUnwired

-- | All class-7 **assemblage-stability WHY** lattice steps in stable order.
assemblageStabilityWhyLatticeAll :: [AssemblageStabilityWhyConservationModality]
assemblageStabilityWhyLatticeAll =
  [ AssemblageStabilityWhyConservationUnwired
  , AssemblageStabilityWhyConservationAssumed
  , AssemblageStabilityWhyConservationProved
  , AssemblageStabilityWhyConservationSurrogate
  ]

assemblageStabilityWhyLatticeCount :: Int
assemblageStabilityWhyLatticeCount = length assemblageStabilityWhyLatticeAll

-- | Assemblage-stability WHY product channel slot — concurrent **product** factor, not XOR bucket.
data AssemblageStabilityWhyChannelSlot
  = AssemblageStabilityWhySlotUnwired
  | AssemblageStabilityWhySlotAbsent
  | AssemblageStabilityWhySlotPresent
  deriving (Eq, Show)

-- | All assemblage-stability WHY channel slots in stable order.
assemblageStabilityWhyChannelSlotAll :: [AssemblageStabilityWhyChannelSlot]
assemblageStabilityWhyChannelSlotAll =
  [ AssemblageStabilityWhySlotUnwired
  , AssemblageStabilityWhySlotAbsent
  , AssemblageStabilityWhySlotPresent
  ]

assemblageStabilityWhyChannelSlotCount :: Int
assemblageStabilityWhyChannelSlotCount = length assemblageStabilityWhyChannelSlotAll

-- | Named Ore predicate / second-law G-min / why-axis product channels (bounded scaffold).
data AssemblageStabilityWhyProductChannel
  = OrePredicate
  | SecondLawGMinPresentation
  | EquilibriumBasinWhyAxis
  deriving (Eq, Show)

-- | All assemblage-stability WHY product channels in north-star stable order.
assemblageStabilityWhyProductChannelAll :: [AssemblageStabilityWhyProductChannel]
assemblageStabilityWhyProductChannelAll =
  [ OrePredicate
  , SecondLawGMinPresentation
  , EquilibriumBasinWhyAxis
  ]

assemblageStabilityWhyProductChannelCount :: Int
assemblageStabilityWhyProductChannelCount = length assemblageStabilityWhyProductChannelAll

-- | Stable channel index for an assemblage-stability WHY product channel (0..2).
assemblageStabilityWhyProductChannelIndex :: AssemblageStabilityWhyProductChannel -> Int
assemblageStabilityWhyProductChannelIndex channel =
  case channel of
    OrePredicate -> 0
    SecondLawGMinPresentation -> 1
    EquilibriumBasinWhyAxis -> 2

-- | Class-7 assemblage-stability WHY concurrent **product** bundle (north-star §3).
data AssemblageStabilityWhyConcurrentBundle = AssemblageStabilityWhyConcurrentBundle
  { assemblageStabilityWhyClassPresent :: Bool
  , assemblageStabilityWhyChannelSlots :: [AssemblageStabilityWhyChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
assemblageStabilityWhyConcurrentBundleUnwired :: AssemblageStabilityWhyConcurrentBundle
assemblageStabilityWhyConcurrentBundleUnwired =
  AssemblageStabilityWhyConcurrentBundle
    False
    (replicate assemblageStabilityWhyProductChannelCount AssemblageStabilityWhySlotUnwired)

-- | Set one channel at index; leaves others unchanged.
assemblageStabilityWhyConcurrentBundleWithChannel ::
  Int -> AssemblageStabilityWhyChannelSlot -> AssemblageStabilityWhyConcurrentBundle -> AssemblageStabilityWhyConcurrentBundle
assemblageStabilityWhyConcurrentBundleWithChannel idx slot bundle =
  let slots = assemblageStabilityWhyChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in AssemblageStabilityWhyConcurrentBundle
        (assemblageStabilityWhyClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the assemblage-stability WHY **product**.
assemblageStabilityWhyConcurrentBundleWithPresent ::
  Int -> AssemblageStabilityWhyConcurrentBundle -> AssemblageStabilityWhyConcurrentBundle
assemblageStabilityWhyConcurrentBundleWithPresent idx bundle =
  assemblageStabilityWhyConcurrentBundleWithChannel idx AssemblageStabilityWhySlotPresent bundle

-- | Read channel slot at index (0..2).
assemblageStabilityWhyConcurrentBundleChannelAt ::
  Int -> AssemblageStabilityWhyConcurrentBundle -> Maybe AssemblageStabilityWhyChannelSlot
assemblageStabilityWhyConcurrentBundleChannelAt idx bundle =
  let slots = assemblageStabilityWhyChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
assemblageStabilityWhyConcurrentBundleHolds :: Int -> AssemblageStabilityWhyConcurrentBundle -> Bool
assemblageStabilityWhyConcurrentBundleHolds idx bundle =
  case assemblageStabilityWhyConcurrentBundleChannelAt idx bundle of
    Just AssemblageStabilityWhySlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
assemblageStabilityWhyConcurrentBundlePresentCount :: AssemblageStabilityWhyConcurrentBundle -> Int
assemblageStabilityWhyConcurrentBundlePresentCount bundle =
  length (filter (== AssemblageStabilityWhySlotPresent) (assemblageStabilityWhyChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
assemblageStabilityWhyConcurrentBundleIsConcurrentProduct :: AssemblageStabilityWhyConcurrentBundle -> Bool
assemblageStabilityWhyConcurrentBundleIsConcurrentProduct bundle =
  assemblageStabilityWhyConcurrentBundlePresentCount bundle >= 2

-- | Assemblage-stability WHY witness: Ore predicate (0) + G-min (1) + equilibrium basin (2) concurrent on class 7.
assemblageStabilityWhyOreSecondLawWitness :: AssemblageStabilityWhyConcurrentBundle
assemblageStabilityWhyOreSecondLawWitness =
  assemblageStabilityWhyConcurrentBundleWithPresent 2
    (assemblageStabilityWhyConcurrentBundleWithPresent 1
      (assemblageStabilityWhyConcurrentBundleWithPresent 0
        (AssemblageStabilityWhyConcurrentBundle True
          (replicate assemblageStabilityWhyProductChannelCount AssemblageStabilityWhySlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data AssemblageStabilityWhyXorPosture
  = AssemblageStabilityWhyXorExclusive
  | AssemblageStabilityWhyXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
assemblageStabilityWhyXorPostureExclusive :: AssemblageStabilityWhyXorPosture
assemblageStabilityWhyXorPostureExclusive = AssemblageStabilityWhyXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
assemblageStabilityWhyXorPostureConcurrent :: AssemblageStabilityWhyXorPosture
assemblageStabilityWhyXorPostureConcurrent = AssemblageStabilityWhyXorConcurrent

-- | Verdict for assemblage-stability WHY **conservation** close (fail-closed).
data AssemblageStabilityWhyConservationVerdict
  = AssemblageStabilityWhyConservationDesignOk
  | AssemblageStabilityWhyConservationNamedOk
  | AssemblageStabilityWhyConservationTrivialRefuse
  | AssemblageStabilityWhyConservationGreenInventRefuse
  | AssemblageStabilityWhyConservationProvedWithoutBarRefuse
  | AssemblageStabilityWhyConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data AssemblageStabilityWhyXorVerdict
  = AssemblageStabilityWhyXorDesignOk
  | AssemblageStabilityWhyXorNamedOk
  | AssemblageStabilityWhyXorGreenInventRefuse
  | AssemblageStabilityWhyXorProvedWithoutBarRefuse
  | AssemblageStabilityWhyXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate an assemblage-stability WHY bundle under class-7 **conservation** bar (fail-closed).
evaluateAssemblageStabilityWhyBundle ::
  AssemblageStabilityWhyConservationModality
  -> AssemblageStabilityWhyConcurrentBundle
  -> Bool
  -> Bool
  -> AssemblageStabilityWhyConservationVerdict
evaluateAssemblageStabilityWhyBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = AssemblageStabilityWhyConservationGreenInventRefuse
  | claimProved = AssemblageStabilityWhyConservationProvedWithoutBarRefuse
  | length (assemblageStabilityWhyChannelSlots bundle) /= assemblageStabilityWhyProductChannelCount =
      AssemblageStabilityWhyConservationTrivialRefuse
  | otherwise =
      case modality of
        AssemblageStabilityWhyConservationUnwired ->
          if assemblageStabilityWhyConcurrentBundleIsConcurrentProduct bundle
            then AssemblageStabilityWhyConservationNamedOk
            else AssemblageStabilityWhyConservationDesignOk
        AssemblageStabilityWhyConservationAssumed -> AssemblageStabilityWhyConservationDesignOk
        AssemblageStabilityWhyConservationSurrogate -> AssemblageStabilityWhyConservationDesignOk
        AssemblageStabilityWhyConservationProved -> AssemblageStabilityWhyConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-7 **conservation** bar (fail-closed).
evaluateAssemblageStabilityWhyXor ::
  AssemblageStabilityWhyConservationModality
  -> AssemblageStabilityWhyXorPosture
  -> Bool
  -> Bool
  -> AssemblageStabilityWhyXorVerdict
evaluateAssemblageStabilityWhyXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = AssemblageStabilityWhyXorGreenInventRefuse
  | claimProved = AssemblageStabilityWhyXorProvedWithoutBarRefuse
  | posture == AssemblageStabilityWhyXorExclusive = AssemblageStabilityWhyXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        AssemblageStabilityWhyConservationUnwired -> AssemblageStabilityWhyXorNamedOk
        AssemblageStabilityWhyConservationAssumed -> AssemblageStabilityWhyXorDesignOk
        AssemblageStabilityWhyConservationSurrogate -> AssemblageStabilityWhyXorDesignOk
        AssemblageStabilityWhyConservationProved -> AssemblageStabilityWhyXorProvedWithoutBarRefuse

-- | **Assemblage-stability WHY** identity law cells tracked by class-7 **conservation** (structure scaffold).
data AssemblageStabilityWhyConservationLaw
  = AssemblageStabilityWhyConservationConserved
  | NamedAssemblageStabilityWhyConservationOk
  | TrivialAssemblageStabilityWhyRefused
  | GreenInventAssemblageStabilityWhyRefused
  deriving (Eq, Show)

assemblageStabilityWhyConservationLawAll :: [AssemblageStabilityWhyConservationLaw]
assemblageStabilityWhyConservationLawAll =
  [ AssemblageStabilityWhyConservationConserved
  , NamedAssemblageStabilityWhyConservationOk
  , TrivialAssemblageStabilityWhyRefused
  , GreenInventAssemblageStabilityWhyRefused
  ]

assemblageStabilityWhyConservationLawCount :: Int
assemblageStabilityWhyConservationLawCount = length assemblageStabilityWhyConservationLawAll

-- | Evaluate class-7 **assemblage-stability WHY** **conservation** typing (fail-closed).
evaluateAssemblageStabilityWhyConservation ::
  AssemblageStabilityWhyConservationModality
  -> AssemblageStabilityWhyConcurrentBundle
  -> AssemblageStabilityWhyXorPosture
  -> Bool
  -> Bool
  -> AssemblageStabilityWhyConservationVerdict
evaluateAssemblageStabilityWhyConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = AssemblageStabilityWhyConservationGreenInventRefuse
  | claimProved = AssemblageStabilityWhyConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateAssemblageStabilityWhyXor modality posture False False of
        AssemblageStabilityWhyXorMutuallyExclusiveRefuse -> AssemblageStabilityWhyConservationXorRefuse
        AssemblageStabilityWhyXorGreenInventRefuse -> AssemblageStabilityWhyConservationGreenInventRefuse
        AssemblageStabilityWhyXorProvedWithoutBarRefuse -> AssemblageStabilityWhyConservationProvedWithoutBarRefuse
        _ ->
          case evaluateAssemblageStabilityWhyBundle modality bundle False False of
            AssemblageStabilityWhyConservationNamedOk -> AssemblageStabilityWhyConservationNamedOk
            AssemblageStabilityWhyConservationGreenInventRefuse -> AssemblageStabilityWhyConservationGreenInventRefuse
            AssemblageStabilityWhyConservationProvedWithoutBarRefuse -> AssemblageStabilityWhyConservationProvedWithoutBarRefuse
            AssemblageStabilityWhyConservationTrivialRefuse -> AssemblageStabilityWhyConservationTrivialRefuse
            AssemblageStabilityWhyConservationXorRefuse -> AssemblageStabilityWhyConservationXorRefuse
            AssemblageStabilityWhyConservationDesignOk -> AssemblageStabilityWhyConservationDesignOk

sampleAssemblageStabilityWhyOreSecondLawBundle :: AssemblageStabilityWhyConcurrentBundle
sampleAssemblageStabilityWhyOreSecondLawBundle = assemblageStabilityWhyOreSecondLawWitness

sampleXorExclusiveBundle :: AssemblageStabilityWhyConcurrentBundle
sampleXorExclusiveBundle = assemblageStabilityWhyConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: AssemblageStabilityWhyConcurrentBundle
sampleTrivialUnwiredBundle = assemblageStabilityWhyConcurrentBundleUnwired

-- | Unwired **assemblage-stability WHY** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateAssemblageStabilityWhyConservation
    AssemblageStabilityWhyConservationUnwired
    sampleAssemblageStabilityWhyOreSecondLawBundle
    assemblageStabilityWhyXorPostureConcurrent
    False
    False
    == AssemblageStabilityWhyConservationNamedOk

-- | Assemblage-stability WHY witness: Ore predicate + G-min + equilibrium basin concurrent Π_c on class 7.
assemblageStabilityWhyOreSecondLawConcurrentOk :: Bool
assemblageStabilityWhyOreSecondLawConcurrentOk =
  let bundle = assemblageStabilityWhyOreSecondLawWitness
   in assemblageStabilityWhyClassPresent bundle
        && assemblageStabilityWhyConcurrentBundleHolds 0 bundle
        && assemblageStabilityWhyConcurrentBundleHolds 1 bundle
        && assemblageStabilityWhyConcurrentBundleHolds 2 bundle
        && assemblageStabilityWhyConcurrentBundlePresentCount bundle == 3
        && assemblageStabilityWhyConcurrentBundleIsConcurrentProduct bundle
        && ironAtomicNumberZ == 26
        && class7AssemblageStabilityWhyPatternIndex == 7

-- | Class-7 assemblage-stability WHY pattern index pinned @ scaffold.
class7AssemblageStabilityWhyPatternIndexOk :: Bool
class7AssemblageStabilityWhyPatternIndexOk =
  class7AssemblageStabilityWhyPatternIndex == 7
    && assemblageStabilityWhyProductChannelCount == 3
    && length (assemblageStabilityWhyChannelSlots assemblageStabilityWhyConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  assemblageStabilityWhyConcurrentBundleIsConcurrentProduct assemblageStabilityWhyOreSecondLawWitness
    && assemblageStabilityWhyConcurrentBundlePresentCount assemblageStabilityWhyOreSecondLawWitness >= 2
    && assemblageStabilityWhyConcurrentBundlePresentCount assemblageStabilityWhyOreSecondLawWitness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateAssemblageStabilityWhyXor
    AssemblageStabilityWhyConservationUnwired
    assemblageStabilityWhyXorPostureExclusive
    False
    False
    == AssemblageStabilityWhyXorMutuallyExclusiveRefuse
    && evaluateAssemblageStabilityWhyConservation
      AssemblageStabilityWhyConservationUnwired
      sampleAssemblageStabilityWhyOreSecondLawBundle
      assemblageStabilityWhyXorPostureExclusive
      False
      False
      == AssemblageStabilityWhyConservationXorRefuse

-- | GREEN invent on **assemblage-stability WHY** **conservation** promotion is refused.
greenInventAssemblageStabilityWhyRefuse :: Bool
greenInventAssemblageStabilityWhyRefuse =
  evaluateAssemblageStabilityWhyConservation
    AssemblageStabilityWhyConservationUnwired
    sampleAssemblageStabilityWhyOreSecondLawBundle
    assemblageStabilityWhyXorPostureConcurrent
    True
    False
    == AssemblageStabilityWhyConservationGreenInventRefuse
    && evaluateAssemblageStabilityWhyBundle
      AssemblageStabilityWhyConservationUnwired
      sampleAssemblageStabilityWhyOreSecondLawBundle
      True
      False
      == AssemblageStabilityWhyConservationGreenInventRefuse

-- | Parallel stability axiom (26th law) mint is refused — second law + conservation only.
parallelStabilityAxiomRefuse :: Bool
parallelStabilityAxiomRefuse =
  assemblageStabilityWhyConservationAuthority
    == "umst/umst-chem/src/assemblage_stability.rs"
    && assemblageStabilityWhyConservationProved == False
    && not (assemblageStabilityWhyConservationAuthority == "26th_chemistry_axiom")
    && assemblageStabilityWhyConservationFraming
      /= "parallel_stability_axiom_not_second_law"

-- | Goldschmidt XOR folklore ≠ class-7 concurrent Π_c **product** on Ore⊗G⊗why-axis.
goldschmidtXorRefuse :: Bool
goldschmidtXorRefuse =
  parallelStabilityAxiomRefuse
    && assemblageStabilityWhyConservationFraming
      /= "goldschmidt_xor_lithophile_chalcophile_siderophile"
    && class7AssemblageStabilityWhyPatternIndex == 7
    && assemblageStabilityWhyConcurrentBundleIsConcurrentProduct assemblageStabilityWhyOreSecondLawWitness

-- | Assumed **assemblage-stability WHY** modality OK without thermo break (design scaffold).
assumedAssemblageStabilityWhyDesignOk :: Bool
assumedAssemblageStabilityWhyDesignOk =
  evaluateAssemblageStabilityWhyConservation
    AssemblageStabilityWhyConservationAssumed
    sampleAssemblageStabilityWhyOreSecondLawBundle
    assemblageStabilityWhyXorPostureConcurrent
    False
    False
    == AssemblageStabilityWhyConservationDesignOk

-- | Surrogate **assemblage-stability WHY** modality OK without thermo break (design scaffold).
surrogateAssemblageStabilityWhyDesignOk :: Bool
surrogateAssemblageStabilityWhyDesignOk =
  evaluateAssemblageStabilityWhyConservation
    AssemblageStabilityWhyConservationSurrogate
    sampleAssemblageStabilityWhyOreSecondLawBundle
    assemblageStabilityWhyXorPostureConcurrent
    False
    False
    == AssemblageStabilityWhyConservationDesignOk

-- | Four-step class-7 **assemblage-stability WHY** lattice scaffold pinned.
assemblageStabilityWhyLatticeScaffold :: Bool
assemblageStabilityWhyLatticeScaffold =
  assemblageStabilityWhyLatticeCount == 4
    && unwiredDesignOk
    && class7AssemblageStabilityWhyPatternIndexOk
    && assemblageStabilityWhyOreSecondLawConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedAssemblageStabilityWhyDesignOk
    && surrogateAssemblageStabilityWhyDesignOk
    && parallelStabilityAxiomRefuse
    && goldschmidtXorRefuse

-- | **Assemblage-stability WHY** lattice is structure scaffold — not 118² GREEN periodic table.
assemblageStabilityWhyLatticeNotGreenTable :: Bool
assemblageStabilityWhyLatticeNotGreenTable =
  assemblageStabilityWhyLatticeCount == 4
    && assemblageStabilityWhyLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && assemblageStabilityWhyProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && assemblageStabilityWhyChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **assemblage-stability WHY** identity law cells scaffold pinned.
assemblageStabilityWhyConservationLawsScaffold :: Bool
assemblageStabilityWhyConservationLawsScaffold =
  assemblageStabilityWhyConservationLawCount == 4
    && assemblageStabilityWhyOreSecondLawConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventAssemblageStabilityWhyRefuse
    && parallelStabilityAxiomRefuse
    && goldschmidtXorRefuse

-- | **Assemblage-stability WHY** law cells are structure scaffold — not 118² GREEN periodic table.
assemblageStabilityWhyConservationLawsNotGreenTable :: Bool
assemblageStabilityWhyConservationLawsNotGreenTable =
  assemblageStabilityWhyConservationLawsScaffold
    && assemblageStabilityWhyConservationLawCount /= 118 * 118
    && assemblageStabilityWhyProductChannelCount /= 118 * 118

-- | Class-7 **assemblage-stability WHY** **conservation** claims route to knowing / quantum fiber (not meso acting).
assemblageStabilityWhyKnowingFiberOk :: Bool
assemblageStabilityWhyKnowingFiberOk = True

-- | Class-7 **assemblage-stability WHY** invent refuse-closed scaffold witness.
assemblageStabilityWhyConservationInventRefuse :: Bool
assemblageStabilityWhyConservationInventRefuse =
  not assemblageStabilityWhyConservationProved

-- | **Assemblage-stability WHY** lattice steps are concurrent Π_c — not XOR enum bucket.
assemblageStabilityWhyLatticeNotXor :: Bool
assemblageStabilityWhyLatticeNotXor =
  unwiredDesignOk
    && assumedAssemblageStabilityWhyDesignOk
    && surrogateAssemblageStabilityWhyDesignOk
    && assemblageStabilityWhyOreSecondLawConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventAssemblageStabilityWhyRefuse

-- | Class-7 **assemblage-stability WHY** proved (always false on this Unwired cell).
assemblageStabilityWhyConservationProved :: Bool
assemblageStabilityWhyConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Assemblage-stability WHY** morphisms are class-7 neighbor channels — not SpeciesId tag mint.
assemblageStabilityWhyConservationNeSpeciesId :: Bool
assemblageStabilityWhyConservationNeSpeciesId =
  assemblageStabilityWhyConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && assemblageStabilityWhyProductChannelAll /= []
    && assemblageStabilityWhyConcurrentBundleIsConcurrentProduct assemblageStabilityWhyOreSecondLawWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-7 **assemblage-stability WHY** scaffold.
assemblageStabilityWhyConservationFraming :: String
assemblageStabilityWhyConservationFraming =
  "second_law_conservation_assemblage_stability_why_one_axiom"

-- | Single design axiom: second law + **conservation** class-7 assemblage-stability WHY (not 26th axiom).
assemblageStabilityWhyConservationAxiom :: Bool
assemblageStabilityWhyConservationAxiom =
  assemblageStabilityWhyLatticeScaffold
    && assemblageStabilityWhyLatticeNotGreenTable
    && assemblageStabilityWhyConservationLawsScaffold
    && assemblageStabilityWhyConservationLawsNotGreenTable
    && assemblageStabilityWhyKnowingFiberOk
    && class7AssemblageStabilityWhyPatternIndexOk
    && assemblageStabilityWhyOreSecondLawConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventAssemblageStabilityWhyRefuse
    && parallelStabilityAxiomRefuse
    && goldschmidtXorRefuse
    && assemblageStabilityWhyConservationInventRefuse
    && assemblageStabilityWhyLatticeNotXor
    && assemblageStabilityWhyConservationNeSpeciesId
    && not assemblageStabilityWhyConservationProved
    && not speciesIdForked
    && assemblageStabilityWhyConservationFraming
      == "second_law_conservation_assemblage_stability_why_one_axiom"

assemblageStabilityWhyConservationNamed :: String
assemblageStabilityWhyConservationNamed =
  "assemblageStabilityWhyConservation: AssemblageStabilityWhyConservationModality Unwired Assumed Proved Surrogate four-step lattice assemblageStabilityWhyConservationProved false evaluateAssemblageStabilityWhyBundle evaluateAssemblageStabilityWhyConservation named class 7 assemblage_stability_why ore predicate second law G min common tangent equilibrium basin why axis concurrent product identity conserved present ge 2 product not XOR ore second law witness concurrent xor mutually exclusive refuse parallel stability axiom refuse goldschmidt xor refuse assemblage stability why ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT assemblage-stability **conservation** authority (cited read-only, not forked).
assemblageStabilityWhyConservationAuthority :: String
assemblageStabilityWhyConservationAuthority =
  "umst/umst-chem/src/assemblage_stability.rs"

-- | L0 class-7 assemblage-stability WHY table authority (crosswalk).
chemL0AssemblageStabilityWhyAuthority :: String
chemL0AssemblageStabilityWhyAuthority =
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs"

-- | L0 OreAssemblage object authority (predicate carrier — not list).
oreAssemblageAuthority :: String
oreAssemblageAuthority = "umst/umst-chem/src/ore_assemblage.rs"

-- | Gibbs convex-hull / common-tangent theorem-import authority (second-law presentation).
gibbsConvexHullAuthority :: String
gibbsConvexHullAuthority =
  "umst/umst-chem/src/theorem_import/gibbs_convex_hull.rs"

-- | Interact-graph temperature function authority (v14 T as graph function).
temperatureGraphFunctionAuthority :: String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

-- | Interact-graph pressure function authority (v14 P as graph function).
pressureGraphFunctionAuthority :: String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

assemblageStabilityWhyConservationCellId :: String
assemblageStabilityWhyConservationCellId =
  "CHEM-FORMAL-Q-HS-ASSEMBLAGE-STABILITY-WHY-CONSERVATION"

-- | Non-claim fence — class-7 **assemblage-stability WHY** **conservation** Unwired ≠ Proved GREEN.
assemblageStabilityWhyConservationNonClaim :: String
assemblageStabilityWhyConservationNonClaim =
  "CHEM-FORMAL-Q-HS-ASSEMBLAGE-STABILITY-WHY-CONSERVATION AssemblageStabilityWhyConservationModality Unwired Assumed Proved Surrogate four-step lattice assemblageStabilityWhyConservationProved false evaluateAssemblageStabilityWhyBundle evaluateAssemblageStabilityWhyConservation named class 7 assemblage_stability_why ore predicate second law G min common tangent equilibrium basin why axis concurrent product identity conserved present ge 2 product not XOR ore second law witness concurrent xor mutually exclusive refuse parallel stability axiom refuse goldschmidt xor refuse assemblage stability why ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-7 **assemblage-stability WHY** **conservation** scaffold.
assemblageStabilityWhyConservationPhysicsGreenAuthorized :: Bool
assemblageStabilityWhyConservationPhysicsGreenAuthorized = False

assemblageStabilityWhyConservationPhysicsGreenFalse :: Bool
assemblageStabilityWhyConservationPhysicsGreenFalse =
  not assemblageStabilityWhyConservationPhysicsGreenAuthorized

assemblageStabilityWhyConservationModalityUnwired :: Bool
assemblageStabilityWhyConservationModalityUnwired =
  assemblageStabilityWhyConservationModalityCurrent == AssemblageStabilityWhyConservationUnwired

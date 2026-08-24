-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.BondRepellingConservation
Description : Pattern class 3 **Bond-repelling** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Bond-repelling** **conservation**: north-star §2 class 3 (`BondRepelling`) — DFT EDA Pauli/steric;
TYPE-05 partiality; Ore-blocking repulsion. Concurrent Π_c identity conserved on named class pins;
Pauli/steric ⊗ Ore-blocking ⊗ TYPE-05 partiality is **product** not XOR. Named bond-repelling
identity conserved under honest scaffold; trivial XOR and GREEN invent fail-closed. Bond-repelling
**conservation** laws are structure witnesses only (@bondRepellingConservationProved@ = False).
Not a 26th chemistry axiom. No SpeciesId fork.

* @BondRepellingConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateBondRepellingBundle@ — named class-3 bond-repelling identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateBondRepellingConservation@ — concurrent Π_c **conservation** typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@bondRepellingConservationAxiom@): second law + **conservation** (not 26th axiom).
* @physics_green@ stays false.

Haskell mirror of class-3 **Bond-repelling** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-BOND-REPELLING-CONSERVATION@.
-}
module UMST.ChemConstants.BondRepellingConservation
  ( BondRepellingConservationModality (..)
  , bondRepellingConservationModalityCurrent
  , bondRepellingLatticeAll
  , bondRepellingLatticeCount
  , class3BondRepellingPatternIndex
  , BondRepellingChannelSlot (..)
  , bondRepellingChannelSlotAll
  , bondRepellingChannelSlotCount
  , BondRepellingProductChannel (..)
  , bondRepellingProductChannelAll
  , bondRepellingProductChannelCount
  , bondRepellingProductChannelIndex
  , BondRepellingConcurrentBundle (..)
  , bondRepellingConcurrentBundleUnwired
  , bondRepellingConcurrentBundleWithChannel
  , bondRepellingConcurrentBundleWithPresent
  , bondRepellingConcurrentBundleChannelAt
  , bondRepellingConcurrentBundleHolds
  , bondRepellingConcurrentBundlePresentCount
  , bondRepellingConcurrentBundleIsConcurrentProduct
  , bondRepellingPauliOreType05Witness
  , BondRepellingXorPosture (..)
  , bondRepellingXorPostureExclusive
  , bondRepellingXorPostureConcurrent
  , BondRepellingConservationVerdict (..)
  , BondRepellingXorVerdict (..)
  , evaluateBondRepellingBundle
  , evaluateBondRepellingXor
  , evaluateBondRepellingConservation
  , BondRepellingConservationLaw (..)
  , bondRepellingConservationLawAll
  , bondRepellingConservationLawCount
  , sampleBondRepellingPauliOreType05Bundle
  , sampleXorExclusiveBundle
  , sampleTrivialUnwiredBundle
  , unwiredDesignOk
  , bondRepellingPauliOreType05ConcurrentOk
  , class3BondRepellingPatternIndexOk
  , concurrentProductNotXorOk
  , xorMutuallyExclusiveRefuse
  , greenInventBondRepellingRefuse
  , parallelAxiomRefuse
  , exchangeRepulsionAxiomRefuse
  , assumedBondRepellingDesignOk
  , surrogateBondRepellingDesignOk
  , bondRepellingLatticeScaffold
  , bondRepellingLatticeNotGreenTable
  , bondRepellingConservationLawsScaffold
  , bondRepellingConservationLawsNotGreenTable
  , bondRepellingKnowingFiberOk
  , bondRepellingConservationInventRefuse
  , bondRepellingLatticeNotXor
  , bondRepellingConservationProved
  , bondRepellingConservationNeSpeciesId
  , speciesIdForked
  , bondRepellingConservationFraming
  , bondRepellingConservationAxiom
  , bondRepellingConservationNamed
  , bondRepellingConservationAuthority
  , chemL0BondRepellingAuthority
  , interactPartialityAuthority
  , chemL0Type05Authority
  , bondRepellingConservationCellId
  , bondRepellingConservationNonClaim
  , bondRepellingConservationPhysicsGreenAuthorized
  , bondRepellingConservationPhysicsGreenFalse
  , bondRepellingConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not bond-repelling GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-3 (`BondRepelling`) pattern index.
class3BondRepellingPatternIndex :: Int
class3BondRepellingPatternIndex = 3

-- | Design **bond-repelling** modality for class-3 **conservation** claims.
data BondRepellingConservationModality
  = BondRepellingConservationUnwired
  | BondRepellingConservationAssumed
  | BondRepellingConservationProved
  | BondRepellingConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **bond-repelling** modality — always Unwired on this cell.
bondRepellingConservationModalityCurrent :: BondRepellingConservationModality
bondRepellingConservationModalityCurrent = BondRepellingConservationUnwired

-- | All class-3 **bond-repelling** lattice steps in stable order.
bondRepellingLatticeAll :: [BondRepellingConservationModality]
bondRepellingLatticeAll =
  [ BondRepellingConservationUnwired
  , BondRepellingConservationAssumed
  , BondRepellingConservationProved
  , BondRepellingConservationSurrogate
  ]

bondRepellingLatticeCount :: Int
bondRepellingLatticeCount = length bondRepellingLatticeAll

-- | Bond-repelling product channel slot — concurrent **product** factor, not XOR bucket.
data BondRepellingChannelSlot
  = BondRepellingSlotUnwired
  | BondRepellingSlotAbsent
  | BondRepellingSlotPresent
  deriving (Eq, Show)

-- | All bond-repelling channel slots in stable order.
bondRepellingChannelSlotAll :: [BondRepellingChannelSlot]
bondRepellingChannelSlotAll =
  [ BondRepellingSlotUnwired
  , BondRepellingSlotAbsent
  , BondRepellingSlotPresent
  ]

bondRepellingChannelSlotCount :: Int
bondRepellingChannelSlotCount = length bondRepellingChannelSlotAll

-- | Named Pauli/steric / Ore-blocking / TYPE-05 partiality product channels (bounded scaffold).
data BondRepellingProductChannel
  = PauliStericPartial
  | OreBlockingRepulsion
  | Type05Partiality
  deriving (Eq, Show)

-- | All bond-repelling product channels in north-star stable order.
bondRepellingProductChannelAll :: [BondRepellingProductChannel]
bondRepellingProductChannelAll =
  [ PauliStericPartial
  , OreBlockingRepulsion
  , Type05Partiality
  ]

bondRepellingProductChannelCount :: Int
bondRepellingProductChannelCount = length bondRepellingProductChannelAll

-- | Stable channel index for a bond-repelling product channel (0..2).
bondRepellingProductChannelIndex :: BondRepellingProductChannel -> Int
bondRepellingProductChannelIndex channel =
  case channel of
    PauliStericPartial -> 0
    OreBlockingRepulsion -> 1
    Type05Partiality -> 2

-- | Class-3 bond-repelling concurrent **product** bundle (north-star §3).
data BondRepellingConcurrentBundle = BondRepellingConcurrentBundle
  { bondRepellingClassPresent :: Bool
  , bondRepellingChannelSlots :: [BondRepellingChannelSlot]
  }
  deriving (Eq, Show)

-- | All channels Unwired — honest scaffold baseline.
bondRepellingConcurrentBundleUnwired :: BondRepellingConcurrentBundle
bondRepellingConcurrentBundleUnwired =
  BondRepellingConcurrentBundle
    False
    (replicate bondRepellingProductChannelCount BondRepellingSlotUnwired)

-- | Set one channel at index; leaves others unchanged.
bondRepellingConcurrentBundleWithChannel ::
  Int -> BondRepellingChannelSlot -> BondRepellingConcurrentBundle -> BondRepellingConcurrentBundle
bondRepellingConcurrentBundleWithChannel idx slot bundle =
  let slots = bondRepellingChannelSlots bundle
      before = take idx slots
      after = drop (idx + 1) slots
      current = if idx >= 0 && idx < length slots then slot else slots !! idx
   in BondRepellingConcurrentBundle
        (bondRepellingClassPresent bundle)
        (before ++ [current] ++ after)

-- | Mark channel index Present on the bond-repelling **product**.
bondRepellingConcurrentBundleWithPresent ::
  Int -> BondRepellingConcurrentBundle -> BondRepellingConcurrentBundle
bondRepellingConcurrentBundleWithPresent idx bundle =
  bondRepellingConcurrentBundleWithChannel idx BondRepellingSlotPresent bundle

-- | Read channel slot at index (0..2).
bondRepellingConcurrentBundleChannelAt ::
  Int -> BondRepellingConcurrentBundle -> Maybe BondRepellingChannelSlot
bondRepellingConcurrentBundleChannelAt idx bundle =
  let slots = bondRepellingChannelSlots bundle
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether channel index is Present on the concurrent **product**.
bondRepellingConcurrentBundleHolds :: Int -> BondRepellingConcurrentBundle -> Bool
bondRepellingConcurrentBundleHolds idx bundle =
  case bondRepellingConcurrentBundleChannelAt idx bundle of
    Just BondRepellingSlotPresent -> True
    _ -> False

-- | Count of Present channels (may exceed 1 — concurrent **product**).
bondRepellingConcurrentBundlePresentCount :: BondRepellingConcurrentBundle -> Int
bondRepellingConcurrentBundlePresentCount bundle =
  length (filter (== BondRepellingSlotPresent) (bondRepellingChannelSlots bundle))

-- | Whether bundle demonstrates concurrent **product** (≥2 Present channels).
bondRepellingConcurrentBundleIsConcurrentProduct :: BondRepellingConcurrentBundle -> Bool
bondRepellingConcurrentBundleIsConcurrentProduct bundle =
  bondRepellingConcurrentBundlePresentCount bundle >= 2

-- | Bond-repelling witness: Pauli/steric (0) + Ore-blocking (1) + TYPE-05 (2) concurrent on class 3.
bondRepellingPauliOreType05Witness :: BondRepellingConcurrentBundle
bondRepellingPauliOreType05Witness =
  bondRepellingConcurrentBundleWithPresent 2
    (bondRepellingConcurrentBundleWithPresent 1
      (bondRepellingConcurrentBundleWithPresent 0
        (BondRepellingConcurrentBundle True (replicate bondRepellingProductChannelCount BondRepellingSlotUnwired))))

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data BondRepellingXorPosture
  = BondRepellingXorExclusive
  | BondRepellingXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
bondRepellingXorPostureExclusive :: BondRepellingXorPosture
bondRepellingXorPostureExclusive = BondRepellingXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
bondRepellingXorPostureConcurrent :: BondRepellingXorPosture
bondRepellingXorPostureConcurrent = BondRepellingXorConcurrent

-- | Verdict for bond-repelling **conservation** close (fail-closed).
data BondRepellingConservationVerdict
  = BondRepellingConservationDesignOk
  | BondRepellingConservationNamedOk
  | BondRepellingConservationTrivialRefuse
  | BondRepellingConservationGreenInventRefuse
  | BondRepellingConservationProvedWithoutBarRefuse
  | BondRepellingConservationXorRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data BondRepellingXorVerdict
  = BondRepellingXorDesignOk
  | BondRepellingXorNamedOk
  | BondRepellingXorGreenInventRefuse
  | BondRepellingXorProvedWithoutBarRefuse
  | BondRepellingXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Evaluate a bond-repelling bundle under class-3 **conservation** bar (fail-closed).
evaluateBondRepellingBundle ::
  BondRepellingConservationModality
  -> BondRepellingConcurrentBundle
  -> Bool
  -> Bool
  -> BondRepellingConservationVerdict
evaluateBondRepellingBundle modality bundle claimPhysicsGreen claimProved
  | claimPhysicsGreen = BondRepellingConservationGreenInventRefuse
  | claimProved = BondRepellingConservationProvedWithoutBarRefuse
  | length (bondRepellingChannelSlots bundle) /= bondRepellingProductChannelCount =
      BondRepellingConservationTrivialRefuse
  | otherwise =
      case modality of
        BondRepellingConservationUnwired ->
          if bondRepellingConcurrentBundleIsConcurrentProduct bundle
            then BondRepellingConservationNamedOk
            else BondRepellingConservationDesignOk
        BondRepellingConservationAssumed -> BondRepellingConservationDesignOk
        BondRepellingConservationSurrogate -> BondRepellingConservationDesignOk
        BondRepellingConservationProved -> BondRepellingConservationProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-3 **conservation** bar (fail-closed).
evaluateBondRepellingXor ::
  BondRepellingConservationModality
  -> BondRepellingXorPosture
  -> Bool
  -> Bool
  -> BondRepellingXorVerdict
evaluateBondRepellingXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = BondRepellingXorGreenInventRefuse
  | claimProved = BondRepellingXorProvedWithoutBarRefuse
  | posture == BondRepellingXorExclusive = BondRepellingXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        BondRepellingConservationUnwired -> BondRepellingXorNamedOk
        BondRepellingConservationAssumed -> BondRepellingXorDesignOk
        BondRepellingConservationSurrogate -> BondRepellingXorDesignOk
        BondRepellingConservationProved -> BondRepellingXorProvedWithoutBarRefuse

-- | **Bond-repelling** identity law cells tracked by class-3 **conservation** (structure scaffold).
data BondRepellingConservationLaw
  = BondRepellingConservationConserved
  | NamedBondRepellingConservationOk
  | TrivialBondRepellingRefused
  | GreenInventBondRepellingRefused
  deriving (Eq, Show)

bondRepellingConservationLawAll :: [BondRepellingConservationLaw]
bondRepellingConservationLawAll =
  [ BondRepellingConservationConserved
  , NamedBondRepellingConservationOk
  , TrivialBondRepellingRefused
  , GreenInventBondRepellingRefused
  ]

bondRepellingConservationLawCount :: Int
bondRepellingConservationLawCount = length bondRepellingConservationLawAll

-- | Evaluate class-3 **Bond-repelling** **conservation** typing (fail-closed).
evaluateBondRepellingConservation ::
  BondRepellingConservationModality
  -> BondRepellingConcurrentBundle
  -> BondRepellingXorPosture
  -> Bool
  -> Bool
  -> BondRepellingConservationVerdict
evaluateBondRepellingConservation modality bundle posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = BondRepellingConservationGreenInventRefuse
  | claimProved = BondRepellingConservationProvedWithoutBarRefuse
  | otherwise =
      case evaluateBondRepellingXor modality posture False False of
        BondRepellingXorMutuallyExclusiveRefuse -> BondRepellingConservationXorRefuse
        BondRepellingXorGreenInventRefuse -> BondRepellingConservationGreenInventRefuse
        BondRepellingXorProvedWithoutBarRefuse -> BondRepellingConservationProvedWithoutBarRefuse
        _ ->
          case evaluateBondRepellingBundle modality bundle False False of
            BondRepellingConservationNamedOk -> BondRepellingConservationNamedOk
            BondRepellingConservationGreenInventRefuse -> BondRepellingConservationGreenInventRefuse
            BondRepellingConservationProvedWithoutBarRefuse -> BondRepellingConservationProvedWithoutBarRefuse
            BondRepellingConservationTrivialRefuse -> BondRepellingConservationTrivialRefuse
            BondRepellingConservationXorRefuse -> BondRepellingConservationXorRefuse
            BondRepellingConservationDesignOk -> BondRepellingConservationDesignOk

sampleBondRepellingPauliOreType05Bundle :: BondRepellingConcurrentBundle
sampleBondRepellingPauliOreType05Bundle = bondRepellingPauliOreType05Witness

sampleXorExclusiveBundle :: BondRepellingConcurrentBundle
sampleXorExclusiveBundle = bondRepellingConcurrentBundleUnwired

sampleTrivialUnwiredBundle :: BondRepellingConcurrentBundle
sampleTrivialUnwiredBundle = bondRepellingConcurrentBundleUnwired

-- | Unwired **bond-repelling** modality OK without thermo break.
unwiredDesignOk :: Bool
unwiredDesignOk =
  evaluateBondRepellingConservation
    BondRepellingConservationUnwired
    sampleBondRepellingPauliOreType05Bundle
    bondRepellingXorPostureConcurrent
    False
    False
    == BondRepellingConservationNamedOk

-- | Bond-repelling witness: Pauli/steric + Ore-blocking + TYPE-05 concurrent Π_c on class 3.
bondRepellingPauliOreType05ConcurrentOk :: Bool
bondRepellingPauliOreType05ConcurrentOk =
  let bundle = bondRepellingPauliOreType05Witness
   in bondRepellingClassPresent bundle
        && bondRepellingConcurrentBundleHolds 0 bundle
        && bondRepellingConcurrentBundleHolds 1 bundle
        && bondRepellingConcurrentBundleHolds 2 bundle
        && bondRepellingConcurrentBundlePresentCount bundle == 3
        && bondRepellingConcurrentBundleIsConcurrentProduct bundle

-- | Class-3 Bond-repelling pattern index pinned @ scaffold.
class3BondRepellingPatternIndexOk :: Bool
class3BondRepellingPatternIndexOk =
  class3BondRepellingPatternIndex == 3
    && bondRepellingProductChannelCount == 3
    && length (bondRepellingChannelSlots bondRepellingConcurrentBundleUnwired) == 3

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  bondRepellingConcurrentBundleIsConcurrentProduct bondRepellingPauliOreType05Witness
    && bondRepellingConcurrentBundlePresentCount bondRepellingPauliOreType05Witness >= 2
    && bondRepellingConcurrentBundlePresentCount bondRepellingPauliOreType05Witness == 3

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateBondRepellingXor
    BondRepellingConservationUnwired
    bondRepellingXorPostureExclusive
    False
    False
    == BondRepellingXorMutuallyExclusiveRefuse
    && evaluateBondRepellingConservation
      BondRepellingConservationUnwired
      sampleBondRepellingPauliOreType05Bundle
      bondRepellingXorPostureExclusive
      False
      False
      == BondRepellingConservationXorRefuse

-- | GREEN invent on **bond-repelling** **conservation** promotion is refused.
greenInventBondRepellingRefuse :: Bool
greenInventBondRepellingRefuse =
  evaluateBondRepellingConservation
    BondRepellingConservationUnwired
    sampleBondRepellingPauliOreType05Bundle
    bondRepellingXorPostureConcurrent
    True
    False
    == BondRepellingConservationGreenInventRefuse
    && evaluateBondRepellingBundle
      BondRepellingConservationUnwired
      sampleBondRepellingPauliOreType05Bundle
      True
      False
      == BondRepellingConservationGreenInventRefuse

-- | Parallel bond-repelling axiom (26th law) mint is refused.
parallelAxiomRefuse :: Bool
parallelAxiomRefuse =
  bondRepellingConservationAuthority
    == "umst/umst-chem/src/x_rows/bond_repelling_conservation.rs"
    && bondRepellingConservationProved == False
    && not (bondRepellingConservationAuthority == "26th_chemistry_axiom")

-- | Exchange repulsion / Pauli steric ≠ 26th chemistry axiom.
exchangeRepulsionAxiomRefuse :: Bool
exchangeRepulsionAxiomRefuse =
  parallelAxiomRefuse
    && bondRepellingConservationFraming
      /= "exchange_repulsion_26th_chem_axiom"

-- | Assumed **bond-repelling** modality OK without thermo break (design scaffold).
assumedBondRepellingDesignOk :: Bool
assumedBondRepellingDesignOk =
  evaluateBondRepellingConservation
    BondRepellingConservationAssumed
    sampleBondRepellingPauliOreType05Bundle
    bondRepellingXorPostureConcurrent
    False
    False
    == BondRepellingConservationDesignOk

-- | Surrogate **bond-repelling** modality OK without thermo break (design scaffold).
surrogateBondRepellingDesignOk :: Bool
surrogateBondRepellingDesignOk =
  evaluateBondRepellingConservation
    BondRepellingConservationSurrogate
    sampleBondRepellingPauliOreType05Bundle
    bondRepellingXorPostureConcurrent
    False
    False
    == BondRepellingConservationDesignOk

-- | Four-step class-3 **bond-repelling** lattice scaffold pinned.
bondRepellingLatticeScaffold :: Bool
bondRepellingLatticeScaffold =
  bondRepellingLatticeCount == 4
    && unwiredDesignOk
    && class3BondRepellingPatternIndexOk
    && bondRepellingPauliOreType05ConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && assumedBondRepellingDesignOk
    && surrogateBondRepellingDesignOk
    && parallelAxiomRefuse
    && exchangeRepulsionAxiomRefuse

-- | **Bond-repelling** lattice is structure scaffold — not 118² GREEN periodic table.
bondRepellingLatticeNotGreenTable :: Bool
bondRepellingLatticeNotGreenTable =
  bondRepellingLatticeCount == 4
    && bondRepellingLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && bondRepellingProductChannelCount /= iupacTableCardinality * iupacTableCardinality
    && bondRepellingChannelSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **bond-repelling** identity law cells scaffold pinned.
bondRepellingConservationLawsScaffold :: Bool
bondRepellingConservationLawsScaffold =
  bondRepellingConservationLawCount == 4
    && bondRepellingPauliOreType05ConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventBondRepellingRefuse
    && parallelAxiomRefuse
    && exchangeRepulsionAxiomRefuse

-- | **Bond-repelling** law cells are structure scaffold — not 118² GREEN periodic table.
bondRepellingConservationLawsNotGreenTable :: Bool
bondRepellingConservationLawsNotGreenTable =
  bondRepellingConservationLawsScaffold
    && bondRepellingConservationLawCount /= 118 * 118
    && bondRepellingProductChannelCount /= 118 * 118

-- | Class-3 **Bond-repelling** **conservation** claims route to knowing / quantum fiber (not meso acting).
bondRepellingKnowingFiberOk :: Bool
bondRepellingKnowingFiberOk = True

-- | Class-3 **Bond-repelling** invent refuse-closed scaffold witness.
bondRepellingConservationInventRefuse :: Bool
bondRepellingConservationInventRefuse = not bondRepellingConservationProved

-- | **Bond-repelling** lattice steps are concurrent Π_c — not XOR enum bucket.
bondRepellingLatticeNotXor :: Bool
bondRepellingLatticeNotXor =
  unwiredDesignOk
    && assumedBondRepellingDesignOk
    && surrogateBondRepellingDesignOk
    && bondRepellingPauliOreType05ConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventBondRepellingRefuse

-- | Class-3 **Bond-repelling** proved (always false on this Unwired cell).
bondRepellingConservationProved :: Bool
bondRepellingConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Bond-repelling** morphisms are class-3 neighbor channels — not SpeciesId tag mint.
bondRepellingConservationNeSpeciesId :: Bool
bondRepellingConservationNeSpeciesId =
  bondRepellingConservationAuthority
    /= "umst/umst-chem/src/species_id.rs"
    && bondRepellingProductChannelAll /= []
    && bondRepellingConcurrentBundleIsConcurrentProduct bondRepellingPauliOreType05Witness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-3 **Bond-repelling** scaffold.
bondRepellingConservationFraming :: String
bondRepellingConservationFraming =
  "second_law_conservation_bond_repelling_one_axiom"

-- | Single design axiom: second law + **conservation** class-3 Bond-repelling (not 26th axiom).
bondRepellingConservationAxiom :: Bool
bondRepellingConservationAxiom =
  bondRepellingLatticeScaffold
    && bondRepellingLatticeNotGreenTable
    && bondRepellingConservationLawsScaffold
    && bondRepellingConservationLawsNotGreenTable
    && bondRepellingKnowingFiberOk
    && class3BondRepellingPatternIndexOk
    && bondRepellingPauliOreType05ConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventBondRepellingRefuse
    && parallelAxiomRefuse
    && exchangeRepulsionAxiomRefuse
    && bondRepellingConservationInventRefuse
    && bondRepellingLatticeNotXor
    && bondRepellingConservationNeSpeciesId
    && not bondRepellingConservationProved
    && not speciesIdForked
    && bondRepellingConservationFraming
      == "second_law_conservation_bond_repelling_one_axiom"

bondRepellingConservationNamed :: String
bondRepellingConservationNamed =
  "bondRepellingConservation: BondRepellingConservationModality Unwired Assumed Proved Surrogate four-step lattice bondRepellingConservationProved false evaluateBondRepellingBundle evaluateBondRepellingConservation named class 3 BondRepelling Pauli steric Ore blocking TYPE-05 partiality concurrent product identity conserved present ge 2 product not XOR pauli ore type05 xor mutually exclusive refuse parallel axiom refuse exchange repulsion ne 26th chem axiom bond repelling ne SpeciesId fork second law conservation one axiom"

-- | Upstream INT bond-repelling **conservation** authority (cited read-only, not forked).
bondRepellingConservationAuthority :: String
bondRepellingConservationAuthority =
  "umst/umst-chem/src/x_rows/bond_repelling_conservation.rs"

-- | L0 class-3 bond-repelling table authority (crosswalk).
chemL0BondRepellingAuthority :: String
chemL0BondRepellingAuthority = "umst/umst-chem/src/l0_tables/bond_repelling.rs"

-- | TYPE-05 Interact partiality authority (crosswalk).
interactPartialityAuthority :: String
interactPartialityAuthority = "umst/umst-chem/src/interact_partiality.rs"

-- | L0 TYPE-05 partiality cell id authority (crosswalk).
chemL0Type05Authority :: String
chemL0Type05Authority = "CHEM-L0-TYPE-05"

bondRepellingConservationCellId :: String
bondRepellingConservationCellId = "CHEM-FORMAL-Q-HS-BOND-REPELLING-CONSERVATION"

-- | Non-claim fence — class-3 **Bond-repelling** **conservation** Unwired ≠ Proved GREEN.
bondRepellingConservationNonClaim :: String
bondRepellingConservationNonClaim =
  "CHEM-FORMAL-Q-HS-BOND-REPELLING-CONSERVATION BondRepellingConservationModality Unwired Assumed Proved Surrogate four-step lattice bondRepellingConservationProved false evaluateBondRepellingBundle evaluateBondRepellingConservation named class 3 BondRepelling Pauli steric Ore blocking TYPE-05 partiality concurrent product identity conserved present ge 2 product not XOR pauli ore type05 xor mutually exclusive refuse parallel axiom refuse exchange repulsion ne 26th chem axiom bond repelling ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing class-3 **Bond-repelling** **conservation** scaffold.
bondRepellingConservationPhysicsGreenAuthorized :: Bool
bondRepellingConservationPhysicsGreenAuthorized = False

bondRepellingConservationPhysicsGreenFalse :: Bool
bondRepellingConservationPhysicsGreenFalse =
  not bondRepellingConservationPhysicsGreenAuthorized

bondRepellingConservationModalityUnwired :: Bool
bondRepellingConservationModalityUnwired =
  bondRepellingConservationModalityCurrent == BondRepellingConservationUnwired

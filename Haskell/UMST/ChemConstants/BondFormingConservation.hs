-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.BondFormingConservation
Description : Class-2 **bond-forming** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Bond-forming** **conservation**: north-star §2 class 2 (@bond_forming@) — QTAIM BCP;
Mayer/DDEC; DFT BDE; forming arrow on Kleisli @Interact@ **not** @Refine@. Concurrent
Π_c identity conserved on named class pins; QTAIM ⊗ Mayer ⊗ Interact is **product** not
XOR. Named class-2 **bond-forming** identity conserved under honest scaffold; trivial XOR,
Refine-as-forming, parallel-axiom, bond-order-axiom, and GREEN invent fail-closed.
Class-2 **bond-forming** laws are structure witnesses only
(@bondFormingConservationProved@ = False). Bond-forming ≠ SpeciesId fork.

* @BondFormingConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateBondFormingProduct@ — named class-2 concurrent Π_c identity conserved; XOR mutual-exclusivity refuse-closed.
* @evaluateBondFormingConservation@ — QTAIM BCP + Interact≠Refine typed @ scaffold; Present ≥2 is **product** not XOR.
* **One** design axiom (@bondFormingConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of class-2 **bond-forming** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-BOND-FORMING-CONSERVATION@.
WAVE100: not wired in cabal / lib.rs / eos.rs / nano.
-}
module UMST.ChemConstants.BondFormingConservation
  ( BondFormingConservationModality (..)
  , bondFormingConservationModalityCurrent
  , bondFormingLatticeAll
  , bondFormingLatticeCount
  , class2BondFormingPatternIndex
  , bondFormingTableCardinality
  , BondFormingDomain (..)
  , bondFormingDomainAll
  , bondFormingDomainCount
  , BondFormingDomainSlot (..)
  , bondFormingDomainSlotAll
  , bondFormingDomainSlotCount
  , BondFormingChannelPosture (..)
  , bondFormingChannelInteractApply
  , bondFormingChannelRefineSeparation
  , BondFormingProduct (..)
  , bondFormingProductUnwired
  , bondFormingProductWithPresent
  , bondFormingProductSlotAt
  , bondFormingProductHolds
  , bondFormingProductPresentCount
  , bondFormingProductIsConcurrent
  , hydrogenOxygenBondFormingWitness
  , carbonCarbonBondFormingWitness
  , BondFormingXorPosture (..)
  , bondFormingXorPostureExclusive
  , bondFormingXorPostureConcurrent
  , BondFormingVerdict (..)
  , BondFormingXorVerdict (..)
  , evaluateBondFormingProduct
  , evaluateBondFormingXor
  , evaluateBondFormingChannel
  , evaluateBondFormingConservation
  , BondFormingLaw (..)
  , bondFormingLawAll
  , bondFormingLawCount
  , sampleHydrogenOxygenBondFormingProduct
  , sampleCarbonCarbonBondFormingProduct
  , sampleTrivialUnwiredProduct
  , unwiredBondFormingDesignOk
  , hydrogenOxygenBondFormingConcurrentOk
  , carbonCarbonBondFormingConcurrentOk
  , concurrentProductNotXorOk
  , qtaimBcpOk
  , interactNotRefineOk
  , refineAsFormingRefuse
  , xorMutuallyExclusiveRefuse
  , greenInventBondFormingRefuse
  , parallelAxiomRefuse
  , bondOrderAxiomRefuse
  , assumedBondFormingDesignOk
  , surrogateBondFormingDesignOk
  , bondFormingLatticeScaffold
  , bondFormingLatticeNotGreenTable
  , bondFormingConservationLawsScaffold
  , bondFormingConservationLawsNotGreenTable
  , bondFormingKnowingFiberOk
  , bondFormingInventRefuse
  , bondFormingLatticeNotXor
  , bondFormingConservationProved
  , bondFormingNeSpeciesId
  , speciesIdForked
  , hydrogenZ
  , oxygenZ
  , carbonZ
  , bondFormingConservationFraming
  , bondFormingConservationAxiom
  , bondFormingConservationNamed
  , patternProductConservationAuthority
  , bondFormingConservationIntAuthority
  , bondFormingTableAuthority
  , kleisliInteractAuthority
  , chemL0Class2BondFormingAuthority
  , bondFormingConservationCellId
  , bondFormingConservationNonClaim
  , bondFormingConservationPhysicsGreenAuthorized
  , bondFormingConservationPhysicsGreenFalse
  , bondFormingConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not bond-forming GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | North-star §2 class-2 pattern index (@bond_forming@).
class2BondFormingPatternIndex :: Int
class2BondFormingPatternIndex = 2

-- | Z-keyed bond-forming table cardinality (Z=1..118).
bondFormingTableCardinality :: Int
bondFormingTableCardinality = 118

-- | Design **bond-forming** modality for class-2 **conservation** claims.
data BondFormingConservationModality
  = BondFormingConservationUnwired
  | BondFormingConservationAssumed
  | BondFormingConservationProved
  | BondFormingConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **bond-forming** modality — always Unwired on this cell.
bondFormingConservationModalityCurrent :: BondFormingConservationModality
bondFormingConservationModalityCurrent = BondFormingConservationUnwired

-- | All class-2 **bond-forming** lattice steps in stable order.
bondFormingLatticeAll :: [BondFormingConservationModality]
bondFormingLatticeAll =
  [ BondFormingConservationUnwired
  , BondFormingConservationAssumed
  , BondFormingConservationProved
  , BondFormingConservationSurrogate
  ]

bondFormingLatticeCount :: Int
bondFormingLatticeCount = length bondFormingLatticeAll

-- | Bond-forming domain channel — QTAIM BCP, Mayer/DDEC, Kleisli Interact Apply.
data BondFormingDomain
  = QtaimBcp
  | MayerDdec
  | InteractApply
  deriving (Eq, Show)

-- | All class-2 domain channels in stable order (concurrent Π_c factors — not XOR enum).
bondFormingDomainAll :: [BondFormingDomain]
bondFormingDomainAll =
  [ QtaimBcp
  , MayerDdec
  , InteractApply
  ]

bondFormingDomainCount :: Int
bondFormingDomainCount = length bondFormingDomainAll

-- | Domain slot modality — concurrent **product** factor, not XOR bucket.
data BondFormingDomainSlot
  = BondFormingSlotUnwired
  | BondFormingSlotAbsent
  | BondFormingSlotPresent
  deriving (Eq, Show)

-- | All domain slot modalities in stable order.
bondFormingDomainSlotAll :: [BondFormingDomainSlot]
bondFormingDomainSlotAll =
  [ BondFormingSlotUnwired
  , BondFormingSlotAbsent
  , BondFormingSlotPresent
  ]

bondFormingDomainSlotCount :: Int
bondFormingDomainSlotCount = length bondFormingDomainSlotAll

-- | Forming-arrow channel posture — Interact Apply vs Refine separation (must refuse Refine).
data BondFormingChannelPosture
  = BondFormingInteractApply
  | BondFormingRefineSeparation
  deriving (Eq, Show)

-- | Kleisli Interact Apply — honest forming-arrow carrier.
bondFormingChannelInteractApply :: BondFormingChannelPosture
bondFormingChannelInteractApply = BondFormingInteractApply

-- | Refine separation — must not authorize forming arrow.
bondFormingChannelRefineSeparation :: BondFormingChannelPosture
bondFormingChannelRefineSeparation = BondFormingRefineSeparation

-- | Class-2 bond-forming concurrent Π_c product (three domain channels).
data BondFormingProduct = BondFormingProduct
  { bondFormingDomainSlots :: [BondFormingDomainSlot]
  }
  deriving (Eq, Show)

-- | All domain slots Unwired — honest scaffold baseline.
bondFormingProductUnwired :: BondFormingProduct
bondFormingProductUnwired =
  BondFormingProduct (replicate bondFormingDomainCount BondFormingSlotUnwired)

-- | Mark domain index Present on the concurrent **product**.
bondFormingProductWithPresent :: Int -> BondFormingProduct -> BondFormingProduct
bondFormingProductWithPresent idx bondProduct =
  let slots = bondFormingDomainSlots bondProduct
      before = take idx slots
      after = drop (idx + 1) slots
      current =
        if idx >= 0 && idx < length slots
          then BondFormingSlotPresent
          else slots !! idx
   in BondFormingProduct (before ++ [current] ++ after)

-- | Read slot at domain index (0..2).
bondFormingProductSlotAt :: Int -> BondFormingProduct -> Maybe BondFormingDomainSlot
bondFormingProductSlotAt idx bondProduct =
  let slots = bondFormingDomainSlots bondProduct
   in if idx >= 0 && idx < length slots
        then Just (slots !! idx)
        else Nothing

-- | Whether domain index is Present on the concurrent **product**.
bondFormingProductHolds :: Int -> BondFormingProduct -> Bool
bondFormingProductHolds idx bondProduct =
  case bondFormingProductSlotAt idx bondProduct of
    Just BondFormingSlotPresent -> True
    _ -> False

-- | Count of Present domain slots (may exceed 1 — concurrent **product**).
bondFormingProductPresentCount :: BondFormingProduct -> Int
bondFormingProductPresentCount bondProduct =
  length (filter (== BondFormingSlotPresent) (bondFormingDomainSlots bondProduct))

-- | Whether product demonstrates concurrent Π_c (≥2 Present domain slots).
bondFormingProductIsConcurrent :: BondFormingProduct -> Bool
bondFormingProductIsConcurrent bondProduct =
  bondFormingProductPresentCount bondProduct >= 2

-- | H–O bond-forming witness: QTAIM BCP (0) + Mayer/DDEC (1) + Interact (2) concurrent.
hydrogenOxygenBondFormingWitness :: BondFormingProduct
hydrogenOxygenBondFormingWitness =
  bondFormingProductWithPresent 2
    (bondFormingProductWithPresent 1
      (bondFormingProductWithPresent 0 bondFormingProductUnwired))

-- | C–C bond-forming witness: QTAIM BCP (0) + Interact (2) concurrent.
carbonCarbonBondFormingWitness :: BondFormingProduct
carbonCarbonBondFormingWitness =
  bondFormingProductWithPresent 2
    (bondFormingProductWithPresent 0 bondFormingProductUnwired)

-- | XOR posture — mutual exclusivity scaffold defect (must refuse).
data BondFormingXorPosture
  = BondFormingXorExclusive
  | BondFormingXorConcurrent
  deriving (Eq, Show)

-- | XOR mutual-exclusivity posture — must fail-closed.
bondFormingXorPostureExclusive :: BondFormingXorPosture
bondFormingXorPostureExclusive = BondFormingXorExclusive

-- | Concurrent Π_c posture — honest **product** scaffold.
bondFormingXorPostureConcurrent :: BondFormingXorPosture
bondFormingXorPostureConcurrent = BondFormingXorConcurrent

-- | Verdict for class-2 **bond-forming** close (fail-closed).
data BondFormingVerdict
  = BondFormingDesignOk
  | BondFormingNamedOk
  | BondFormingTrivialRefuse
  | BondFormingGreenInventRefuse
  | BondFormingProvedWithoutBarRefuse
  | BondFormingXorRefuse
  | BondFormingParallelAxiomRefuse
  | BondFormingBondOrderAxiomRefuse
  | BondFormingRefineAsFormingRefuse
  deriving (Eq, Show)

-- | Verdict for XOR posture close (fail-closed).
data BondFormingXorVerdict
  = BondFormingXorDesignOk
  | BondFormingXorNamedOk
  | BondFormingXorGreenInventRefuse
  | BondFormingXorProvedWithoutBarRefuse
  | BondFormingXorMutuallyExclusiveRefuse
  deriving (Eq, Show)

-- | Verdict for forming-channel posture close (fail-closed).
data BondFormingChannelVerdict
  = BondFormingChannelDesignOk
  | BondFormingChannelNamedOk
  | BondFormingChannelGreenInventRefuse
  | BondFormingChannelProvedWithoutBarRefuse
  | BondFormingChannelRefineAsFormingRefuse
  deriving (Eq, Show)

-- | Evaluate class-2 bond-forming product under conservation bar (fail-closed).
evaluateBondFormingProduct ::
  BondFormingConservationModality
  -> BondFormingProduct
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> BondFormingVerdict
evaluateBondFormingProduct modality bondProduct claimPhysicsGreen claimProved claimParallelAxiom claimBondOrderAxiom
  | claimPhysicsGreen = BondFormingGreenInventRefuse
  | claimProved = BondFormingProvedWithoutBarRefuse
  | claimParallelAxiom = BondFormingParallelAxiomRefuse
  | claimBondOrderAxiom = BondFormingBondOrderAxiomRefuse
  | length (bondFormingDomainSlots bondProduct) /= bondFormingDomainCount =
      BondFormingTrivialRefuse
  | otherwise =
      case modality of
        BondFormingConservationUnwired ->
          if bondFormingProductIsConcurrent bondProduct
            then BondFormingNamedOk
            else BondFormingDesignOk
        BondFormingConservationAssumed -> BondFormingDesignOk
        BondFormingConservationSurrogate -> BondFormingDesignOk
        BondFormingConservationProved -> BondFormingProvedWithoutBarRefuse

-- | Evaluate XOR posture under class-2 **conservation** bar (fail-closed).
evaluateBondFormingXor ::
  BondFormingConservationModality
  -> BondFormingXorPosture
  -> Bool
  -> Bool
  -> BondFormingXorVerdict
evaluateBondFormingXor modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = BondFormingXorGreenInventRefuse
  | claimProved = BondFormingXorProvedWithoutBarRefuse
  | posture == BondFormingXorExclusive = BondFormingXorMutuallyExclusiveRefuse
  | otherwise =
      case modality of
        BondFormingConservationUnwired -> BondFormingXorNamedOk
        BondFormingConservationAssumed -> BondFormingXorDesignOk
        BondFormingConservationSurrogate -> BondFormingXorDesignOk
        BondFormingConservationProved -> BondFormingXorProvedWithoutBarRefuse

-- | Evaluate forming-channel posture — Interact Apply vs Refine separation (fail-closed).
evaluateBondFormingChannel ::
  BondFormingConservationModality
  -> BondFormingChannelPosture
  -> Bool
  -> Bool
  -> BondFormingChannelVerdict
evaluateBondFormingChannel modality posture claimPhysicsGreen claimProved
  | claimPhysicsGreen = BondFormingChannelGreenInventRefuse
  | claimProved = BondFormingChannelProvedWithoutBarRefuse
  | posture == BondFormingRefineSeparation = BondFormingChannelRefineAsFormingRefuse
  | otherwise =
      case modality of
        BondFormingConservationUnwired -> BondFormingChannelNamedOk
        BondFormingConservationAssumed -> BondFormingChannelDesignOk
        BondFormingConservationSurrogate -> BondFormingChannelDesignOk
        BondFormingConservationProved -> BondFormingChannelProvedWithoutBarRefuse

-- | Class-2 **bond-forming** identity law cells (structure scaffold).
data BondFormingLaw
  = BondFormingConserved
  | NamedBondFormingOk
  | TrivialBondFormingRefused
  | GreenInventBondFormingRefused
  deriving (Eq, Show)

bondFormingLawAll :: [BondFormingLaw]
bondFormingLawAll =
  [ BondFormingConserved
  , NamedBondFormingOk
  , TrivialBondFormingRefused
  , GreenInventBondFormingRefused
  ]

bondFormingLawCount :: Int
bondFormingLawCount = length bondFormingLawAll

-- | Evaluate class-2 **bond-forming** **conservation** typing (fail-closed).
evaluateBondFormingConservation ::
  BondFormingConservationModality
  -> BondFormingProduct
  -> BondFormingXorPosture
  -> BondFormingChannelPosture
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> BondFormingVerdict
evaluateBondFormingConservation modality bondProduct xorPosture channelPosture claimPhysicsGreen claimProved claimParallelAxiom claimBondOrderAxiom
  | claimPhysicsGreen = BondFormingGreenInventRefuse
  | claimProved = BondFormingProvedWithoutBarRefuse
  | claimParallelAxiom = BondFormingParallelAxiomRefuse
  | claimBondOrderAxiom = BondFormingBondOrderAxiomRefuse
  | otherwise =
      case evaluateBondFormingChannel modality channelPosture False False of
        BondFormingChannelRefineAsFormingRefuse -> BondFormingRefineAsFormingRefuse
        BondFormingChannelGreenInventRefuse -> BondFormingGreenInventRefuse
        BondFormingChannelProvedWithoutBarRefuse -> BondFormingProvedWithoutBarRefuse
        _ ->
          case evaluateBondFormingXor modality xorPosture False False of
            BondFormingXorMutuallyExclusiveRefuse -> BondFormingXorRefuse
            BondFormingXorGreenInventRefuse -> BondFormingGreenInventRefuse
            BondFormingXorProvedWithoutBarRefuse -> BondFormingProvedWithoutBarRefuse
            _ ->
              case evaluateBondFormingProduct modality bondProduct False False False False of
                BondFormingNamedOk -> BondFormingNamedOk
                BondFormingGreenInventRefuse -> BondFormingGreenInventRefuse
                BondFormingProvedWithoutBarRefuse -> BondFormingProvedWithoutBarRefuse
                BondFormingTrivialRefuse -> BondFormingTrivialRefuse
                BondFormingXorRefuse -> BondFormingXorRefuse
                BondFormingParallelAxiomRefuse -> BondFormingParallelAxiomRefuse
                BondFormingBondOrderAxiomRefuse -> BondFormingBondOrderAxiomRefuse
                BondFormingRefineAsFormingRefuse -> BondFormingRefineAsFormingRefuse
                BondFormingDesignOk -> BondFormingDesignOk

sampleHydrogenOxygenBondFormingProduct :: BondFormingProduct
sampleHydrogenOxygenBondFormingProduct = hydrogenOxygenBondFormingWitness

sampleCarbonCarbonBondFormingProduct :: BondFormingProduct
sampleCarbonCarbonBondFormingProduct = carbonCarbonBondFormingWitness

sampleTrivialUnwiredProduct :: BondFormingProduct
sampleTrivialUnwiredProduct = bondFormingProductUnwired

-- | Unwired **bond-forming** modality OK without thermo break.
unwiredBondFormingDesignOk :: Bool
unwiredBondFormingDesignOk =
  evaluateBondFormingConservation
    BondFormingConservationUnwired
    sampleHydrogenOxygenBondFormingProduct
    bondFormingXorPostureConcurrent
    bondFormingChannelInteractApply
    False
    False
    False
    False
    == BondFormingNamedOk

-- | H–O bond-forming witness: QTAIM BCP + Mayer/DDEC + Interact concurrent Π_c.
hydrogenOxygenBondFormingConcurrentOk :: Bool
hydrogenOxygenBondFormingConcurrentOk =
  let witness = hydrogenOxygenBondFormingWitness
   in bondFormingProductHolds 0 witness
        && bondFormingProductHolds 1 witness
        && bondFormingProductHolds 2 witness
        && bondFormingProductPresentCount witness == 3
        && bondFormingProductIsConcurrent witness

-- | C–C bond-forming witness: QTAIM BCP + Interact concurrent Π_c.
carbonCarbonBondFormingConcurrentOk :: Bool
carbonCarbonBondFormingConcurrentOk =
  let witness = carbonCarbonBondFormingWitness
   in bondFormingProductHolds 0 witness
        && bondFormingProductHolds 2 witness
        && bondFormingProductPresentCount witness == 2
        && bondFormingProductIsConcurrent witness

-- | Concurrent **product** Π_c — ≥2 Present is **product** not XOR.
concurrentProductNotXorOk :: Bool
concurrentProductNotXorOk =
  bondFormingProductIsConcurrent hydrogenOxygenBondFormingWitness
    && bondFormingProductPresentCount hydrogenOxygenBondFormingWitness >= 2
    && bondFormingProductPresentCount hydrogenOxygenBondFormingWitness == 3

-- | QTAIM BCP is the primary domain channel (class 2 bond-forming).
qtaimBcpOk :: Bool
qtaimBcpOk =
  bondFormingProductHolds 0 hydrogenOxygenBondFormingWitness
    && bondFormingProductHolds 0 carbonCarbonBondFormingWitness
    && class2BondFormingPatternIndex == 2

-- | Forming arrow on Kleisli Interact — not Refine separation.
interactNotRefineOk :: Bool
interactNotRefineOk =
  evaluateBondFormingChannel
    BondFormingConservationUnwired
    bondFormingChannelInteractApply
    False
    False
    == BondFormingChannelNamedOk
    && bondFormingProductHolds 2 hydrogenOxygenBondFormingWitness

-- | Refine-as-forming posture is fail-closed.
refineAsFormingRefuse :: Bool
refineAsFormingRefuse =
  evaluateBondFormingChannel
    BondFormingConservationUnwired
    bondFormingChannelRefineSeparation
    False
    False
    == BondFormingChannelRefineAsFormingRefuse
    && evaluateBondFormingConservation
      BondFormingConservationUnwired
      sampleHydrogenOxygenBondFormingProduct
      bondFormingXorPostureConcurrent
      bondFormingChannelRefineSeparation
      False
      False
      False
      False
      == BondFormingRefineAsFormingRefuse

-- | Hydrogen atomic number (H–O bond-forming witness pin).
hydrogenZ :: Int
hydrogenZ = 1

-- | Oxygen atomic number (H–O bond-forming witness pin).
oxygenZ :: Int
oxygenZ = 8

-- | Carbon atomic number (C–C bond-forming witness pin).
carbonZ :: Int
carbonZ = 6

-- | XOR mutually-exclusive posture is fail-closed.
xorMutuallyExclusiveRefuse :: Bool
xorMutuallyExclusiveRefuse =
  evaluateBondFormingXor
    BondFormingConservationUnwired
    bondFormingXorPostureExclusive
    False
    False
    == BondFormingXorMutuallyExclusiveRefuse
    && evaluateBondFormingConservation
      BondFormingConservationUnwired
      sampleHydrogenOxygenBondFormingProduct
      bondFormingXorPostureExclusive
      bondFormingChannelInteractApply
      False
      False
      False
      False
      == BondFormingXorRefuse

-- | GREEN invent on **bond-forming** **conservation** promotion is refused.
greenInventBondFormingRefuse :: Bool
greenInventBondFormingRefuse =
  evaluateBondFormingConservation
    BondFormingConservationUnwired
    sampleHydrogenOxygenBondFormingProduct
    bondFormingXorPostureConcurrent
    bondFormingChannelInteractApply
    True
    False
    False
    False
    == BondFormingGreenInventRefuse
    && evaluateBondFormingProduct
      BondFormingConservationUnwired
      sampleHydrogenOxygenBondFormingProduct
      True
      False
      False
      False
      == BondFormingGreenInventRefuse

-- | Parallel bond-forming axiom mint is refused (sole axiom = second law + conservation).
parallelAxiomRefuse :: Bool
parallelAxiomRefuse =
  evaluateBondFormingConservation
    BondFormingConservationUnwired
    sampleHydrogenOxygenBondFormingProduct
    bondFormingXorPostureConcurrent
    bondFormingChannelInteractApply
    False
    False
    True
    False
    == BondFormingParallelAxiomRefuse
    && evaluateBondFormingProduct
      BondFormingConservationUnwired
      sampleHydrogenOxygenBondFormingProduct
      False
      False
      True
      False
      == BondFormingParallelAxiomRefuse

-- | Bond order as standalone axiom mint is refused.
bondOrderAxiomRefuse :: Bool
bondOrderAxiomRefuse =
  evaluateBondFormingConservation
    BondFormingConservationUnwired
    sampleHydrogenOxygenBondFormingProduct
    bondFormingXorPostureConcurrent
    bondFormingChannelInteractApply
    False
    False
    False
    True
    == BondFormingBondOrderAxiomRefuse
    && evaluateBondFormingProduct
      BondFormingConservationUnwired
      sampleHydrogenOxygenBondFormingProduct
      False
      False
      False
      True
      == BondFormingBondOrderAxiomRefuse

-- | Assumed **bond-forming** modality OK without thermo break (design scaffold).
assumedBondFormingDesignOk :: Bool
assumedBondFormingDesignOk =
  evaluateBondFormingConservation
    BondFormingConservationAssumed
    sampleHydrogenOxygenBondFormingProduct
    bondFormingXorPostureConcurrent
    bondFormingChannelInteractApply
    False
    False
    False
    False
    == BondFormingDesignOk

-- | Surrogate **bond-forming** modality OK without thermo break (design scaffold).
surrogateBondFormingDesignOk :: Bool
surrogateBondFormingDesignOk =
  evaluateBondFormingConservation
    BondFormingConservationSurrogate
    sampleHydrogenOxygenBondFormingProduct
    bondFormingXorPostureConcurrent
    bondFormingChannelInteractApply
    False
    False
    False
    False
    == BondFormingDesignOk

-- | Four-step class-2 **bond-forming** lattice scaffold pinned.
bondFormingLatticeScaffold :: Bool
bondFormingLatticeScaffold =
  bondFormingLatticeCount == 4
    && unwiredBondFormingDesignOk
    && qtaimBcpOk
    && interactNotRefineOk
    && hydrogenOxygenBondFormingConcurrentOk
    && carbonCarbonBondFormingConcurrentOk
    && concurrentProductNotXorOk
    && refineAsFormingRefuse
    && xorMutuallyExclusiveRefuse
    && parallelAxiomRefuse
    && bondOrderAxiomRefuse
    && assumedBondFormingDesignOk
    && surrogateBondFormingDesignOk

-- | **Bond-forming** lattice is structure scaffold — not 118² GREEN periodic table.
bondFormingLatticeNotGreenTable :: Bool
bondFormingLatticeNotGreenTable =
  bondFormingLatticeCount == 4
    && bondFormingLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && bondFormingDomainCount /= iupacTableCardinality * iupacTableCardinality
    && bondFormingDomainSlotCount /= iupacTableCardinality * iupacTableCardinality

-- | Four **bond-forming** identity law cells scaffold pinned.
bondFormingConservationLawsScaffold :: Bool
bondFormingConservationLawsScaffold =
  bondFormingLawCount == 4
    && hydrogenOxygenBondFormingConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventBondFormingRefuse
    && parallelAxiomRefuse
    && bondOrderAxiomRefuse
    && refineAsFormingRefuse

-- | **Bond-forming** law cells are structure scaffold — not 118² GREEN periodic table.
bondFormingConservationLawsNotGreenTable :: Bool
bondFormingConservationLawsNotGreenTable =
  bondFormingConservationLawsScaffold
    && bondFormingLawCount /= 118 * 118
    && bondFormingDomainCount /= 118 * 118

-- | Class-2 **bond-forming** **conservation** claims route to knowing / quantum fiber (not meso acting).
bondFormingKnowingFiberOk :: Bool
bondFormingKnowingFiberOk = True

-- | Class-2 **bond-forming** invent refuse-closed scaffold witness.
bondFormingInventRefuse :: Bool
bondFormingInventRefuse = not bondFormingConservationProved

-- | **Bond-forming** lattice steps are concurrent Π_c — not XOR enum bucket.
bondFormingLatticeNotXor :: Bool
bondFormingLatticeNotXor =
  unwiredBondFormingDesignOk
    && assumedBondFormingDesignOk
    && surrogateBondFormingDesignOk
    && hydrogenOxygenBondFormingConcurrentOk
    && concurrentProductNotXorOk
    && xorMutuallyExclusiveRefuse
    && greenInventBondFormingRefuse

-- | Class-2 **bond-forming** proved (always false on this Unwired cell).
bondFormingConservationProved :: Bool
bondFormingConservationProved = False

-- | `SpeciesId` is **not** forked into this cell.
speciesIdForked :: Bool
speciesIdForked = False

-- | **Bond-forming** morphisms are concurrent Π_c class-2 factors — not SpeciesId fork.
bondFormingNeSpeciesId :: Bool
bondFormingNeSpeciesId =
  patternProductConservationAuthority
    /= "umst/umst-chem/src/bond_reaction_graph.rs"
    && bondFormingConservationIntAuthority
      /= "umst/umst-chem/src/bond_reaction_graph.rs"
    && bondFormingDomainAll /= []
    && bondFormingProductIsConcurrent hydrogenOxygenBondFormingWitness
    && not speciesIdForked

-- | One axiom framing: second law + **conservation** for class-2 **bond-forming** scaffold.
bondFormingConservationFraming :: String
bondFormingConservationFraming =
  "second_law_conservation_bond_forming_one_axiom"

-- | Single design axiom: second law + **conservation** class-2 **bond-forming** (not second axiom).
bondFormingConservationAxiom :: Bool
bondFormingConservationAxiom =
  bondFormingLatticeScaffold
    && bondFormingLatticeNotGreenTable
    && bondFormingConservationLawsScaffold
    && bondFormingConservationLawsNotGreenTable
    && bondFormingKnowingFiberOk
    && qtaimBcpOk
    && interactNotRefineOk
    && hydrogenOxygenBondFormingConcurrentOk
    && carbonCarbonBondFormingConcurrentOk
    && concurrentProductNotXorOk
    && refineAsFormingRefuse
    && xorMutuallyExclusiveRefuse
    && parallelAxiomRefuse
    && bondOrderAxiomRefuse
    && greenInventBondFormingRefuse
    && bondFormingInventRefuse
    && bondFormingLatticeNotXor
    && bondFormingNeSpeciesId
    && not bondFormingConservationProved
    && not speciesIdForked
    && bondFormingConservationFraming
      == "second_law_conservation_bond_forming_one_axiom"

bondFormingConservationNamed :: String
bondFormingConservationNamed =
  "bondFormingConservation: BondFormingConservationModality Unwired Assumed Proved Surrogate four-step lattice bondFormingConservationProved false evaluateBondFormingProduct evaluateBondFormingConservation named class 2 bond_forming concurrent product identity conserved QTAIM BCP Mayer DDEC Interact Apply forming arrow not Refine present ge 2 product not XOR hydrogen oxygen carbon bond forming witness xor mutually exclusive refuse parallel axiom refuse bond order axiom refuse no SpeciesId fork second law conservation one axiom"

-- | Upstream PatternProductConservation authority (cited, not forked).
patternProductConservationAuthority :: String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

-- | INT bond_forming_conservation cross-row authority (read-only cite).
bondFormingConservationIntAuthority :: String
bondFormingConservationIntAuthority =
  "umst/umst-chem/src/x_rows/bond_forming_conservation.rs"

-- | L0 bond-forming table authority (read-only cite).
bondFormingTableAuthority :: String
bondFormingTableAuthority = "umst/umst-chem/src/l0_tables/bond_forming.rs"

-- | Kleisli Interact authority (read-only cite — forming arrow carrier).
kleisliInteractAuthority :: String
kleisliInteractAuthority = "umst/umst-chem/src/kleisli_interact.rs"

-- | L0 class-2 bond-forming scaffold authority (crosswalk).
chemL0Class2BondFormingAuthority :: String
chemL0Class2BondFormingAuthority = "CHEM-INT-NUANCE-BOND_FORMING"

bondFormingConservationCellId :: String
bondFormingConservationCellId = "CHEM-FORMAL-Q-HS-BOND-FORMING-CONSERVATION"

-- | Non-claim fence — class-2 **bond-forming** **conservation** Unwired ≠ Proved GREEN.
bondFormingConservationNonClaim :: String
bondFormingConservationNonClaim =
  "CHEM-FORMAL-Q-HS-BOND-FORMING-CONSERVATION BondFormingConservationModality Unwired Assumed Proved Surrogate four-step lattice bondFormingConservationProved false evaluateBondFormingProduct evaluateBondFormingConservation named class 2 bond_forming concurrent product identity conserved QTAIM BCP Mayer DDEC Interact Apply forming arrow not Refine present ge 2 product not XOR hydrogen oxygen carbon bond forming witness xor mutually exclusive refuse parallel axiom refuse bond order axiom refuse cite PatternProductConservation bond_forming_conservation INT not fork Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired not lib.rs not eos.rs not nano"

-- | Physics GREEN is unauthorized on the knowing class-2 **bond-forming** **conservation** scaffold.
bondFormingConservationPhysicsGreenAuthorized :: Bool
bondFormingConservationPhysicsGreenAuthorized = False

bondFormingConservationPhysicsGreenFalse :: Bool
bondFormingConservationPhysicsGreenFalse =
  not bondFormingConservationPhysicsGreenAuthorized

bondFormingConservationModalityUnwired :: Bool
bondFormingConservationModalityUnwired =
  bondFormingConservationModalityCurrent == BondFormingConservationUnwired

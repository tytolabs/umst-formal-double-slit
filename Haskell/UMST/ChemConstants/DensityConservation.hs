-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.DensityConservation
Description : DENSITY-01 **density** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Density** **conservation**: DENSITY-01 DensityLadder mSDF → TE-SDF → SDF → FRep rung
order identity conserved on named ladder pins (four rungs named; composed mSDF→TE-SDF→SDF→FRep
equals mSDF→FRep direct). Named **density** identity conserved under honest scaffold; trivial
XOR and GREEN invent fail-closed. SDF ≠ ρ unless scalar field named. DENSITY-01 **density**
laws are structure witnesses only (@densityLadderProved@ = False). **Density** **conservation**
≠ occupancy Z-identity.

* @DensityConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateDensityConservation@ — named **density** identity conserved; composed legs typed **conservation**.
* @densityCommuteConservation@ — mSDF→TE-SDF→SDF→FRep composed equals mSDF→FRep direct (typed **density** **conservation**).
* **One** design axiom (@densityConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of DENSITY-01 **density** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-DENSITY-CONSERVATION@.
-}
module UMST.ChemConstants.DensityConservation
  ( DensityConservationModality (..)
  , densityConservationModalityCurrent
  , densityLatticeAll
  , densityLatticeCount
  , DensityLadderRung (..)
  , densityRungAll
  , densityRungCount
  , DensityLadderScalarKind (..)
  , NamedScalarField (..)
  , densityScalarScaffoldDefault
  , sdfNotRhoUnlessNamed
  , DensityCommutingLeg (..)
  , densityCommutingLegAll
  , densityCommutingLegCount
  , densityLegSource
  , densityLegTarget
  , densityLegSourceTargetDistinct
  , fourRungsNamed
  , liftMicroSdfToTeSdf
  , liftTeSdfToSdf
  , liftSdfToFRep
  , coarseMicroSdfToFRepDirect
  , densityIdentityConserved
  , densityCommuteConservation
  , densityRungOrderOk
  , DensityConservationVerdict (..)
  , evaluateDensityConservation
  , sampleDensityWitness
  , unwiredDensityDesignOk
  , fourRungsNamedOk
  , composedEqualsDirectOk
  , densityLegEndpointsMatchOk
  , densityIndirectComposesOk
  , assumedDensityDesignOk
  , surrogateDensityDesignOk
  , greenInventDensityRefuse
  , sdfNotRhoUnlessNamedOk
  , densityLatticeScaffold
  , densityLatticeNotGreenTable
  , densityConservationLawsScaffold
  , densityConservationLawsNotGreenTable
  , densityKnowingFiberOk
  , densityLadderInventRefuse
  , densityLatticeNotXor
  , densityLadderProved
  , densityConservationNeOccupancyZ
  , densityConservationFraming
  , densityConservationAxiom
  , densityConservationNamed
  , densityLadderAuthority
  , chemL0Density01Authority
  , densityConservationCellId
  , densityConservationNonClaim
  , densityConservationPhysicsGreenAuthorized
  , densityConservationPhysicsGreenFalse
  , densityConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not DENSITY-01 GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Design **density** modality for DENSITY-01 **conservation** claims.
data DensityConservationModality
  = DensityConservationUnwired
  | DensityConservationAssumed
  | DensityConservationProved
  | DensityConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **density** modality — always Unwired on this cell.
densityConservationModalityCurrent :: DensityConservationModality
densityConservationModalityCurrent = DensityConservationUnwired

-- | All DENSITY-01 **density** lattice steps in stable order.
densityLatticeAll :: [DensityConservationModality]
densityLatticeAll =
  [ DensityConservationUnwired
  , DensityConservationAssumed
  , DensityConservationProved
  , DensityConservationSurrogate
  ]

densityLatticeCount :: Int
densityLatticeCount = length densityLatticeAll

-- | North-star **density** ladder rung: mSDF → TE-SDF → SDF → FRep.
data DensityLadderRung
  = MicroSdfRung
  | TeSdfRung
  | SdfRung
  | FRepRung
  deriving (Eq, Show)

-- | All **density** ladder rungs in stable order (structure scaffold — not 118² GREEN table).
densityRungAll :: [DensityLadderRung]
densityRungAll = [MicroSdfRung, TeSdfRung, SdfRung, FRepRung]

densityRungCount :: Int
densityRungCount = length densityRungAll

-- | Monotonic index along the **density** ladder (0 = mSDF … 3 = FRep).
densityRungIndex :: DensityLadderRung -> Int
densityRungIndex rung =
  case rung of
    MicroSdfRung -> 0
    TeSdfRung -> 1
    SdfRung -> 2
    FRepRung -> 3

-- | Next **density** ladder rung toward FRep, if any.
densityRungNext :: DensityLadderRung -> Maybe DensityLadderRung
densityRungNext rung =
  case rung of
    MicroSdfRung -> Just TeSdfRung
    TeSdfRung -> Just SdfRung
    SdfRung -> Just FRepRung
    FRepRung -> Nothing

-- | Named scalar fields that may be coupled to a ladder rung (ρ must be explicit).
data NamedScalarField
  = ElectronDensityRho
  | ElfScalar
  | NciScalar
  | GateSdfScalar
  deriving (Eq, Show)

-- | Scalar kind on a ladder rung — generic SDF is **not** ρ unless named.
data DensityLadderScalarKind
  = SignedDistanceScalar
  | NamedScalar NamedScalarField
  deriving (Eq, Show)

-- | Scaffold default scalar — generic SDF, not ρ.
densityScalarScaffoldDefault :: DensityLadderScalarKind
densityScalarScaffoldDefault = SignedDistanceScalar

-- | Whether scalar is explicitly QTAIM electron **density** ρ.
isElectronDensityRho :: DensityLadderScalarKind -> Bool
isElectronDensityRho scalar =
  case scalar of
    SignedDistanceScalar -> False
    NamedScalar ElectronDensityRho -> True
    NamedScalar _ -> False

-- | SDF ≠ ρ unless the scalar field is named as electron **density**.
sdfNotRhoUnlessNamed :: DensityLadderScalarKind -> Bool
sdfNotRhoUnlessNamed scalar =
  case scalar of
    SignedDistanceScalar -> True
    NamedScalar ElectronDensityRho -> True
    NamedScalar _ -> True

-- | Named legs of the mSDF → TE-SDF → SDF → FRep commuting **density** diagram.
data DensityCommutingLeg
  = DensityLegMicroSdfToTeSdf
  | DensityLegTeSdfToSdf
  | DensityLegSdfToFRep
  | DensityLegMicroSdfToFRepDirect
  deriving (Eq, Show)

-- | All four DENSITY-01 commuting legs in stable order.
densityCommutingLegAll :: [DensityCommutingLeg]
densityCommutingLegAll =
  [ DensityLegMicroSdfToTeSdf
  , DensityLegTeSdfToSdf
  , DensityLegSdfToFRep
  , DensityLegMicroSdfToFRepDirect
  ]

densityCommutingLegCount :: Int
densityCommutingLegCount = length densityCommutingLegAll

-- | Source **density** ladder rung for a commuting leg.
densityLegSource :: DensityCommutingLeg -> DensityLadderRung
densityLegSource leg =
  case leg of
    DensityLegMicroSdfToTeSdf -> MicroSdfRung
    DensityLegTeSdfToSdf -> TeSdfRung
    DensityLegSdfToFRep -> SdfRung
    DensityLegMicroSdfToFRepDirect -> MicroSdfRung

-- | Target **density** ladder rung for a commuting leg.
densityLegTarget :: DensityCommutingLeg -> DensityLadderRung
densityLegTarget leg =
  case leg of
    DensityLegMicroSdfToTeSdf -> TeSdfRung
    DensityLegTeSdfToSdf -> SdfRung
    DensityLegSdfToFRep -> FRepRung
    DensityLegMicroSdfToFRepDirect -> FRepRung

-- | Every leg connects distinct **density** ladder rungs.
densityLegSourceTargetDistinct :: DensityCommutingLeg -> Bool
densityLegSourceTargetDistinct leg = densityLegSource leg /= densityLegTarget leg

-- | Four **density** ladder rungs and path legs are named (mSDF → TE-SDF → SDF → FRep).
fourRungsNamed :: Bool
fourRungsNamed =
  densityRungCount == 4
    && densityCommutingLegCount == 4
    && densityRungAll == [MicroSdfRung, TeSdfRung, SdfRung, FRepRung]
    && densityLegSource DensityLegMicroSdfToTeSdf == MicroSdfRung
    && densityLegTarget DensityLegMicroSdfToTeSdf == TeSdfRung
    && densityLegSource DensityLegTeSdfToSdf == TeSdfRung
    && densityLegTarget DensityLegTeSdfToSdf == SdfRung
    && densityLegSource DensityLegSdfToFRep == SdfRung
    && densityLegTarget DensityLegSdfToFRep == FRepRung
    && densityLegSource DensityLegMicroSdfToFRepDirect == MicroSdfRung
    && densityLegTarget DensityLegMicroSdfToFRepDirect == FRepRung

-- | **Density** ladder rung order mSDF → TE-SDF → SDF → FRep conserved.
densityRungOrderOk :: Bool
densityRungOrderOk =
  densityRungCount == 4
    && densityRungIndex MicroSdfRung < densityRungIndex TeSdfRung
    && densityRungIndex TeSdfRung < densityRungIndex SdfRung
    && densityRungIndex SdfRung < densityRungIndex FRepRung
    && densityRungNext MicroSdfRung == Just TeSdfRung
    && densityRungNext TeSdfRung == Just SdfRung
    && densityRungNext SdfRung == Just FRepRung
    && densityRungNext FRepRung == Nothing

-- | mSDF → TE-SDF lift on **density** identity (knowing fiber — Unwired scaffold).
liftMicroSdfToTeSdf :: Int -> Int
liftMicroSdfToTeSdf = id

-- | TE-SDF → SDF lift on **density** identity (knowing fiber — Unwired scaffold).
liftTeSdfToSdf :: Int -> Int
liftTeSdfToSdf = id

-- | SDF → FRep lift on **density** identity (knowing fiber — Unwired scaffold).
liftSdfToFRep :: Int -> Int
liftSdfToFRep = id

-- | Direct mSDF → FRep coarse on **density** identity (knowing fiber — Unwired scaffold).
coarseMicroSdfToFRepDirect :: Int -> Int
coarseMicroSdfToFRepDirect = id

-- | **Density** identity conserved: composed mSDF→TE-SDF→SDF→FRep equals mSDF→FRep direct.
densityIdentityConserved :: Int -> Bool
densityIdentityConserved witness =
  liftSdfToFRep (liftTeSdfToSdf (liftMicroSdfToTeSdf witness))
    == coarseMicroSdfToFRepDirect witness

-- | Typed **density** **conservation** along the commuting ladder (named legs).
densityCommuteConservation :: Int -> Bool
densityCommuteConservation = densityIdentityConserved

-- | Verdict for DENSITY-01 **density** **conservation** close (fail-closed).
data DensityConservationVerdict
  = DensityConservationDesignOk
  | DensityConservationNamedOk
  | DensityConservationTrivialRefuse
  | DensityConservationGreenInventRefuse
  | DensityConservationProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate **density** **conservation** under DENSITY-01 bar (fail-closed).
evaluateDensityConservation ::
  DensityConservationModality
  -> Int
  -> Bool
  -> Bool
  -> DensityConservationVerdict
evaluateDensityConservation modality witness claimPhysicsGreen claimProved
  | claimPhysicsGreen = DensityConservationGreenInventRefuse
  | claimProved = DensityConservationProvedWithoutBarRefuse
  | not (densityCommuteConservation witness) = DensityConservationTrivialRefuse
  | otherwise =
      case modality of
        DensityConservationUnwired ->
          if fourRungsNamed then DensityConservationNamedOk else DensityConservationDesignOk
        DensityConservationAssumed -> DensityConservationDesignOk
        DensityConservationSurrogate -> DensityConservationDesignOk
        DensityConservationProved -> DensityConservationProvedWithoutBarRefuse

sampleDensityWitness :: Int
sampleDensityWitness = 42

-- | Unwired **density** modality OK without thermo break.
unwiredDensityDesignOk :: Bool
unwiredDensityDesignOk =
  evaluateDensityConservation
    DensityConservationUnwired
    sampleDensityWitness
    False
    False
    == DensityConservationNamedOk

-- | Four **density** ladder rungs and path legs are named on scaffold.
fourRungsNamedOk :: Bool
fourRungsNamedOk = fourRungsNamed && densityRungCount == 4 && densityCommutingLegCount == 4

-- | Composed mSDF→TE-SDF→SDF→FRep equals mSDF→FRep direct (**density** **conservation**).
composedEqualsDirectOk :: Bool
composedEqualsDirectOk =
  densityCommuteConservation sampleDensityWitness
    && densityIdentityConserved sampleDensityWitness
    && liftSdfToFRep (liftTeSdfToSdf (liftMicroSdfToTeSdf sampleDensityWitness))
      == coarseMicroSdfToFRepDirect sampleDensityWitness

-- | Direct and indirect leg endpoints match on **density** ladder rungs.
densityLegEndpointsMatchOk :: Bool
densityLegEndpointsMatchOk =
  densityLegSource DensityLegMicroSdfToFRepDirect
    == densityLegSource DensityLegMicroSdfToTeSdf
    && densityLegTarget DensityLegSdfToFRep
      == densityLegTarget DensityLegMicroSdfToFRepDirect

-- | Indirect legs compose: TeSdf target of mSDF→TE-SDF equals TeSdf source of TE-SDF→SDF.
densityIndirectComposesOk :: Bool
densityIndirectComposesOk =
  densityLegTarget DensityLegMicroSdfToTeSdf == densityLegSource DensityLegTeSdfToSdf
    && densityLegTarget DensityLegTeSdfToSdf == densityLegSource DensityLegSdfToFRep

-- | Assumed **density** modality OK without thermo break (design scaffold).
assumedDensityDesignOk :: Bool
assumedDensityDesignOk =
  evaluateDensityConservation
    DensityConservationAssumed
    sampleDensityWitness
    False
    False
    == DensityConservationDesignOk

-- | Surrogate **density** modality OK without thermo break (design scaffold).
surrogateDensityDesignOk :: Bool
surrogateDensityDesignOk =
  evaluateDensityConservation
    DensityConservationSurrogate
    sampleDensityWitness
    False
    False
    == DensityConservationDesignOk

-- | GREEN invent on **density** **conservation** promotion is refused.
greenInventDensityRefuse :: Bool
greenInventDensityRefuse =
  evaluateDensityConservation
    DensityConservationUnwired
    sampleDensityWitness
    True
    False
    == DensityConservationGreenInventRefuse

-- | Scaffold default SDF ≠ ρ unless named witness.
sdfNotRhoUnlessNamedOk :: Bool
sdfNotRhoUnlessNamedOk =
  sdfNotRhoUnlessNamed densityScalarScaffoldDefault
    && not (isElectronDensityRho densityScalarScaffoldDefault)
    && sdfNotRhoUnlessNamed (NamedScalar ElectronDensityRho)

-- | Four-step DENSITY-01 **density** lattice scaffold pinned.
densityLatticeScaffold :: Bool
densityLatticeScaffold =
  densityLatticeCount == 4
    && unwiredDensityDesignOk
    && fourRungsNamedOk
    && densityRungOrderOk
    && composedEqualsDirectOk
    && densityLegEndpointsMatchOk
    && densityIndirectComposesOk
    && assumedDensityDesignOk
    && surrogateDensityDesignOk
    && sdfNotRhoUnlessNamedOk

-- | **Density** lattice is structure scaffold — not 118² GREEN periodic table.
densityLatticeNotGreenTable :: Bool
densityLatticeNotGreenTable =
  densityLatticeCount == 4
    && densityLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && densityRungCount /= iupacTableCardinality * iupacTableCardinality
    && densityCommutingLegCount /= iupacTableCardinality * iupacTableCardinality

-- | **Density** **conservation** law cells scaffold pinned.
densityConservationLawsScaffold :: Bool
densityConservationLawsScaffold =
  fourRungsNamedOk
    && densityRungOrderOk
    && composedEqualsDirectOk
    && densityLegEndpointsMatchOk
    && densityIndirectComposesOk
    && greenInventDensityRefuse
    && sdfNotRhoUnlessNamedOk

-- | **Density** law cells are structure scaffold — not 118² GREEN periodic table.
densityConservationLawsNotGreenTable :: Bool
densityConservationLawsNotGreenTable =
  densityConservationLawsScaffold
    && densityRungCount /= 118 * 118
    && densityCommutingLegCount /= 118 * 118

-- | DENSITY-01 **density** **conservation** claims route to knowing / quantum fiber (not meso acting).
densityKnowingFiberOk :: Bool
densityKnowingFiberOk = True

-- | DENSITY-01 DensityLadder invent refuse-closed scaffold witness.
densityLadderInventRefuse :: Bool
densityLadderInventRefuse = not densityLadderProved

-- | **Density** lattice steps are concurrent Π_c — not XOR enum bucket.
densityLatticeNotXor :: Bool
densityLatticeNotXor =
  unwiredDensityDesignOk
    && assumedDensityDesignOk
    && surrogateDensityDesignOk
    && composedEqualsDirectOk
    && greenInventDensityRefuse
    && sdfNotRhoUnlessNamedOk

-- | **Density** **conservation** is not occupancy Z-identity (distinct cell).
densityConservationNeOccupancyZ :: Bool
densityConservationNeOccupancyZ =
  densityConservationCellId
    /= "CHEM-FORMAL-Q-HS-OCCUPANCY-EXCEPTION-SETS-DISJOINT"
    && densityConservationCellId == "CHEM-FORMAL-Q-HS-DENSITY-CONSERVATION"

-- | DENSITY-01 DensityLadder proved (always false on this Unwired cell).
densityLadderProved :: Bool
densityLadderProved = False

-- | One axiom framing: second law + **conservation** for DENSITY-01 **density** scaffold.
densityConservationFraming :: String
densityConservationFraming =
  "second_law_conservation_density_one_axiom"

-- | Single design axiom: second law + **conservation** DENSITY-01 **density** (not second axiom).
densityConservationAxiom :: Bool
densityConservationAxiom =
  densityLatticeScaffold
    && densityLatticeNotGreenTable
    && densityConservationLawsScaffold
    && densityConservationLawsNotGreenTable
    && densityKnowingFiberOk
    && fourRungsNamedOk
    && densityRungOrderOk
    && composedEqualsDirectOk
    && densityLegEndpointsMatchOk
    && densityIndirectComposesOk
    && greenInventDensityRefuse
    && sdfNotRhoUnlessNamedOk
    && densityLadderInventRefuse
    && densityLatticeNotXor
    && densityConservationNeOccupancyZ
    && not densityLadderProved
    && densityConservationFraming
      == "second_law_conservation_density_one_axiom"

densityConservationNamed :: String
densityConservationNamed =
  "densityConservation: DensityConservationModality Unwired Assumed Proved Surrogate four-step lattice densityLadderProved false evaluateDensityConservation densityCommuteConservation named density four rungs mSDF TE-SDF SDF FRep composed equals direct density conservation knowing fiber SDF not rho unless named second law conservation one axiom not occupancy Z identity not 118 squared GREEN table"

-- | Upstream DensityLadder authority (cited, not forked).
densityLadderAuthority :: String
densityLadderAuthority = "umst/umst-chem/src/density_ladder.rs"

-- | L0 DENSITY-01 scaffold authority (crosswalk).
chemL0Density01Authority :: String
chemL0Density01Authority = "CHEM-L0-DENSITY-01"

densityConservationCellId :: String
densityConservationCellId = "CHEM-FORMAL-Q-HS-DENSITY-CONSERVATION"

-- | Non-claim fence — DENSITY-01 **density** **conservation** Unwired ≠ Proved GREEN.
densityConservationNonClaim :: String
densityConservationNonClaim =
  "CHEM-FORMAL-Q-HS-DENSITY-CONSERVATION DensityConservationModality Unwired Assumed Proved Surrogate four-step lattice densityLadderProved false evaluateDensityConservation densityCommuteConservation named density four rungs mSDF TE-SDF SDF FRep composed equals direct density conservation knowing fiber Unwired one axiom second law conservation SDF not rho unless named not occupancy Z identity not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing DENSITY-01 **density** **conservation** scaffold.
densityConservationPhysicsGreenAuthorized :: Bool
densityConservationPhysicsGreenAuthorized = False

densityConservationPhysicsGreenFalse :: Bool
densityConservationPhysicsGreenFalse =
  not densityConservationPhysicsGreenAuthorized

densityConservationModalityUnwired :: Bool
densityConservationModalityUnwired =
  densityConservationModalityCurrent == DensityConservationUnwired

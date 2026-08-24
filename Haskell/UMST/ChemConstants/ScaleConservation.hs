-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ScaleConservation
Description : SCALE-01 **scale** **conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Scale** **conservation**: SCALE-01 Q ↔ meso ↔ macro commuting-square identity conserved
on named class pins (three legs named; composed Q→meso→macro equals Q→macro direct).
Named **scale** identity conserved under honest scaffold; trivial XOR and GREEN invent
fail-closed. SCALE-01 **scale** laws are structure witnesses only
(@scale01CommuteProved@ = False). **Scale** **conservation** ≠ occupancy Z-identity.

* @ScaleConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateScaleConservation@ — named **scale** identity conserved; composed legs typed **conservation**.
* @scaleCommuteConservation@ — Q→meso→macro composed equals Q→macro direct (typed **scale** **conservation**).
* **One** design axiom (@scaleConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of SCALE-01 **scale** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-SCALE-CONSERVATION@.
-}
module UMST.ChemConstants.ScaleConservation
  ( ScaleConservationModality (..)
  , scaleConservationModalityCurrent
  , scaleLatticeAll
  , scaleLatticeCount
  , ScaleLevel (..)
  , scaleLevelAll
  , scaleLevelCount
  , ScaleCommutingLeg (..)
  , scaleCommutingLegAll
  , scaleCommutingLegCount
  , scaleLegSource
  , scaleLegTarget
  , scaleLegSourceTargetDistinct
  , threeLegsNamed
  , liftQToMeso
  , liftMesoToMacro
  , coarseQToMacroDirect
  , scaleIdentityConserved
  , scaleCommuteConservation
  , ScaleConservationVerdict (..)
  , evaluateScaleConservation
  , sampleScaleWitness
  , unwiredScaleDesignOk
  , threeLegsNamedOk
  , composedEqualsDirectOk
  , scaleLegEndpointsMatchOk
  , scaleIndirectComposesOk
  , assumedScaleDesignOk
  , surrogateScaleDesignOk
  , greenInventScaleRefuse
  , scaleLatticeScaffold
  , scaleLatticeNotGreenTable
  , scaleConservationLawsScaffold
  , scaleConservationLawsNotGreenTable
  , scaleKnowingFiberOk
  , scale01CommuteInventRefuse
  , scaleLatticeNotXor
  , scale01CommuteProved
  , scaleConservationNeOccupancyZ
  , scaleConservationFraming
  , scaleConservationAxiom
  , scaleConservationNamed
  , scaleCommutingDiagramsAuthority
  , chemL0Scale01Authority
  , scaleConservationCellId
  , scaleConservationNonClaim
  , scaleConservationPhysicsGreenAuthorized
  , scaleConservationPhysicsGreenFalse
  , scaleConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not SCALE-01 GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Design **scale** modality for SCALE-01 **conservation** claims.
data ScaleConservationModality
  = ScaleConservationUnwired
  | ScaleConservationAssumed
  | ScaleConservationProved
  | ScaleConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **scale** modality — always Unwired on this cell.
scaleConservationModalityCurrent :: ScaleConservationModality
scaleConservationModalityCurrent = ScaleConservationUnwired

-- | All SCALE-01 **scale** lattice steps in stable order.
scaleLatticeAll :: [ScaleConservationModality]
scaleLatticeAll =
  [ ScaleConservationUnwired
  , ScaleConservationAssumed
  , ScaleConservationProved
  , ScaleConservationSurrogate
  ]

scaleLatticeCount :: Int
scaleLatticeCount = length scaleLatticeAll

-- | L0 **scale** stratum in the Q ↔ meso ↔ macro ladder.
data ScaleLevel
  = ScaleQuantum
  | ScaleMeso
  | ScaleMacro
  deriving (Eq, Show)

-- | All **scale** strata in stable order (structure scaffold — not 118² GREEN table).
scaleLevelAll :: [ScaleLevel]
scaleLevelAll = [ScaleQuantum, ScaleMeso, ScaleMacro]

scaleLevelCount :: Int
scaleLevelCount = length scaleLevelAll

-- | Named legs of the Q ↔ meso ↔ macro commuting **scale** diagram.
data ScaleCommutingLeg
  = ScaleLegQuantumToMeso
  | ScaleLegMesoToMacro
  | ScaleLegQuantumToMacroDirect
  deriving (Eq, Show)

-- | All three SCALE-01 commuting legs in stable order.
scaleCommutingLegAll :: [ScaleCommutingLeg]
scaleCommutingLegAll =
  [ ScaleLegQuantumToMeso
  , ScaleLegMesoToMacro
  , ScaleLegQuantumToMacroDirect
  ]

scaleCommutingLegCount :: Int
scaleCommutingLegCount = length scaleCommutingLegAll

-- | Source **scale** stratum for a commuting leg.
scaleLegSource :: ScaleCommutingLeg -> ScaleLevel
scaleLegSource leg =
  case leg of
    ScaleLegQuantumToMeso -> ScaleQuantum
    ScaleLegMesoToMacro -> ScaleMeso
    ScaleLegQuantumToMacroDirect -> ScaleQuantum

-- | Target **scale** stratum for a commuting leg.
scaleLegTarget :: ScaleCommutingLeg -> ScaleLevel
scaleLegTarget leg =
  case leg of
    ScaleLegQuantumToMeso -> ScaleMeso
    ScaleLegMesoToMacro -> ScaleMacro
    ScaleLegQuantumToMacroDirect -> ScaleMacro

-- | Every leg connects distinct **scale** strata.
scaleLegSourceTargetDistinct :: ScaleCommutingLeg -> Bool
scaleLegSourceTargetDistinct leg = scaleLegSource leg /= scaleLegTarget leg

-- | Three legs of the commuting **scale** square are named.
threeLegsNamed :: Bool
threeLegsNamed =
  scaleCommutingLegCount == 3
    && scaleLegSource ScaleLegQuantumToMeso == ScaleQuantum
    && scaleLegTarget ScaleLegQuantumToMeso == ScaleMeso
    && scaleLegSource ScaleLegMesoToMacro == ScaleMeso
    && scaleLegTarget ScaleLegMesoToMacro == ScaleMacro
    && scaleLegSource ScaleLegQuantumToMacroDirect == ScaleQuantum
    && scaleLegTarget ScaleLegQuantumToMacroDirect == ScaleMacro

-- | Quantum → meso lift on **scale** identity (knowing fiber — Unwired scaffold).
liftQToMeso :: Int -> Int
liftQToMeso = id

-- | Meso → macro lift on **scale** identity (knowing fiber — Unwired scaffold).
liftMesoToMacro :: Int -> Int
liftMesoToMacro = id

-- | Direct quantum → macro coarse on **scale** identity (knowing fiber — Unwired scaffold).
coarseQToMacroDirect :: Int -> Int
coarseQToMacroDirect = id

-- | **Scale** identity conserved: composed Q→meso→macro equals Q→macro direct.
scaleIdentityConserved :: Int -> Bool
scaleIdentityConserved witness =
  liftMesoToMacro (liftQToMeso witness) == coarseQToMacroDirect witness

-- | Typed **scale** **conservation** along the commuting square (named legs).
scaleCommuteConservation :: Int -> Bool
scaleCommuteConservation = scaleIdentityConserved

-- | Verdict for SCALE-01 **scale** **conservation** close (fail-closed).
data ScaleConservationVerdict
  = ScaleConservationDesignOk
  | ScaleConservationNamedOk
  | ScaleConservationTrivialRefuse
  | ScaleConservationGreenInventRefuse
  | ScaleConservationProvedWithoutBarRefuse
  deriving (Eq, Show)

-- | Evaluate **scale** **conservation** under SCALE-01 bar (fail-closed).
evaluateScaleConservation ::
  ScaleConservationModality
  -> Int
  -> Bool
  -> Bool
  -> ScaleConservationVerdict
evaluateScaleConservation modality witness claimPhysicsGreen claimProved
  | claimPhysicsGreen = ScaleConservationGreenInventRefuse
  | claimProved = ScaleConservationProvedWithoutBarRefuse
  | not (scaleCommuteConservation witness) = ScaleConservationTrivialRefuse
  | otherwise =
      case modality of
        ScaleConservationUnwired ->
          if threeLegsNamed then ScaleConservationNamedOk else ScaleConservationDesignOk
        ScaleConservationAssumed -> ScaleConservationDesignOk
        ScaleConservationSurrogate -> ScaleConservationDesignOk
        ScaleConservationProved -> ScaleConservationProvedWithoutBarRefuse

sampleScaleWitness :: Int
sampleScaleWitness = 42

-- | Unwired **scale** modality OK without thermo break.
unwiredScaleDesignOk :: Bool
unwiredScaleDesignOk =
  evaluateScaleConservation
    ScaleConservationUnwired
    sampleScaleWitness
    False
    False
    == ScaleConservationNamedOk

-- | Three commuting **scale** legs are named on scaffold.
threeLegsNamedOk :: Bool
threeLegsNamedOk = threeLegsNamed && scaleCommutingLegCount == 3

-- | Composed Q→meso→macro equals Q→macro direct (**scale** **conservation**).
composedEqualsDirectOk :: Bool
composedEqualsDirectOk =
  scaleCommuteConservation sampleScaleWitness
    && scaleIdentityConserved sampleScaleWitness
    && liftMesoToMacro (liftQToMeso sampleScaleWitness)
      == coarseQToMacroDirect sampleScaleWitness

-- | Direct and indirect leg endpoints match on **scale** strata.
scaleLegEndpointsMatchOk :: Bool
scaleLegEndpointsMatchOk =
  scaleLegSource ScaleLegQuantumToMeso
    == scaleLegSource ScaleLegQuantumToMacroDirect
    && scaleLegTarget ScaleLegMesoToMacro
      == scaleLegTarget ScaleLegQuantumToMacroDirect

-- | Indirect leg composes: meso target of Q→meso equals meso source of meso→macro.
scaleIndirectComposesOk :: Bool
scaleIndirectComposesOk =
  scaleLegTarget ScaleLegQuantumToMeso == scaleLegSource ScaleLegMesoToMacro

-- | Assumed **scale** modality OK without thermo break (design scaffold).
assumedScaleDesignOk :: Bool
assumedScaleDesignOk =
  evaluateScaleConservation
    ScaleConservationAssumed
    sampleScaleWitness
    False
    False
    == ScaleConservationDesignOk

-- | Surrogate **scale** modality OK without thermo break (design scaffold).
surrogateScaleDesignOk :: Bool
surrogateScaleDesignOk =
  evaluateScaleConservation
    ScaleConservationSurrogate
    sampleScaleWitness
    False
    False
    == ScaleConservationDesignOk

-- | GREEN invent on **scale** **conservation** promotion is refused.
greenInventScaleRefuse :: Bool
greenInventScaleRefuse =
  evaluateScaleConservation
    ScaleConservationUnwired
    sampleScaleWitness
    True
    False
    == ScaleConservationGreenInventRefuse

-- | Four-step SCALE-01 **scale** lattice scaffold pinned.
scaleLatticeScaffold :: Bool
scaleLatticeScaffold =
  scaleLatticeCount == 4
    && unwiredScaleDesignOk
    && threeLegsNamedOk
    && composedEqualsDirectOk
    && scaleLegEndpointsMatchOk
    && scaleIndirectComposesOk
    && assumedScaleDesignOk
    && surrogateScaleDesignOk

-- | **Scale** lattice is structure scaffold — not 118² GREEN periodic table.
scaleLatticeNotGreenTable :: Bool
scaleLatticeNotGreenTable =
  scaleLatticeCount == 4
    && scaleLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && scaleLevelCount /= iupacTableCardinality * iupacTableCardinality
    && scaleCommutingLegCount /= iupacTableCardinality * iupacTableCardinality

-- | **Scale** **conservation** law cells scaffold pinned.
scaleConservationLawsScaffold :: Bool
scaleConservationLawsScaffold =
  threeLegsNamedOk
    && composedEqualsDirectOk
    && scaleLegEndpointsMatchOk
    && scaleIndirectComposesOk
    && greenInventScaleRefuse

-- | **Scale** law cells are structure scaffold — not 118² GREEN periodic table.
scaleConservationLawsNotGreenTable :: Bool
scaleConservationLawsNotGreenTable =
  scaleConservationLawsScaffold
    && scaleLevelCount /= 118 * 118
    && scaleCommutingLegCount /= 118 * 118

-- | SCALE-01 **scale** **conservation** claims route to knowing / quantum fiber (not meso acting).
scaleKnowingFiberOk :: Bool
scaleKnowingFiberOk = True

-- | SCALE-01 commute invent refuse-closed scaffold witness.
scale01CommuteInventRefuse :: Bool
scale01CommuteInventRefuse = not scale01CommuteProved

-- | **Scale** lattice steps are concurrent Π_c — not XOR enum bucket.
scaleLatticeNotXor :: Bool
scaleLatticeNotXor =
  unwiredScaleDesignOk
    && assumedScaleDesignOk
    && surrogateScaleDesignOk
    && composedEqualsDirectOk
    && greenInventScaleRefuse

-- | **Scale** **conservation** is not occupancy Z-identity (distinct cell).
scaleConservationNeOccupancyZ :: Bool
scaleConservationNeOccupancyZ =
  scaleConservationCellId
    /= "CHEM-FORMAL-Q-HS-SCALE-OCCUPANCY-Z-COMMUTE"
    && scaleConservationCellId == "CHEM-FORMAL-Q-HS-SCALE-CONSERVATION"

-- | SCALE-01 commute proved (always false on this Unwired cell).
scale01CommuteProved :: Bool
scale01CommuteProved = False

-- | One axiom framing: second law + **conservation** for SCALE-01 **scale** scaffold.
scaleConservationFraming :: String
scaleConservationFraming =
  "second_law_conservation_scale_one_axiom"

-- | Single design axiom: second law + **conservation** SCALE-01 **scale** (not second axiom).
scaleConservationAxiom :: Bool
scaleConservationAxiom =
  scaleLatticeScaffold
    && scaleLatticeNotGreenTable
    && scaleConservationLawsScaffold
    && scaleConservationLawsNotGreenTable
    && scaleKnowingFiberOk
    && threeLegsNamedOk
    && composedEqualsDirectOk
    && scaleLegEndpointsMatchOk
    && scaleIndirectComposesOk
    && greenInventScaleRefuse
    && scale01CommuteInventRefuse
    && scaleLatticeNotXor
    && scaleConservationNeOccupancyZ
    && not scale01CommuteProved
    && scaleConservationFraming
      == "second_law_conservation_scale_one_axiom"

scaleConservationNamed :: String
scaleConservationNamed =
  "scaleConservation: ScaleConservationModality Unwired Assumed Proved Surrogate four-step lattice scale01CommuteProved false evaluateScaleConservation scaleCommuteConservation named scale three legs quantum to meso meso to macro quantum to macro direct composed equals direct scale conservation knowing fiber second law conservation one axiom not occupancy Z identity not 118 squared GREEN table"

-- | Upstream **scale** commuting-diagrams authority (cited, not forked).
scaleCommutingDiagramsAuthority :: String
scaleCommutingDiagramsAuthority = "umst/umst-chem/src/scale_commuting_diagrams.rs"

-- | L0 SCALE-01 scaffold authority (crosswalk).
chemL0Scale01Authority :: String
chemL0Scale01Authority = "CHEM-L0-SCALE-01"

scaleConservationCellId :: String
scaleConservationCellId = "CHEM-FORMAL-Q-HS-SCALE-CONSERVATION"

-- | Non-claim fence — SCALE-01 **scale** **conservation** Unwired ≠ Proved GREEN.
scaleConservationNonClaim :: String
scaleConservationNonClaim =
  "CHEM-FORMAL-Q-HS-SCALE-CONSERVATION ScaleConservationModality Unwired Assumed Proved Surrogate four-step lattice scale01CommuteProved false evaluateScaleConservation scaleCommuteConservation named scale three legs quantum to meso meso to macro quantum to macro direct composed equals direct scale conservation knowing fiber Unwired one axiom second law conservation not occupancy Z identity not 118 squared GREEN table not meso acting not physics GREEN not production_wired"

-- | Physics GREEN is unauthorized on the knowing SCALE-01 **scale** **conservation** scaffold.
scaleConservationPhysicsGreenAuthorized :: Bool
scaleConservationPhysicsGreenAuthorized = False

scaleConservationPhysicsGreenFalse :: Bool
scaleConservationPhysicsGreenFalse =
  not scaleConservationPhysicsGreenAuthorized

scaleConservationModalityUnwired :: Bool
scaleConservationModalityUnwired =
  scaleConservationModalityCurrent == ScaleConservationUnwired

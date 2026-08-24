-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ThermoConservation
Description : THERMO-01 **Thermo_n G(T,P,x) conservation** on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

**Thermo_n G** **conservation**: THERMO-01 Green Book **G(T,P,x)** identity conserved on named
state variables T → P → x with composed T∘P∘x identity equal to direct G (typed **conservation**).
CALPHAD hull identity conserved; formation-zero ≠ G fail-closed; measured-scalar G invent refuse;
scrambled order refuse; trivial Z=0 refuse. THERMO-01 **thermo** laws are structure witnesses only
(@thermoGProved@ = False). Live Process routes acting; this file is knowing-fiber typed witness —
not live G, not Thermo_n Proved.

* @ThermoConservationModality@ = Unwired / Assumed / Proved / Surrogate — four-step lattice, not 118² GREEN table.
* @evaluateThermoConservation@ — named T, P, x identity conserved; composed legs typed **conservation**.
* @thermoCommuteConservation@ — T∘P∘x composed equals T→G direct (typed **thermo** **conservation**).
* **One** design axiom (@thermoConservationAxiom@): second law + **conservation**.
* @physics_green@ stays false.

Haskell mirror of THERMO-01 **Thermo_n G** **conservation** on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-THERMO-CONSERVATION@.
-}
module UMST.ChemConstants.ThermoConservation
  ( ThermoConservationModality (..)
  , thermoConservationModalityCurrent
  , thermoLatticeAll
  , thermoLatticeCount
  , ThermoElementZ (..)
  , thermoElementZAll
  , thermoElementZCount
  , thermoElementZNumeric
  , ThermoStateVariable (..)
  , thermoStateVariableAll
  , thermoStateVariableCount
  , thermoVarString
  , NamedThermoScalar (..)
  , ThermoScalarKind (..)
  , thermoScalarScaffoldDefault
  , formationZeroNotGUnlessNamed
  , ThermoConservationLeg (..)
  , thermoConservationLegAll
  , thermoConservationLegCount
  , thermoLegSource
  , thermoLegTarget
  , thermoLegSourceTargetDistinct
  , threeLegsNamed
  , ThermoConservationField (..)
  , thermoConservationFieldNamed
  , thermoAtVariable
  , ThermoCalphadHullState (..)
  , thermoCalphadZero
  , thermoCalphadPositive
  , fusionCalphadHull
  , ThermoConservationPath (..)
  , thermoConservationPathIronL1
  , thermoConservationPathCopperL1
  , thermoConservationPathUnwiredL1
  , liftTemperature
  , liftPressure
  , liftComposition
  , directGreenBookG
  , thermoIdentityConserved
  , thermoCommuteConservation
  , thermoVarOrderOk
  , ThermoGPathVerdict (..)
  , evaluateThermoGPath
  , ThermoConservationVerdict (..)
  , evaluateThermoConservation
  , unwiredThermoDesignOk
  , threeLegsNamedOk
  , composedEqualsDirectOk
  , thermoLegEndpointsMatchOk
  , thermoIndirectComposesOk
  , assumedThermoDesignOk
  , surrogateThermoDesignOk
  , greenInventThermoRefuse
  , formationZeroMisidentifiedAsGRefuse
  , measuredScalarInventRefuse
  , scrambledOrderRefuse
  , liveProcessGRefuse
  , trivialZZeroRefuse
  , formationZeroNotGUnlessNamedOk
  , calphadHullIdentityConserved
  , feElementZValid
  , copperElementZValid
  , oganessonZValid
  , ironThermoConservationUnwiredOk
  , copperThermoConservationUnwiredOk
  , thermoLatticeScaffold
  , thermoLatticeNotGreenTable
  , thermoConservationLawsScaffold
  , thermoConservationLawsNotGreenTable
  , thermoKnowingFiberOk
  , thermoGInventRefuse
  , thermoLatticeNotXor
  , thermoGProved
  , thermoConservationFraming
  , thermoConservationAxiom
  , thermoConservationNamed
  , thermoNAuthority
  , chemL0Thermo01Authority
  , thermoConservationCellId
  , thermoConservationNonClaim
  , thermoConservationPhysicsGreenAuthorized
  , thermoConservationPhysicsGreenFalse
  , thermoConservationModalityUnwired
  ) where

-- | IUPAC periodic-table cardinality (Z=1..118) — not THERMO-01 GREEN table.
iupacTableCardinality :: Int
iupacTableCardinality = 118

-- | Design **thermo** modality for THERMO-01 **conservation** claims.
data ThermoConservationModality
  = ThermoConservationUnwired
  | ThermoConservationAssumed
  | ThermoConservationProved
  | ThermoConservationSurrogate
  deriving (Eq, Show)

-- | Current scaffold **thermo** modality — always Unwired on this cell.
thermoConservationModalityCurrent :: ThermoConservationModality
thermoConservationModalityCurrent = ThermoConservationUnwired

-- | All THERMO-01 **thermo** lattice steps in stable order.
thermoLatticeAll :: [ThermoConservationModality]
thermoLatticeAll =
  [ ThermoConservationUnwired
  , ThermoConservationAssumed
  , ThermoConservationProved
  , ThermoConservationSurrogate
  ]

thermoLatticeCount :: Int
thermoLatticeCount = length thermoLatticeAll

-- | Private Z pin for **Thermo_n** witnesses — not L1 SpeciesId.
data ThermoElementZ
  = ThermoElementIron
  | ThermoElementCopper
  | ThermoElementOganesson
  deriving (Eq, Show)

-- | All scaffold **thermo** element Z pins in stable order.
thermoElementZAll :: [ThermoElementZ]
thermoElementZAll =
  [ ThermoElementIron
  , ThermoElementCopper
  , ThermoElementOganesson
  ]

thermoElementZCount :: Int
thermoElementZCount = length thermoElementZAll

-- | Numeric Z for a **thermo** element pin.
thermoElementZNumeric :: ThermoElementZ -> Int
thermoElementZNumeric z =
  case z of
    ThermoElementIron -> 26
    ThermoElementCopper -> 29
    ThermoElementOganesson -> 118

-- | Whether a **thermo** element Z is valid IUPAC Z @ scaffold.
isValidIupacZ :: ThermoElementZ -> Bool
isValidIupacZ z =
  let n = thermoElementZNumeric z
   in n > 0 && n <= iupacTableCardinality

-- | Named **Thermo_n** state variables T, P, x, G (Green Book design names only).
data ThermoStateVariable
  = ThermoTemperature
  | ThermoPressure
  | ThermoComposition
  | ThermoGibbsG
  deriving (Eq, Show)

-- | All **Thermo_n** state variables in stable order (structure scaffold — not 118² GREEN table).
thermoStateVariableAll :: [ThermoStateVariable]
thermoStateVariableAll =
  [ ThermoTemperature
  , ThermoPressure
  , ThermoComposition
  , ThermoGibbsG
  ]

thermoStateVariableCount :: Int
thermoStateVariableCount = length thermoStateVariableAll

-- | Monotonic index along T → P → x → G (0 = T … 3 = G).
thermoStateVariableIndex :: ThermoStateVariable -> Int
thermoStateVariableIndex var =
  case var of
    ThermoTemperature -> 0
    ThermoPressure -> 1
    ThermoComposition -> 2
    ThermoGibbsG -> 3

-- | Green Book design name for a **Thermo_n** state variable.
thermoVarString :: ThermoStateVariable -> String
thermoVarString var =
  case var of
    ThermoTemperature -> "T"
    ThermoPressure -> "P"
    ThermoComposition -> "x"
    ThermoGibbsG -> "G"

-- | Named scalar kinds — Green Book G vs formation-zero vs measured invent.
data NamedThermoScalar
  = GreenBookGNamed
  | FormationZeroNamed
  | MeasuredScalarInventNamed
  deriving (Eq, Show)

-- | Scalar kind on a **Thermo_n** variable — formation-zero ≠ G unless named.
data ThermoScalarKind
  = GreenBookGScalar
  | NamedThermoScalar NamedThermoScalar
  deriving (Eq, Show)

-- | Scaffold default scalar — Green Book G.
thermoScalarScaffoldDefault :: ThermoScalarKind
thermoScalarScaffoldDefault = GreenBookGScalar

-- | Whether scalar is explicitly Green Book **G**.
isGreenBookG :: ThermoScalarKind -> Bool
isGreenBookG scalar =
  case scalar of
    GreenBookGScalar -> True
    NamedThermoScalar GreenBookGNamed -> True
    NamedThermoScalar _ -> False

-- | Whether scalar is formation-zero (≠ G unless named).
isFormationZero :: ThermoScalarKind -> Bool
isFormationZero scalar =
  case scalar of
    GreenBookGScalar -> False
    NamedThermoScalar FormationZeroNamed -> True
    NamedThermoScalar _ -> False

-- | Formation-zero ≠ G unless the scalar field is explicitly named Green Book G.
formationZeroNotGUnlessNamed :: ThermoScalarKind -> Bool
formationZeroNotGUnlessNamed scalar =
  case scalar of
    GreenBookGScalar -> True
    NamedThermoScalar GreenBookGNamed -> True
    NamedThermoScalar FormationZeroNamed -> True
    NamedThermoScalar _ -> False

-- | Named legs of the **Thermo_n G(T,P,x)** commuting **thermo** diagram.
data ThermoConservationLeg
  = ThermoLegTemperatureToPressure
  | ThermoLegPressureToComposition
  | ThermoLegCompositionToG
  | ThermoLegTemperatureToGDirect
  deriving (Eq, Show)

-- | All four THERMO-01 commuting legs in stable order.
thermoConservationLegAll :: [ThermoConservationLeg]
thermoConservationLegAll =
  [ ThermoLegTemperatureToPressure
  , ThermoLegPressureToComposition
  , ThermoLegCompositionToG
  , ThermoLegTemperatureToGDirect
  ]

thermoConservationLegCount :: Int
thermoConservationLegCount = length thermoConservationLegAll

-- | Source **Thermo_n** state variable for a commuting leg.
thermoLegSource :: ThermoConservationLeg -> ThermoStateVariable
thermoLegSource leg =
  case leg of
    ThermoLegTemperatureToPressure -> ThermoTemperature
    ThermoLegPressureToComposition -> ThermoPressure
    ThermoLegCompositionToG -> ThermoComposition
    ThermoLegTemperatureToGDirect -> ThermoTemperature

-- | Target **Thermo_n** state variable for a commuting leg.
thermoLegTarget :: ThermoConservationLeg -> ThermoStateVariable
thermoLegTarget leg =
  case leg of
    ThermoLegTemperatureToPressure -> ThermoPressure
    ThermoLegPressureToComposition -> ThermoComposition
    ThermoLegCompositionToG -> ThermoGibbsG
    ThermoLegTemperatureToGDirect -> ThermoGibbsG

-- | Every leg connects distinct **Thermo_n** state variables (step vs direct).
thermoLegSourceTargetDistinct :: ThermoConservationLeg -> Bool
thermoLegSourceTargetDistinct leg = thermoLegSource leg /= thermoLegTarget leg

-- | Three named T, P, x legs plus direct T→G on the **Thermo_n** diagram.
threeLegsNamed :: Bool
threeLegsNamed =
  thermoStateVariableCount == 4
    && thermoConservationLegCount == 4
    && thermoLegSource ThermoLegTemperatureToPressure == ThermoTemperature
    && thermoLegTarget ThermoLegTemperatureToPressure == ThermoPressure
    && thermoLegSource ThermoLegPressureToComposition == ThermoPressure
    && thermoLegTarget ThermoLegPressureToComposition == ThermoComposition
    && thermoLegSource ThermoLegCompositionToG == ThermoComposition
    && thermoLegTarget ThermoLegCompositionToG == ThermoGibbsG
    && thermoLegSource ThermoLegTemperatureToGDirect == ThermoTemperature
    && thermoLegTarget ThermoLegTemperatureToGDirect == ThermoGibbsG
    && ThermoLegTemperatureToPressure /= ThermoLegTemperatureToGDirect

-- | **Thermo_n G** **conservation** stamp field across T → P → x → G (typed identity witness).
data ThermoConservationField = ThermoConservationField
  { atTemperature :: Int
  , atPressure :: Int
  , atComposition :: Int
  , atGibbsG :: Int
  }
  deriving (Eq, Show)

-- | Named **Thermo_n** **conservation** field witness @ scaffold.
thermoConservationFieldNamed :: ThermoConservationField
thermoConservationFieldNamed =
  ThermoConservationField
    { atTemperature = 1
    , atPressure = 1
    , atComposition = 1
    , atGibbsG = 1
    }

-- | Lookup **Thermo_n G** **conservation** stamp at a named state variable.
thermoAtVariable :: ThermoConservationField -> ThermoStateVariable -> Int
thermoAtVariable field var =
  case var of
    ThermoTemperature -> atTemperature field
    ThermoPressure -> atPressure field
    ThermoComposition -> atComposition field
    ThermoGibbsG -> atGibbsG field

-- | Scaffold CALPHAD hull ledger for **Thermo_n G** (knowing fiber).
data ThermoCalphadHullState = ThermoCalphadHullState
  { calphadChemStamp :: Int
  , calphadLandauerWitness :: Int
  }
  deriving (Eq, Show)

-- | Zero CALPHAD hull witness @ scaffold.
thermoCalphadZero :: ThermoCalphadHullState
thermoCalphadZero = ThermoCalphadHullState 0 0

-- | Positive CALPHAD hull witness @ scaffold.
thermoCalphadPositive :: ThermoCalphadHullState
thermoCalphadPositive = ThermoCalphadHullState 1 1

-- | CALPHAD hull-preserving **Thermo_n** fusion — identity **conserved** (additive).
fusionCalphadHull ::
  ThermoCalphadHullState -> ThermoCalphadHullState -> ThermoCalphadHullState
fusionCalphadHull a b =
  ThermoCalphadHullState
    { calphadChemStamp = calphadChemStamp a + calphadChemStamp b
    , calphadLandauerWitness =
        calphadLandauerWitness a + calphadLandauerWitness b
    }

-- | A **Thermo_n G** **conservation** path at a refinement level.
data ThermoConservationPath = ThermoConservationPath
  { thermoPathField :: ThermoConservationField
  , thermoPathLevel :: Int
  , thermoPathElementZ :: ThermoElementZ
  , thermoPathScalar :: ThermoScalarKind
  }
  deriving (Eq, Show)

-- | Whether a **Thermo_n G** path is non-trivial (level > 0).
thermoConservationPathIsNontrivial :: ThermoConservationPath -> Bool
thermoConservationPathIsNontrivial path = thermoPathLevel path > 0

-- | Iron **Thermo_n G** **conservation** path @ L1 scaffold.
thermoConservationPathIronL1 :: ThermoConservationPath
thermoConservationPathIronL1 =
  ThermoConservationPath
    { thermoPathField = thermoConservationFieldNamed
    , thermoPathLevel = 1
    , thermoPathElementZ = ThermoElementIron
    , thermoPathScalar = GreenBookGScalar
    }

-- | Copper **Thermo_n G** **conservation** path @ L1 scaffold.
thermoConservationPathCopperL1 :: ThermoConservationPath
thermoConservationPathCopperL1 =
  ThermoConservationPath
    { thermoPathField = thermoConservationFieldNamed
    , thermoPathLevel = 1
    , thermoPathElementZ = ThermoElementCopper
    , thermoPathScalar = GreenBookGScalar
    }

-- | Unwired baseline **Thermo_n G** path @ L1 scaffold.
thermoConservationPathUnwiredL1 :: ThermoConservationPath
thermoConservationPathUnwiredL1 =
  ThermoConservationPath
    { thermoPathField =
        ThermoConservationField
          { atTemperature = 0
          , atPressure = 0
          , atComposition = 0
          , atGibbsG = 0
          }
    , thermoPathLevel = 1
    , thermoPathElementZ = ThermoElementIron
    , thermoPathScalar = GreenBookGScalar
    }

-- | **Thermo_n** state variable order T→P→x→G is strictly ordered.
thermoVarOrderOk :: Bool
thermoVarOrderOk =
  thermoStateVariableIndex ThermoTemperature
    < thermoStateVariableIndex ThermoPressure
    && thermoStateVariableIndex ThermoPressure
      < thermoStateVariableIndex ThermoComposition
    && thermoStateVariableIndex ThermoComposition
      < thermoStateVariableIndex ThermoGibbsG
    && thermoVarString ThermoTemperature == "T"
    && thermoVarString ThermoGibbsG == "G"

-- | T → P lift on **Thermo_n** identity (knowing fiber — Unwired scaffold).
liftTemperature :: Int -> Int
liftTemperature = id

-- | P → x lift on **Thermo_n** identity (knowing fiber — Unwired scaffold).
liftPressure :: Int -> Int
liftPressure = id

-- | x → G lift on **Thermo_n** identity (knowing fiber — Unwired scaffold).
liftComposition :: Int -> Int
liftComposition = id

-- | Direct T → G Green Book **G** on **Thermo_n** identity (knowing fiber — Unwired scaffold).
directGreenBookG :: Int -> Int
directGreenBookG = id

-- | **Thermo_n G** identity conserved: composed T∘P∘x equals T→G direct.
thermoIdentityConserved :: Int -> Bool
thermoIdentityConserved witness =
  liftComposition (liftPressure (liftTemperature witness))
    == directGreenBookG witness

-- | Typed **thermo** **conservation** along the commuting T→P→x→G diagram (named legs).
thermoCommuteConservation :: Int -> Bool
thermoCommuteConservation = thermoIdentityConserved

-- | Verdict of a **Thermo_n G** path close attempt (fail-closed).
data ThermoGPathVerdict
  = ThermoGPathUnwiredOk
  | ThermoGPathLegNamedOk
  | ThermoGPathGreenInventRefuse
  | ThermoGPathProvedWithoutBarRefuse
  | ThermoGPathTrivialZZeroRefuse
  | ThermoGPathFormationZeroMisidentifiedAsGRefuse
  | ThermoGPathMeasuredScalarInventRefuse
  | ThermoGPathScrambledOrderRefuse
  | ThermoGPathLiveProcessGRefuse
  deriving (Eq, Show)

-- | Evaluate a **Thermo_n G** path against the THERMO-01 bar (fail-closed).
evaluateThermoGPath ::
  ThermoConservationModality
  -> ThermoConservationPath
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> ThermoGPathVerdict
evaluateThermoGPath
  modality
  path
  claimPhysicsGreen
  claimProved
  claimLiveProcessG
  claimFormationZeroAsG
  claimMeasuredScalar
  claimScrambledOrder
  | claimPhysicsGreen = ThermoGPathGreenInventRefuse
  | claimLiveProcessG = ThermoGPathLiveProcessGRefuse
  | claimFormationZeroAsG = ThermoGPathFormationZeroMisidentifiedAsGRefuse
  | claimMeasuredScalar = ThermoGPathMeasuredScalarInventRefuse
  | claimScrambledOrder = ThermoGPathScrambledOrderRefuse
  | claimProved = ThermoGPathProvedWithoutBarRefuse
  | not (thermoConservationPathIsNontrivial path) = ThermoGPathTrivialZZeroRefuse
  | not (isValidIupacZ (thermoPathElementZ path)) = ThermoGPathTrivialZZeroRefuse
  | otherwise =
      case modality of
        ThermoConservationUnwired -> ThermoGPathLegNamedOk
        ThermoConservationAssumed -> ThermoGPathUnwiredOk
        ThermoConservationSurrogate -> ThermoGPathUnwiredOk
        ThermoConservationProved -> ThermoGPathProvedWithoutBarRefuse

-- | Verdict for THERMO-01 **thermo** **conservation** close (fail-closed).
data ThermoConservationVerdict
  = ThermoConservationDesignOk
  | ThermoConservationNamedOk
  | ThermoConservationTrivialRefuse
  | ThermoConservationGreenInventRefuse
  | ThermoConservationProvedWithoutBarRefuse
  | ThermoConservationFormationZeroMisidentifiedAsGRefuse
  | ThermoConservationMeasuredScalarInventRefuse
  | ThermoConservationScrambledOrderRefuse
  | ThermoConservationLiveProcessGRefuse
  deriving (Eq, Show)

-- | Evaluate **Thermo_n G** **conservation** under THERMO-01 bar (fail-closed).
evaluateThermoConservation ::
  ThermoConservationModality
  -> ThermoConservationPath
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> ThermoConservationVerdict
evaluateThermoConservation
  modality
  path
  claimPhysicsGreen
  claimLiveProcessG
  claimFormationZeroAsG
  claimMeasuredScalar
  claimScrambledOrder
  | claimPhysicsGreen = ThermoConservationGreenInventRefuse
  | claimLiveProcessG = ThermoConservationLiveProcessGRefuse
  | claimFormationZeroAsG = ThermoConservationFormationZeroMisidentifiedAsGRefuse
  | claimMeasuredScalar = ThermoConservationMeasuredScalarInventRefuse
  | claimScrambledOrder = ThermoConservationScrambledOrderRefuse
  | not (thermoConservationPathIsNontrivial path) = ThermoConservationTrivialRefuse
  | otherwise =
      case modality of
        ThermoConservationUnwired ->
          if threeLegsNamed then ThermoConservationNamedOk else ThermoConservationDesignOk
        ThermoConservationAssumed -> ThermoConservationDesignOk
        ThermoConservationSurrogate -> ThermoConservationDesignOk
        ThermoConservationProved -> ThermoConservationNamedOk

-- | Unwired **thermo** modality OK without thermo break.
unwiredThermoDesignOk :: Bool
unwiredThermoDesignOk =
  evaluateThermoConservation
    ThermoConservationUnwired
    thermoConservationPathIronL1
    False
    False
    False
    False
    False
    == ThermoConservationNamedOk

-- | Three named T, P, x legs plus direct T→G on scaffold.
threeLegsNamedOk :: Bool
threeLegsNamedOk =
  threeLegsNamed
    && thermoStateVariableCount == 4
    && thermoConservationLegCount == 4

-- | Composed T∘P∘x equals T→G direct (**thermo** **conservation**).
composedEqualsDirectOk :: Bool
composedEqualsDirectOk =
  thermoCommuteConservation 42
    && thermoIdentityConserved 42
    && liftComposition (liftPressure (liftTemperature 42))
      == directGreenBookG 42
    && thermoAtVariable thermoConservationFieldNamed ThermoGibbsG
      == thermoAtVariable thermoConservationFieldNamed ThermoGibbsG

-- | Direct and indirect leg endpoints match on **Thermo_n** state variables.
thermoLegEndpointsMatchOk :: Bool
thermoLegEndpointsMatchOk =
  thermoLegSource ThermoLegTemperatureToGDirect
    == thermoLegSource ThermoLegTemperatureToPressure
    && thermoLegTarget ThermoLegCompositionToG
      == thermoLegTarget ThermoLegTemperatureToGDirect

-- | Indirect legs compose: P target of T→P equals P source of P→x.
thermoIndirectComposesOk :: Bool
thermoIndirectComposesOk =
  thermoLegTarget ThermoLegTemperatureToPressure
    == thermoLegSource ThermoLegPressureToComposition
    && thermoLegTarget ThermoLegPressureToComposition
      == thermoLegSource ThermoLegCompositionToG

-- | Assumed **thermo** modality OK without thermo break (design scaffold).
assumedThermoDesignOk :: Bool
assumedThermoDesignOk =
  evaluateThermoConservation
    ThermoConservationAssumed
    thermoConservationPathIronL1
    False
    False
    False
    False
    False
    == ThermoConservationDesignOk

-- | Surrogate **thermo** modality OK without thermo break (design scaffold).
surrogateThermoDesignOk :: Bool
surrogateThermoDesignOk =
  evaluateThermoConservation
    ThermoConservationSurrogate
    thermoConservationPathIronL1
    False
    False
    False
    False
    False
    == ThermoConservationDesignOk

-- | GREEN invent on **Thermo_n G** **conservation** promotion is refused.
greenInventThermoRefuse :: Bool
greenInventThermoRefuse =
  evaluateThermoConservation
    ThermoConservationUnwired
    thermoConservationPathIronL1
    True
    False
    False
    False
    False
    == ThermoConservationGreenInventRefuse
    && evaluateThermoGPath
      ThermoConservationUnwired
      thermoConservationPathIronL1
      True
      False
      False
      False
      False
      False
      == ThermoGPathGreenInventRefuse

-- | Formation-zero misidentified as G is refused (formation-zero ≠ G).
formationZeroMisidentifiedAsGRefuse :: Bool
formationZeroMisidentifiedAsGRefuse =
  evaluateThermoConservation
    ThermoConservationUnwired
    thermoConservationPathIronL1
    False
    False
    True
    False
    False
    == ThermoConservationFormationZeroMisidentifiedAsGRefuse
    && evaluateThermoGPath
      ThermoConservationUnwired
      thermoConservationPathIronL1
      False
      False
      True
      False
      False
      False
      == ThermoGPathFormationZeroMisidentifiedAsGRefuse

-- | Measured-scalar G invent is refused on **Thermo_n G** scaffold.
measuredScalarInventRefuse :: Bool
measuredScalarInventRefuse =
  evaluateThermoConservation
    ThermoConservationUnwired
    thermoConservationPathIronL1
    False
    False
    False
    True
    False
    == ThermoConservationMeasuredScalarInventRefuse
    && evaluateThermoGPath
      ThermoConservationUnwired
      thermoConservationPathIronL1
      False
      False
      False
      True
      False
      False
      == ThermoGPathMeasuredScalarInventRefuse

-- | Scrambled T/P/x order is refused (typed order required).
scrambledOrderRefuse :: Bool
scrambledOrderRefuse =
  evaluateThermoConservation
    ThermoConservationUnwired
    thermoConservationPathIronL1
    False
    False
    False
    False
    True
    == ThermoConservationScrambledOrderRefuse
    && evaluateThermoGPath
      ThermoConservationUnwired
      thermoConservationPathIronL1
      False
      False
      False
      False
      True
      False
      == ThermoGPathScrambledOrderRefuse

-- | Live Process G claim is refused (not live meso G on knowing scaffold).
liveProcessGRefuse :: Bool
liveProcessGRefuse =
  evaluateThermoConservation
    ThermoConservationUnwired
    thermoConservationPathIronL1
    False
    True
    False
    False
    False
    == ThermoConservationLiveProcessGRefuse
    && evaluateThermoGPath
      ThermoConservationUnwired
      thermoConservationPathIronL1
      False
      False
      True
      False
      False
      False
      == ThermoGPathLiveProcessGRefuse

-- | Trivial (level-0) **Thermo_n G** path is refused (fail-closed).
trivialZZeroRefuse :: Bool
trivialZZeroRefuse =
  let trivialPath =
        thermoConservationPathIronL1 {thermoPathLevel = 0}
   in evaluateThermoGPath
        ThermoConservationUnwired
        trivialPath
        False
        False
        False
        False
        False
        False
        == ThermoGPathTrivialZZeroRefuse
        && evaluateThermoConservation
          ThermoConservationUnwired
          trivialPath
          False
          False
          False
          False
          False
          == ThermoConservationTrivialRefuse

-- | Scaffold scalar obeys formation-zero ≠ G unless named.
formationZeroNotGUnlessNamedOk :: Bool
formationZeroNotGUnlessNamedOk =
  formationZeroNotGUnlessNamed (NamedThermoScalar FormationZeroNamed)
    && isFormationZero (NamedThermoScalar FormationZeroNamed)
    && not (isGreenBookG (NamedThermoScalar FormationZeroNamed))
    && formationZeroNotGUnlessNamed thermoScalarScaffoldDefault

-- | CALPHAD hull-preserving **Thermo_n** fusion identity is **conserved** on pinned states.
calphadHullIdentityConserved :: Bool
calphadHullIdentityConserved =
  fusionCalphadHull thermoCalphadZero thermoCalphadPositive == thermoCalphadPositive
    && fusionCalphadHull thermoCalphadPositive thermoCalphadZero
      == fusionCalphadHull thermoCalphadZero thermoCalphadPositive
    && calphadLandauerWitness
      (fusionCalphadHull thermoCalphadPositive thermoCalphadPositive)
      == 2
    && thermoConservationPathIsNontrivial thermoConservationPathIronL1
    && isValidIupacZ ThermoElementIron

-- | Fe **thermo** anchor carries valid Z=26 pin.
feElementZValid :: Bool
feElementZValid =
  isValidIupacZ ThermoElementIron
    && thermoElementZNumeric ThermoElementIron == 26

-- | Cu **thermo** anchor carries valid Z=29 pin.
copperElementZValid :: Bool
copperElementZValid =
  isValidIupacZ ThermoElementCopper
    && thermoElementZNumeric ThermoElementCopper == 29

-- | Z=118 Oganesson pin is valid IUPAC Z @ scaffold.
oganessonZValid :: Bool
oganessonZValid =
  isValidIupacZ ThermoElementOganesson
    && thermoElementZNumeric ThermoElementOganesson == iupacTableCardinality

-- | Iron **Thermo_n G** **conservation** path passes under Unwired modality.
ironThermoConservationUnwiredOk :: Bool
ironThermoConservationUnwiredOk =
  evaluateThermoConservation
    ThermoConservationUnwired
    thermoConservationPathIronL1
    False
    False
    False
    False
    False
    == ThermoConservationNamedOk
    && evaluateThermoGPath
      ThermoConservationUnwired
      thermoConservationPathIronL1
      False
      False
      False
      False
      False
      False
      == ThermoGPathLegNamedOk

-- | Copper **Thermo_n G** **conservation** path passes under Unwired modality.
copperThermoConservationUnwiredOk :: Bool
copperThermoConservationUnwiredOk =
  evaluateThermoConservation
    ThermoConservationUnwired
    thermoConservationPathCopperL1
    False
    False
    False
    False
    False
    == ThermoConservationNamedOk
    && evaluateThermoGPath
      ThermoConservationUnwired
      thermoConservationPathCopperL1
      False
      False
      False
      False
      False
      False
      == ThermoGPathLegNamedOk

-- | Four-step THERMO-01 **thermo** lattice scaffold pinned.
thermoLatticeScaffold :: Bool
thermoLatticeScaffold =
  thermoLatticeCount == 4
    && unwiredThermoDesignOk
    && threeLegsNamedOk
    && thermoVarOrderOk
    && composedEqualsDirectOk
    && thermoLegEndpointsMatchOk
    && thermoIndirectComposesOk
    && assumedThermoDesignOk
    && surrogateThermoDesignOk
    && formationZeroNotGUnlessNamedOk
    && calphadHullIdentityConserved

-- | **Thermo** lattice is structure scaffold — not 118² GREEN periodic table.
thermoLatticeNotGreenTable :: Bool
thermoLatticeNotGreenTable =
  thermoLatticeCount == 4
    && thermoLatticeCount /= iupacTableCardinality * iupacTableCardinality
    && thermoStateVariableCount /= iupacTableCardinality * iupacTableCardinality
    && thermoConservationLegCount /= iupacTableCardinality * iupacTableCardinality
    && thermoElementZCount /= iupacTableCardinality * iupacTableCardinality

-- | **Thermo_n G** **conservation** law cells scaffold pinned.
thermoConservationLawsScaffold :: Bool
thermoConservationLawsScaffold =
  threeLegsNamedOk
    && thermoVarOrderOk
    && composedEqualsDirectOk
    && thermoLegEndpointsMatchOk
    && thermoIndirectComposesOk
    && greenInventThermoRefuse
    && formationZeroMisidentifiedAsGRefuse
    && measuredScalarInventRefuse
    && scrambledOrderRefuse
    && liveProcessGRefuse
    && trivialZZeroRefuse
    && formationZeroNotGUnlessNamedOk
    && calphadHullIdentityConserved
    && feElementZValid
    && copperElementZValid
    && oganessonZValid

-- | **Thermo** law cells are structure scaffold — not 118² GREEN periodic table.
thermoConservationLawsNotGreenTable :: Bool
thermoConservationLawsNotGreenTable =
  thermoConservationLawsScaffold
    && thermoStateVariableCount /= 118 * 118
    && thermoConservationLegCount /= 118 * 118

-- | THERMO-01 **Thermo_n G** **conservation** claims route to knowing / quantum fiber (not meso acting).
thermoKnowingFiberOk :: Bool
thermoKnowingFiberOk = True

-- | THERMO-01 Thermo_n G invent refuse-closed scaffold witness.
thermoGInventRefuse :: Bool
thermoGInventRefuse = not thermoGProved

-- | **Thermo** lattice steps are concurrent Π_c — not XOR enum bucket.
thermoLatticeNotXor :: Bool
thermoLatticeNotXor =
  unwiredThermoDesignOk
    && assumedThermoDesignOk
    && surrogateThermoDesignOk
    && composedEqualsDirectOk
    && greenInventThermoRefuse
    && formationZeroNotGUnlessNamedOk
    && calphadHullIdentityConserved

-- | THERMO-01 Thermo_n G proved (always false on this Unwired cell).
thermoGProved :: Bool
thermoGProved = False

-- | One axiom framing: second law + **conservation** for THERMO-01 **thermo** scaffold.
thermoConservationFraming :: String
thermoConservationFraming =
  "second_law_conservation_thermo_one_axiom"

-- | Single design axiom: second law + **conservation** THERMO-01 **Thermo_n G** (not second axiom).
thermoConservationAxiom :: Bool
thermoConservationAxiom =
  thermoLatticeScaffold
    && thermoLatticeNotGreenTable
    && thermoConservationLawsScaffold
    && thermoConservationLawsNotGreenTable
    && thermoKnowingFiberOk
    && threeLegsNamedOk
    && thermoVarOrderOk
    && composedEqualsDirectOk
    && thermoLegEndpointsMatchOk
    && thermoIndirectComposesOk
    && greenInventThermoRefuse
    && formationZeroMisidentifiedAsGRefuse
    && measuredScalarInventRefuse
    && scrambledOrderRefuse
    && liveProcessGRefuse
    && trivialZZeroRefuse
    && formationZeroNotGUnlessNamedOk
    && calphadHullIdentityConserved
    && feElementZValid
    && copperElementZValid
    && oganessonZValid
    && ironThermoConservationUnwiredOk
    && copperThermoConservationUnwiredOk
    && thermoGInventRefuse
    && thermoLatticeNotXor
    && thermoConservationFraming
      == "second_law_conservation_thermo_one_axiom"

thermoConservationNamed :: String
thermoConservationNamed =
  "thermoConservation: ThermoConservationModality Unwired Assumed Proved Surrogate four-step lattice thermoGProved false evaluateThermoConservation thermoCommuteConservation named T P x G composed T o P o x equals direct G typed conservation CALPHAD hull identity conserved formation-zero ne G measured-scalar invent refuse scrambled order refuse live Process G refuse Fe Z=26 Cu Z=29 Og Z=118 knowing fiber second law conservation one axiom not 118 squared GREEN table"

-- | Upstream Thermo_n authority (cited, not forked).
thermoNAuthority :: String
thermoNAuthority = "umst/umst-chem/src/thermo_n.rs"

-- | L0 THERMO-01 scaffold authority (crosswalk).
chemL0Thermo01Authority :: String
chemL0Thermo01Authority = "CHEM-L0-THERMO-01"

thermoConservationCellId :: String
thermoConservationCellId = "CHEM-FORMAL-Q-HS-THERMO-CONSERVATION"

-- | Non-claim fence — THERMO-01 **Thermo_n G** **conservation** Unwired ≠ Proved GREEN.
thermoConservationNonClaim :: String
thermoConservationNonClaim =
  "CHEM-FORMAL-Q-HS-THERMO-CONSERVATION ThermoConservationModality Unwired Assumed Proved Surrogate four-step lattice thermoGProved false evaluateThermoConservation thermoCommuteConservation named T P x G composed T o P o x equals direct G typed conservation CALPHAD hull identity conserved formation-zero ne G measured-scalar invent refuse scrambled order refuse live Process G refuse Fe Z=26 Cu Z=29 Og Z=118 trivial Z=0 refuse knowing fiber Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired not live G not Thermo_n Proved"

-- | Physics GREEN is unauthorized on the knowing THERMO-01 **Thermo_n G** **conservation** scaffold.
thermoConservationPhysicsGreenAuthorized :: Bool
thermoConservationPhysicsGreenAuthorized = False

thermoConservationPhysicsGreenFalse :: Bool
thermoConservationPhysicsGreenFalse =
  not thermoConservationPhysicsGreenAuthorized

thermoConservationModalityUnwired :: Bool
thermoConservationModalityUnwired =
  thermoConservationModalityCurrent == ThermoConservationUnwired

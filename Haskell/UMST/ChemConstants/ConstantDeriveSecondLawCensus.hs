-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ConstantDeriveSecondLawCensus
Description : Constant-derive second-law census conservation on the knowing fiber
Copyright   : (c) UMST Project, 2026

Constant-derive second-law census conservation: constitutive engines **consult** the existing
ExactSI / occupancy / derived-morphism sheaf; they do **not** mint **k**, **R**, or **ε₀**.
Fine-structure **α** stays **MeasuredCited** — not Landauer-faked as ExactSI or FormalLift.

* **One** design axiom (@constantDeriveSecondLawCensusAxiom@): second law + conservation.
* Sorting cites upstream sheaf pins — **not** a 26th axiom.
* @physics_green@ stays false.

Haskell mirror of @umst-chem@ @constant_derive_second_law_census.rs@ on the quantum /
knowing fiber. Cell: @CHEM-FORMAL-Q-HS-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.ConstantDeriveSecondLawCensus
  ( ConstantDeriveSecondLawCensusModality (..)
  , constantDeriveSecondLawCensusModalityCurrent
  , SheafConsultLayer (..)
  , sheafConsultLayerTag
  , sheafConsultLayerCount
  , EngineCensusRowTag (..)
  , engineCensusRowCount
  , rowMayMintSi
  , rowSheafLayer
  , rowCensusConservationHolds
  , allEngineCensusRowsConsultSheaf
  , enginesMayMintForbiddenSi
  , forbiddenSiMintsPinned
  , enginesUseExistingSheafCensus
  , fineStructureAlphaPinKind
  , landauerFakeAlphaMinted
  , fineStructureAlphaIsMeasuredCitedNotLandauerFake
  , landauerBridgeCoversKcNotAlpha
  , landauerBridgeScopedKcNotAlpha
  , exactSiKCitedNotMinted
  , engineRefusesNewSiCitedNotForked
  , constantDerivePreferenceCited
  , siExactDefiningConstantsCited
  , qlatticeTypeCited
  , constantDeriveSecondLawCensusHonestConjunct
  , constantDeriveSecondLawCensusScaffold
  , ConstantDeriveSecondLawCensusProbe (..)
  , constantDeriveSecondLawCensusProbe
  , constantDeriveSecondLawCensusHonest
  , constantDeriveSecondLawCensusRowProved
  , constantDeriveSecondLawCensusFraming
  , constantDeriveSecondLawCensusAxiom
  , constantDeriveSecondLawCensusNamed
  , constantDeriveSecondLawCensusMarker
  , constantDeriveSecondLawCensusSurface
  , constantDeriveSecondLawCensusAuthority
  , engineRefusesNewSiAuthority
  , constantDerivePreferenceAuthority
  , siExactDefiningConstantsAuthority
  , gasConstantDerivedMorphismAuthority
  , vacuumPermittivitySiDerivedAuthority
  , qlatticeAuthority
  , secondLawConservationAxiom
  , censusNotSiMintOrLandauerFakeAlphaOr26thAxiom
  , constantDeriveSecondLawCensusCellId
  , constantDeriveSecondLawCensusIntCellId
  , constantDeriveSecondLawCensusNonClaim
  , constantDeriveSecondLawCensusPhysicsGreenAuthorized
  , constantDeriveSecondLawCensusPhysicsGreenFalse
  , constantDeriveSecondLawCensusModalityUnwired
  , productionWired
  , wave100LibRsWired
  , wave100EosRsWired
  , productNotXor
  ) where

import UMST.ChemConstants.EngineRefusesNewSi
  ( engineMayMintSi
  , engineUsesExistingSheaf
  , forbiddenSiMintCount
  , forbiddenSiMints
  )
import UMST.ChemConstants.FineStructureAlphaMeasuredRemainder
  ( alphaDerivedFromLandauerKtLn2
  , codataMeasuredFineStructureAlpha
  , fineStructureAlphaPinKindTag
  , FineStructureAlphaPinKind (MeasuredCitedPin)
  , landauerRefKJoulesPerKelvin
  , soleAxiomCount
  )

-- | Design modality for constant-derive second-law census claims (TYPE-03 preview).
data ConstantDeriveSecondLawCensusModality
  = ConstantDeriveSecondLawCensusUnwired
  | ConstantDeriveSecondLawCensusAssumed
  | ConstantDeriveSecondLawCensusProved
  | ConstantDeriveSecondLawCensusSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
constantDeriveSecondLawCensusModalityCurrent :: ConstantDeriveSecondLawCensusModality
constantDeriveSecondLawCensusModalityCurrent = ConstantDeriveSecondLawCensusUnwired

-- | Sheaf layer consulted by constitutive engines.
data SheafConsultLayer
  = ExactSiLayer
  | OccupancyLayer
  | DerivedMorphismLayer
  deriving (Eq, Show)

sheafConsultLayerTag :: SheafConsultLayer -> String
sheafConsultLayerTag ExactSiLayer = "ExactSI"
sheafConsultLayerTag OccupancyLayer = "occupancy"
sheafConsultLayerTag DerivedMorphismLayer = "derived_morphism"

sheafConsultLayerCount :: Int
sheafConsultLayerCount = 3

-- | Engine census row tags — consult sheaf, do not mint k/R/ε₀.
data EngineCensusRowTag
  = SiExactDefiningConstantsRow
  | QlatticeRow
  | GasConstantDerivedMorphismRow
  | VacuumPermittivityDerivedRow
  | EngineRefusesNewSiRow
  deriving (Eq, Show)

engineCensusRowCount :: Int
engineCensusRowCount = 5

rowMayMintSi :: EngineCensusRowTag -> Bool
rowMayMintSi _ = False

rowSheafLayer :: EngineCensusRowTag -> SheafConsultLayer
rowSheafLayer SiExactDefiningConstantsRow = ExactSiLayer
rowSheafLayer QlatticeRow = OccupancyLayer
rowSheafLayer GasConstantDerivedMorphismRow = DerivedMorphismLayer
rowSheafLayer VacuumPermittivityDerivedRow = DerivedMorphismLayer
rowSheafLayer EngineRefusesNewSiRow = ExactSiLayer

rowCensusConservationHolds :: EngineCensusRowTag -> Bool
rowCensusConservationHolds row = not (rowMayMintSi row)

allEngineCensusRows :: [EngineCensusRowTag]
allEngineCensusRows =
  [ SiExactDefiningConstantsRow
  , QlatticeRow
  , GasConstantDerivedMorphismRow
  , VacuumPermittivityDerivedRow
  , EngineRefusesNewSiRow
  ]

allEngineCensusRowsConsultSheaf :: Bool
allEngineCensusRowsConsultSheaf =
  length allEngineCensusRows == engineCensusRowCount
    && all rowCensusConservationHolds allEngineCensusRows

enginesMayMintForbiddenSi :: Bool
enginesMayMintForbiddenSi = engineMayMintSi

forbiddenSiMintsPinned :: Bool
forbiddenSiMintsPinned =
  forbiddenSiMintCount == 3
    && "k" `elem` forbiddenSiMints
    && "R" `elem` forbiddenSiMints
    && "epsilon_0" `elem` forbiddenSiMints

enginesUseExistingSheafCensus :: Bool
enginesUseExistingSheafCensus =
  engineUsesExistingSheaf && not engineMayMintSi

fineStructureAlphaPinKind :: String
fineStructureAlphaPinKind = fineStructureAlphaPinKindTag MeasuredCitedPin

landauerFakeAlphaMinted :: Bool
landauerFakeAlphaMinted = False

fineStructureAlphaIsMeasuredCitedNotLandauerFake :: Bool
fineStructureAlphaIsMeasuredCitedNotLandauerFake =
  fineStructureAlphaPinKind == "MeasuredCited"
    && not landauerFakeAlphaMinted
    && not alphaDerivedFromLandauerKtLn2

landauerBridgeCoversKcNotAlpha :: String
landauerBridgeCoversKcNotAlpha =
  "LandauerEinsteinBridge.lean FormalLift k c — alpha remains MeasuredCited not Landauer-faked"

landauerBridgeScopedKcNotAlpha :: Bool
landauerBridgeScopedKcNotAlpha =
  "LandauerEinsteinBridge" `elem` (words landauerBridgeCoversKcNotAlpha)
    && "not" `elem` (words landauerBridgeCoversKcNotAlpha)
    && fineStructureAlphaIsMeasuredCitedNotLandauerFake

exactSiKCitedNotMinted :: Bool
exactSiKCitedNotMinted =
  landauerRefKJoulesPerKelvin > 0
    && "si_exact_defining_constants" `elem` (words siExactDefiningConstantsAuthority)

engineRefusesNewSiCitedNotForked :: Bool
engineRefusesNewSiCitedNotForked =
  "engine_refuses_new_si" `elem` (words engineRefusesNewSiAuthority)
    && "engine_refuses_new_si" `elem` (words constantDeriveSecondLawCensusNonClaim)
    && "CHEM-INT-CROSS-ENGINE-REFUSES-NEW-SI-CONSERVATION"
      `elem` (words constantDeriveSecondLawCensusNonClaim)

constantDerivePreferenceCited :: Bool
constantDerivePreferenceCited =
  "constant_derive_preference" `elem` (words constantDerivePreferenceAuthority)
    && "constant_derive_preference" `elem` (words constantDeriveSecondLawCensusNonClaim)

siExactDefiningConstantsCited :: Bool
siExactDefiningConstantsCited =
  "si_exact_defining_constants" `elem` (words siExactDefiningConstantsAuthority)

qlatticeTypeCited :: Bool
qlatticeTypeCited =
  qlatticeAuthority == "umst/umst-chem/src/qlattice.rs"
    && "qlattice" `elem` (words constantDeriveSecondLawCensusNonClaim)

constantDeriveSecondLawCensusHonestConjunct :: Bool
constantDeriveSecondLawCensusHonestConjunct =
  not enginesMayMintForbiddenSi
    && allEngineCensusRowsConsultSheaf
    && forbiddenSiMintsPinned
    && enginesUseExistingSheafCensus
    && fineStructureAlphaIsMeasuredCitedNotLandauerFake
    && landauerBridgeScopedKcNotAlpha
    && exactSiKCitedNotMinted
    && engineRefusesNewSiCitedNotForked
    && constantDerivePreferenceCited
    && siExactDefiningConstantsCited
    && qlatticeTypeCited
    && not landauerFakeAlphaMinted
    && soleAxiomCount == 1

constantDeriveSecondLawCensusScaffold :: Bool
constantDeriveSecondLawCensusScaffold =
  constantDeriveSecondLawCensusHonestConjunct
    && engineCensusRowCount == 5
    && sheafConsultLayerCount == 3
    && codataMeasuredFineStructureAlpha > 0
    && not productionWired
    && not wave100LibRsWired
    && not wave100EosRsWired
    && productNotXor

productionWired :: Bool
productionWired = False

wave100LibRsWired :: Bool
wave100LibRsWired = False

wave100EosRsWired :: Bool
wave100EosRsWired = False

productNotXor :: Bool
productNotXor = True

data ConstantDeriveSecondLawCensusProbe = ConstantDeriveSecondLawCensusProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  , allCensusRowsConsult :: Bool
  , forbiddenMintsPinned :: Bool
  , enginesUseSheaf :: Bool
  , alphaNotLandauerFake :: Bool
  , landauerBridgeKcNotAlpha :: Bool
  , exactSiKCited :: Bool
  , qlatticeCited :: Bool
  , engineRefusesCited :: Bool
  , derivePreferenceCited :: Bool
  }
  deriving (Eq, Show)

constantDeriveSecondLawCensusProbe :: ConstantDeriveSecondLawCensusProbe
constantDeriveSecondLawCensusProbe =
  ConstantDeriveSecondLawCensusProbe
    { cellIdNamed =
        constantDeriveSecondLawCensusCellId
          == "CHEM-FORMAL-Q-HS-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION"
    , unwired =
        constantDeriveSecondLawCensusModalityCurrent
          == ConstantDeriveSecondLawCensusUnwired
    , physicsGreenRefused =
        not constantDeriveSecondLawCensusPhysicsGreenAuthorized
    , soleAxiom = soleAxiomCount == 1
    , notProved = not constantDeriveSecondLawCensusRowProved
    , allCensusRowsConsult = allEngineCensusRowsConsultSheaf
    , forbiddenMintsPinned = forbiddenSiMintsPinned
    , enginesUseSheaf = enginesUseExistingSheafCensus
    , alphaNotLandauerFake = fineStructureAlphaIsMeasuredCitedNotLandauerFake
    , landauerBridgeKcNotAlpha = landauerBridgeScopedKcNotAlpha
    , exactSiKCited = exactSiKCitedNotMinted
    , qlatticeCited = qlatticeTypeCited
    , engineRefusesCited = engineRefusesNewSiCitedNotForked
    , derivePreferenceCited = constantDerivePreferenceCited
    }

constantDeriveSecondLawCensusHonest :: Bool
constantDeriveSecondLawCensusHonest =
  let p = constantDeriveSecondLawCensusProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && allCensusRowsConsult p
        && forbiddenMintsPinned p
        && enginesUseSheaf p
        && alphaNotLandauerFake p
        && landauerBridgeKcNotAlpha p
        && exactSiKCited p
        && qlatticeCited p
        && engineRefusesCited p
        && derivePreferenceCited p
        && constantDeriveSecondLawCensusScaffold

constantDeriveSecondLawCensusRowProved :: Bool
constantDeriveSecondLawCensusRowProved = False

constantDeriveSecondLawCensusFraming :: String
constantDeriveSecondLawCensusFraming =
  "second_law_conservation_constant_derive_second_law_census_one_axiom"

constantDeriveSecondLawCensusAxiom :: Bool
constantDeriveSecondLawCensusAxiom =
  constantDeriveSecondLawCensusScaffold
    && constantDeriveSecondLawCensusHonestConjunct
    && constantDeriveSecondLawCensusHonest
    && not constantDeriveSecondLawCensusRowProved
    && not productionWired
    && not enginesMayMintForbiddenSi
    && constantDeriveSecondLawCensusFraming
      == "second_law_conservation_constant_derive_second_law_census_one_axiom"

constantDeriveSecondLawCensusNamed :: String
constantDeriveSecondLawCensusNamed =
  "constantDeriveSecondLawCensus: engines consult ExactSI occupancy derived-morphism sheaf do not mint k R epsilon_0 alpha MeasuredCited not Landauer-faked cite engine_refuses_new_si constant_derive_preference si_exact_defining_constants gas_constant_is_derived_morphism vacuum_permittivity_si_derived qlattice not fork sole axiom second law conservation not 26th axiom"

constantDeriveSecondLawCensusMarker :: String
constantDeriveSecondLawCensusMarker =
  "chem_int_cross_constant_derive_second_law_census_v1"

constantDeriveSecondLawCensusSurface :: String
constantDeriveSecondLawCensusSurface = "constant_derive_second_law_census_surface"

constantDeriveSecondLawCensusAuthority :: String
constantDeriveSecondLawCensusAuthority =
  "umst/umst-chem/src/x_rows/constant_derive_second_law_census.rs"

engineRefusesNewSiAuthority :: String
engineRefusesNewSiAuthority =
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs"

constantDerivePreferenceAuthority :: String
constantDerivePreferenceAuthority =
  "umst/umst-chem/src/constant_derive_preference.rs"

siExactDefiningConstantsAuthority :: String
siExactDefiningConstantsAuthority =
  "umst/umst-chem/src/si_exact_defining_constants.rs"

gasConstantDerivedMorphismAuthority :: String
gasConstantDerivedMorphismAuthority =
  "umst/umst-chem/src/gas_constant_is_derived_morphism.rs"

vacuumPermittivitySiDerivedAuthority :: String
vacuumPermittivitySiDerivedAuthority =
  "umst/umst-chem/src/vacuum_permittivity_si_derived.rs"

qlatticeAuthority :: String
qlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

secondLawConservationAxiom :: String
secondLawConservationAxiom =
  "second law conservation — engines consult sheaf; alpha MeasuredCited not Landauer-faked; sole axiom"

censusNotSiMintOrLandauerFakeAlphaOr26thAxiom :: String
censusNotSiMintOrLandauerFakeAlphaOr26thAxiom =
  "constant derive census consults ExactSI occupancy derived-morphism sheaf — not mint k R epsilon_0 not Landauer-fake alpha not 26th axiom"

constantDeriveSecondLawCensusCellId :: String
constantDeriveSecondLawCensusCellId =
  "CHEM-FORMAL-Q-HS-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION"

constantDeriveSecondLawCensusIntCellId :: String
constantDeriveSecondLawCensusIntCellId =
  "CHEM-INT-CROSS-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION"

constantDeriveSecondLawCensusNonClaim :: String
constantDeriveSecondLawCensusNonClaim =
  "CHEM-FORMAL-Q-HS-CONSTANT-DERIVE-SECOND-LAW-CENSUS-CONSERVATION Unwired — engines consult ExactSI occupancy derived-morphism sheaf; do not mint k R epsilon_0; alpha MeasuredCited not Landauer-faked; cite engine_refuses_new_si constant_derive_preference si_exact_defining_constants gas_constant_is_derived_morphism vacuum_permittivity_si_derived qlattice not fork; second law conservation sole axiom not 26th axiom; not physics GREEN; not production_wired"

constantDeriveSecondLawCensusPhysicsGreenAuthorized :: Bool
constantDeriveSecondLawCensusPhysicsGreenAuthorized = False

constantDeriveSecondLawCensusPhysicsGreenFalse :: Bool
constantDeriveSecondLawCensusPhysicsGreenFalse =
  not constantDeriveSecondLawCensusPhysicsGreenAuthorized

constantDeriveSecondLawCensusModalityUnwired :: Bool
constantDeriveSecondLawCensusModalityUnwired =
  constantDeriveSecondLawCensusModalityCurrent == ConstantDeriveSecondLawCensusUnwired

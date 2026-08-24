-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.EngineRefusesNewSi
Description : Engine refuses new SI conservation on the constitutive matter fiber
Copyright   : (c) UMST Project, 2026

Engine refuses new SI conservation: constitutive engines sort using the existing
SI/occupancy/derived-morphism sheaf; they do not mint k, R, or ε₀. Consult
ChemistryService; no second periodic table. Compose laws are structure witnesses
only (@composeLawsProved@ = False).

* @engineMayMintSi@ — engines may not mint new SI defining/derived constants.
* @forbiddenSiMints@ — k, R, ε₀ refused as engine mints.
* @engineUsesExistingSheaf@ — sort consults existing SI sheaf only.
* **One** design axiom (@engineRefusesNewSiAxiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of engine refuses new SI conservation on the constitutive matter fiber.
Cell: @CHEM-FORMAL-Q-HS-ENGINE-REFUSES-NEW-SI-CONSERVATION@.
WAVE100: not wired in cabal. Remainder deferred composition, not impossibility.
-}
module UMST.ChemConstants.EngineRefusesNewSi
  ( EngineRefusesNewSiModality (..)
  , engineRefusesNewSiModalityCurrent
  , ForbiddenSiMintTag (..)
  , forbiddenSiMints
  , forbiddenSiMintCount
  , engineMayMintSi
  , engineUsesExistingSheaf
  , engineSortsSiSheaf
  , sortSiSheafWitness
  , mintSiRefused
  , engineOwnsPeriodicTable
  , sheafSortScaffold
  , engineRefusesNewSiHonestConjunct
  , EngineRefusesNewSiProbe (..)
  , engineRefusesNewSiProbe
  , engineRefusesNewSiHonest
  , composeLawsProved
  , engineRefusesNewSiFraming
  , engineRefusesNewSiAxiom
  , engineRefusesNewSiNamed
  , engineRefusesNewSiAuthority
  , siSheafAuthority
  , chemistryServiceAuthority
  , engineRefusesNewSiCellId
  , engineRefusesNewSiNonClaim
  , engineRefusesNewSiPhysicsGreenAuthorized
  , engineRefusesNewSiPhysicsGreenFalse
  , engineRefusesNewSiModalityUnwired
  ) where

-- | Design modality for engine refuses new SI claims (TYPE-03 preview).
data EngineRefusesNewSiModality
  = EngineRefusesNewSiUnwired
  | EngineRefusesNewSiAssumed
  | EngineRefusesNewSiProved
  | EngineRefusesNewSiSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
engineRefusesNewSiModalityCurrent :: EngineRefusesNewSiModality
engineRefusesNewSiModalityCurrent = EngineRefusesNewSiUnwired

-- | Forbidden SI mint tags — engines do not mint k, R, or ε₀.
data ForbiddenSiMintTag
  = BoltzmannK
  | GasConstantR
  | VacuumPermittivityE0
  deriving (Eq, Show)

-- | Forbidden SI mint names (stable order — consult sheaf, do not mint).
forbiddenSiMints :: [String]
forbiddenSiMints = ["k", "R", "epsilon_0"]

forbiddenSiMintCount :: Int
forbiddenSiMintCount = length forbiddenSiMints

-- | Whether engines may mint a new SI defining/derived constant (always false).
engineMayMintSi :: Bool
engineMayMintSi = False

-- | Engines sort using existing SI/occupancy/derived-morphism sheaf only.
engineUsesExistingSheaf :: Bool
engineUsesExistingSheaf =
  not engineMayMintSi && forbiddenSiMintCount == 3

-- | Engines sort SI sheaf — additive consult, not mint.
engineSortsSiSheaf :: Bool
engineSortsSiSheaf = engineUsesExistingSheaf

-- | Sample sheaf-sort witness — existing constants consulted, none minted.
sortSiSheafWitness :: Int
sortSiSheafWitness =
  sum (map length forbiddenSiMints) - forbiddenSiMintCount

-- | Mint refusal — any forbidden tag refused when engine may not mint.
mintSiRefused :: Bool
mintSiRefused =
  not engineMayMintSi
    && forbiddenSiMintCount == 3
    && all (`elem` forbiddenSiMints) ["k", "R", "epsilon_0"]

-- | Whether engines own a second periodic table.
engineOwnsPeriodicTable :: Bool
engineOwnsPeriodicTable = False

-- | Sheaf-sort scaffold: consult existing SI sheaf, refuse mint.
sheafSortScaffold :: Bool
sheafSortScaffold =
  engineSortsSiSheaf
    && mintSiRefused
    && not engineOwnsPeriodicTable
    && sortSiSheafWitness >= 0
    && forbiddenSiMintCount == 3

-- | Honest conjunct — engines sort sheaf, refuse new SI mint.
engineRefusesNewSiHonestConjunct :: Bool
engineRefusesNewSiHonestConjunct =
  sheafSortScaffold
    && engineUsesExistingSheaf
    && not engineMayMintSi
    && length forbiddenSiMints == 3

-- | Probe bundle for honest posture witnesses.
data EngineRefusesNewSiProbe = EngineRefusesNewSiProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  }
  deriving (Eq, Show)

-- | Honest probe — modality Unwired, physics GREEN refused.
engineRefusesNewSiProbe :: EngineRefusesNewSiProbe
engineRefusesNewSiProbe =
  EngineRefusesNewSiProbe
    { cellIdNamed =
        engineRefusesNewSiCellId
          == "CHEM-FORMAL-Q-HS-ENGINE-REFUSES-NEW-SI-CONSERVATION"
    , unwired =
        engineRefusesNewSiModalityCurrent == EngineRefusesNewSiUnwired
    , physicsGreenRefused = not engineRefusesNewSiPhysicsGreenAuthorized
    , soleAxiom = True
    , notProved = not composeLawsProved
    }

-- | Honest conjunct on probe bundle.
engineRefusesNewSiHonest :: Bool
engineRefusesNewSiHonest =
  let p = engineRefusesNewSiProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && engineRefusesNewSiHonestConjunct

-- | Compose laws proved (always false on this Unwired cell).
composeLawsProved :: Bool
composeLawsProved = False

-- | One axiom framing: second law + conservation for engine SI refusal scaffold.
engineRefusesNewSiFraming :: String
engineRefusesNewSiFraming =
  "second_law_conservation_engine_refuses_new_si_one_axiom"

-- | Single design axiom: second law + conservation engine refuses new SI.
engineRefusesNewSiAxiom :: Bool
engineRefusesNewSiAxiom =
  sheafSortScaffold
    && engineRefusesNewSiHonestConjunct
    && engineRefusesNewSiHonest
    && mintSiRefused
    && not composeLawsProved
    && not engineOwnsPeriodicTable
    && engineRefusesNewSiFraming
      == "second_law_conservation_engine_refuses_new_si_one_axiom"

engineRefusesNewSiNamed :: String
engineRefusesNewSiNamed =
  "engineRefusesNewSi: constitutive engines sort existing SI occupancy derived morphism sheaf do not mint k R epsilon_0 composeLawsProved false second law conservation one axiom"

-- | Upstream engine refuses new SI authority (cited, not forked).
engineRefusesNewSiAuthority :: String
engineRefusesNewSiAuthority =
  "umst/umst-chem/src/x_rows/engine_refuses_new_si.rs"

-- | SI/occupancy/derived-morphism sheaf consult authority.
siSheafAuthority :: String
siSheafAuthority = "umst/umst-chem/src/si_sheaf.rs"

-- | ChemistryService consult authority — no second periodic table.
chemistryServiceAuthority :: String
chemistryServiceAuthority = "umst/umst-chem/src/chemistry_service.rs"

engineRefusesNewSiCellId :: String
engineRefusesNewSiCellId =
  "CHEM-FORMAL-Q-HS-ENGINE-REFUSES-NEW-SI-CONSERVATION"

-- | Non-claim fence — engine SI refusal Unwired ≠ Proved GREEN.
engineRefusesNewSiNonClaim :: String
engineRefusesNewSiNonClaim =
  "CHEM-FORMAL-Q-HS-ENGINE-REFUSES-NEW-SI-CONSERVATION engine sort existing SI sheaf do not mint k R epsilon_0 consult ChemistryService no second periodic table composeLawsProved false Unwired one axiom second law conservation not GREEN DFT not physics GREEN not production_wired WAVE100 deferred composition not impossibility"

-- | Physics GREEN is unauthorized on the engine refuses new SI scaffold.
engineRefusesNewSiPhysicsGreenAuthorized :: Bool
engineRefusesNewSiPhysicsGreenAuthorized = False

engineRefusesNewSiPhysicsGreenFalse :: Bool
engineRefusesNewSiPhysicsGreenFalse =
  not engineRefusesNewSiPhysicsGreenAuthorized

engineRefusesNewSiModalityUnwired :: Bool
engineRefusesNewSiModalityUnwired =
  engineRefusesNewSiModalityCurrent == EngineRefusesNewSiUnwired

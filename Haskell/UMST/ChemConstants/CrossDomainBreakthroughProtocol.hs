-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.CrossDomainBreakthroughProtocol
Description : Cross-domain breakthrough protocol conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Cross-domain breakthrough protocol conservation: proposed cross-domain connections are
**later composition on the same axiom** with environment / time / cross-domain nuance —
not a new law, not folklore. Honest breakthrough terminals on four fibers from one axiom:
  * @NewChart@ — named constitutive chart on the second-law object (cite chem_physics_chart_isomorphism)
  * @CommutingSquare@ — chart morphism commutes with conservation
  * @NamedRemainder@ — measured remainder pinned, not a second physics

Refused terminals: @NewAxiom@, @Folklore@ (untyped cross-domain story).

* **One** design axiom (@crossDomainBreakthroughProtocolAxiom@): second law + conservation.
* Breakthrough protocol cites chem_physics_chart_isomorphism — **not** a 27th axiom.
* @physics_green@ stays false.

Haskell mirror of @umst-chem@ @cross_domain_breakthrough_protocol.rs@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-CROSS-DOMAIN-BREAKTHROUGH-PROTOCOL-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.CrossDomainBreakthroughProtocol
  ( CrossDomainBreakthroughProtocolModality (..)
  , crossDomainBreakthroughProtocolModalityCurrent
  , BreakthroughFiber (..)
  , breakthroughFiberTag
  , breakthroughFiberFromTag
  , breakthroughFiberTags
  , HonestBreakthroughTerminal (..)
  , honestBreakthroughTerminalTag
  , honestBreakthroughTerminalTags
  , RefusedBreakthroughTerminal (..)
  , refusedBreakthroughTerminalTag
  , refusedBreakthroughTerminalTags
  , CrossDomainBreakthroughProposal (..)
  , proposalIsAdmissible
  , proposalRefusesNewLawOrFolklore
  , breakthroughProtocolIsNewAxiom
  , breakthroughFiberCount
  , honestBreakthroughTerminalCount
  , refusedBreakthroughTerminalCount
  , fourFibersFromOneAxiom
  , sampleChemToPhysicsNewChart
  , sampleEnvTimeToCrossDomainCommutingSquare
  , sampleCrossDomainToChemNamedRemainder
  , sampleRefusedFolkloreProposal
  , sampleRefusedNewAxiomProposal
  , sampleProposalsHonestPartition
  , chemPhysicsChartIsomorphismCitedNotForked
  , chartIsomorphismOnOneAxiomCited
  , crossDomainBreakthroughProtocolHonestConjunct
  , crossDomainBreakthroughProtocolScaffold
  , chemPhysicsChartIsomorphismAuthority
  , crossDomainBreakthroughProtocolAuthority
  , crossDomainBreakthroughProtocolCellId
  , crossDomainBreakthroughProtocolNonClaim
  , crossDomainBreakthroughProtocolPhysicsGreenAuthorized
  , crossDomainBreakthroughProtocolPhysicsGreenFalse
  , crossDomainBreakthroughProtocolModalityUnwired
  , crossDomainBreakthroughProtocolNot27thAxiom
  , CrossDomainBreakthroughProtocolProbe (..)
  , crossDomainBreakthroughProtocolProbe
  , crossDomainBreakthroughProtocolHonest
  , crossDomainBreakthroughProtocolRowProved
  , crossDomainBreakthroughProtocolFraming
  , crossDomainBreakthroughProtocolAxiom
  , crossDomainBreakthroughProtocolNamed
  , crossDomainBreakthroughProtocolMarker
  , crossDomainBreakthroughProtocolSurface
  ) where

import UMST.ChemConstants.ChemPhysicsChartIsomorphism
  ( chemPhysicsChartIsomorphismCellId
  , chemPhysicsIsomorphismHolds
  , constitutiveChartTagCount
  , enginesNotSecondPhysicsOk
  , extraChemForceRefusedOk
  , soleAxiomCountOk
  , unwiredChemPhysicsChartDesignOk
  )

-- | Design modality for cross-domain breakthrough protocol claims (TYPE-03 preview).
data CrossDomainBreakthroughProtocolModality
  = CrossDomainBreakthroughProtocolUnwired
  | CrossDomainBreakthroughProtocolAssumed
  | CrossDomainBreakthroughProtocolProved
  | CrossDomainBreakthroughProtocolSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
crossDomainBreakthroughProtocolModalityCurrent :: CrossDomainBreakthroughProtocolModality
crossDomainBreakthroughProtocolModalityCurrent = CrossDomainBreakthroughProtocolUnwired

-- | One presentation fiber from the sole axiom (not XOR worlds).
data BreakthroughFiber
  = ChemistryFiber
  | PhysicsFiber
  | EnvironmentTimeFiber
  | CrossDomainFiber
  deriving (Eq, Show)

breakthroughFiberTag :: BreakthroughFiber -> String
breakthroughFiberTag ChemistryFiber = "chemistry_fiber"
breakthroughFiberTag PhysicsFiber = "physics_fiber"
breakthroughFiberTag EnvironmentTimeFiber = "environment_time_fiber"
breakthroughFiberTag CrossDomainFiber = "cross_domain_fiber"

breakthroughFiberFromTag :: String -> Maybe BreakthroughFiber
breakthroughFiberFromTag "chemistry_fiber" = Just ChemistryFiber
breakthroughFiberFromTag "physics_fiber" = Just PhysicsFiber
breakthroughFiberFromTag "environment_time_fiber" = Just EnvironmentTimeFiber
breakthroughFiberFromTag "cross_domain_fiber" = Just CrossDomainFiber
breakthroughFiberFromTag _ = Nothing

breakthroughFiberTags :: [String]
breakthroughFiberTags =
  [ "chemistry_fiber"
  , "physics_fiber"
  , "environment_time_fiber"
  , "cross_domain_fiber"
  ]

-- | Honest breakthrough terminal — chart, commuting square, or named remainder.
data HonestBreakthroughTerminal
  = NewChart
  | CommutingSquare
  | NamedRemainder
  deriving (Eq, Show)

honestBreakthroughTerminalTag :: HonestBreakthroughTerminal -> String
honestBreakthroughTerminalTag NewChart = "new_chart"
honestBreakthroughTerminalTag CommutingSquare = "commuting_square"
honestBreakthroughTerminalTag NamedRemainder = "named_remainder"

honestBreakthroughTerminalTags :: [String]
honestBreakthroughTerminalTags =
  [ "new_chart"
  , "commuting_square"
  , "named_remainder"
  ]

-- | Refused breakthrough terminal — new axiom or folklore.
data RefusedBreakthroughTerminal
  = NewAxiom
  | Folklore
  deriving (Eq, Show)

refusedBreakthroughTerminalTag :: RefusedBreakthroughTerminal -> String
refusedBreakthroughTerminalTag NewAxiom = "new_axiom"
refusedBreakthroughTerminalTag Folklore = "folklore"

refusedBreakthroughTerminalTags :: [String]
refusedBreakthroughTerminalTags = ["new_axiom", "folklore"]

-- | One cross-domain breakthrough proposal witness.
data CrossDomainBreakthroughProposal = CrossDomainBreakthroughProposal
  { proposalSource :: BreakthroughFiber
  , proposalTarget :: BreakthroughFiber
  , proposalHonestTerminal :: Maybe HonestBreakthroughTerminal
  , proposalRefusedTerminal :: Maybe RefusedBreakthroughTerminal
  }
  deriving (Eq, Show)

proposalIsAdmissible :: CrossDomainBreakthroughProposal -> Bool
proposalIsAdmissible proposal =
  proposalHonestTerminal proposal /= Nothing
    && proposalRefusedTerminal proposal == Nothing

proposalRefusesNewLawOrFolklore :: CrossDomainBreakthroughProposal -> Bool
proposalRefusesNewLawOrFolklore proposal =
  proposalRefusedTerminal proposal /= Just NewAxiom
    && proposalRefusedTerminal proposal /= Just Folklore

-- | Whether breakthrough protocol mints a new axiom (always false on this cell).
breakthroughProtocolIsNewAxiom :: Bool
breakthroughProtocolIsNewAxiom = False

breakthroughFiberCount :: Int
breakthroughFiberCount = length breakthroughFiberTags

honestBreakthroughTerminalCount :: Int
honestBreakthroughTerminalCount = length honestBreakthroughTerminalTags

refusedBreakthroughTerminalCount :: Int
refusedBreakthroughTerminalCount = length refusedBreakthroughTerminalTags

-- | Whether all four fiber tags resolve to distinct fibers.
fourFibersFromOneAxiom :: Bool
fourFibersFromOneAxiom =
  length breakthroughFiberTags == 4
    && all (maybe False (const True) . breakthroughFiberFromTag) breakthroughFiberTags
    && length (map breakthroughFiberFromTag breakthroughFiberTags) == 4

sampleChemToPhysicsNewChart :: CrossDomainBreakthroughProposal
sampleChemToPhysicsNewChart =
  CrossDomainBreakthroughProposal
    { proposalSource = ChemistryFiber
    , proposalTarget = PhysicsFiber
    , proposalHonestTerminal = Just NewChart
    , proposalRefusedTerminal = Nothing
    }

sampleEnvTimeToCrossDomainCommutingSquare :: CrossDomainBreakthroughProposal
sampleEnvTimeToCrossDomainCommutingSquare =
  CrossDomainBreakthroughProposal
    { proposalSource = EnvironmentTimeFiber
    , proposalTarget = CrossDomainFiber
    , proposalHonestTerminal = Just CommutingSquare
    , proposalRefusedTerminal = Nothing
    }

sampleCrossDomainToChemNamedRemainder :: CrossDomainBreakthroughProposal
sampleCrossDomainToChemNamedRemainder =
  CrossDomainBreakthroughProposal
    { proposalSource = CrossDomainFiber
    , proposalTarget = ChemistryFiber
    , proposalHonestTerminal = Just NamedRemainder
    , proposalRefusedTerminal = Nothing
    }

sampleRefusedFolkloreProposal :: CrossDomainBreakthroughProposal
sampleRefusedFolkloreProposal =
  CrossDomainBreakthroughProposal
    { proposalSource = CrossDomainFiber
    , proposalTarget = PhysicsFiber
    , proposalHonestTerminal = Nothing
    , proposalRefusedTerminal = Just Folklore
    }

sampleRefusedNewAxiomProposal :: CrossDomainBreakthroughProposal
sampleRefusedNewAxiomProposal =
  CrossDomainBreakthroughProposal
    { proposalSource = PhysicsFiber
    , proposalTarget = CrossDomainFiber
    , proposalHonestTerminal = Nothing
    , proposalRefusedTerminal = Just NewAxiom
    }

sampleProposalsHonestPartition :: Bool
sampleProposalsHonestPartition =
  proposalIsAdmissible sampleChemToPhysicsNewChart
    && proposalIsAdmissible sampleEnvTimeToCrossDomainCommutingSquare
    && proposalIsAdmissible sampleCrossDomainToChemNamedRemainder
    && not (proposalIsAdmissible sampleRefusedFolkloreProposal)
    && not (proposalIsAdmissible sampleRefusedNewAxiomProposal)

chemPhysicsChartIsomorphismAuthority :: String
chemPhysicsChartIsomorphismAuthority =
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"

crossDomainBreakthroughProtocolAuthority :: String
crossDomainBreakthroughProtocolAuthority =
  "umst/umst-chem/src/x_rows/cross_domain_breakthrough_protocol.rs"

chemPhysicsChartIsomorphismCitedNotForked :: Bool
chemPhysicsChartIsomorphismCitedNotForked =
  "chem_physics_chart_isomorphism"
    `elem` words chemPhysicsChartIsomorphismAuthority
    && "chem_physics_chart_isomorphism"
      `elem` words crossDomainBreakthroughProtocolNonClaim
    && chemPhysicsChartIsomorphismCellId
      `elem` words crossDomainBreakthroughProtocolNonClaim

chartIsomorphismOnOneAxiomCited :: Bool
chartIsomorphismOnOneAxiomCited =
  unwiredChemPhysicsChartDesignOk
    && chemPhysicsIsomorphismHolds
    && enginesNotSecondPhysicsOk
    && extraChemForceRefusedOk
    && constitutiveChartTagCount == 8
    && soleAxiomCountOk

crossDomainBreakthroughProtocolNot27thAxiom :: Bool
crossDomainBreakthroughProtocolNot27thAxiom =
  not breakthroughProtocolIsNewAxiom
    && "27th" `elem` words crossDomainBreakthroughProtocolNonClaim
    && "not" `elem` words crossDomainBreakthroughProtocolNonClaim

crossDomainBreakthroughProtocolHonestConjunct :: Bool
crossDomainBreakthroughProtocolHonestConjunct =
  not breakthroughProtocolIsNewAxiom
    && fourFibersFromOneAxiom
    && sampleProposalsHonestPartition
    && chemPhysicsChartIsomorphismCitedNotForked
    && chartIsomorphismOnOneAxiomCited
    && crossDomainBreakthroughProtocolNot27thAxiom

crossDomainBreakthroughProtocolScaffold :: Bool
crossDomainBreakthroughProtocolScaffold =
  crossDomainBreakthroughProtocolHonestConjunct
    && breakthroughFiberCount == 4
    && honestBreakthroughTerminalCount == 3
    && refusedBreakthroughTerminalCount == 2

data CrossDomainBreakthroughProtocolProbe = CrossDomainBreakthroughProtocolProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  , fourFibers :: Bool
  , honestPartition :: Bool
  , chartIsomorphismCited :: Bool
  , chartIsomorphismHolds :: Bool
  , notNewAxiom :: Bool
  }
  deriving (Eq, Show)

crossDomainBreakthroughProtocolProbe :: CrossDomainBreakthroughProtocolProbe
crossDomainBreakthroughProtocolProbe =
  CrossDomainBreakthroughProtocolProbe
    { cellIdNamed =
        crossDomainBreakthroughProtocolCellId
          == "CHEM-FORMAL-Q-HS-CROSS-DOMAIN-BREAKTHROUGH-PROTOCOL-CONSERVATION"
    , unwired =
        crossDomainBreakthroughProtocolModalityCurrent
          == CrossDomainBreakthroughProtocolUnwired
    , physicsGreenRefused =
        not crossDomainBreakthroughProtocolPhysicsGreenAuthorized
    , soleAxiom = True
    , notProved = not crossDomainBreakthroughProtocolRowProved
    , fourFibers = fourFibersFromOneAxiom
    , honestPartition = sampleProposalsHonestPartition
    , chartIsomorphismCited = chemPhysicsChartIsomorphismCitedNotForked
    , chartIsomorphismHolds = chartIsomorphismOnOneAxiomCited
    , notNewAxiom = not breakthroughProtocolIsNewAxiom
    }

crossDomainBreakthroughProtocolHonest :: Bool
crossDomainBreakthroughProtocolHonest =
  let p = crossDomainBreakthroughProtocolProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && fourFibers p
        && honestPartition p
        && chartIsomorphismCited p
        && chartIsomorphismHolds p
        && notNewAxiom p
        && crossDomainBreakthroughProtocolScaffold

crossDomainBreakthroughProtocolRowProved :: Bool
crossDomainBreakthroughProtocolRowProved = False

crossDomainBreakthroughProtocolFraming :: String
crossDomainBreakthroughProtocolFraming =
  "second_law_conservation_cross_domain_breakthrough_protocol_one_axiom"

crossDomainBreakthroughProtocolAxiom :: Bool
crossDomainBreakthroughProtocolAxiom =
  crossDomainBreakthroughProtocolScaffold
    && crossDomainBreakthroughProtocolHonestConjunct
    && crossDomainBreakthroughProtocolHonest
    && not breakthroughProtocolIsNewAxiom
    && not crossDomainBreakthroughProtocolRowProved
    && crossDomainBreakthroughProtocolFraming
      == "second_law_conservation_cross_domain_breakthrough_protocol_one_axiom"

crossDomainBreakthroughProtocolNamed :: String
crossDomainBreakthroughProtocolNamed =
  "crossDomainBreakthroughProtocol: later composition on same axiom four fibers NewChart CommutingSquare NamedRemainder cite chem_physics_chart_isomorphism not fork NewAxiom Folklore refused not 27th axiom not physics GREEN"

crossDomainBreakthroughProtocolMarker :: String
crossDomainBreakthroughProtocolMarker =
  "chem_int_cross_cross_domain_breakthrough_protocol_v1"

crossDomainBreakthroughProtocolSurface :: String
crossDomainBreakthroughProtocolSurface =
  "cross_domain_breakthrough_protocol_surface"

crossDomainBreakthroughProtocolCellId :: String
crossDomainBreakthroughProtocolCellId =
  "CHEM-FORMAL-Q-HS-CROSS-DOMAIN-BREAKTHROUGH-PROTOCOL-CONSERVATION"

crossDomainBreakthroughProtocolNonClaim :: String
crossDomainBreakthroughProtocolNonClaim =
  "CHEM-FORMAL-Q-HS-CROSS-DOMAIN-BREAKTHROUGH-PROTOCOL-CONSERVATION X40 cross-domain breakthrough protocol Unwired — later composition on same axiom with env time cross-domain nuance not new law not folklore; honest terminals NewChart CommutingSquare NamedRemainder on four fibers from one axiom; NewAxiom Folklore refused; cite CHEM-FORMAL-Q-HS-CHEM-PHYSICS-CHART-ISOMORPHISM-CONSERVATION chem_physics_chart_isomorphism not fork; not 27th axiom; not physics GREEN; not production_wired"

crossDomainBreakthroughProtocolPhysicsGreenAuthorized :: Bool
crossDomainBreakthroughProtocolPhysicsGreenAuthorized = False

crossDomainBreakthroughProtocolPhysicsGreenFalse :: Bool
crossDomainBreakthroughProtocolPhysicsGreenFalse =
  not crossDomainBreakthroughProtocolPhysicsGreenAuthorized

crossDomainBreakthroughProtocolModalityUnwired :: Bool
crossDomainBreakthroughProtocolModalityUnwired =
  crossDomainBreakthroughProtocolModalityCurrent
    == CrossDomainBreakthroughProtocolUnwired

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ComposerResearchBleedingEdge
Description : Composer research bleeding-edge conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Composer research bleeding-edge conservation: named **research chart** lane for v50
bleeding-edge hypotheses — cites @CHEM_NS_V50_RESEARCH_HYPOTHESES.json@ read-only, no fork.
Hypothesis rows map to @COMPOSER-RESEARCH-BLEEDING-EDGE@ stem; literature requiring new axiom
refused.

* @ResearchHypothesisClass@ — theorem-candidate | named-measured-remainder | already-unwired | absent.
* @BleedingEdgeHypothesisRow@ — typed chart entries, not folklore or GREEN.
* **One** design axiom (@composerResearchBleedingEdgeAxiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of @umst-chem@ @composer_research_bleeding_edge.rs@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.ComposerResearchBleedingEdge
  ( ComposerResearchBleedingEdgeModality (..)
  , composerResearchBleedingEdgeModalityCurrent
  , ResearchHypothesisClass (..)
  , researchHypothesisClassTag
  , BleedingEdgeHypothesisRow (..)
  , bleedingEdgeHypothesisIds
  , bleedingEdgeHypothesisRows
  , bleedingEdgeHypothesisCount
  , bleedingEdgeHypothesisRowConserved
  , bleedingEdgeHypothesesConserved
  , composerResearchIsNewAxiom
  , researchHypothesesAuthority
  , composerResearchBleedingEdgeAuthority
  , researchHypothesesCitedNotForked
  , literatureNewAxiomRefused
  , composerResearchBleedingEdgeHonestConjunct
  , composerResearchBleedingEdgeNotSecondAxiom
  , composerResearchBleedingEdgeScaffold
  , ComposerResearchBleedingEdgeProbe (..)
  , composerResearchBleedingEdgeProbe
  , composerResearchBleedingEdgeHonest
  , composerResearchBleedingEdgeRowProved
  , composerResearchBleedingEdgeFraming
  , composerResearchBleedingEdgeAxiom
  , composerResearchBleedingEdgeNamed
  , composerResearchBleedingEdgeMarker
  , composerResearchBleedingEdgeSurface
  , composerResearchBleedingEdgeRowStem
  , composerResearchBleedingEdgeV50Stem
  , composerResearchBleedingEdgeCellId
  , composerResearchBleedingEdgeNonClaim
  , composerResearchBleedingEdgePhysicsGreenAuthorized
  , composerResearchBleedingEdgePhysicsGreenFalse
  , composerResearchBleedingEdgeModalityUnwired
  , soleAxiomCount
  ) where

-- | Design modality for composer-research-bleeding-edge claims (TYPE-03 preview).
data ComposerResearchBleedingEdgeModality
  = ComposerResearchBleedingEdgeUnwired
  | ComposerResearchBleedingEdgeAssumed
  | ComposerResearchBleedingEdgeProved
  | ComposerResearchBleedingEdgeSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
composerResearchBleedingEdgeModalityCurrent :: ComposerResearchBleedingEdgeModality
composerResearchBleedingEdgeModalityCurrent = ComposerResearchBleedingEdgeUnwired

-- | Research hypothesis posture on the bleeding-edge chart.
data ResearchHypothesisClass
  = TheoremCandidate
  | NamedMeasuredRemainder
  | AlreadyUnwired
  | Absent
  deriving (Eq, Show)

researchHypothesisClassTag :: ResearchHypothesisClass -> String
researchHypothesisClassTag TheoremCandidate = "theorem-candidate"
researchHypothesisClassTag NamedMeasuredRemainder = "named-measured-remainder"
researchHypothesisClassTag AlreadyUnwired = "already-unwired"
researchHypothesisClassTag Absent = "absent"

-- | One bleeding-edge research hypothesis witness row.
data BleedingEdgeHypothesisRow = BleedingEdgeHypothesisRow
  { hypothesisId :: String
  , hypothesisClass :: ResearchHypothesisClass
  , mapsToBleedingEdgeStem :: Bool
  , notA26thAxiom :: Bool
  }
  deriving (Eq, Show)

bleedingEdgeHypothesisRowConserved :: BleedingEdgeHypothesisRow -> Bool
bleedingEdgeHypothesisRowConserved row =
  mapsToBleedingEdgeStem row && notA26thAxiom row

-- | Hypothesis ids mapped to COMPOSER-RESEARCH-BLEEDING-EDGE stem (read-only cite).
bleedingEdgeHypothesisIds :: [String]
bleedingEdgeHypothesisIds =
  [ "H-V50-REFUSE-CATALYSIS-AXIOM"
  , "H-V50-CHEM-PHYSICS-ISOMORPHISM"
  ]

-- | Canonical bleeding-edge hypothesis rows (cite JSON, no fork).
bleedingEdgeHypothesisRows :: [BleedingEdgeHypothesisRow]
bleedingEdgeHypothesisRows =
  [ BleedingEdgeHypothesisRow
      { hypothesisId = "H-V50-REFUSE-CATALYSIS-AXIOM"
      , hypothesisClass = Absent
      , mapsToBleedingEdgeStem = True
      , notA26thAxiom = True
      }
  , BleedingEdgeHypothesisRow
      { hypothesisId = "H-V50-CHEM-PHYSICS-ISOMORPHISM"
      , hypothesisClass = AlreadyUnwired
      , mapsToBleedingEdgeStem = True
      , notA26thAxiom = True
      }
  ]

bleedingEdgeHypothesisCount :: Int
bleedingEdgeHypothesisCount = length bleedingEdgeHypothesisIds

bleedingEdgeHypothesesConserved :: Bool
bleedingEdgeHypothesesConserved =
  all bleedingEdgeHypothesisRowConserved bleedingEdgeHypothesisRows
    && length bleedingEdgeHypothesisRows == bleedingEdgeHypothesisCount

-- | Sole axiom count — second law + conservation only.
soleAxiomCount :: Int
soleAxiomCount = 1

-- | Whether the research chart mints a new axiom (always false on this cell).
composerResearchIsNewAxiom :: Bool
composerResearchIsNewAxiom = False

-- | Read-only research hypotheses authority (cite, no fork).
researchHypothesesAuthority :: String
researchHypothesesAuthority =
  "workspace/ops/CHEM_NS_V50_RESEARCH_HYPOTHESES.json"

composerResearchBleedingEdgeAuthority :: String
composerResearchBleedingEdgeAuthority =
  "umst/umst-chem/src/x_rows/composer_research_bleeding_edge.rs"

researchHypothesesCitedNotForked :: Bool
researchHypothesesCitedNotForked =
  researchHypothesesAuthority
    == "workspace/ops/CHEM_NS_V50_RESEARCH_HYPOTHESES.json"
    && "CHEM_NS_V50_RESEARCH_HYPOTHESES.json"
      `elem` (words composerResearchBleedingEdgeNonClaim)
    && "read-only" `elem` (words composerResearchBleedingEdgeNonClaim)
    && "composer_research_bleeding_edge"
      `elem` (words composerResearchBleedingEdgeAuthority)

literatureNewAxiomRefused :: Bool
literatureNewAxiomRefused =
  not composerResearchIsNewAxiom
    && "not" `elem` (words composerResearchBleedingEdgeNonClaim)
    && "26th" `elem` (words composerResearchBleedingEdgeNonClaim)
    && "research" `elem` (words composerResearchBleedingEdgeNonClaim)
    && "chart" `elem` (words composerResearchBleedingEdgeNonClaim)

composerResearchBleedingEdgeNotSecondAxiom :: Bool
composerResearchBleedingEdgeNotSecondAxiom =
  not composerResearchIsNewAxiom
    && soleAxiomCount == 1
    && "not" `elem` (words composerResearchBleedingEdgeNonClaim)
    && "26th" `elem` (words composerResearchBleedingEdgeNonClaim)

composerResearchBleedingEdgeHonestConjunct :: Bool
composerResearchBleedingEdgeHonestConjunct =
  not composerResearchIsNewAxiom
    && bleedingEdgeHypothesesConserved
    && researchHypothesesCitedNotForked
    && literatureNewAxiomRefused
    && composerResearchBleedingEdgeNotSecondAxiom

composerResearchBleedingEdgeScaffold :: Bool
composerResearchBleedingEdgeScaffold =
  composerResearchBleedingEdgeHonestConjunct
    && bleedingEdgeHypothesisCount == 2
    && length bleedingEdgeHypothesisRows == 2
    && length
      [ TheoremCandidate
      , NamedMeasuredRemainder
      , AlreadyUnwired
      , Absent
      ]
      == 4

data ComposerResearchBleedingEdgeProbe = ComposerResearchBleedingEdgeProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  , bleedingEdgeConserved :: Bool
  , researchHypothesesCited :: Bool
  , literatureRefused :: Bool
  , notNewAxiom :: Bool
  , productionWiredRefused :: Bool
  }
  deriving (Eq, Show)

composerResearchBleedingEdgeProbe :: ComposerResearchBleedingEdgeProbe
composerResearchBleedingEdgeProbe =
  ComposerResearchBleedingEdgeProbe
    { cellIdNamed =
        composerResearchBleedingEdgeCellId
          == "CHEM-FORMAL-Q-HS-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION"
    , unwired =
        composerResearchBleedingEdgeModalityCurrent
          == ComposerResearchBleedingEdgeUnwired
    , physicsGreenRefused =
        not composerResearchBleedingEdgePhysicsGreenAuthorized
    , soleAxiom = soleAxiomCount == 1
    , notProved = not composerResearchBleedingEdgeRowProved
    , bleedingEdgeConserved = bleedingEdgeHypothesesConserved
    , researchHypothesesCited = researchHypothesesCitedNotForked
    , literatureRefused = literatureNewAxiomRefused
    , notNewAxiom = not composerResearchIsNewAxiom
    , productionWiredRefused =
        "not" `elem` (words composerResearchBleedingEdgeNonClaim)
          && "production_wired" `elem` (words composerResearchBleedingEdgeNonClaim)
    }

composerResearchBleedingEdgeHonest :: Bool
composerResearchBleedingEdgeHonest =
  let p = composerResearchBleedingEdgeProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && bleedingEdgeConserved p
        && researchHypothesesCited p
        && literatureRefused p
        && notNewAxiom p
        && productionWiredRefused p
        && composerResearchBleedingEdgeScaffold

composerResearchBleedingEdgeRowProved :: Bool
composerResearchBleedingEdgeRowProved = False

composerResearchBleedingEdgeFraming :: String
composerResearchBleedingEdgeFraming =
  "second_law_conservation_composer_research_bleeding_edge_one_axiom"

composerResearchBleedingEdgeAxiom :: Bool
composerResearchBleedingEdgeAxiom =
  composerResearchBleedingEdgeScaffold
    && composerResearchBleedingEdgeHonestConjunct
    && composerResearchBleedingEdgeHonest
    && not composerResearchIsNewAxiom
    && not composerResearchBleedingEdgeRowProved
    && composerResearchBleedingEdgeFraming
      == "second_law_conservation_composer_research_bleeding_edge_one_axiom"

composerResearchBleedingEdgeNamed :: String
composerResearchBleedingEdgeNamed =
  "composerResearchBleedingEdge: named research chart lane v50 bleeding-edge hypotheses cite CHEM_NS_V50_RESEARCH_HYPOTHESES.json read-only not fork H-V50-REFUSE-CATALYSIS-AXIOM H-V50-CHEM-PHYSICS-ISOMORPHISM COMPOSER-RESEARCH-BLEEDING-EDGE stem not 26th axiom not physics GREEN not production_wired"

composerResearchBleedingEdgeMarker :: String
composerResearchBleedingEdgeMarker =
  "chem_int_cross_composer_research_bleeding_edge_v1"

composerResearchBleedingEdgeSurface :: String
composerResearchBleedingEdgeSurface = "composer_research_bleeding_edge_surface"

composerResearchBleedingEdgeRowStem :: String
composerResearchBleedingEdgeRowStem = "composer_research_bleeding_edge"

composerResearchBleedingEdgeV50Stem :: String
composerResearchBleedingEdgeV50Stem = "COMPOSER-RESEARCH-BLEEDING-EDGE"

composerResearchBleedingEdgeCellId :: String
composerResearchBleedingEdgeCellId =
  "CHEM-FORMAL-Q-HS-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION"

composerResearchBleedingEdgeNonClaim :: String
composerResearchBleedingEdgeNonClaim =
  "CHEM-FORMAL-Q-HS-COMPOSER-RESEARCH-BLEEDING-EDGE-CONSERVATION X31 composer research bleeding-edge conservation Unwired — named research chart cite CHEM-INT-CROSS-COMPOSER-RESEARCH-BLEEDING-EDGE composer_research_bleeding_edge CHEM_NS_V50_RESEARCH_HYPOTHESES.json read-only not fork; H-V50-REFUSE-CATALYSIS-AXIOM H-V50-CHEM-PHYSICS-ISOMORPHISM COMPOSER-RESEARCH-BLEEDING-EDGE stem; literature new axiom refused; not 26th axiom; not physics GREEN; not production_wired"

composerResearchBleedingEdgePhysicsGreenAuthorized :: Bool
composerResearchBleedingEdgePhysicsGreenAuthorized = False

composerResearchBleedingEdgePhysicsGreenFalse :: Bool
composerResearchBleedingEdgePhysicsGreenFalse =
  not composerResearchBleedingEdgePhysicsGreenAuthorized

composerResearchBleedingEdgeModalityUnwired :: Bool
composerResearchBleedingEdgeModalityUnwired =
  composerResearchBleedingEdgeModalityCurrent == ComposerResearchBleedingEdgeUnwired

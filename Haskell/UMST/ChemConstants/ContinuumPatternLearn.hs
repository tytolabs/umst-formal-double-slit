-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ContinuumPatternLearn
Description : Continuum pattern-learn conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Continuum pattern-learn conservation: X55 named chart of concurrent §2 pattern classifiers
evaluated along the environment continuum (vacuum | contained | messy). Cite upstream
@pattern_taxonomy@ SSOT — **not** a live PatternBundle Π_c wire hop.

Concurrent product discipline: many pattern classes may hold at once (Π_c not XOR); chart
names classifier slots for learn-along-continuum — not minting a 26th axiom.

* **One** design axiom (@continuumPatternLearnAxiom@): second law + conservation.
* Chart cites @pattern_taxonomy@ + @nuance_along_environment_continuum@ — not a second axiom fork.
* @physics_green@ stays false; live PatternBundle wire refused.

Haskell mirror of @umst-chem@ @continuum_pattern_learn.rs@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-CONTINUUM-PATTERN-LEARN-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.ContinuumPatternLearn
  ( ContinuumPatternLearnModality (..)
  , continuumPatternLearnModalityCurrent
  , ContinuumPatternLearnChartRow (..)
  , continuumPatternLearnChartRow
  , continuumLearnSectionTags
  , explicitEnvCoordinateClassIndices
  , carbonNuanceChartClassIndices
  , continuumVsDiscreteClassIndex
  , livePatternBundlePiCWire
  , soleAxiomCount
  , continuumLearnSectionsNamed
  , patternClassCardinality25
  , carbonNuanceChartClassesNamed
  , concurrentClassifiersNotXor
  , explicitEnvCoordinatesNamedNotExtraAxiom
  , continuumClass23Named
  , livePatternBundlePiCWireRefused
  , continuumPatternLearnIsNewAxiom
  , patternTaxonomyAuthority
  , nuanceAlongEnvContinuumAuthority
  , nuanceAlongEnvContinuumCellId
  , continuumVsDiscreteAuthority
  , continuumPatternLearnAuthority
  , chemL0Pattern00CellId
  , patternTaxonomyMarker
  , patternTaxonomyCitedNotForked
  , nuanceAlongEnvContinuumCited
  , continuumPatternLearnChartHops
  , continuumPatternLearnChartHopsNamed
  , patternTaxonomyAllClassifiersPresent
  , patternTaxonomyHonest
  , continuumPatternLearnHonestConjunct
  , continuumPatternLearnScaffold
  , ContinuumPatternLearnProbe (..)
  , continuumPatternLearnProbe
  , continuumPatternLearnHonest
  , continuumPatternLearnRowProved
  , continuumPatternLearnFraming
  , continuumPatternLearnAxiom
  , continuumPatternLearnNamed
  , continuumPatternLearnMarker
  , continuumPatternLearnSurface
  , continuumPatternLearnCellId
  , continuumPatternLearnNonClaim
  , continuumPatternLearnPhysicsGreenAuthorized
  , continuumPatternLearnPhysicsGreenFalse
  , continuumPatternLearnModalityUnwired
  ) where

import UMST.ChemConstants.PatternProductConservation
  ( PatternClassTag (..)
  , carbonNuanceWitness
  , patternBundleHolds
  , patternBundleIsConcurrentProduct
  , patternClassCardinality
  , patternClassTagIndex
  )

-- | Design modality for continuum pattern-learn claims (TYPE-03 preview).
data ContinuumPatternLearnModality
  = ContinuumPatternLearnUnwired
  | ContinuumPatternLearnAssumed
  | ContinuumPatternLearnProved
  | ContinuumPatternLearnSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
continuumPatternLearnModalityCurrent :: ContinuumPatternLearnModality
continuumPatternLearnModalityCurrent = ContinuumPatternLearnUnwired

-- | Stable §2 class tags in north-star order (cite pattern_taxonomy SSOT).
patternClassTagStrings :: [String]
patternClassTagStrings =
  [ "per_element_nuance"
  , "shared"
  , "bond_forming"
  , "bond_repelling"
  , "structure_enabling"
  , "structure_blocking_inertness"
  , "natural_ore_assemblage"
  , "assemblage_stability_why"
  , "impure_component_morphism"
  , "processing_refining"
  , "allotrope"
  , "isotope"
  , "metastable_vs_equilibrium"
  , "phase_eutectic_solid_solution"
  , "catalysis"
  , "surface_vs_bulk_sdf"
  , "aqueous_vs_mineral"
  , "redox_ladder"
  , "polymorphism"
  , "tp_parametric"
  , "contamination_reverse_refine"
  , "assay_measurement_landauer"
  , "vacuum_inert_limit"
  , "continuum_vs_discrete_element_id"
  , "other_named_nuance"
  ]

patternClassTagAtIndex :: Int -> Maybe String
patternClassTagAtIndex idx =
  if idx >= 0 && idx < length patternClassTagStrings
    then Just (patternClassTagStrings !! idx)
    else Nothing

-- | One named chart row — concurrent classifier slot on the continuum learn ladder.
data ContinuumPatternLearnChartRow = ContinuumPatternLearnChartRow
  { chartClassIndex :: Int
  , chartClassTag :: String
  , chartIsExplicitEnvCoordinate :: Bool
  }
  deriving (Eq, Show)

-- | Build one chart row for a §2 class index.
continuumPatternLearnChartRow :: Int -> Maybe ContinuumPatternLearnChartRow
continuumPatternLearnChartRow idx =
  case patternClassTagAtIndex idx of
    Nothing -> Nothing
    Just tag ->
      Just
        ContinuumPatternLearnChartRow
          { chartClassIndex = idx
          , chartClassTag = tag
          , chartIsExplicitEnvCoordinate = idx `elem` explicitEnvCoordinateClassIndices
          }

-- | Continuum sample sections on the learn chart (vacuum | contained | messy).
continuumLearnSectionTags :: [String]
continuumLearnSectionTags = ["vacuum", "contained", "messy"]

-- | Explicit environmental §2 class indices on the continuum chart (not extra axioms).
explicitEnvCoordinateClassIndices :: [Int]
explicitEnvCoordinateClassIndices =
  [ patternClassTagIndex SurfaceVsBulkSdf
  , patternClassTagIndex AqueousVsMineral
  , patternClassTagIndex TpParametric
  , patternClassTagIndex ContaminationReverseRefine
  , patternClassTagIndex AssayMeasurementLandauer
  , patternClassTagIndex VacuumInertLimit
  ]

-- | Carbon nuance witness class indices cited on chart (allotrope + catalysis + continuum).
carbonNuanceChartClassIndices :: [Int]
carbonNuanceChartClassIndices =
  [ patternClassTagIndex Allotrope
  , patternClassTagIndex Catalysis
  , patternClassTagIndex ContinuumVsDiscreteElementId
  ]

-- | Continuum-vs-discrete §2 class index (north-star class 23).
continuumVsDiscreteClassIndex :: Int
continuumVsDiscreteClassIndex = patternClassTagIndex ContinuumVsDiscreteElementId

-- | Whether live PatternBundle Π_c is wired on this cell (always false — chart only).
livePatternBundlePiCWire :: Bool
livePatternBundlePiCWire = False

-- | Sole axiom count — second law + conservation only.
soleAxiomCount :: Int
soleAxiomCount = 1

-- | Named chart hop ids — concurrent classifier slots along continuum learn ladder.
continuumPatternLearnChartHops :: [String]
continuumPatternLearnChartHops =
  [ "pattern_taxonomy_cited"
  , "continuum_sections_named"
  , "concurrent_classifiers_not_xor"
  , "explicit_env_coordinates_not_extra_axiom"
  , "continuum_class_23_named"
  , "live_pi_c_wire_refused"
  , "chart_not_second_axiom"
  , "sole_axiom_second_law_conservation"
  ]

patternTaxonomyAuthority :: String
patternTaxonomyAuthority = "umst/umst-chem/src/pattern_taxonomy.rs"

nuanceAlongEnvContinuumAuthority :: String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

nuanceAlongEnvContinuumCellId :: String
nuanceAlongEnvContinuumCellId = "CHEM-INT-NUANCE-ALONG-ENV-CONTINUUM"

continuumVsDiscreteAuthority :: String
continuumVsDiscreteAuthority =
  "umst/umst-chem/src/l0_tables/continuum_vs_discrete_element_id.rs"

continuumPatternLearnAuthority :: String
continuumPatternLearnAuthority = "umst/umst-chem/src/x_rows/continuum_pattern_learn.rs"

chemL0Pattern00CellId :: String
chemL0Pattern00CellId = "CHEM-L0-PATTERN-00"

patternTaxonomyMarker :: String
patternTaxonomyMarker = "chem_l0_pattern_taxonomy_v1"

-- | Whether all three continuum learn sections are named.
continuumLearnSectionsNamed :: Bool
continuumLearnSectionsNamed =
  length continuumLearnSectionTags == 3
    && continuumLearnSectionTags == ["vacuum", "contained", "messy"]

-- | Whether §2 class cardinality remains pinned at 25 on the chart.
patternClassCardinality25 :: Bool
patternClassCardinality25 =
  patternClassCardinality == 25 && length patternClassTagStrings == 25

-- | Whether carbon nuance chart pins allotrope + catalysis + continuum class indices.
carbonNuanceChartClassesNamed :: Bool
carbonNuanceChartClassesNamed =
  carbonNuanceChartClassIndices
    == [ patternClassTagIndex Allotrope
       , patternClassTagIndex Catalysis
       , patternClassTagIndex ContinuumVsDiscreteElementId
       ]
    && patternClassTagStrings !! patternClassTagIndex Allotrope == "allotrope"
    && patternClassTagStrings !! patternClassTagIndex Catalysis == "catalysis"
    && patternClassTagStrings
      !! patternClassTagIndex ContinuumVsDiscreteElementId
      == "continuum_vs_discrete_element_id"

-- | Whether concurrent classifier chart refuses XOR / mutually-exclusive folklore.
concurrentClassifiersNotXor :: Bool
concurrentClassifiersNotXor =
  carbonNuanceChartClassesNamed
    && patternClassCardinality25
    && patternBundleIsConcurrentProduct carbonNuanceWitness
    && patternBundleHolds (patternClassTagIndex Allotrope) carbonNuanceWitness
    && patternBundleHolds (patternClassTagIndex Catalysis) carbonNuanceWitness
    && patternBundleHolds
      (patternClassTagIndex ContinuumVsDiscreteElementId)
      carbonNuanceWitness

-- | Whether explicit env coordinate classes are named — not minted as extra axioms.
explicitEnvCoordinatesNamedNotExtraAxiom :: Bool
explicitEnvCoordinatesNamedNotExtraAxiom =
  all
    ( \idx ->
        case continuumPatternLearnChartRow idx of
          Nothing -> False
          Just row -> chartIsExplicitEnvCoordinate row
    )
    explicitEnvCoordinateClassIndices

-- | Whether continuum class 23 (continuum_vs_discrete_element_id) is named on chart.
continuumClass23Named :: Bool
continuumClass23Named =
  case continuumPatternLearnChartRow continuumVsDiscreteClassIndex of
    Nothing -> False
    Just row ->
      chartClassTag row == "continuum_vs_discrete_element_id"
        && chartClassIndex row == 23

-- | Whether live PatternBundle Π_c wire is refused on this cell.
livePatternBundlePiCWireRefused :: Bool
livePatternBundlePiCWireRefused = not livePatternBundlePiCWire

-- | Whether chart mints a new axiom (always false on this cell).
continuumPatternLearnIsNewAxiom :: Bool
continuumPatternLearnIsNewAxiom = False

patternTaxonomyCitedNotForked :: Bool
patternTaxonomyCitedNotForked =
  patternTaxonomyAuthority == "umst/umst-chem/src/pattern_taxonomy.rs"
    && "pattern_taxonomy" `elem` (words continuumPatternLearnNonClaim)
    && "not" `elem` (words continuumPatternLearnNonClaim)
    && "live" `elem` (words continuumPatternLearnNonClaim)
    && "PatternBundle" `elem` (words continuumPatternLearnNonClaim)
    && chemL0Pattern00CellId == "CHEM-L0-PATTERN-00"
    && not (null patternTaxonomyMarker)

nuanceAlongEnvContinuumCited :: Bool
nuanceAlongEnvContinuumCited =
  "nuance_along_environment_continuum" `elem` (words nuanceAlongEnvContinuumAuthority)
    && "nuance_along_environment_continuum"
      `elem` (words continuumPatternLearnNonClaim)
    && nuanceAlongEnvContinuumCellId == "CHEM-INT-NUANCE-ALONG-ENV-CONTINUUM"

continuumPatternLearnChartHopsNamed :: Bool
continuumPatternLearnChartHopsNamed = length continuumPatternLearnChartHops == 8

patternTaxonomyAllClassifiersPresent :: Bool
patternTaxonomyAllClassifiersPresent =
  patternClassCardinality25
    && length patternClassTagStrings == 25
    && all isClassifierSlotNamed
      [0 .. patternClassCardinality - 1]

  where
    isClassifierSlotNamed idx =
      case continuumPatternLearnChartRow idx of
        Nothing -> False
        Just row ->
          chartClassIndex row == idx
            && chartClassTag row == patternClassTagStrings !! idx

patternTaxonomyHonest :: Bool
patternTaxonomyHonest =
  patternTaxonomyAllClassifiersPresent
    && patternClassCardinality25
    && not continuumPatternLearnIsNewAxiom

continuumPatternLearnHonestConjunct :: Bool
continuumPatternLearnHonestConjunct =
  not continuumPatternLearnIsNewAxiom
    && continuumLearnSectionsNamed
    && concurrentClassifiersNotXor
    && explicitEnvCoordinatesNamedNotExtraAxiom
    && continuumClass23Named
    && livePatternBundlePiCWireRefused
    && patternTaxonomyCitedNotForked
    && nuanceAlongEnvContinuumCited
    && patternTaxonomyAllClassifiersPresent

continuumPatternLearnScaffold :: Bool
continuumPatternLearnScaffold =
  continuumPatternLearnHonestConjunct
    && patternTaxonomyHonest
    && continuumPatternLearnChartHopsNamed
    && soleAxiomCount == 1

data ContinuumPatternLearnProbe = ContinuumPatternLearnProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  , continuumSectionsNamed :: Bool
  , concurrentNotXor :: Bool
  , explicitEnvNamed :: Bool
  , continuumClass23 :: Bool
  , livePiCWireRefused :: Bool
  , patternTaxonomyCited :: Bool
  , nuanceAlongEnvCited :: Bool
  , taxonomyHonest :: Bool
  , chartHopsNamed :: Bool
  }
  deriving (Eq, Show)

continuumPatternLearnProbe :: ContinuumPatternLearnProbe
continuumPatternLearnProbe =
  ContinuumPatternLearnProbe
    { cellIdNamed =
        continuumPatternLearnCellId
          == "CHEM-FORMAL-Q-HS-CONTINUUM-PATTERN-LEARN-CONSERVATION"
    , unwired =
        continuumPatternLearnModalityCurrent == ContinuumPatternLearnUnwired
    , physicsGreenRefused =
        not continuumPatternLearnPhysicsGreenAuthorized
    , soleAxiom = soleAxiomCount == 1
    , notProved = not continuumPatternLearnRowProved
    , continuumSectionsNamed = continuumLearnSectionsNamed
    , concurrentNotXor = concurrentClassifiersNotXor
    , explicitEnvNamed = explicitEnvCoordinatesNamedNotExtraAxiom
    , continuumClass23 = continuumClass23Named
    , livePiCWireRefused = livePatternBundlePiCWireRefused
    , patternTaxonomyCited = patternTaxonomyCitedNotForked
    , nuanceAlongEnvCited = nuanceAlongEnvContinuumCited
    , taxonomyHonest = patternTaxonomyHonest
    , chartHopsNamed = continuumPatternLearnChartHopsNamed
    }

continuumPatternLearnHonest :: Bool
continuumPatternLearnHonest =
  let p = continuumPatternLearnProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && continuumSectionsNamed p
        && concurrentNotXor p
        && explicitEnvNamed p
        && continuumClass23 p
        && livePiCWireRefused p
        && patternTaxonomyCited p
        && nuanceAlongEnvCited p
        && taxonomyHonest p
        && chartHopsNamed p
        && continuumPatternLearnScaffold

continuumPatternLearnRowProved :: Bool
continuumPatternLearnRowProved = False

continuumPatternLearnFraming :: String
continuumPatternLearnFraming =
  "second_law_conservation_continuum_pattern_learn_one_axiom"

continuumPatternLearnAxiom :: Bool
continuumPatternLearnAxiom =
  continuumPatternLearnScaffold
    && continuumPatternLearnHonestConjunct
    && continuumPatternLearnHonest
    && not continuumPatternLearnIsNewAxiom
    && not continuumPatternLearnRowProved
    && continuumPatternLearnFraming
      == "second_law_conservation_continuum_pattern_learn_one_axiom"

continuumPatternLearnNamed :: String
continuumPatternLearnNamed =
  "continuumPatternLearn: X55 named chart concurrent pattern classifiers along vacuum contained messy continuum cite pattern_taxonomy SSOT not live PatternBundle Pi_c wire not XOR env tags nuance_along_environment_continuum cited not fork explicit env coordinates not extra axioms not 26th axiom not physics GREEN"

continuumPatternLearnMarker :: String
continuumPatternLearnMarker = "chem_int_cross_continuum_pattern_learn_v1"

continuumPatternLearnSurface :: String
continuumPatternLearnSurface = "continuum_pattern_learn_surface"

continuumPatternLearnCellId :: String
continuumPatternLearnCellId =
  "CHEM-FORMAL-Q-HS-CONTINUUM-PATTERN-LEARN-CONSERVATION"

continuumPatternLearnNonClaim :: String
continuumPatternLearnNonClaim =
  "CHEM-FORMAL-Q-HS-CONTINUUM-PATTERN-LEARN-CONSERVATION X55 continuum pattern-learn named chart concurrent pattern classifiers along vacuum contained messy continuum cite pattern_taxonomy SSOT not live PatternBundle Pi_c wire not XOR env tags; nuance_along_environment_continuum cited not fork; explicit env coordinates 15 16 19 20 21 22 not extra axioms; not 26th axiom; not physics GREEN; not production_wired"

continuumPatternLearnPhysicsGreenAuthorized :: Bool
continuumPatternLearnPhysicsGreenAuthorized = False

continuumPatternLearnPhysicsGreenFalse :: Bool
continuumPatternLearnPhysicsGreenFalse =
  not continuumPatternLearnPhysicsGreenAuthorized

continuumPatternLearnModalityUnwired :: Bool
continuumPatternLearnModalityUnwired =
  continuumPatternLearnModalityCurrent == ContinuumPatternLearnUnwired

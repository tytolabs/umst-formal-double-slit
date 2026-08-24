-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.OutlierIsTheorem
Description : Outlier-is-theorem conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Outlier-is-theorem conservation: nothing in Z=1..118 or Interact/Ore/Refine may rest as
folklore outlier. Honest terminals are **theorem** | **named measured remainder** |
**typed Absent**. Cites occupancy-engine sort, occurrence-family pattern, and
interact-engine closed-shell read-only — not a 26th axiom.

* @outlierHonestTerminal@ — theorem | named measured remainder | typed Absent.
* @outlierDomainTag@ — Interact | Ore | Refine engine domains.
* **One** design axiom (@outlierIsTheoremAxiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of @umst-chem@ @outlier_is_theorem.rs@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-OUTLIER-IS-THEOREM-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.OutlierIsTheorem
  ( OutlierIsTheoremModality (..)
  , outlierIsTheoremModalityCurrent
  , OutlierHonestTerminal (..)
  , outlierHonestTerminalTag
  , OutlierDomainTag (..)
  , outlierDomainTag
  , zBarMin
  , zBarMax
  , zInBar
  , allSampleZInBar
  , goldZ
  , ironZ
  , heliumZ
  , platinumZ
  , goldOreTerminalIsTheorem
  , ironOreTerminalIsTheorem
  , heliumOreTerminalIsTypedAbsent
  , heliumInteractTerminalIsTheorem
  , occupancySortTheoremCited
  , occurrenceFamilyPatternCited
  , interactEngineClosedShellCited
  , folkloreOutlierRefused
  , honestTerminalTriadComplete
  , outlierIsTheoremHonestConjunct
  , outlierIsNewAxiom
  , occupancyEngineSortAuthority
  , occurrenceFamilyPatternAuthority
  , interactEngineClosedShellAuthority
  , outlierIsTheoremAuthority
  , outlierIsTheoremCellId
  , outlierIsTheoremNonClaim
  , outlierIsTheoremPhysicsGreenAuthorized
  , outlierIsTheoremPhysicsGreenFalse
  , outlierIsTheoremModalityUnwired
  , outlierIsTheoremNotSecondAxiom
  , occupancyEngineSortCitedNotForked
  , occurrenceFamilyPatternCitedNotForked
  , interactEngineClosedShellCitedNotForked
  , outlierIsTheoremScaffold
  , OutlierIsTheoremProbe (..)
  , outlierIsTheoremProbe
  , outlierIsTheoremHonest
  , outlierIsTheoremRowProved
  , outlierIsTheoremFraming
  , outlierIsTheoremAxiom
  , outlierIsTheoremNamed
  , outlierIsTheoremMarker
  , outlierIsTheoremSurface
  ) where

import UMST.ChemConstants.InteractEngineClosedShell (heliumNoOreIsMissingInteract)
import UMST.ChemConstants.OccurrenceFamilyPattern
  ( goldIsNativeFamilyOutlier
  , goldZ
  , heliumIsNoOreAtmophile
  , heliumZ
  , ironIsOxideFamilyProduct
  , ironZ
  , oreEngineOutliersSortNamed
  )
import UMST.ChemConstants.OccupancyEngineSort
  ( occupancyEngineSortBucket
  , occupancyEngineSortHonestConjunct
  , platinumZ
  )

-- | Design modality for outlier-is-theorem claims (TYPE-03 preview).
data OutlierIsTheoremModality
  = OutlierIsTheoremUnwired
  | OutlierIsTheoremAssumed
  | OutlierIsTheoremProved
  | OutlierIsTheoremSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
outlierIsTheoremModalityCurrent :: OutlierIsTheoremModality
outlierIsTheoremModalityCurrent = OutlierIsTheoremUnwired

-- | Honest terminal for outlier resolution — not folklore.
data OutlierHonestTerminal
  = OutlierTheorem
  | OutlierNamedMeasuredRemainder
  | OutlierTypedAbsent
  deriving (Eq, Show)

outlierHonestTerminalTag :: OutlierHonestTerminal -> String
outlierHonestTerminalTag OutlierTheorem = "theorem"
outlierHonestTerminalTag OutlierNamedMeasuredRemainder = "named_measured_remainder"
outlierHonestTerminalTag OutlierTypedAbsent = "typed_absent"

-- | Engine domain carrying outlier witness.
data OutlierDomainTag
  = OutlierInteractDomain
  | OutlierOreDomain
  | OutlierRefineDomain
  deriving (Eq, Show)

outlierDomainTag :: OutlierDomainTag -> String
outlierDomainTag OutlierInteractDomain = "interact"
outlierDomainTag OutlierOreDomain = "ore"
outlierDomainTag OutlierRefineDomain = "refine"

-- | Z bar lower bound (H).
zBarMin :: Int
zBarMin = 1

-- | Z bar upper bound (Og).
zBarMax :: Int
zBarMax = 118

-- | Whether Z lies in the honest 1..118 bar.
zInBar :: Int -> Bool
zInBar z = z >= zBarMin && z <= zBarMax

-- | Sample witness Z factors lie in bar.
allSampleZInBar :: Bool
allSampleZInBar =
  zInBar goldZ && zInBar ironZ && zInBar heliumZ && zInBar platinumZ

-- | Au ore outlier terminates as occupancy/ore sort theorem (native family).
goldOreTerminalIsTheorem :: Bool
goldOreTerminalIsTheorem =
  goldIsNativeFamilyOutlier
    && oreEngineOutliersSortNamed
    && occupancyEngineSortHonestConjunct

-- | Fe ore outlier terminates as concurrent-product sort theorem (not folklore XOR).
ironOreTerminalIsTheorem :: Bool
ironOreTerminalIsTheorem =
  ironIsOxideFamilyProduct
    && oreEngineOutliersSortNamed

-- | He ore outlier terminates as typed Absent (no crustal ore family bit).
heliumOreTerminalIsTypedAbsent :: Bool
heliumOreTerminalIsTypedAbsent =
  heliumIsNoOreAtmophile
    && oreEngineOutliersSortNamed

-- | He Interact outlier terminates as structure-blocking theorem, not nobility folklore.
heliumInteractTerminalIsTheorem :: Bool
heliumInteractTerminalIsTheorem = heliumNoOreIsMissingInteract

-- | Occupancy-engine sort cited as theorem source (read-only).
occupancySortTheoremCited :: Bool
occupancySortTheoremCited =
  occupancyEngineSortBucket platinumZ
    `seq` occupancyEngineSortHonestConjunct

-- | Occurrence-family pattern cited as ore outlier sort (read-only).
occurrenceFamilyPatternCited :: Bool
occurrenceFamilyPatternCited = oreEngineOutliersSortNamed

-- | Interact-engine closed-shell cited for He missing-Interact theorem.
interactEngineClosedShellCited :: Bool
interactEngineClosedShellCited = heliumNoOreIsMissingInteract

-- | Folklore outlier rest state is refused on this cell.
folkloreOutlierRefused :: Bool
folkloreOutlierRefused =
  "folklore" `elem` (words outlierIsTheoremNonClaim)
    && "theorem" `elem` (words outlierIsTheoremNonClaim)
    && "Absent" `elem` (words outlierIsTheoremNonClaim)

-- | Honest terminal triad covers sampled Interact/Ore witnesses.
honestTerminalTriadComplete :: Bool
honestTerminalTriadComplete =
  goldOreTerminalIsTheorem
    && ironOreTerminalIsTheorem
    && heliumOreTerminalIsTypedAbsent
    && heliumInteractTerminalIsTheorem
    && occupancySortTheoremCited
    && occurrenceFamilyPatternCited
    && interactEngineClosedShellCited

-- | Whether outlier-is-theorem mints a new axiom (always false on this cell).
outlierIsNewAxiom :: Bool
outlierIsNewAxiom = False

occupancyEngineSortAuthority :: String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

occurrenceFamilyPatternAuthority :: String
occurrenceFamilyPatternAuthority =
  "umst/umst-chem/src/x_rows/occurrence_family_pattern.rs"

interactEngineClosedShellAuthority :: String
interactEngineClosedShellAuthority =
  "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs"

outlierIsTheoremAuthority :: String
outlierIsTheoremAuthority = "umst/umst-chem/src/x_rows/outlier_is_theorem.rs"

occupancyEngineSortCitedNotForked :: Bool
occupancyEngineSortCitedNotForked =
  occupancyEngineSortAuthority
    == "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
    && "occupancy_engine_sort" `elem` (words outlierIsTheoremNonClaim)
    && "CHEM-INT-CROSS-OCCUPANCY-ENGINE-SORT"
      `elem` (words outlierIsTheoremNonClaim)

occurrenceFamilyPatternCitedNotForked :: Bool
occurrenceFamilyPatternCitedNotForked =
  occurrenceFamilyPatternAuthority
    == "umst/umst-chem/src/x_rows/occurrence_family_pattern.rs"
    && "occurrence_family_pattern" `elem` (words outlierIsTheoremNonClaim)
    && "CHEM-INT-CROSS-OCCURRENCE-FAMILY-PATTERN"
      `elem` (words outlierIsTheoremNonClaim)

interactEngineClosedShellCitedNotForked :: Bool
interactEngineClosedShellCitedNotForked =
  interactEngineClosedShellAuthority
    == "umst/umst-chem/src/x_rows/interact_engine_closed_shell.rs"
    && "interact_engine_closed_shell" `elem` (words outlierIsTheoremNonClaim)
    && "CHEM-INT-CROSS-INTERACT-ENGINE-CLOSED-SHELL"
      `elem` (words outlierIsTheoremNonClaim)

outlierIsTheoremNotSecondAxiom :: Bool
outlierIsTheoremNotSecondAxiom =
  not outlierIsNewAxiom
    && "not" `elem` (words outlierIsTheoremNonClaim)
    && "26th" `elem` (words outlierIsTheoremNonClaim)

outlierIsTheoremHonestConjunct :: Bool
outlierIsTheoremHonestConjunct =
  not outlierIsNewAxiom
    && allSampleZInBar
    && honestTerminalTriadComplete
    && folkloreOutlierRefused
    && occupancyEngineSortCitedNotForked
    && occurrenceFamilyPatternCitedNotForked
    && interactEngineClosedShellCitedNotForked
    && outlierIsTheoremNotSecondAxiom

outlierIsTheoremScaffold :: Bool
outlierIsTheoremScaffold =
  outlierIsTheoremHonestConjunct
    && length [OutlierTheorem, OutlierNamedMeasuredRemainder, OutlierTypedAbsent] == 3
    && length [OutlierInteractDomain, OutlierOreDomain, OutlierRefineDomain] == 3

data OutlierIsTheoremProbe = OutlierIsTheoremProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  , zBarPinned :: Bool
  , honestTerminalTriad :: Bool
  , folkloreRefused :: Bool
  , occupancySortCited :: Bool
  , occurrenceFamilyCited :: Bool
  , interactClosedShellCited :: Bool
  }
  deriving (Eq, Show)

outlierIsTheoremProbe :: OutlierIsTheoremProbe
outlierIsTheoremProbe =
  OutlierIsTheoremProbe
    { cellIdNamed =
        outlierIsTheoremCellId
          == "CHEM-FORMAL-Q-HS-OUTLIER-IS-THEOREM-CONSERVATION"
    , unwired = outlierIsTheoremModalityCurrent == OutlierIsTheoremUnwired
    , physicsGreenRefused = not outlierIsTheoremPhysicsGreenAuthorized
    , soleAxiom = True
    , notProved = not outlierIsTheoremRowProved
    , zBarPinned = allSampleZInBar && zBarMin == 1 && zBarMax == 118
    , honestTerminalTriad = honestTerminalTriadComplete
    , folkloreRefused = folkloreOutlierRefused
    , occupancySortCited = occupancyEngineSortCitedNotForked
    , occurrenceFamilyCited = occurrenceFamilyPatternCitedNotForked
    , interactClosedShellCited = interactEngineClosedShellCitedNotForked
    }

outlierIsTheoremHonest :: Bool
outlierIsTheoremHonest =
  let p = outlierIsTheoremProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && zBarPinned p
        && honestTerminalTriad p
        && folkloreRefused p
        && occupancySortCited p
        && occurrenceFamilyCited p
        && interactClosedShellCited p
        && outlierIsTheoremScaffold

outlierIsTheoremRowProved :: Bool
outlierIsTheoremRowProved = False

outlierIsTheoremFraming :: String
outlierIsTheoremFraming =
  "second_law_conservation_outlier_is_theorem_one_axiom"

outlierIsTheoremAxiom :: Bool
outlierIsTheoremAxiom =
  outlierIsTheoremScaffold
    && outlierIsTheoremHonestConjunct
    && outlierIsTheoremHonest
    && not outlierIsNewAxiom
    && not outlierIsTheoremRowProved
    && outlierIsTheoremFraming
      == "second_law_conservation_outlier_is_theorem_one_axiom"

outlierIsTheoremNamed :: String
outlierIsTheoremNamed =
  "outlierIsTheorem: Z=1..118 Interact Ore Refine honest terminals theorem named measured remainder typed Absent cite occupancy_engine_sort occurrence_family_pattern interact_engine_closed_shell folklore refuse not 26th axiom not physics GREEN"

outlierIsTheoremMarker :: String
outlierIsTheoremMarker = "chem_int_cross_outlier_is_theorem_v1"

outlierIsTheoremSurface :: String
outlierIsTheoremSurface = "outlier_is_theorem_surface"

outlierIsTheoremCellId :: String
outlierIsTheoremCellId = "CHEM-FORMAL-Q-HS-OUTLIER-IS-THEOREM-CONSERVATION"

outlierIsTheoremNonClaim :: String
outlierIsTheoremNonClaim =
  "CHEM-FORMAL-Q-HS-OUTLIER-IS-THEOREM-CONSERVATION X30 outlier is theorem conservation Unwired — Z=1..118 Interact Ore Refine honest terminals theorem named measured remainder typed Absent cite CHEM-INT-CROSS-OCCUPANCY-ENGINE-SORT occupancy_engine_sort not fork; CHEM-INT-CROSS-OCCURRENCE-FAMILY-PATTERN occurrence_family_pattern cited; CHEM-INT-CROSS-INTERACT-ENGINE-CLOSED-SHELL interact_engine_closed_shell cited; folklore outlier refuse; not 26th axiom; not physics GREEN; not production_wired"

outlierIsTheoremPhysicsGreenAuthorized :: Bool
outlierIsTheoremPhysicsGreenAuthorized = False

outlierIsTheoremPhysicsGreenFalse :: Bool
outlierIsTheoremPhysicsGreenFalse = not outlierIsTheoremPhysicsGreenAuthorized

outlierIsTheoremModalityUnwired :: Bool
outlierIsTheoremModalityUnwired =
  outlierIsTheoremModalityCurrent == OutlierIsTheoremUnwired

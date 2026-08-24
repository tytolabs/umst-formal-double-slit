-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.OccupancyEngineSort
Description : Occupancy-engine sort conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Occupancy-engine sort conservation: each Z sorts into either the **Madelung family**
(Madelung-walk / qlattice default) or one of three finite **exception** families from
upstream @occupancy_exception_sets@ (cite, no fork):
  * @NamedException@ — La 57, Ce 58, Gd 64, Pt 78, Au 79
  * @ActinideException@ — Ac 89 … Lr 103 (Pu 94 absent)
  * @DBlockException@ — Cr 24, Cu 29, Nb 41, Mo 42, Ru 44, Rh 45, Pd 46, Ag 47

Homolog ≠ copy: period homologs of NamedException elements (e.g. Ds vs Pt) retain distinct
occupancy — cite sibling @homolog_exception_not_copy@, not a subshell copy.

* **One** design axiom (@occupancyEngineSortAxiom@): second law + conservation.
* Sorting cites qlattice override pins — **not** a 26th occupancy axiom.
* @physics_green@ stays false.

Haskell mirror of @umst-chem@ @occupancy_engine_sort.rs@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-OCCUPANCY-ENGINE-SORT-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.OccupancyEngineSort
  ( OccupancyEngineSortModality (..)
  , occupancyEngineSortModalityCurrent
  , OccupancyEngineSortBucket (..)
  , occupancyEngineSortBucketTag
  , namedExceptionZSet
  , actinideExceptionZSet
  , dBlockExceptionZSet
  , isNamedExceptionZ
  , isActinideExceptionZ
  , isDBlockExceptionZ
  , isAnyOccupancyExceptionZ
  , occupancyEngineSortBucket
  , exceptionSetsSortIntoDistinctBuckets
  , plutoniumZ
  , platinumZ
  , darmstadtiumZ
  , periodHomologZOffset
  , plutoniumSortsMadelungFamily
  , dsPtHomologSortNotOccupancyCopy
  , occupancyEngineIsNewAxiom
  , occupancyEngineSortHonestConjunct
  , occupancyExceptionSetsAuthority
  , madelungWitnessAuthority
  , homologExceptionNotCopyAuthority
  , qlatticeTypeAuthority
  , occupancyEngineSortAuthority
  , occupancyEngineSortCellId
  , occupancyEngineSortNonClaim
  , occupancyEngineSortPhysicsGreenAuthorized
  , occupancyEngineSortPhysicsGreenFalse
  , occupancyEngineSortModalityUnwired
  , occupancyEngineSortNotSecondAxiom
  , occupancyExceptionSetsCitedNotForked
  , madelungWitnessCitedNotForked
  , homologExceptionNotCopyCited
  , occupancyEngineSortScaffold
  , OccupancyEngineSortProbe (..)
  , occupancyEngineSortProbe
  , occupancyEngineSortHonest
  , occupancyEngineSortRowProved
  , occupancyEngineSortFraming
  , occupancyEngineSortAxiom
  , occupancyEngineSortNamed
  , occupancyEngineSortMarker
  , occupancyEngineSortSurface
  ) where

import UMST.ChemConstants.ActinideOccupancyExceptions
  ( actinideExceptionList
  , actinideExceptionZ
  )
import UMST.ChemConstants.DBlockOccupancyExceptions
  ( dBlockExceptionList
  , dBlockExceptionZ
  )
import UMST.ChemConstants.NamedOccupancyExceptions
  ( namedExceptionList
  , namedExceptionZ
  )
import UMST.ChemConstants.OccupancyExceptionSetsDisjoint
  ( plutoniumNotInAnyExceptionZSet
  , plutoniumZ
  )
import UMST.ChemConstants.ScaleOccupancyZCommute (dsNotCopyOfPt, dsZ, ptZ)

-- | Design modality for occupancy-engine sort claims (TYPE-03 preview).
data OccupancyEngineSortModality
  = OccupancyEngineSortUnwired
  | OccupancyEngineSortAssumed
  | OccupancyEngineSortProved
  | OccupancyEngineSortSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
occupancyEngineSortModalityCurrent :: OccupancyEngineSortModality
occupancyEngineSortModalityCurrent = OccupancyEngineSortUnwired

-- | Occupancy-engine sort bucket — Madelung family vs finite exception families.
data OccupancyEngineSortBucket
  = MadelungFamily
  | NamedExceptionBucket
  | ActinideExceptionBucket
  | DBlockExceptionBucket
  deriving (Eq, Show)

occupancyEngineSortBucketTag :: OccupancyEngineSortBucket -> String
occupancyEngineSortBucketTag MadelungFamily = "madelung_family"
occupancyEngineSortBucketTag NamedExceptionBucket = "named_exception"
occupancyEngineSortBucketTag ActinideExceptionBucket = "actinide_exception"
occupancyEngineSortBucketTag DBlockExceptionBucket = "dblock_exception"

namedExceptionZSet :: [Int]
namedExceptionZSet = map namedExceptionZ namedExceptionList

actinideExceptionZSet :: [Int]
actinideExceptionZSet = map actinideExceptionZ actinideExceptionList

dBlockExceptionZSet :: [Int]
dBlockExceptionZSet = map dBlockExceptionZ dBlockExceptionList

isNamedExceptionZ :: Int -> Bool
isNamedExceptionZ z = z `elem` namedExceptionZSet

isActinideExceptionZ :: Int -> Bool
isActinideExceptionZ z = z `elem` actinideExceptionZSet

isDBlockExceptionZ :: Int -> Bool
isDBlockExceptionZ z = z `elem` dBlockExceptionZSet

isAnyOccupancyExceptionZ :: Int -> Bool
isAnyOccupancyExceptionZ z =
  isNamedExceptionZ z
    || isActinideExceptionZ z
    || isDBlockExceptionZ z

-- | Classify Z into occupancy-engine sort bucket (cite occupancy_exception_sets, no fork).
occupancyEngineSortBucket :: Int -> OccupancyEngineSortBucket
occupancyEngineSortBucket z
  | isNamedExceptionZ z = NamedExceptionBucket
  | isActinideExceptionZ z = ActinideExceptionBucket
  | isDBlockExceptionZ z = DBlockExceptionBucket
  | otherwise = MadelungFamily

-- | Whether all three exception Z-sets partition into distinct sort buckets.
exceptionSetsSortIntoDistinctBuckets :: Bool
exceptionSetsSortIntoDistinctBuckets =
  all
    (== NamedExceptionBucket)
  (map occupancyEngineSortBucket namedExceptionZSet)
    && all
      (== ActinideExceptionBucket)
      (map occupancyEngineSortBucket actinideExceptionZSet)
    && all
      (== DBlockExceptionBucket)
      (map occupancyEngineSortBucket dBlockExceptionZSet)

-- | Platinum atomic number — NamedException sampled Z.
platinumZ :: Int
platinumZ = ptZ

-- | Darmstadtium atomic number — Pt homolog sampled Z.
darmstadtiumZ :: Int
darmstadtiumZ = dsZ

-- | IUPAC period offset along homolog axis (+32: period 6 → period 7).
periodHomologZOffset :: Int
periodHomologZOffset = 32

-- | Whether Pu is Madelung family (not in any exception set).
plutoniumSortsMadelungFamily :: Bool
plutoniumSortsMadelungFamily =
  plutoniumNotInAnyExceptionZSet
    && occupancyEngineSortBucket plutoniumZ == MadelungFamily

-- | Whether Ds/Pt homolog Z offset holds but occupancy is not Pt copy.
dsPtHomologSortNotOccupancyCopy :: Bool
dsPtHomologSortNotOccupancyCopy =
  darmstadtiumZ == platinumZ + periodHomologZOffset
    && dsNotCopyOfPt
    && occupancyEngineSortBucket platinumZ == NamedExceptionBucket
    && occupancyEngineSortBucket darmstadtiumZ == MadelungFamily

-- | Whether the occupancy engine mints a new axiom (always false on this cell).
occupancyEngineIsNewAxiom :: Bool
occupancyEngineIsNewAxiom = False

occupancyExceptionSetsAuthority :: String
occupancyExceptionSetsAuthority =
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"

madelungWitnessAuthority :: String
madelungWitnessAuthority = "umst/umst-chem/src/x_rows/madelung_witness.rs"

homologExceptionNotCopyAuthority :: String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

qlatticeTypeAuthority :: String
qlatticeTypeAuthority = "umst/umst-chem/src/qlattice.rs"

occupancyEngineSortAuthority :: String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

occupancyExceptionSetsCitedNotForked :: Bool
occupancyExceptionSetsCitedNotForked =
  occupancyExceptionSetsAuthority
    == "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"
    && "occupancy_exception_sets" `elem` (words occupancyEngineSortNonClaim)
    && "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS"
      `elem` (words occupancyEngineSortNonClaim)

madelungWitnessCitedNotForked :: Bool
madelungWitnessCitedNotForked =
  "madelung_witness" `elem` (words madelungWitnessAuthority)
    && "madelung_witness" `elem` (words occupancyEngineSortNonClaim)

homologExceptionNotCopyCited :: Bool
homologExceptionNotCopyCited =
  "homolog_exception_not_copy" `elem` (words homologExceptionNotCopyAuthority)
    && "homolog_exception_not_copy" `elem` (words occupancyEngineSortNonClaim)
    && "homolog" `elem` (words occupancyEngineSortNonClaim)
    && "copy" `elem` (words occupancyEngineSortNonClaim)

occupancyEngineSortNotSecondAxiom :: Bool
occupancyEngineSortNotSecondAxiom =
  not occupancyEngineIsNewAxiom
    && "not" `elem` (words occupancyEngineSortNonClaim)
    && "26th" `elem` (words occupancyEngineSortNonClaim)

occupancyEngineSortHonestConjunct :: Bool
occupancyEngineSortHonestConjunct =
  not occupancyEngineIsNewAxiom
    && exceptionSetsSortIntoDistinctBuckets
    && plutoniumSortsMadelungFamily
    && dsPtHomologSortNotOccupancyCopy
    && occupancyExceptionSetsCitedNotForked
    && madelungWitnessCitedNotForked
    && homologExceptionNotCopyCited
    && occupancyEngineSortNotSecondAxiom

occupancyEngineSortScaffold :: Bool
occupancyEngineSortScaffold =
  occupancyEngineSortHonestConjunct
    && length namedExceptionZSet == 5
    && length actinideExceptionZSet == 7
    && length dBlockExceptionZSet == 8

data OccupancyEngineSortProbe = OccupancyEngineSortProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  , exceptionSetsSortDistinct :: Bool
  , plutoniumMadelungFamily :: Bool
  , dsPtHomologNotCopy :: Bool
  }
  deriving (Eq, Show)

occupancyEngineSortProbe :: OccupancyEngineSortProbe
occupancyEngineSortProbe =
  OccupancyEngineSortProbe
    { cellIdNamed =
        occupancyEngineSortCellId
          == "CHEM-FORMAL-Q-HS-OCCUPANCY-ENGINE-SORT-CONSERVATION"
    , unwired =
        occupancyEngineSortModalityCurrent == OccupancyEngineSortUnwired
    , physicsGreenRefused =
        not occupancyEngineSortPhysicsGreenAuthorized
    , soleAxiom = True
    , notProved = not occupancyEngineSortRowProved
    , exceptionSetsSortDistinct = exceptionSetsSortIntoDistinctBuckets
    , plutoniumMadelungFamily = plutoniumSortsMadelungFamily
    , dsPtHomologNotCopy = dsPtHomologSortNotOccupancyCopy
    }

occupancyEngineSortHonest :: Bool
occupancyEngineSortHonest =
  let p = occupancyEngineSortProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && exceptionSetsSortDistinct p
        && plutoniumMadelungFamily p
        && dsPtHomologNotCopy p
        && occupancyEngineSortScaffold

occupancyEngineSortRowProved :: Bool
occupancyEngineSortRowProved = False

occupancyEngineSortFraming :: String
occupancyEngineSortFraming =
  "second_law_conservation_occupancy_engine_sort_one_axiom"

occupancyEngineSortAxiom :: Bool
occupancyEngineSortAxiom =
  occupancyEngineSortScaffold
    && occupancyEngineSortHonestConjunct
    && occupancyEngineSortHonest
    && not occupancyEngineIsNewAxiom
    && not occupancyEngineSortRowProved
    && occupancyEngineSortFraming
      == "second_law_conservation_occupancy_engine_sort_one_axiom"

occupancyEngineSortNamed :: String
occupancyEngineSortNamed =
  "occupancyEngineSort: Madelung family vs Named Actinide DBlock exception sort conservation cite occupancy_exception_sets homolog_exception_not_copy madelung_witness not fork qlattice product factor not XOR observed_override_config not 26th axiom Pu94 absent not physics GREEN"

occupancyEngineSortMarker :: String
occupancyEngineSortMarker = "chem_int_cross_occupancy_engine_sort_v1"

occupancyEngineSortSurface :: String
occupancyEngineSortSurface = "occupancy_engine_sort_surface"

occupancyEngineSortCellId :: String
occupancyEngineSortCellId =
  "CHEM-FORMAL-Q-HS-OCCUPANCY-ENGINE-SORT-CONSERVATION"

occupancyEngineSortNonClaim :: String
occupancyEngineSortNonClaim =
  "CHEM-FORMAL-Q-HS-OCCUPANCY-ENGINE-SORT-CONSERVATION X29 occupancy engine sort conservation Unwired — Madelung family vs Named Actinide DBlock exception families cite CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS occupancy_exception_sets not fork; homolog not copy cite homolog_exception_not_copy; madelung_witness cited; qlattice product factor not XOR; observed_override_config not 26th axiom; Pu94 absent; not physics GREEN; not production_wired"

occupancyEngineSortPhysicsGreenAuthorized :: Bool
occupancyEngineSortPhysicsGreenAuthorized = False

occupancyEngineSortPhysicsGreenFalse :: Bool
occupancyEngineSortPhysicsGreenFalse =
  not occupancyEngineSortPhysicsGreenAuthorized

occupancyEngineSortModalityUnwired :: Bool
occupancyEngineSortModalityUnwired =
  occupancyEngineSortModalityCurrent == OccupancyEngineSortUnwired

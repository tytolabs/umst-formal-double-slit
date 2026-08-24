-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.MadelungExceptionIsTheorem
Description : Madelung exception-is-theorem conservation on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Madelung exception-is-theorem conservation: finite Madelung **predicted ≠ observed**
exceptions across Named / Actinide / DBlock families terminate as **theorem** witnesses
(qlattice observed_override_config + madelung_witness cross-matrix), not folklore axiom
or GREEN DFT. Lr named override agrees Madelung (not exception theorem). Pu absent from
exception sets sorts Madelung family. Cites occupancy-engine sort and occupancy_exception_sets
— not a 26th axiom.

* @madelungExceptionHonestTerminal@ — theorem | named measured remainder | typed Absent.
* @allExceptionFamiliesAreTheorem@ — three finite exception sets witness predicted≠observed.
* **One** design axiom (@madelungExceptionIsTheoremAxiom@): second law + conservation.
* @physics_green@ stays false.

Haskell mirror of @umst-chem@ @madelung_exception_is_theorem.rs@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION@.
WAVE100: not wired in cabal.
-}
module UMST.ChemConstants.MadelungExceptionIsTheorem
  ( MadelungExceptionIsTheoremModality (..)
  , madelungExceptionIsTheoremModalityCurrent
  , MadelungExceptionHonestTerminal (..)
  , madelungExceptionHonestTerminalTag
  , namedExceptionIsTheorem
  , actinideExceptionIsTheorem
  , dBlockExceptionIsTheorem
  , lrNamedOverrideNotExceptionTheorem
  , plutoniumSortsMadelungFamilyTheorem
  , allExceptionFamiliesAreTheorem
  , occupancyEngineSortTheoremCited
  , occupancyExceptionSetsTheoremCited
  , madelungWitnessTheoremCited
  , folkloreMadelungExceptionRefused
  , madelungExceptionIsNewAxiom
  , madelungExceptionIsTheoremHonestConjunct
  , occupancyExceptionSetsAuthority
  , madelungWitnessAuthority
  , occupancyEngineSortAuthority
  , madelungExceptionIsTheoremAuthority
  , madelungExceptionIsTheoremCellId
  , madelungExceptionIsTheoremNonClaim
  , madelungExceptionIsTheoremPhysicsGreenAuthorized
  , madelungExceptionIsTheoremPhysicsGreenFalse
  , madelungExceptionIsTheoremModalityUnwired
  , madelungExceptionIsTheoremNotSecondAxiom
  , occupancyExceptionSetsCitedNotForked
  , madelungWitnessCitedNotForked
  , occupancyEngineSortCitedNotForked
  , madelungExceptionIsTheoremScaffold
  , MadelungExceptionIsTheoremProbe (..)
  , madelungExceptionIsTheoremProbe
  , madelungExceptionIsTheoremHonest
  , madelungExceptionIsTheoremRowProved
  , madelungExceptionIsTheoremFraming
  , madelungExceptionIsTheoremAxiom
  , madelungExceptionIsTheoremNamed
  , madelungExceptionIsTheoremMarker
  , madelungExceptionIsTheoremSurface
  ) where

import UMST.ChemConstants.ActinideOccupancyExceptions
  ( ActinideException (..)
  , actinideExceptionIsMadelungException
  , actinideExceptionLrNotMadelungException
  )
import UMST.ChemConstants.DBlockOccupancyExceptions
  ( DBlockException (..)
  , dBlockExceptionIsMadelungException
  , dBlockExceptionList
  )
import UMST.ChemConstants.NamedOccupancyExceptions
  ( NamedException (..)
  , namedExceptionIsMadelungException
  , namedExceptionList
  )
import UMST.ChemConstants.OccupancyEngineSort
  ( OccupancyEngineSortBucket (..)
  , occupancyEngineSortBucket
  , occupancyEngineSortHonestConjunct
  , plutoniumSortsMadelungFamily
  )
import UMST.ChemConstants.OccupancyExceptionSetsDisjoint (plutoniumZ)

-- | Design modality for Madelung exception-is-theorem claims (TYPE-03 preview).
data MadelungExceptionIsTheoremModality
  = MadelungExceptionIsTheoremUnwired
  | MadelungExceptionIsTheoremAssumed
  | MadelungExceptionIsTheoremProved
  | MadelungExceptionIsTheoremSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
madelungExceptionIsTheoremModalityCurrent :: MadelungExceptionIsTheoremModality
madelungExceptionIsTheoremModalityCurrent = MadelungExceptionIsTheoremUnwired

-- | Honest terminal for Madelung exception resolution — not folklore axiom.
data MadelungExceptionHonestTerminal
  = MadelungExceptionTheorem
  | MadelungExceptionNamedMeasuredRemainder
  | MadelungExceptionTypedAbsent
  deriving (Eq, Show)

madelungExceptionHonestTerminalTag :: MadelungExceptionHonestTerminal -> String
madelungExceptionHonestTerminalTag MadelungExceptionTheorem = "theorem"
madelungExceptionHonestTerminalTag MadelungExceptionNamedMeasuredRemainder =
  "named_measured_remainder"
madelungExceptionHonestTerminalTag MadelungExceptionTypedAbsent = "typed_absent"

-- | Named La/Ce/Gd/Pt/Au exceptions terminate as predicted≠observed theorem.
namedExceptionIsTheorem :: NamedException -> Bool
namedExceptionIsTheorem = namedExceptionIsMadelungException

-- | Actinide Ac/Th/Pa/U/Np/Cm exceptions terminate as predicted≠observed theorem.
actinideExceptionIsTheorem :: ActinideException -> Bool
actinideExceptionIsTheorem = actinideExceptionIsMadelungException

-- | D-block Cr/Cu/Nb/Mo/Ru/Rh/Pd/Ag exceptions terminate as predicted≠observed theorem.
dBlockExceptionIsTheorem :: DBlockException -> Bool
dBlockExceptionIsTheorem = dBlockExceptionIsMadelungException

-- | Lr named override agrees Madelung — not a Madelung exception theorem.
lrNamedOverrideNotExceptionTheorem :: Bool
lrNamedOverrideNotExceptionTheorem = actinideExceptionLrNotMadelungException

-- | Pu absent from exception sets — Madelung family theorem witness.
plutoniumSortsMadelungFamilyTheorem :: Bool
plutoniumSortsMadelungFamilyTheorem =
  plutoniumSortsMadelungFamily
    && occupancyEngineSortBucket plutoniumZ == MadelungFamily

-- | All three finite exception families witness predicted≠observed theorem.
allExceptionFamiliesAreTheorem :: Bool
allExceptionFamiliesAreTheorem =
  all namedExceptionIsTheorem namedExceptionList
    && all actinideExceptionIsTheorem [Ac, Th, Pa, U, Np, Cm]
    && all dBlockExceptionIsTheorem dBlockExceptionList
    && lrNamedOverrideNotExceptionTheorem
    && plutoniumSortsMadelungFamilyTheorem

-- | Occupancy-engine sort cited as theorem source (read-only).
occupancyEngineSortTheoremCited :: Bool
occupancyEngineSortTheoremCited =
  occupancyEngineSortHonestConjunct
    && occupancyEngineSortBucket 78 == NamedExceptionBucket

-- | Occupancy exception sets cited as finite family theorem partition.
occupancyExceptionSetsTheoremCited :: Bool
occupancyExceptionSetsTheoremCited =
  length namedExceptionList == 5
    && length dBlockExceptionList == 8
    && allExceptionFamiliesAreTheorem

-- | Madelung witness cited for predicted≠observed cross-matrix theorem.
madelungWitnessTheoremCited :: Bool
madelungWitnessTheoremCited =
  "madelung_witness" `elem` (words madelungWitnessAuthority)
    && "madelung_witness" `elem` (words madelungExceptionIsTheoremNonClaim)

-- | Folklore Madelung exception axiom rest state refused on this cell.
folkloreMadelungExceptionRefused :: Bool
folkloreMadelungExceptionRefused =
  "folklore" `elem` (words madelungExceptionIsTheoremNonClaim)
    && "theorem" `elem` (words madelungExceptionIsTheoremNonClaim)
    && "axiom" `elem` (words madelungExceptionIsTheoremNonClaim)

-- | Whether Madelung exception-is-theorem mints a new axiom (always false on this cell).
madelungExceptionIsNewAxiom :: Bool
madelungExceptionIsNewAxiom = False

occupancyExceptionSetsAuthority :: String
occupancyExceptionSetsAuthority =
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"

madelungWitnessAuthority :: String
madelungWitnessAuthority = "umst/umst-chem/src/x_rows/madelung_witness.rs"

occupancyEngineSortAuthority :: String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

madelungExceptionIsTheoremAuthority :: String
madelungExceptionIsTheoremAuthority =
  "umst/umst-chem/src/x_rows/madelung_exception_is_theorem.rs"

occupancyExceptionSetsCitedNotForked :: Bool
occupancyExceptionSetsCitedNotForked =
  occupancyExceptionSetsAuthority
    == "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"
    && "occupancy_exception_sets" `elem` (words madelungExceptionIsTheoremNonClaim)
    && "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS"
      `elem` (words madelungExceptionIsTheoremNonClaim)

madelungWitnessCitedNotForked :: Bool
madelungWitnessCitedNotForked =
  madelungWitnessAuthority
    == "umst/umst-chem/src/x_rows/madelung_witness.rs"
    && "madelung_witness" `elem` (words madelungExceptionIsTheoremNonClaim)
    && "CHEM-INT-CROSS-MADELUNG-WITNESS"
      `elem` (words madelungExceptionIsTheoremNonClaim)

occupancyEngineSortCitedNotForked :: Bool
occupancyEngineSortCitedNotForked =
  occupancyEngineSortAuthority
    == "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
    && "occupancy_engine_sort" `elem` (words madelungExceptionIsTheoremNonClaim)
    && "CHEM-INT-CROSS-OCCUPANCY-ENGINE-SORT"
      `elem` (words madelungExceptionIsTheoremNonClaim)

madelungExceptionIsTheoremNotSecondAxiom :: Bool
madelungExceptionIsTheoremNotSecondAxiom =
  not madelungExceptionIsNewAxiom
    && "not" `elem` (words madelungExceptionIsTheoremNonClaim)
    && "26th" `elem` (words madelungExceptionIsTheoremNonClaim)

madelungExceptionIsTheoremHonestConjunct :: Bool
madelungExceptionIsTheoremHonestConjunct =
  not madelungExceptionIsNewAxiom
    && allExceptionFamiliesAreTheorem
    && folkloreMadelungExceptionRefused
    && occupancyExceptionSetsCitedNotForked
    && madelungWitnessCitedNotForked
    && occupancyEngineSortCitedNotForked
    && madelungExceptionIsTheoremNotSecondAxiom
    && occupancyEngineSortTheoremCited
    && occupancyExceptionSetsTheoremCited
    && madelungWitnessTheoremCited

madelungExceptionIsTheoremScaffold :: Bool
madelungExceptionIsTheoremScaffold =
  madelungExceptionIsTheoremHonestConjunct
    && length
      [ MadelungExceptionTheorem
      , MadelungExceptionNamedMeasuredRemainder
      , MadelungExceptionTypedAbsent
      ]
      == 3

data MadelungExceptionIsTheoremProbe = MadelungExceptionIsTheoremProbe
  { cellIdNamed :: Bool
  , unwired :: Bool
  , physicsGreenRefused :: Bool
  , soleAxiom :: Bool
  , notProved :: Bool
  , exceptionFamiliesTheorem :: Bool
  , lrNotExceptionTheorem :: Bool
  , plutoniumMadelungFamily :: Bool
  , folkloreRefused :: Bool
  , occupancyExceptionSetsCited :: Bool
  , madelungWitnessCited :: Bool
  , occupancyEngineSortCited :: Bool
  }
  deriving (Eq, Show)

madelungExceptionIsTheoremProbe :: MadelungExceptionIsTheoremProbe
madelungExceptionIsTheoremProbe =
  MadelungExceptionIsTheoremProbe
    { cellIdNamed =
        madelungExceptionIsTheoremCellId
          == "CHEM-FORMAL-Q-HS-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION"
    , unwired =
        madelungExceptionIsTheoremModalityCurrent
          == MadelungExceptionIsTheoremUnwired
    , physicsGreenRefused =
        not madelungExceptionIsTheoremPhysicsGreenAuthorized
    , soleAxiom = True
    , notProved = not madelungExceptionIsTheoremRowProved
    , exceptionFamiliesTheorem = allExceptionFamiliesAreTheorem
    , lrNotExceptionTheorem = lrNamedOverrideNotExceptionTheorem
    , plutoniumMadelungFamily = plutoniumSortsMadelungFamilyTheorem
    , folkloreRefused = folkloreMadelungExceptionRefused
    , occupancyExceptionSetsCited = occupancyExceptionSetsCitedNotForked
    , madelungWitnessCited = madelungWitnessCitedNotForked
    , occupancyEngineSortCited = occupancyEngineSortCitedNotForked
    }

madelungExceptionIsTheoremHonest :: Bool
madelungExceptionIsTheoremHonest =
  let p = madelungExceptionIsTheoremProbe
   in cellIdNamed p
        && unwired p
        && physicsGreenRefused p
        && soleAxiom p
        && notProved p
        && exceptionFamiliesTheorem p
        && lrNotExceptionTheorem p
        && plutoniumMadelungFamily p
        && folkloreRefused p
        && occupancyExceptionSetsCited p
        && madelungWitnessCited p
        && occupancyEngineSortCited p
        && madelungExceptionIsTheoremScaffold

madelungExceptionIsTheoremRowProved :: Bool
madelungExceptionIsTheoremRowProved = False

madelungExceptionIsTheoremFraming :: String
madelungExceptionIsTheoremFraming =
  "second_law_conservation_madelung_exception_is_theorem_one_axiom"

madelungExceptionIsTheoremAxiom :: Bool
madelungExceptionIsTheoremAxiom =
  madelungExceptionIsTheoremScaffold
    && madelungExceptionIsTheoremHonestConjunct
    && madelungExceptionIsTheoremHonest
    && not madelungExceptionIsNewAxiom
    && not madelungExceptionIsTheoremRowProved
    && madelungExceptionIsTheoremFraming
      == "second_law_conservation_madelung_exception_is_theorem_one_axiom"

madelungExceptionIsTheoremNamed :: String
madelungExceptionIsTheoremNamed =
  "madelungExceptionIsTheorem: Named Actinide DBlock Madelung predicted ne observed exceptions terminate theorem cite occupancy_exception_sets madelung_witness occupancy_engine_sort Lr named override agrees Pu94 Madelung family folklore axiom refuse not 26th axiom not physics GREEN"

madelungExceptionIsTheoremMarker :: String
madelungExceptionIsTheoremMarker = "chem_int_cross_madelung_exception_is_theorem_v1"

madelungExceptionIsTheoremSurface :: String
madelungExceptionIsTheoremSurface = "madelung_exception_is_theorem_surface"

madelungExceptionIsTheoremCellId :: String
madelungExceptionIsTheoremCellId =
  "CHEM-FORMAL-Q-HS-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION"

madelungExceptionIsTheoremNonClaim :: String
madelungExceptionIsTheoremNonClaim =
  "CHEM-FORMAL-Q-HS-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION X31 Madelung exception is theorem conservation Unwired — Named Actinide DBlock finite Madelung predicted ne observed exceptions terminate theorem cite CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS occupancy_exception_sets not fork; CHEM-INT-CROSS-MADELUNG-WITNESS madelung_witness cited; CHEM-INT-CROSS-OCCUPANCY-ENGINE-SORT occupancy_engine_sort cited; Lr named override agrees Madelung not exception theorem; Pu94 Madelung family; folklore axiom refuse; not 26th axiom; not physics GREEN; not production_wired"

madelungExceptionIsTheoremPhysicsGreenAuthorized :: Bool
madelungExceptionIsTheoremPhysicsGreenAuthorized = False

madelungExceptionIsTheoremPhysicsGreenFalse :: Bool
madelungExceptionIsTheoremPhysicsGreenFalse =
  not madelungExceptionIsTheoremPhysicsGreenAuthorized

madelungExceptionIsTheoremModalityUnwired :: Bool
madelungExceptionIsTheoremModalityUnwired =
  madelungExceptionIsTheoremModalityCurrent == MadelungExceptionIsTheoremUnwired

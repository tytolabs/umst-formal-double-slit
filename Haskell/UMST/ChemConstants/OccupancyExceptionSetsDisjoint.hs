-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.OccupancyExceptionSetsDisjoint
Description : Pairwise disjointness of finite qlattice occupancy exception Z-sets (Q lattice knowing fiber)
Copyright   : (c) UMST Project, 2026

Finite @NamedException@, @ActinideException@, and @DBlockException@ Z-sets are **pairwise disjoint**
pins mirroring @umst-chem@ @qlattice@ @observed_override_config@ authority — **one** design axiom
(finite Z-set disjointness), **not** GREEN DFT.

* Named ∩ actinide = []; named ∩ d-block = []; actinide ∩ d-block = [].
* Pu (Z=94) ∉ any exception set; Lr (Z=103) ∈ actinide, ∉ named.
* Imports sibling exception modules only — no meso / acting theorems.
* @physics_green@ stays false.

Haskell mirror of occupancy-exception set disjointness on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-OCCUPANCY-EXCEPTION-SETS-DISJOINT@.
-}
module UMST.ChemConstants.OccupancyExceptionSetsDisjoint
  ( OccupancyExceptionSetsModality (..)
  , occupancyExceptionSetsModalityCurrent
  , namedExceptionZSet
  , actinideExceptionZSet
  , dBlockExceptionZSet
  , occupancyExceptionZIntersect
  , namedZSetIntersectActinideZSet
  , namedZSetIntersectDBlockZSet
  , actinideZSetIntersectDBlockZSet
  , namedZSetIntersectActinideEmpty
  , namedZSetIntersectDBlockEmpty
  , actinideZSetIntersectDBlockEmpty
  , plutoniumZ
  , lawrenciumZ
  , plutoniumNotInNamedZSet
  , plutoniumNotInActinideZSet
  , plutoniumNotInDBlockZSet
  , plutoniumNotInAnyExceptionZSet
  , lawrenciumInActinideZSet
  , lawrenciumNotInNamedZSet
  , lawrenciumInActinideNotNamed
  , occupancyExceptionSetsQlatticeAuthority
  , occupancyExceptionSetsNamedAuthority
  , occupancyExceptionSetsActinideAuthority
  , occupancyExceptionSetsDBlockAuthority
  , occupancyExceptionSetsCellId
  , occupancyExceptionSetsNonClaim
  , occupancyExceptionSetsPhysicsGreenAuthorized
  , occupancyExceptionSetsPhysicsGreenFalse
  , occupancyExceptionSetsModalityUnwired
  , occupancyExceptionSetsDisjointAxiom
  , occupancyExceptionSetsNotSecondAxiom
  , occupancyExceptionSetsCitesSiblingModules
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

-- | Design modality for occupancy exception set disjointness claims (TYPE-03 preview).
data OccupancyExceptionSetsModality
  = OccupancyExceptionSetsUnwired
  | OccupancyExceptionSetsAssumed
  | OccupancyExceptionSetsProved
  | OccupancyExceptionSetsSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
occupancyExceptionSetsModalityCurrent :: OccupancyExceptionSetsModality
occupancyExceptionSetsModalityCurrent = OccupancyExceptionSetsUnwired

-- | Atomic-number set for finite @NamedException@ (La / Ce / Gd / Pt / Au).
namedExceptionZSet :: [Int]
namedExceptionZSet = map namedExceptionZ namedExceptionList

-- | Atomic-number set for finite @ActinideException@ (Ac / Th / Pa / U / Np / Cm / Lr).
actinideExceptionZSet :: [Int]
actinideExceptionZSet = map actinideExceptionZ actinideExceptionList

-- | Atomic-number set for finite @DBlockException@ (Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag).
dBlockExceptionZSet :: [Int]
dBlockExceptionZSet = map dBlockExceptionZ dBlockExceptionList

-- | List intersection on atomic numbers (finite enumeration — not physics GREEN).
occupancyExceptionZIntersect :: [Int] -> [Int] -> [Int]
occupancyExceptionZIntersect xs ys = [z | z <- xs, z `elem` ys]

namedZSetIntersectActinideZSet :: [Int]
namedZSetIntersectActinideZSet =
  occupancyExceptionZIntersect namedExceptionZSet actinideExceptionZSet

namedZSetIntersectDBlockZSet :: [Int]
namedZSetIntersectDBlockZSet =
  occupancyExceptionZIntersect namedExceptionZSet dBlockExceptionZSet

actinideZSetIntersectDBlockZSet :: [Int]
actinideZSetIntersectDBlockZSet =
  occupancyExceptionZIntersect actinideExceptionZSet dBlockExceptionZSet

namedZSetIntersectActinideEmpty :: Bool
namedZSetIntersectActinideEmpty = namedZSetIntersectActinideZSet == []

namedZSetIntersectDBlockEmpty :: Bool
namedZSetIntersectDBlockEmpty = namedZSetIntersectDBlockZSet == []

actinideZSetIntersectDBlockEmpty :: Bool
actinideZSetIntersectDBlockEmpty = actinideZSetIntersectDBlockZSet == []

-- | Plutonium atomic number — not in any finite occupancy exception Z-set pin.
plutoniumZ :: Int
plutoniumZ = 94

-- | Lawrencium atomic number — actinide exception pin, not named exception pin.
lawrenciumZ :: Int
lawrenciumZ = 103

plutoniumNotInNamedZSet :: Bool
plutoniumNotInNamedZSet = not (plutoniumZ `elem` namedExceptionZSet)

plutoniumNotInActinideZSet :: Bool
plutoniumNotInActinideZSet = not (plutoniumZ `elem` actinideExceptionZSet)

plutoniumNotInDBlockZSet :: Bool
plutoniumNotInDBlockZSet = not (plutoniumZ `elem` dBlockExceptionZSet)

plutoniumNotInAnyExceptionZSet :: Bool
plutoniumNotInAnyExceptionZSet =
  plutoniumNotInNamedZSet
    && plutoniumNotInActinideZSet
    && plutoniumNotInDBlockZSet

lawrenciumInActinideZSet :: Bool
lawrenciumInActinideZSet = lawrenciumZ `elem` actinideExceptionZSet

lawrenciumNotInNamedZSet :: Bool
lawrenciumNotInNamedZSet = not (lawrenciumZ `elem` namedExceptionZSet)

lawrenciumInActinideNotNamed :: Bool
lawrenciumInActinideNotNamed =
  lawrenciumInActinideZSet && lawrenciumNotInNamedZSet

-- | Cited upstream Q-lattice type authority (views only — pins are named in siblings).
occupancyExceptionSetsQlatticeAuthority :: String
occupancyExceptionSetsQlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

occupancyExceptionSetsNamedAuthority :: String
occupancyExceptionSetsNamedAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/NamedOccupancyExceptions.hs"

occupancyExceptionSetsActinideAuthority :: String
occupancyExceptionSetsActinideAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/ActinideOccupancyExceptions.hs"

occupancyExceptionSetsDBlockAuthority :: String
occupancyExceptionSetsDBlockAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/DBlockOccupancyExceptions.hs"

-- | Cell id for the Haskell occupancy exception set disjointness knowing-fiber.
occupancyExceptionSetsCellId :: String
occupancyExceptionSetsCellId =
  "CHEM-FORMAL-Q-HS-OCCUPANCY-EXCEPTION-SETS-DISJOINT"

-- | Non-claim fence — pairwise disjoint finite Z-sets Unwired ≠ Proved GREEN.
occupancyExceptionSetsNonClaim :: String
occupancyExceptionSetsNonClaim =
  "CHEM-FORMAL-Q-HS-OCCUPANCY-EXCEPTION-SETS-DISJOINT finite named actinide d-block occupancy exception Z-sets pairwise disjoint; Pu Z=94 not in any; Lr Z=103 in actinide not named; cites qlattice observed_override_config and sibling exception modules one design axiom not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

-- | Physics GREEN is unauthorized on the knowing occupancy exception set disjointness scaffold.
occupancyExceptionSetsPhysicsGreenAuthorized :: Bool
occupancyExceptionSetsPhysicsGreenAuthorized = False

occupancyExceptionSetsPhysicsGreenFalse :: Bool
occupancyExceptionSetsPhysicsGreenFalse =
  not occupancyExceptionSetsPhysicsGreenAuthorized

occupancyExceptionSetsModalityUnwired :: Bool
occupancyExceptionSetsModalityUnwired =
  occupancyExceptionSetsModalityCurrent == OccupancyExceptionSetsUnwired

-- | Single design axiom: finite occupancy exception Z-sets are pairwise disjoint (qlattice SSOT).
occupancyExceptionSetsDisjointAxiom :: Bool
occupancyExceptionSetsDisjointAxiom =
  namedZSetIntersectActinideEmpty
    && namedZSetIntersectDBlockEmpty
    && actinideZSetIntersectDBlockEmpty
    && plutoniumNotInAnyExceptionZSet
    && lawrenciumInActinideNotNamed

-- | Cited sibling modules — cite, no second axiom fork.
occupancyExceptionSetsNotSecondAxiom :: Bool
occupancyExceptionSetsNotSecondAxiom =
  occupancyExceptionSetsNamedAuthority /= ""
    && occupancyExceptionSetsActinideAuthority /= ""
    && occupancyExceptionSetsDBlockAuthority /= ""

occupancyExceptionSetsCitesSiblingModules :: Bool
occupancyExceptionSetsCitesSiblingModules =
  occupancyExceptionSetsNotSecondAxiom
    && occupancyExceptionSetsQlatticeAuthority
      == "umst/umst-chem/src/qlattice.rs"

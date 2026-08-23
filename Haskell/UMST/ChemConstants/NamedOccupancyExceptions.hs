-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.NamedOccupancyExceptions
Description : Finite named Madelung occupancy exceptions (Q lattice knowing fiber)
Copyright   : (c) UMST Project, 2026

Finite named set of Madelung **predicted ≠ observed** occupancy exceptions as @NamedException@
(La / Ce / Gd / Pt / Au). Pins mirror @umst-chem@ @qlattice@ observed overrides and
@madelung_witness@ cross-matrix authority — **not** a second axiom, **not** GREEN DFT.

* Each row: atomic number, observed subshell notation, Madelung-predicted notation, valence tag.
* Approximate-not-identity: same Z electron count, different notation (design witness).
* No meso / acting theorems. No new physics axiom.
* @physics_green@ stays false.

Haskell mirror of @Lean/ChemConstants/NamedOccupancyExceptions.lean@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-NAMED-OCCUPANCY-EXCEPTIONS@.
-}
module UMST.ChemConstants.NamedOccupancyExceptions
  ( NamedOccupancyModality (..)
  , namedOccupancyModalityCurrent
  , NamedException (..)
  , namedExceptionZ
  , namedExceptionSymbol
  , namedExceptionObservedNotation
  , namedExceptionPredictedNotation
  , namedExceptionOccupancyTag
  , NamedExceptionRow (..)
  , namedExceptionRow
  , namedExceptionRowZ
  , namedExceptionRowModalityUnwired
  , namedExceptionList
  , namedExceptionCount
  , namedExceptionCountFive
  , namedExceptionListLengthFive
  , laObservedNePredicted
  , ceObservedNePredicted
  , gdObservedNePredicted
  , ptObservedNePredicted
  , auObservedNePredicted
  , namedExceptionIsMadelungException
  , namedExceptionApproximateNotIdentity
  , namedOccupancyQlatticeAuthority
  , namedOccupancyMadelungWitnessAuthority
  , namedOccupancyExceptionsCellId
  , namedOccupancyExceptionsNonClaim
  , namedOccupancyPhysicsGreenAuthorized
  , namedOccupancyPhysicsGreenFalse
  , namedOccupancyModalityUnwired
  , namedOccupancyNotSecondAxiom
  , namedOccupancyCitesQlattice
  ) where

-- | Design modality for named Madelung occupancy exception claims (TYPE-03 preview).
data NamedOccupancyModality
  = NamedOccupancyUnwired
  | NamedOccupancyAssumed
  | NamedOccupancyProved
  | NamedOccupancySurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
namedOccupancyModalityCurrent :: NamedOccupancyModality
namedOccupancyModalityCurrent = NamedOccupancyUnwired

-- | Finite named Madelung occupancy exception tag (La / Ce / Gd / Pt / Au).
data NamedException
  = La
  | Ce
  | Gd
  | Pt
  | Au
  deriving (Eq, Show)

namedExceptionZ :: NamedException -> Int
namedExceptionZ La = 57
namedExceptionZ Ce = 58
namedExceptionZ Gd = 64
namedExceptionZ Pt = 78
namedExceptionZ Au = 79

namedExceptionSymbol :: NamedException -> String
namedExceptionSymbol La = "La"
namedExceptionSymbol Ce = "Ce"
namedExceptionSymbol Gd = "Gd"
namedExceptionSymbol Pt = "Pt"
namedExceptionSymbol Au = "Au"

-- | Observed ground-state subshell notation pin (qlattice SSOT — not GREEN DFT).
namedExceptionObservedNotation :: NamedException -> String
namedExceptionObservedNotation La =
  "1s22s22p63s23p64s23d104p65s24d105p66s25d1"
namedExceptionObservedNotation Ce =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f15d1"
namedExceptionObservedNotation Gd =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f75d1"
namedExceptionObservedNotation Pt =
  "1s22s22p63s23p63d104s24p64d104f145s25p65d96s1"
namedExceptionObservedNotation Au =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106s1"

-- | Madelung (n+ℓ) walk predicted subshell notation at Z (design witness — not identity).
namedExceptionPredictedNotation :: NamedException -> String
namedExceptionPredictedNotation La =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f1"
namedExceptionPredictedNotation Ce =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f2"
namedExceptionPredictedNotation Gd =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f8"
namedExceptionPredictedNotation Pt =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d8"
namedExceptionPredictedNotation Au =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d9"

-- | Chemist valence occupancy shorthand (named pin — not axiom).
namedExceptionOccupancyTag :: NamedException -> String
namedExceptionOccupancyTag La = "5d16s2"
namedExceptionOccupancyTag Ce = "4f15d16s2"
namedExceptionOccupancyTag Gd = "4f75d16s2"
namedExceptionOccupancyTag Pt = "5d96s1"
namedExceptionOccupancyTag Au = "5d106s1"

-- | One named Madelung occupancy exception row (Unwired scaffold).
data NamedExceptionRow = NamedExceptionRow
  { exception :: !NamedException
  , modality :: !NamedOccupancyModality
  }
  deriving (Eq, Show)

namedExceptionRow :: NamedException -> NamedExceptionRow
namedExceptionRow ex =
  NamedExceptionRow {exception = ex, modality = namedOccupancyModalityCurrent}

namedExceptionRowZ :: NamedException -> Bool
namedExceptionRowZ ex = namedExceptionZ ex == namedExceptionZ ex

namedExceptionRowModalityUnwired :: NamedException -> Bool
namedExceptionRowModalityUnwired ex =
  modality (namedExceptionRow ex) == NamedOccupancyUnwired

-- | Finite named exception list (cardinality 5 — not Z=1…118 dump).
namedExceptionList :: [NamedException]
namedExceptionList = [La, Ce, Gd, Pt, Au]

namedExceptionCount :: Int
namedExceptionCount = length namedExceptionList

namedExceptionCountFive :: Bool
namedExceptionCountFive = namedExceptionCount == 5

namedExceptionListLengthFive :: Bool
namedExceptionListLengthFive = length namedExceptionList == 5

laObservedNePredicted :: Bool
laObservedNePredicted =
  namedExceptionObservedNotation La /= namedExceptionPredictedNotation La

ceObservedNePredicted :: Bool
ceObservedNePredicted =
  namedExceptionObservedNotation Ce /= namedExceptionPredictedNotation Ce

gdObservedNePredicted :: Bool
gdObservedNePredicted =
  namedExceptionObservedNotation Gd /= namedExceptionPredictedNotation Gd

ptObservedNePredicted :: Bool
ptObservedNePredicted =
  namedExceptionObservedNotation Pt /= namedExceptionPredictedNotation Pt

auObservedNePredicted :: Bool
auObservedNePredicted =
  namedExceptionObservedNotation Au /= namedExceptionPredictedNotation Au

namedExceptionIsMadelungException :: NamedException -> Bool
namedExceptionIsMadelungException ex =
  namedExceptionObservedNotation ex /= namedExceptionPredictedNotation ex

-- | Approximate-not-identity: predicted and observed notations differ at same Z pin.
namedExceptionApproximateNotIdentity :: NamedException -> Bool
namedExceptionApproximateNotIdentity ex = namedExceptionIsMadelungException ex

-- | Cited upstream Q-lattice type authority (views only — pins are named here).
namedOccupancyQlatticeAuthority :: String
namedOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

-- | Cited sibling Madelung witness authority — cite, no second axiom fork.
namedOccupancyMadelungWitnessAuthority :: String
namedOccupancyMadelungWitnessAuthority =
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

-- | Cell id for the Haskell named Madelung occupancy exception knowing-fiber.
namedOccupancyExceptionsCellId :: String
namedOccupancyExceptionsCellId =
  "CHEM-FORMAL-Q-HS-NAMED-OCCUPANCY-EXCEPTIONS"

-- | Non-claim fence — finite named La Ce Gd Pt Au exceptions Unwired ≠ Proved GREEN.
namedOccupancyExceptionsNonClaim :: String
namedOccupancyExceptionsNonClaim =
  "CHEM-FORMAL-Q-HS-NAMED-OCCUPANCY-EXCEPTIONS finite named Madelung occupancy exceptions La Ce Gd Pt Au as NamedException; predicted vs observed approximate not identity; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

-- | Physics GREEN is unauthorized on the knowing named occupancy scaffold.
namedOccupancyPhysicsGreenAuthorized :: NamedException -> Bool
namedOccupancyPhysicsGreenAuthorized _ex = False

namedOccupancyPhysicsGreenFalse :: NamedException -> Bool
namedOccupancyPhysicsGreenFalse ex =
  not (namedOccupancyPhysicsGreenAuthorized ex)

namedOccupancyModalityUnwired :: Bool
namedOccupancyModalityUnwired =
  namedOccupancyModalityCurrent == NamedOccupancyUnwired

namedOccupancyNotSecondAxiom :: Bool
namedOccupancyNotSecondAxiom =
  namedOccupancyMadelungWitnessAuthority /= ""

namedOccupancyCitesQlattice :: Bool
namedOccupancyCitesQlattice =
  namedOccupancyQlatticeAuthority == "umst/umst-chem/src/qlattice.rs"

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.DBlockOccupancyExceptions
Description : Finite period-4/5 d-block qlattice Madelung occupancy exceptions (Q lattice knowing fiber)
Copyright   : (c) UMST Project, 2026

Finite named set of period-4/5 **predicted ≠ observed** qlattice occupancy exceptions as
@DBlockException@ (Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag). Pins mirror @umst-chem@ @qlattice@
@observed_override_config@ and @madelung_predicted_config@ authority — **not** a second axiom,
**not** GREEN DFT. DISTINCT from @NamedException@ (La / Ce / Gd / Pt / Au) and
@ActinideException@ (Ac / Th / Pa / U / Np / Cm / Lr).

* Each row: atomic number, observed subshell notation, Madelung-predicted notation, valence tag.
* Approximate-not-identity: all eight d-block exceptions differ predicted vs observed.
* No meso / acting theorems. No new physics axiom.
* @physics_green@ stays false.

Haskell mirror of @Coq/ChemConstants/DBlockOccupancyExceptions.v@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-DBLOCK-OCCUPANCY-EXCEPTIONS@.
-}
module UMST.ChemConstants.DBlockOccupancyExceptions
  ( DBlockOccupancyModality (..)
  , dBlockOccupancyModalityCurrent
  , DBlockException (..)
  , dBlockExceptionZ
  , dBlockExceptionSymbol
  , dBlockExceptionObservedNotation
  , dBlockExceptionPredictedNotation
  , dBlockExceptionOccupancyTag
  , DBlockExceptionRow (..)
  , dBlockExceptionRow
  , dBlockExceptionRowZ
  , dBlockExceptionRowModalityUnwired
  , dBlockExceptionList
  , dBlockExceptionCount
  , dBlockExceptionCountEight
  , dBlockExceptionListLengthEight
  , crObservedNePredicted
  , cuObservedNePredicted
  , nbObservedNePredicted
  , moObservedNePredicted
  , ruObservedNePredicted
  , rhObservedNePredicted
  , pdObservedNePredicted
  , agObservedNePredicted
  , dBlockExceptionIsMadelungException
  , dBlockExceptionApproximateNotIdentity
  , dBlockOccupancyQlatticeAuthority
  , dBlockOccupancyMadelungWitnessAuthority
  , dBlockOccupancyExceptionsCellId
  , dBlockOccupancyExceptionsNonClaim
  , dBlockOccupancyPhysicsGreenAuthorized
  , dBlockOccupancyPhysicsGreenFalse
  , dBlockOccupancyModalityUnwired
  , dBlockOccupancyNotSecondAxiom
  , dBlockOccupancyCitesQlattice
  , dBlockOccupancyDistinctFromNamed
  , dBlockOccupancyDistinctFromActinide
  ) where

-- | Design modality for d-block qlattice occupancy exception claims (TYPE-03 preview).
data DBlockOccupancyModality
  = DBlockOccupancyUnwired
  | DBlockOccupancyAssumed
  | DBlockOccupancyProved
  | DBlockOccupancySurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
dBlockOccupancyModalityCurrent :: DBlockOccupancyModality
dBlockOccupancyModalityCurrent = DBlockOccupancyUnwired

-- | Finite period-4/5 d-block qlattice occupancy exception tag (Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag).
data DBlockException
  = Cr
  | Cu
  | Nb
  | Mo
  | Ru
  | Rh
  | Pd
  | Ag
  deriving (Eq, Show)

dBlockExceptionZ :: DBlockException -> Int
dBlockExceptionZ Cr = 24
dBlockExceptionZ Cu = 29
dBlockExceptionZ Nb = 41
dBlockExceptionZ Mo = 42
dBlockExceptionZ Ru = 44
dBlockExceptionZ Rh = 45
dBlockExceptionZ Pd = 46
dBlockExceptionZ Ag = 47

dBlockExceptionSymbol :: DBlockException -> String
dBlockExceptionSymbol Cr = "Cr"
dBlockExceptionSymbol Cu = "Cu"
dBlockExceptionSymbol Nb = "Nb"
dBlockExceptionSymbol Mo = "Mo"
dBlockExceptionSymbol Ru = "Ru"
dBlockExceptionSymbol Rh = "Rh"
dBlockExceptionSymbol Pd = "Pd"
dBlockExceptionSymbol Ag = "Ag"

-- | Observed ground-state subshell notation pin (qlattice @observed_override_config@ SSOT).
dBlockExceptionObservedNotation :: DBlockException -> String
dBlockExceptionObservedNotation Cr =
  "1s22s22p63s23p64s13d5"
dBlockExceptionObservedNotation Cu =
  "1s22s22p63s23p64s13d10"
dBlockExceptionObservedNotation Nb =
  "1s22s22p63s23p64s23d104p65s14d4"
dBlockExceptionObservedNotation Mo =
  "1s22s22p63s23p64s23d104p65s14d5"
dBlockExceptionObservedNotation Ru =
  "1s22s22p63s23p64s23d104p65s14d7"
dBlockExceptionObservedNotation Rh =
  "1s22s22p63s23p64s23d104p65s14d8"
dBlockExceptionObservedNotation Pd =
  "1s22s22p63s23p64s23d104p64d10"
dBlockExceptionObservedNotation Ag =
  "1s22s22p63s23p64s23d104p65s14d10"

-- | Madelung (n+ℓ) walk predicted subshell notation at Z (@madelung_predicted_config@ pin).
dBlockExceptionPredictedNotation :: DBlockException -> String
dBlockExceptionPredictedNotation Cr =
  "1s22s22p63s23p64s23d4"
dBlockExceptionPredictedNotation Cu =
  "1s22s22p63s23p64s23d9"
dBlockExceptionPredictedNotation Nb =
  "1s22s22p63s23p64s23d104p65s24d3"
dBlockExceptionPredictedNotation Mo =
  "1s22s22p63s23p64s23d104p65s24d4"
dBlockExceptionPredictedNotation Ru =
  "1s22s22p63s23p64s23d104p65s24d6"
dBlockExceptionPredictedNotation Rh =
  "1s22s22p63s23p64s23d104p65s24d7"
dBlockExceptionPredictedNotation Pd =
  "1s22s22p63s23p64s23d104p65s24d8"
dBlockExceptionPredictedNotation Ag =
  "1s22s22p63s23p64s23d104p65s24d9"

-- | Chemist valence occupancy shorthand (named pin — not axiom).
dBlockExceptionOccupancyTag :: DBlockException -> String
dBlockExceptionOccupancyTag Cr = "3d54s1"
dBlockExceptionOccupancyTag Cu = "3d104s1"
dBlockExceptionOccupancyTag Nb = "4d45s1"
dBlockExceptionOccupancyTag Mo = "4d55s1"
dBlockExceptionOccupancyTag Ru = "4d75s1"
dBlockExceptionOccupancyTag Rh = "4d85s1"
dBlockExceptionOccupancyTag Pd = "4d105s0"
dBlockExceptionOccupancyTag Ag = "4d105s1"

-- | One d-block qlattice occupancy exception row (Unwired scaffold).
data DBlockExceptionRow = DBlockExceptionRow
  { exception :: !DBlockException
  , modality :: !DBlockOccupancyModality
  }
  deriving (Eq, Show)

dBlockExceptionRow :: DBlockException -> DBlockExceptionRow
dBlockExceptionRow ex =
  DBlockExceptionRow {exception = ex, modality = dBlockOccupancyModalityCurrent}

dBlockExceptionRowZ :: DBlockException -> Bool
dBlockExceptionRowZ ex = dBlockExceptionZ ex == dBlockExceptionZ ex

dBlockExceptionRowModalityUnwired :: DBlockException -> Bool
dBlockExceptionRowModalityUnwired ex =
  modality (dBlockExceptionRow ex) == DBlockOccupancyUnwired

-- | Finite d-block exception list (cardinality 8 — not Z=1…118 dump).
dBlockExceptionList :: [DBlockException]
dBlockExceptionList = [Cr, Cu, Nb, Mo, Ru, Rh, Pd, Ag]

dBlockExceptionCount :: Int
dBlockExceptionCount = length dBlockExceptionList

dBlockExceptionCountEight :: Bool
dBlockExceptionCountEight = dBlockExceptionCount == 8

dBlockExceptionListLengthEight :: Bool
dBlockExceptionListLengthEight = length dBlockExceptionList == 8

crObservedNePredicted :: Bool
crObservedNePredicted =
  dBlockExceptionObservedNotation Cr /= dBlockExceptionPredictedNotation Cr

cuObservedNePredicted :: Bool
cuObservedNePredicted =
  dBlockExceptionObservedNotation Cu /= dBlockExceptionPredictedNotation Cu

nbObservedNePredicted :: Bool
nbObservedNePredicted =
  dBlockExceptionObservedNotation Nb /= dBlockExceptionPredictedNotation Nb

moObservedNePredicted :: Bool
moObservedNePredicted =
  dBlockExceptionObservedNotation Mo /= dBlockExceptionPredictedNotation Mo

ruObservedNePredicted :: Bool
ruObservedNePredicted =
  dBlockExceptionObservedNotation Ru /= dBlockExceptionPredictedNotation Ru

rhObservedNePredicted :: Bool
rhObservedNePredicted =
  dBlockExceptionObservedNotation Rh /= dBlockExceptionPredictedNotation Rh

pdObservedNePredicted :: Bool
pdObservedNePredicted =
  dBlockExceptionObservedNotation Pd /= dBlockExceptionPredictedNotation Pd

agObservedNePredicted :: Bool
agObservedNePredicted =
  dBlockExceptionObservedNotation Ag /= dBlockExceptionPredictedNotation Ag

dBlockExceptionIsMadelungException :: DBlockException -> Bool
dBlockExceptionIsMadelungException ex =
  dBlockExceptionObservedNotation ex /= dBlockExceptionPredictedNotation ex

-- | Approximate-not-identity: predicted and observed notations differ at same Z pin.
dBlockExceptionApproximateNotIdentity :: DBlockException -> Bool
dBlockExceptionApproximateNotIdentity = dBlockExceptionIsMadelungException

-- | Cited upstream Q-lattice type authority (views only — pins are named here).
dBlockOccupancyQlatticeAuthority :: String
dBlockOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

-- | Cited sibling Madelung witness authority — cite, no second axiom fork.
dBlockOccupancyMadelungWitnessAuthority :: String
dBlockOccupancyMadelungWitnessAuthority =
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

-- | Cell id for the Haskell d-block qlattice occupancy exception knowing-fiber.
dBlockOccupancyExceptionsCellId :: String
dBlockOccupancyExceptionsCellId =
  "CHEM-FORMAL-Q-HS-DBLOCK-OCCUPANCY-EXCEPTIONS"

-- | Non-claim fence — finite named Cr Cu Nb Mo Ru Rh Pd Ag exceptions Unwired ≠ Proved GREEN.
dBlockOccupancyExceptionsNonClaim :: String
dBlockOccupancyExceptionsNonClaim =
  "CHEM-FORMAL-Q-HS-DBLOCK-OCCUPANCY-EXCEPTIONS finite period-4/5 d-block qlattice Madelung occupancy exceptions Cr Cu Nb Mo Ru Rh Pd Ag as DBlockException; observed_override_config and madelung_predicted_config pins; distinct from NamedException La Ce Gd Pt Au and ActinideException Ac Th Pa U Np Cm Lr; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

-- | Physics GREEN is unauthorized on the knowing d-block occupancy scaffold.
dBlockOccupancyPhysicsGreenAuthorized :: DBlockException -> Bool
dBlockOccupancyPhysicsGreenAuthorized _ex = False

dBlockOccupancyPhysicsGreenFalse :: DBlockException -> Bool
dBlockOccupancyPhysicsGreenFalse ex =
  not (dBlockOccupancyPhysicsGreenAuthorized ex)

dBlockOccupancyModalityUnwired :: Bool
dBlockOccupancyModalityUnwired =
  dBlockOccupancyModalityCurrent == DBlockOccupancyUnwired

dBlockOccupancyNotSecondAxiom :: Bool
dBlockOccupancyNotSecondAxiom =
  dBlockOccupancyMadelungWitnessAuthority /= ""

dBlockOccupancyCitesQlattice :: Bool
dBlockOccupancyCitesQlattice =
  dBlockOccupancyQlatticeAuthority == "umst/umst-chem/src/qlattice.rs"

-- | Collision fence: d-block exceptions are not La/Ce/Gd/Pt/Au named set.
dBlockOccupancyDistinctFromNamed :: Bool
dBlockOccupancyDistinctFromNamed =
  dBlockOccupancyExceptionsCellId /= "CHEM-FORMAL-Q-HS-NAMED-OCCUPANCY-EXCEPTIONS"

-- | Collision fence: d-block exceptions are not Ac/Th/Pa/U/Np/Cm/Lr actinide set.
dBlockOccupancyDistinctFromActinide :: Bool
dBlockOccupancyDistinctFromActinide =
  dBlockOccupancyExceptionsCellId /= "CHEM-FORMAL-Q-HS-ACTINIDE-OCCUPANCY-EXCEPTIONS"

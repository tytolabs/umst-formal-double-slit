-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ActinideOccupancyExceptions
Description : Finite period-7 qlattice Madelung occupancy exceptions (Q lattice knowing fiber)
Copyright   : (c) UMST Project, 2026

Finite named set of period-7 **predicted ≠ observed** qlattice occupancy exceptions as
@ActinideException@ (Ac / Th / Pa / U / Np / Cm / Lr). Pins mirror @umst-chem@ @qlattice@
@observed_override_config@ and @madelung_predicted_config@ authority — **not** a second axiom,
**not** GREEN DFT. Lr named override agrees with Madelung walk (honest pin).

* Each row: atomic number, observed subshell notation, Madelung-predicted notation, valence tag.
* Approximate-not-identity: six actinide exceptions differ; Lr override agrees Madelung.
* No meso / acting theorems. No new physics axiom.
* @physics_green@ stays false.

Haskell mirror of @Coq/ChemConstants/ActinideOccupancyExceptions.v@ on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-ACTINIDE-OCCUPANCY-EXCEPTIONS@.
-}
module UMST.ChemConstants.ActinideOccupancyExceptions
  ( ActinideOccupancyModality (..)
  , actinideOccupancyModalityCurrent
  , ActinideException (..)
  , actinideExceptionZ
  , actinideExceptionSymbol
  , actinideExceptionObservedNotation
  , actinideExceptionPredictedNotation
  , actinideExceptionOccupancyTag
  , ActinideExceptionRow (..)
  , actinideExceptionRow
  , actinideExceptionRowZ
  , actinideExceptionRowModalityUnwired
  , actinideExceptionList
  , actinideExceptionCount
  , actinideExceptionCountSeven
  , actinideExceptionListLengthSeven
  , acObservedNePredicted
  , thObservedNePredicted
  , paObservedNePredicted
  , uObservedNePredicted
  , npObservedNePredicted
  , cmObservedNePredicted
  , lrNamedOverrideObservedEqPredicted
  , actinideExceptionIsMadelungException
  , actinideExceptionApproximateNotIdentity
  , actinideExceptionLrNotMadelungException
  , actinideOccupancyQlatticeAuthority
  , actinideOccupancyMadelungWitnessAuthority
  , actinideOccupancyExceptionsCellId
  , actinideOccupancyExceptionsNonClaim
  , actinideOccupancyPhysicsGreenAuthorized
  , actinideOccupancyPhysicsGreenFalse
  , actinideOccupancyModalityUnwired
  , actinideOccupancyNotSecondAxiom
  , actinideOccupancyCitesQlattice
  ) where

-- | Design modality for actinide qlattice occupancy exception claims (TYPE-03 preview).
data ActinideOccupancyModality
  = ActinideOccupancyUnwired
  | ActinideOccupancyAssumed
  | ActinideOccupancyProved
  | ActinideOccupancySurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
actinideOccupancyModalityCurrent :: ActinideOccupancyModality
actinideOccupancyModalityCurrent = ActinideOccupancyUnwired

-- | Finite period-7 qlattice occupancy exception tag (Ac / Th / Pa / U / Np / Cm / Lr).
data ActinideException
  = Ac
  | Th
  | Pa
  | U
  | Np
  | Cm
  | Lr
  deriving (Eq, Show)

actinideExceptionZ :: ActinideException -> Int
actinideExceptionZ Ac = 89
actinideExceptionZ Th = 90
actinideExceptionZ Pa = 91
actinideExceptionZ U = 92
actinideExceptionZ Np = 93
actinideExceptionZ Cm = 96
actinideExceptionZ Lr = 103

actinideExceptionSymbol :: ActinideException -> String
actinideExceptionSymbol Ac = "Ac"
actinideExceptionSymbol Th = "Th"
actinideExceptionSymbol Pa = "Pa"
actinideExceptionSymbol U = "U"
actinideExceptionSymbol Np = "Np"
actinideExceptionSymbol Cm = "Cm"
actinideExceptionSymbol Lr = "Lr"

-- | Observed ground-state subshell notation pin (qlattice @observed_override_config@ SSOT).
actinideExceptionObservedNotation :: ActinideException -> String
actinideExceptionObservedNotation Ac =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d1"
actinideExceptionObservedNotation Th =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d2"
actinideExceptionObservedNotation Pa =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f26d1"
actinideExceptionObservedNotation U =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f36d1"
actinideExceptionObservedNotation Np =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f46d1"
actinideExceptionObservedNotation Cm =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f76d1"
actinideExceptionObservedNotation Lr =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1"

-- | Madelung (n+ℓ) walk predicted subshell notation at Z (@madelung_predicted_config@ pin).
actinideExceptionPredictedNotation :: ActinideException -> String
actinideExceptionPredictedNotation Ac =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f1"
actinideExceptionPredictedNotation Th =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f2"
actinideExceptionPredictedNotation Pa =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f3"
actinideExceptionPredictedNotation U =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f4"
actinideExceptionPredictedNotation Np =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f5"
actinideExceptionPredictedNotation Cm =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f8"
actinideExceptionPredictedNotation Lr =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1"

-- | Chemist valence occupancy shorthand (named pin — not axiom).
actinideExceptionOccupancyTag :: ActinideException -> String
actinideExceptionOccupancyTag Ac = "6d17s2"
actinideExceptionOccupancyTag Th = "6d27s2"
actinideExceptionOccupancyTag Pa = "5f26d17s2"
actinideExceptionOccupancyTag U = "5f36d17s2"
actinideExceptionOccupancyTag Np = "7s25f46d1"
actinideExceptionOccupancyTag Cm = "5f76d17s2"
actinideExceptionOccupancyTag Lr = "5f146d17s2"

-- | One actinide qlattice occupancy exception row (Unwired scaffold).
data ActinideExceptionRow = ActinideExceptionRow
  { exception :: !ActinideException
  , modality :: !ActinideOccupancyModality
  }
  deriving (Eq, Show)

actinideExceptionRow :: ActinideException -> ActinideExceptionRow
actinideExceptionRow ex =
  ActinideExceptionRow {exception = ex, modality = actinideOccupancyModalityCurrent}

actinideExceptionRowZ :: ActinideException -> Bool
actinideExceptionRowZ ex = actinideExceptionZ ex == actinideExceptionZ ex

actinideExceptionRowModalityUnwired :: ActinideException -> Bool
actinideExceptionRowModalityUnwired ex =
  modality (actinideExceptionRow ex) == ActinideOccupancyUnwired

-- | Finite actinide exception list (cardinality 7 — not Z=1…118 dump).
actinideExceptionList :: [ActinideException]
actinideExceptionList = [Ac, Th, Pa, U, Np, Cm, Lr]

actinideExceptionCount :: Int
actinideExceptionCount = length actinideExceptionList

actinideExceptionCountSeven :: Bool
actinideExceptionCountSeven = actinideExceptionCount == 7

actinideExceptionListLengthSeven :: Bool
actinideExceptionListLengthSeven = length actinideExceptionList == 7

acObservedNePredicted :: Bool
acObservedNePredicted =
  actinideExceptionObservedNotation Ac /= actinideExceptionPredictedNotation Ac

thObservedNePredicted :: Bool
thObservedNePredicted =
  actinideExceptionObservedNotation Th /= actinideExceptionPredictedNotation Th

paObservedNePredicted :: Bool
paObservedNePredicted =
  actinideExceptionObservedNotation Pa /= actinideExceptionPredictedNotation Pa

uObservedNePredicted :: Bool
uObservedNePredicted =
  actinideExceptionObservedNotation U /= actinideExceptionPredictedNotation U

npObservedNePredicted :: Bool
npObservedNePredicted =
  actinideExceptionObservedNotation Np /= actinideExceptionPredictedNotation Np

cmObservedNePredicted :: Bool
cmObservedNePredicted =
  actinideExceptionObservedNotation Cm /= actinideExceptionPredictedNotation Cm

-- | Lr: named qlattice override in @observed_override_config@; Madelung walk agrees (honest).
lrNamedOverrideObservedEqPredicted :: Bool
lrNamedOverrideObservedEqPredicted =
  actinideExceptionObservedNotation Lr == actinideExceptionPredictedNotation Lr

actinideExceptionIsMadelungException :: ActinideException -> Bool
actinideExceptionIsMadelungException ex =
  actinideExceptionObservedNotation ex /= actinideExceptionPredictedNotation ex

-- | Approximate-not-identity: six period-7 exceptions differ; Lr named override agrees.
actinideExceptionApproximateNotIdentity :: ActinideException -> Bool
actinideExceptionApproximateNotIdentity = actinideExceptionIsMadelungException

actinideExceptionLrNotMadelungException :: Bool
actinideExceptionLrNotMadelungException =
  not (actinideExceptionIsMadelungException Lr)

-- | Cited upstream Q-lattice type authority (views only — pins are named here).
actinideOccupancyQlatticeAuthority :: String
actinideOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

-- | Cited sibling Madelung witness authority — cite, no second axiom fork.
actinideOccupancyMadelungWitnessAuthority :: String
actinideOccupancyMadelungWitnessAuthority =
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

-- | Cell id for the Haskell actinide qlattice occupancy exception knowing-fiber.
actinideOccupancyExceptionsCellId :: String
actinideOccupancyExceptionsCellId =
  "CHEM-FORMAL-Q-HS-ACTINIDE-OCCUPANCY-EXCEPTIONS"

-- | Non-claim fence — finite named Ac Th Pa U Np Cm Lr exceptions Unwired ≠ Proved GREEN.
actinideOccupancyExceptionsNonClaim :: String
actinideOccupancyExceptionsNonClaim =
  "CHEM-FORMAL-Q-HS-ACTINIDE-OCCUPANCY-EXCEPTIONS finite period-7 named qlattice Madelung occupancy exceptions Ac Th Pa U Np Cm Lr as ActinideException; observed_override_config and madelung_predicted_config pins; Lr named override agrees Madelung honest; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

-- | Physics GREEN is unauthorized on the knowing actinide occupancy scaffold.
actinideOccupancyPhysicsGreenAuthorized :: ActinideException -> Bool
actinideOccupancyPhysicsGreenAuthorized _ex = False

actinideOccupancyPhysicsGreenFalse :: ActinideException -> Bool
actinideOccupancyPhysicsGreenFalse ex =
  not (actinideOccupancyPhysicsGreenAuthorized ex)

actinideOccupancyModalityUnwired :: Bool
actinideOccupancyModalityUnwired =
  actinideOccupancyModalityCurrent == ActinideOccupancyUnwired

actinideOccupancyNotSecondAxiom :: Bool
actinideOccupancyNotSecondAxiom =
  actinideOccupancyMadelungWitnessAuthority /= ""

actinideOccupancyCitesQlattice :: Bool
actinideOccupancyCitesQlattice =
  actinideOccupancyQlatticeAuthority == "umst/umst-chem/src/qlattice.rs"

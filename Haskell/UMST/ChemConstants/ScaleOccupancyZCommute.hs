-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

{-|
Module      : UMST.ChemConstants.ScaleOccupancyZCommute
Description : SCALE occupancy Z-commute on the knowing fiber (Q lattice)
Copyright   : (c) UMST Project, 2026

Atomic-number @Z@ commutes along the Q ↔ meso ↔ macro SCALE ladder when occupancy
is lifted and coarsened: @scaleOccupancyZCommute@ witnesses **conservation of atomic
number** (identity lifts on the knowing fiber). Homolog ≠ copy: Ds (Z=110) is not
a Pt (Z=78) copy.

* @liftQM@, @liftMM@, @coarseQM@ are identity on @Z@ (Unwired scaffold).
* @scaleOccupancyZCommute z@ = @liftMM (liftQM z) == coarseQM z@ — True for all @z@.
* @dsNotCopyOfPt@ = 110 /= 78 (homolog witness, not identity copy).
* **One** design axiom (@scaleOccupancyZCommuteAxiom@); no meso / acting theorems.
* @physics_green@ stays false.

Haskell mirror of SCALE occupancy Z-commute on the quantum / knowing fiber.
Cell: @CHEM-FORMAL-Q-HS-SCALE-OCCUPANCY-Z-COMMUTE@.
-}
module UMST.ChemConstants.ScaleOccupancyZCommute
  ( ScaleOccupancyZModality (..)
  , scaleOccupancyZModalityCurrent
  , liftQM
  , liftMM
  , coarseQM
  , scaleOccupancyZCommute
  , dsZ
  , ptZ
  , dsNotCopyOfPt
  , homologNotCopyWitness
  , scaleOccupancyZCommuteAxiom
  , scaleOccupancyZCommuteCellId
  , scaleOccupancyZCommuteNonClaim
  , scaleOccupancyZPhysicsGreenAuthorized
  , scaleOccupancyZPhysicsGreenFalse
  , scaleOccupancyZModalityUnwired
  , scaleOccupancyZConservationNamed
  ) where

-- | Design modality for SCALE occupancy Z-commute claims (TYPE-03 preview).
data ScaleOccupancyZModality
  = ScaleOccupancyZUnwired
  | ScaleOccupancyZAssumed
  | ScaleOccupancyZProved
  | ScaleOccupancyZSurrogate
  deriving (Eq, Show)

-- | Current scaffold modality — always Unwired on this cell.
scaleOccupancyZModalityCurrent :: ScaleOccupancyZModality
scaleOccupancyZModalityCurrent = ScaleOccupancyZUnwired

-- | Quantum → meso lift on atomic number (identity on knowing fiber — Unwired).
liftQM :: Int -> Int
liftQM = id

-- | Meso → macro lift on atomic number (identity on knowing fiber — Unwired).
liftMM :: Int -> Int
liftMM = id

-- | Macro coarse readback of atomic number (identity on knowing fiber — Unwired).
coarseQM :: Int -> Int
coarseQM = id

-- | SCALE occupancy Z-commute: lift then coarse preserves atomic number.
scaleOccupancyZCommute :: Int -> Bool
scaleOccupancyZCommute z = liftMM (liftQM z) == coarseQM z

-- | Darmstadtium atomic number (period-7 d-block homolog pin).
dsZ :: Int
dsZ = 110

-- | Platinum atomic number (period-6 d-block homolog reference).
ptZ :: Int
ptZ = 78

-- | Homolog ≠ copy: Ds (Z=110) is not a Pt (Z=78) identity copy.
dsNotCopyOfPt :: Bool
dsNotCopyOfPt = dsZ /= ptZ

homologNotCopyWitness :: Bool
homologNotCopyWitness = dsNotCopyOfPt

-- | Single design axiom: Z commutes along SCALE (conservation of atomic number).
scaleOccupancyZCommuteAxiom :: Bool
scaleOccupancyZCommuteAxiom =
  scaleOccupancyZCommute dsZ
    && scaleOccupancyZCommute ptZ
    && homologNotCopyWitness

scaleOccupancyZConservationNamed :: String
scaleOccupancyZConservationNamed =
  "scaleOccupancyZCommute: liftMM (liftQM z) == coarseQM z"

scaleOccupancyZCommuteCellId :: String
scaleOccupancyZCommuteCellId = "CHEM-FORMAL-Q-HS-SCALE-OCCUPANCY-Z-COMMUTE"

-- | Non-claim fence — Z-commute Unwired ≠ Proved GREEN.
scaleOccupancyZCommuteNonClaim :: String
scaleOccupancyZCommuteNonClaim =
  "CHEM-FORMAL-Q-HS-SCALE-OCCUPANCY-Z-COMMUTE SCALE occupancy Z-commute conservation of atomic number; liftQM liftMM coarseQM identity Unwired; dsNotCopyOfPt homolog 110 ne 78 not Pt copy; one design axiom not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

-- | Physics GREEN is unauthorized on the knowing SCALE occupancy Z-commute scaffold.
scaleOccupancyZPhysicsGreenAuthorized :: Bool
scaleOccupancyZPhysicsGreenAuthorized = False

scaleOccupancyZPhysicsGreenFalse :: Bool
scaleOccupancyZPhysicsGreenFalse = not scaleOccupancyZPhysicsGreenAuthorized

scaleOccupancyZModalityUnwired :: Bool
scaleOccupancyZModalityUnwired =
  scaleOccupancyZModalityCurrent == ScaleOccupancyZUnwired

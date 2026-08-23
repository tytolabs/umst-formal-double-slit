-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ScaleOccupancyZCommute.agda
--
-- SCALE occupancy Z-commute on the knowing fiber (Q lattice):
--   * liftQM / liftMM / coarseQM are identity on atomic number ℕ
--   * Z commutes along Q ↔ meso ↔ macro (conservation of atomic number)
--   * Homolog ≠ copy: Ds (Z=110) is not a Pt (Z=78) identity copy
--
-- Mirrors `Haskell/UMST/ChemConstants/ScaleOccupancyZCommute.hs` +
-- sibling `ChemConstants/ConstantsScaleSheaf.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ScaleOccupancyZCommute where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (no; yes)

------------------------------------------------------------------------
-- Modality + identity SCALE lifts on atomic number
------------------------------------------------------------------------

data ScaleOccupancyZModality : Set where
  scale-occupancy-z-unwired scale-occupancy-z-assumed scale-occupancy-z-proved scale-occupancy-z-surrogate
    : ScaleOccupancyZModality

scaleOccupancyZModalityCurrent : ScaleOccupancyZModality
scaleOccupancyZModalityCurrent = scale-occupancy-z-unwired

liftQM liftMM coarseQM : ℕ → ℕ
liftQM = id
liftMM = id
coarseQM = id

commute : ∀ z → liftMM (liftQM z) ≡ coarseQM z
commute z = refl

scaleOccupancyZCommute : ℕ → Set
scaleOccupancyZCommute z = liftMM (liftQM z) ≡ coarseQM z

scale-occupancy-z-commute-all : ∀ z → scaleOccupancyZCommute z
scale-occupancy-z-commute-all z = commute z

------------------------------------------------------------------------
-- Homolog ≠ copy (Ds Z=110, Pt Z=78)
------------------------------------------------------------------------

dsZ ptZ : ℕ
dsZ = 110
ptZ = 78

private
  ds-ne-pt : dsZ ≢ ptZ
  ds-ne-pt eq with dsZ ≟ ptZ
  ds-ne-pt eq | no ¬pq = ¬pq eq

dsNotCopyOfPt : 110 ≢ 78
dsNotCopyOfPt = ds-ne-pt

homologNotCopyWitness : dsZ ≢ ptZ
homologNotCopyWitness = ds-ne-pt

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second axiom fork)
------------------------------------------------------------------------

scaleOccupancyZCommuteAxiom : scaleOccupancyZCommute dsZ × scaleOccupancyZCommute ptZ × (dsZ ≢ ptZ)
scaleOccupancyZCommuteAxiom = commute dsZ , commute ptZ , homologNotCopyWitness

scaleOccupancyZConservationNamed : String
scaleOccupancyZConservationNamed =
  "scaleOccupancyZCommute: liftMM (liftQM z) ≡ coarseQM z"

scaleOccupancyZCommuteCellId : String
scaleOccupancyZCommuteCellId = "CHEM-FORMAL-Q-AGDA-SCALE-OCCUPANCY-Z-COMMUTE"

scaleOccupancyZCommuteNonClaim : String
scaleOccupancyZCommuteNonClaim =
  "CHEM-FORMAL-Q-AGDA-SCALE-OCCUPANCY-Z-COMMUTE SCALE occupancy Z-commute conservation of atomic number; liftQM liftMM coarseQM identity Unwired; dsNotCopyOfPt homolog 110 ne 78 not Pt copy; one design axiom not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

scale-occupancy-z-modality-unwired : scaleOccupancyZModalityCurrent ≡ scale-occupancy-z-unwired
scale-occupancy-z-modality-unwired = refl

scaleOccupancyZPhysicsGreenAuthorized : Set
scaleOccupancyZPhysicsGreenAuthorized = ⊥

scale-occupancy-z-physics-green-false : ¬ scaleOccupancyZPhysicsGreenAuthorized
scale-occupancy-z-physics-green-false ()

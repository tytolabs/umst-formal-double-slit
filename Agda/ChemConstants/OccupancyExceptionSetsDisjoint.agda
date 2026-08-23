-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.OccupancyExceptionSetsDisjoint.agda
--
-- Agda composition of Named / Actinide / DBlock occupancy exception modules:
--   * Pairwise disjoint atomic-number Z-sets (finite pin level)
--   * Pu (Z=94) absent from all three families
--   * Lr (Z=103) in actinide set, not in named set
--   * One design axiom (finite Z-set disjointness) — cites qlattice SSOT
--
-- Mirrors `Lean/ChemConstants/OccupancyExceptionSetsDisjoint.lean` +
-- sibling `Haskell/UMST/ChemConstants/OccupancyExceptionSetsDisjoint.hs` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.OccupancyExceptionSetsDisjoint where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; no)

open import ChemConstants.NamedOccupancyExceptions using
  ( NamedException; named-La; named-Ce; named-Gd; named-Pt; named-Au
  ; NamedException-z; namedExceptionList; namedExceptionCount
  ; named-exception-count-five; namedOccupancyModalityCurrent
  ; named-occupancy-modality-unwired; namedOccupancyExceptionsCellId
  ; namedOccupancyMadelungWitnessAuthority; named-occupancy-not-second-axiom
  ; namedOccupancyPhysicsGreenAuthorized; named-occupancy-physics-green-false
  ; named-occupancy-unwired
  )
open import ChemConstants.ActinideOccupancyExceptions using
  ( ActinideException; actinide-Ac; actinide-Th; actinide-Pa; actinide-U
  ; actinide-Np; actinide-Cm; actinide-Lr
  ; ActinideException-z; actinide-exception-lr-z
  ; actinideExceptionList; actinideExceptionCount
  ; actinide-exception-count-seven
  ; actinideOccupancyModalityCurrent; actinide-occupancy-modality-unwired
  ; actinideOccupancyExceptionsCellId
  ; actinideOccupancyMadelungWitnessAuthority; actinide-occupancy-not-second-axiom
  ; actinideOccupancyPhysicsGreenAuthorized; actinide-occupancy-physics-green-false
  ; actinide-occupancy-unwired
  )
open import ChemConstants.DBlockOccupancyExceptions using
  ( DBlockException; dblock-Cr; dblock-Cu; dblock-Nb; dblock-Mo
  ; dblock-Ru; dblock-Rh; dblock-Pd; dblock-Ag
  ; DBlockException-z; dblockExceptionList; dblockExceptionCount
  ; dblock-exception-count-eight
  ; dblockOccupancyModalityCurrent; dblock-occupancy-modality-unwired
  ; dblockOccupancyExceptionsCellId
  ; dblockOccupancyMadelungWitnessAuthority; dblock-occupancy-not-second-axiom
  ; dblockOccupancyPhysicsGreenAuthorized; dblock-occupancy-physics-green-false
  ; dblock-occupancy-unwired
  )

------------------------------------------------------------------------
-- Modality + Z-set projections from sibling finite exception lists
------------------------------------------------------------------------

data OccupancyExceptionSetsModality : Set where
  occupancy-exception-sets-unwired occupancy-exception-sets-assumed
    occupancy-exception-sets-proved occupancy-exception-sets-surrogate
    : OccupancyExceptionSetsModality

occupancyExceptionSetsModalityCurrent : OccupancyExceptionSetsModality
occupancyExceptionSetsModalityCurrent = occupancy-exception-sets-unwired

namedExceptionZList : List ℕ
namedExceptionZList = map NamedException-z namedExceptionList

actinideExceptionZList : List ℕ
actinideExceptionZList = map ActinideException-z actinideExceptionList

dBlockExceptionZList : List ℕ
dBlockExceptionZList = map DBlockException-z dblockExceptionList

named-occupancy-exception-z-set-five :
  length namedExceptionZList ≡ namedExceptionCount
named-occupancy-exception-z-set-five = refl

actinide-occupancy-exception-z-set-seven :
  length actinideExceptionZList ≡ actinideExceptionCount
actinide-occupancy-exception-z-set-seven = refl

d-block-occupancy-exception-z-set-eight :
  length dBlockExceptionZList ≡ dblockExceptionCount
d-block-occupancy-exception-z-set-eight = refl

plutoniumZ : ℕ
plutoniumZ = 94

lawrenciumZ : ℕ
lawrenciumZ = 103

------------------------------------------------------------------------
-- Pairwise disjoint Z-sets (refl / contradiction on Nat equality)
------------------------------------------------------------------------

named-actinide-exception-z-disjoint : ∀ (n : NamedException) (a : ActinideException) → NamedException-z n ≢ ActinideException-z a
named-actinide-exception-z-disjoint named-La actinide-Ac ()
named-actinide-exception-z-disjoint named-La actinide-Th ()
named-actinide-exception-z-disjoint named-La actinide-Pa ()
named-actinide-exception-z-disjoint named-La actinide-U ()
named-actinide-exception-z-disjoint named-La actinide-Np ()
named-actinide-exception-z-disjoint named-La actinide-Cm ()
named-actinide-exception-z-disjoint named-La actinide-Lr ()
named-actinide-exception-z-disjoint named-Ce actinide-Ac ()
named-actinide-exception-z-disjoint named-Ce actinide-Th ()
named-actinide-exception-z-disjoint named-Ce actinide-Pa ()
named-actinide-exception-z-disjoint named-Ce actinide-U ()
named-actinide-exception-z-disjoint named-Ce actinide-Np ()
named-actinide-exception-z-disjoint named-Ce actinide-Cm ()
named-actinide-exception-z-disjoint named-Ce actinide-Lr ()
named-actinide-exception-z-disjoint named-Gd actinide-Ac ()
named-actinide-exception-z-disjoint named-Gd actinide-Th ()
named-actinide-exception-z-disjoint named-Gd actinide-Pa ()
named-actinide-exception-z-disjoint named-Gd actinide-U ()
named-actinide-exception-z-disjoint named-Gd actinide-Np ()
named-actinide-exception-z-disjoint named-Gd actinide-Cm ()
named-actinide-exception-z-disjoint named-Gd actinide-Lr ()
named-actinide-exception-z-disjoint named-Pt actinide-Ac ()
named-actinide-exception-z-disjoint named-Pt actinide-Th ()
named-actinide-exception-z-disjoint named-Pt actinide-Pa ()
named-actinide-exception-z-disjoint named-Pt actinide-U ()
named-actinide-exception-z-disjoint named-Pt actinide-Np ()
named-actinide-exception-z-disjoint named-Pt actinide-Cm ()
named-actinide-exception-z-disjoint named-Pt actinide-Lr ()
named-actinide-exception-z-disjoint named-Au actinide-Ac ()
named-actinide-exception-z-disjoint named-Au actinide-Th ()
named-actinide-exception-z-disjoint named-Au actinide-Pa ()
named-actinide-exception-z-disjoint named-Au actinide-U ()
named-actinide-exception-z-disjoint named-Au actinide-Np ()
named-actinide-exception-z-disjoint named-Au actinide-Cm ()
named-actinide-exception-z-disjoint named-Au actinide-Lr ()

named-dblock-exception-z-disjoint : ∀ (n : NamedException) (d : DBlockException) → NamedException-z n ≢ DBlockException-z d
named-dblock-exception-z-disjoint named-La dblock-Cr ()
named-dblock-exception-z-disjoint named-La dblock-Cu ()
named-dblock-exception-z-disjoint named-La dblock-Nb ()
named-dblock-exception-z-disjoint named-La dblock-Mo ()
named-dblock-exception-z-disjoint named-La dblock-Ru ()
named-dblock-exception-z-disjoint named-La dblock-Rh ()
named-dblock-exception-z-disjoint named-La dblock-Pd ()
named-dblock-exception-z-disjoint named-La dblock-Ag ()
named-dblock-exception-z-disjoint named-Ce dblock-Cr ()
named-dblock-exception-z-disjoint named-Ce dblock-Cu ()
named-dblock-exception-z-disjoint named-Ce dblock-Nb ()
named-dblock-exception-z-disjoint named-Ce dblock-Mo ()
named-dblock-exception-z-disjoint named-Ce dblock-Ru ()
named-dblock-exception-z-disjoint named-Ce dblock-Rh ()
named-dblock-exception-z-disjoint named-Ce dblock-Pd ()
named-dblock-exception-z-disjoint named-Ce dblock-Ag ()
named-dblock-exception-z-disjoint named-Gd dblock-Cr ()
named-dblock-exception-z-disjoint named-Gd dblock-Cu ()
named-dblock-exception-z-disjoint named-Gd dblock-Nb ()
named-dblock-exception-z-disjoint named-Gd dblock-Mo ()
named-dblock-exception-z-disjoint named-Gd dblock-Ru ()
named-dblock-exception-z-disjoint named-Gd dblock-Rh ()
named-dblock-exception-z-disjoint named-Gd dblock-Pd ()
named-dblock-exception-z-disjoint named-Gd dblock-Ag ()
named-dblock-exception-z-disjoint named-Pt dblock-Cr ()
named-dblock-exception-z-disjoint named-Pt dblock-Cu ()
named-dblock-exception-z-disjoint named-Pt dblock-Nb ()
named-dblock-exception-z-disjoint named-Pt dblock-Mo ()
named-dblock-exception-z-disjoint named-Pt dblock-Ru ()
named-dblock-exception-z-disjoint named-Pt dblock-Rh ()
named-dblock-exception-z-disjoint named-Pt dblock-Pd ()
named-dblock-exception-z-disjoint named-Pt dblock-Ag ()
named-dblock-exception-z-disjoint named-Au dblock-Cr ()
named-dblock-exception-z-disjoint named-Au dblock-Cu ()
named-dblock-exception-z-disjoint named-Au dblock-Nb ()
named-dblock-exception-z-disjoint named-Au dblock-Mo ()
named-dblock-exception-z-disjoint named-Au dblock-Ru ()
named-dblock-exception-z-disjoint named-Au dblock-Rh ()
named-dblock-exception-z-disjoint named-Au dblock-Pd ()
named-dblock-exception-z-disjoint named-Au dblock-Ag ()

actinide-dblock-exception-z-disjoint : ∀ (a : ActinideException) (d : DBlockException) → ActinideException-z a ≢ DBlockException-z d
actinide-dblock-exception-z-disjoint actinide-Ac dblock-Cr ()
actinide-dblock-exception-z-disjoint actinide-Ac dblock-Cu ()
actinide-dblock-exception-z-disjoint actinide-Ac dblock-Nb ()
actinide-dblock-exception-z-disjoint actinide-Ac dblock-Mo ()
actinide-dblock-exception-z-disjoint actinide-Ac dblock-Ru ()
actinide-dblock-exception-z-disjoint actinide-Ac dblock-Rh ()
actinide-dblock-exception-z-disjoint actinide-Ac dblock-Pd ()
actinide-dblock-exception-z-disjoint actinide-Ac dblock-Ag ()
actinide-dblock-exception-z-disjoint actinide-Th dblock-Cr ()
actinide-dblock-exception-z-disjoint actinide-Th dblock-Cu ()
actinide-dblock-exception-z-disjoint actinide-Th dblock-Nb ()
actinide-dblock-exception-z-disjoint actinide-Th dblock-Mo ()
actinide-dblock-exception-z-disjoint actinide-Th dblock-Ru ()
actinide-dblock-exception-z-disjoint actinide-Th dblock-Rh ()
actinide-dblock-exception-z-disjoint actinide-Th dblock-Pd ()
actinide-dblock-exception-z-disjoint actinide-Th dblock-Ag ()
actinide-dblock-exception-z-disjoint actinide-Pa dblock-Cr ()
actinide-dblock-exception-z-disjoint actinide-Pa dblock-Cu ()
actinide-dblock-exception-z-disjoint actinide-Pa dblock-Nb ()
actinide-dblock-exception-z-disjoint actinide-Pa dblock-Mo ()
actinide-dblock-exception-z-disjoint actinide-Pa dblock-Ru ()
actinide-dblock-exception-z-disjoint actinide-Pa dblock-Rh ()
actinide-dblock-exception-z-disjoint actinide-Pa dblock-Pd ()
actinide-dblock-exception-z-disjoint actinide-Pa dblock-Ag ()
actinide-dblock-exception-z-disjoint actinide-U dblock-Cr ()
actinide-dblock-exception-z-disjoint actinide-U dblock-Cu ()
actinide-dblock-exception-z-disjoint actinide-U dblock-Nb ()
actinide-dblock-exception-z-disjoint actinide-U dblock-Mo ()
actinide-dblock-exception-z-disjoint actinide-U dblock-Ru ()
actinide-dblock-exception-z-disjoint actinide-U dblock-Rh ()
actinide-dblock-exception-z-disjoint actinide-U dblock-Pd ()
actinide-dblock-exception-z-disjoint actinide-U dblock-Ag ()
actinide-dblock-exception-z-disjoint actinide-Np dblock-Cr ()
actinide-dblock-exception-z-disjoint actinide-Np dblock-Cu ()
actinide-dblock-exception-z-disjoint actinide-Np dblock-Nb ()
actinide-dblock-exception-z-disjoint actinide-Np dblock-Mo ()
actinide-dblock-exception-z-disjoint actinide-Np dblock-Ru ()
actinide-dblock-exception-z-disjoint actinide-Np dblock-Rh ()
actinide-dblock-exception-z-disjoint actinide-Np dblock-Pd ()
actinide-dblock-exception-z-disjoint actinide-Np dblock-Ag ()
actinide-dblock-exception-z-disjoint actinide-Cm dblock-Cr ()
actinide-dblock-exception-z-disjoint actinide-Cm dblock-Cu ()
actinide-dblock-exception-z-disjoint actinide-Cm dblock-Nb ()
actinide-dblock-exception-z-disjoint actinide-Cm dblock-Mo ()
actinide-dblock-exception-z-disjoint actinide-Cm dblock-Ru ()
actinide-dblock-exception-z-disjoint actinide-Cm dblock-Rh ()
actinide-dblock-exception-z-disjoint actinide-Cm dblock-Pd ()
actinide-dblock-exception-z-disjoint actinide-Cm dblock-Ag ()
actinide-dblock-exception-z-disjoint actinide-Lr dblock-Cr ()
actinide-dblock-exception-z-disjoint actinide-Lr dblock-Cu ()
actinide-dblock-exception-z-disjoint actinide-Lr dblock-Nb ()
actinide-dblock-exception-z-disjoint actinide-Lr dblock-Mo ()
actinide-dblock-exception-z-disjoint actinide-Lr dblock-Ru ()
actinide-dblock-exception-z-disjoint actinide-Lr dblock-Rh ()
actinide-dblock-exception-z-disjoint actinide-Lr dblock-Pd ()
actinide-dblock-exception-z-disjoint actinide-Lr dblock-Ag ()

occupancyExceptionZSetsPairwiseDisjoint : Set
occupancyExceptionZSetsPairwiseDisjoint =
  (∀ (n : NamedException) (a : ActinideException) → NamedException-z n ≢ ActinideException-z a) ×
  (∀ (n : NamedException) (d : DBlockException) → NamedException-z n ≢ DBlockException-z d) ×
  (∀ (a : ActinideException) (d : DBlockException) → ActinideException-z a ≢ DBlockException-z d)

occupancy-exception-z-sets-pairwise-disjoint : occupancyExceptionZSetsPairwiseDisjoint
occupancy-exception-z-sets-pairwise-disjoint =
  named-actinide-exception-z-disjoint ,
  named-dblock-exception-z-disjoint ,
  actinide-dblock-exception-z-disjoint

------------------------------------------------------------------------
-- Pu (Z=94) absent from all three exception Z-sets
------------------------------------------------------------------------

z94-not-named-exception-z : ∀ (ex : NamedException) → NamedException-z ex ≢ plutoniumZ
z94-not-named-exception-z named-La ()
z94-not-named-exception-z named-Ce ()
z94-not-named-exception-z named-Gd ()
z94-not-named-exception-z named-Pt ()
z94-not-named-exception-z named-Au ()

z94-not-actinide-exception-z : ∀ (ex : ActinideException) → ActinideException-z ex ≢ plutoniumZ
z94-not-actinide-exception-z actinide-Ac ()
z94-not-actinide-exception-z actinide-Th ()
z94-not-actinide-exception-z actinide-Pa ()
z94-not-actinide-exception-z actinide-U ()
z94-not-actinide-exception-z actinide-Np ()
z94-not-actinide-exception-z actinide-Cm ()
z94-not-actinide-exception-z actinide-Lr ()

z94-not-dblock-exception-z : ∀ (ex : DBlockException) → DBlockException-z ex ≢ plutoniumZ
z94-not-dblock-exception-z dblock-Cr ()
z94-not-dblock-exception-z dblock-Cu ()
z94-not-dblock-exception-z dblock-Nb ()
z94-not-dblock-exception-z dblock-Mo ()
z94-not-dblock-exception-z dblock-Ru ()
z94-not-dblock-exception-z dblock-Rh ()
z94-not-dblock-exception-z dblock-Pd ()
z94-not-dblock-exception-z dblock-Ag ()

z94NotInAnyOccupancyExceptionSet : Set
z94NotInAnyOccupancyExceptionSet =
  (∀ (ex : NamedException) → NamedException-z ex ≢ plutoniumZ) ×
  (∀ (ex : ActinideException) → ActinideException-z ex ≢ plutoniumZ) ×
  (∀ (ex : DBlockException) → DBlockException-z ex ≢ plutoniumZ)

z94-not-in-any-occupancy-exception-set : z94NotInAnyOccupancyExceptionSet
z94-not-in-any-occupancy-exception-set =
  z94-not-named-exception-z ,
  z94-not-actinide-exception-z ,
  z94-not-dblock-exception-z

------------------------------------------------------------------------
-- Lr (Z=103) actinide pin — not in NamedException set
------------------------------------------------------------------------

z103-in-actinide-occupancy-exception-set :
  Σ ActinideException (λ ex → ActinideException-z ex ≡ lawrenciumZ)
z103-in-actinide-occupancy-exception-set = actinide-Lr , actinide-exception-lr-z

z103-not-named-exception-z : ∀ (ex : NamedException) → NamedException-z ex ≢ lawrenciumZ
z103-not-named-exception-z named-La ()
z103-not-named-exception-z named-Ce ()
z103-not-named-exception-z named-Gd ()
z103-not-named-exception-z named-Pt ()
z103-not-named-exception-z named-Au ()

z103InActinideNotNamed : Set
z103InActinideNotNamed =
  Σ ActinideException (λ ex → ActinideException-z ex ≡ lawrenciumZ) ×
  (∀ (ex : NamedException) → NamedException-z ex ≢ lawrenciumZ)

z103-in-actinide-not-named : z103InActinideNotNamed
z103-in-actinide-not-named =
  z103-in-actinide-occupancy-exception-set ,
  z103-not-named-exception-z

lawrencium-in-actinide-not-named :
  ActinideException-z actinide-Lr ≡ lawrenciumZ ×
  (∀ (ex : NamedException) → NamedException-z ex ≢ lawrenciumZ)
lawrencium-in-actinide-not-named =
  actinide-exception-lr-z ,
  z103-not-named-exception-z

------------------------------------------------------------------------
-- One design axiom: finite occupancy exception Z-sets disjoint
------------------------------------------------------------------------

occupancyExceptionSetsDisjointAxiom : Set
occupancyExceptionSetsDisjointAxiom =
  occupancyExceptionZSetsPairwiseDisjoint ×
  z94NotInAnyOccupancyExceptionSet ×
  z103InActinideNotNamed

occupancy-exception-sets-disjoint-axiom : occupancyExceptionSetsDisjointAxiom
occupancy-exception-sets-disjoint-axiom =
  occupancy-exception-z-sets-pairwise-disjoint ,
  z94-not-in-any-occupancy-exception-set ,
  z103-in-actinide-not-named

------------------------------------------------------------------------
-- Sibling modality pins (all Unwired — composition witness)
------------------------------------------------------------------------

occupancy-exception-sets-modality-unwired :
  occupancyExceptionSetsModalityCurrent ≡ occupancy-exception-sets-unwired
occupancy-exception-sets-modality-unwired = refl

named-occupancy-modality-still-unwired :
  namedOccupancyModalityCurrent ≡ named-occupancy-unwired
named-occupancy-modality-still-unwired = named-occupancy-modality-unwired

actinide-occupancy-modality-still-unwired :
  actinideOccupancyModalityCurrent ≡ actinide-occupancy-unwired
actinide-occupancy-modality-still-unwired = actinide-occupancy-modality-unwired

d-block-occupancy-modality-still-unwired :
  dblockOccupancyModalityCurrent ≡ dblock-occupancy-unwired
d-block-occupancy-modality-still-unwired = dblock-occupancy-modality-unwired

------------------------------------------------------------------------
-- Cited upstream authority (views only — pins named in siblings)
------------------------------------------------------------------------

occupancyExceptionSetsQlatticeAuthority : String
occupancyExceptionSetsQlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

occupancyExceptionSetsNamedAuthority : String
occupancyExceptionSetsNamedAuthority = namedOccupancyExceptionsCellId

occupancyExceptionSetsActinideAuthority : String
occupancyExceptionSetsActinideAuthority = actinideOccupancyExceptionsCellId

occupancyExceptionSetsDBlockAuthority : String
occupancyExceptionSetsDBlockAuthority = dblockOccupancyExceptionsCellId

occupancyExceptionSetsCellId : String
occupancyExceptionSetsCellId = "CHEM-FORMAL-Q-AGDA-OCCUPANCY-EXCEPTION-SETS-DISJOINT"

occupancyExceptionSetsNonClaim : String
occupancyExceptionSetsNonClaim =
  "CHEM-FORMAL-Q-AGDA-OCCUPANCY-EXCEPTION-SETS-DISJOINT Agda composition Named Actinide DBlock occupancy exception Z-sets pairwise disjoint; Pu Z=94 not in any; Lr Z=103 in actinide not named; cites qlattice observed_override_config and sibling exception modules one design axiom not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

occupancy-exception-sets-cell-id :
  occupancyExceptionSetsCellId ≡
  "CHEM-FORMAL-Q-AGDA-OCCUPANCY-EXCEPTION-SETS-DISJOINT"
occupancy-exception-sets-cell-id = refl

occupancy-exception-sets-cites-qlattice :
  occupancyExceptionSetsQlatticeAuthority ≡ "umst/umst-chem/src/qlattice.rs"
occupancy-exception-sets-cites-qlattice = refl

occupancy-exception-sets-not-second-axiom :
  namedOccupancyMadelungWitnessAuthority ≢ ""
occupancy-exception-sets-not-second-axiom = named-occupancy-not-second-axiom

private
  occupancy-exception-sets-named-authority-nonempty :
    occupancyExceptionSetsNamedAuthority ≢ ""
  occupancy-exception-sets-named-authority-nonempty eq with occupancyExceptionSetsNamedAuthority ≟ ""
  occupancy-exception-sets-named-authority-nonempty eq | no ¬pq = ¬pq eq

  occupancy-exception-sets-actinide-authority-nonempty :
    occupancyExceptionSetsActinideAuthority ≢ ""
  occupancy-exception-sets-actinide-authority-nonempty eq with occupancyExceptionSetsActinideAuthority ≟ ""
  occupancy-exception-sets-actinide-authority-nonempty eq | no ¬pq = ¬pq eq

  occupancy-exception-sets-dblock-authority-nonempty :
    occupancyExceptionSetsDBlockAuthority ≢ ""
  occupancy-exception-sets-dblock-authority-nonempty eq with occupancyExceptionSetsDBlockAuthority ≟ ""
  occupancy-exception-sets-dblock-authority-nonempty eq | no ¬pq = ¬pq eq

occupancy-exception-sets-cites-sibling-modules :
  occupancyExceptionSetsNamedAuthority ≢ "" ×
  occupancyExceptionSetsActinideAuthority ≢ "" ×
  occupancyExceptionSetsDBlockAuthority ≢ ""
occupancy-exception-sets-cites-sibling-modules =
  occupancy-exception-sets-named-authority-nonempty ,
  occupancy-exception-sets-actinide-authority-nonempty ,
  occupancy-exception-sets-dblock-authority-nonempty

------------------------------------------------------------------------
-- Physics GREEN unauthorized (Unwired scaffold)
------------------------------------------------------------------------

occupancyExceptionSetsPhysicsGreenAuthorized : Set
occupancyExceptionSetsPhysicsGreenAuthorized = ⊥

occupancy-exception-sets-physics-green-false :
  ¬ occupancyExceptionSetsPhysicsGreenAuthorized
occupancy-exception-sets-physics-green-false h = h

occupancy-exception-sets-named-physics-green-false :
  ¬ namedOccupancyPhysicsGreenAuthorized
occupancy-exception-sets-named-physics-green-false = named-occupancy-physics-green-false

occupancy-exception-sets-actinide-physics-green-false :
  ¬ actinideOccupancyPhysicsGreenAuthorized
occupancy-exception-sets-actinide-physics-green-false = actinide-occupancy-physics-green-false

occupancy-exception-sets-d-block-physics-green-false :
  ¬ dblockOccupancyPhysicsGreenAuthorized
occupancy-exception-sets-d-block-physics-green-false = dblock-occupancy-physics-green-false

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ActinideOccupancyExceptions.agda
--
-- Finite named period-7 qlattice Madelung occupancy exception set:
--   * Ac / Th / Pa / U / Np / Cm / Lr as ActinideException
--   * Six Madelung predicted ≠ observed pins; Lr named override agrees (honest)
--   * Cites umst-chem qlattice + madelung_witness — not a second axiom
--
-- Mirrors `Coq/ChemConstants/ActinideOccupancyExceptions.v` +
-- sibling `ChemConstants/NamedOccupancyExceptions.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ActinideOccupancyExceptions where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; length; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; no)

------------------------------------------------------------------------
-- Modality + finite actinide exception tags (Ac / Th / Pa / U / Np / Cm / Lr)
------------------------------------------------------------------------

data ActinideOccupancyModality : Set where
  actinide-occupancy-unwired actinide-occupancy-assumed actinide-occupancy-proved actinide-occupancy-surrogate
    : ActinideOccupancyModality

actinideOccupancyModalityCurrent : ActinideOccupancyModality
actinideOccupancyModalityCurrent = actinide-occupancy-unwired

data ActinideException : Set where
  actinide-Ac actinide-Th actinide-Pa actinide-U actinide-Np actinide-Cm actinide-Lr
    : ActinideException

ActinideException-z : ActinideException → ℕ
ActinideException-z actinide-Ac = 89
ActinideException-z actinide-Th = 90
ActinideException-z actinide-Pa = 91
ActinideException-z actinide-U = 92
ActinideException-z actinide-Np = 93
ActinideException-z actinide-Cm = 96
ActinideException-z actinide-Lr = 103

ActinideException-symbol : ActinideException → String
ActinideException-symbol actinide-Ac = "Ac"
ActinideException-symbol actinide-Th = "Th"
ActinideException-symbol actinide-Pa = "Pa"
ActinideException-symbol actinide-U = "U"
ActinideException-symbol actinide-Np = "Np"
ActinideException-symbol actinide-Cm = "Cm"
ActinideException-symbol actinide-Lr = "Lr"

actinide-exception-ac-z : ActinideException-z actinide-Ac ≡ 89
actinide-exception-ac-z = refl

actinide-exception-th-z : ActinideException-z actinide-Th ≡ 90
actinide-exception-th-z = refl

actinide-exception-pa-z : ActinideException-z actinide-Pa ≡ 91
actinide-exception-pa-z = refl

actinide-exception-u-z : ActinideException-z actinide-U ≡ 92
actinide-exception-u-z = refl

actinide-exception-np-z : ActinideException-z actinide-Np ≡ 93
actinide-exception-np-z = refl

actinide-exception-cm-z : ActinideException-z actinide-Cm ≡ 96
actinide-exception-cm-z = refl

actinide-exception-lr-z : ActinideException-z actinide-Lr ≡ 103
actinide-exception-lr-z = refl

ActinideException-observedNotation : ActinideException → String
ActinideException-observedNotation actinide-Ac =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d1"
ActinideException-observedNotation actinide-Th =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d2"
ActinideException-observedNotation actinide-Pa =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f26d1"
ActinideException-observedNotation actinide-U =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f36d1"
ActinideException-observedNotation actinide-Np =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f46d1"
ActinideException-observedNotation actinide-Cm =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f76d1"
ActinideException-observedNotation actinide-Lr =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1"

ActinideException-predictedNotation : ActinideException → String
ActinideException-predictedNotation actinide-Ac =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f1"
ActinideException-predictedNotation actinide-Th =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f2"
ActinideException-predictedNotation actinide-Pa =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f3"
ActinideException-predictedNotation actinide-U =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f4"
ActinideException-predictedNotation actinide-Np =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f5"
ActinideException-predictedNotation actinide-Cm =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f8"
ActinideException-predictedNotation actinide-Lr =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1"

ActinideException-occupancyTag : ActinideException → String
ActinideException-occupancyTag actinide-Ac = "6d17s2"
ActinideException-occupancyTag actinide-Th = "6d27s2"
ActinideException-occupancyTag actinide-Pa = "5f26d17s2"
ActinideException-occupancyTag actinide-U = "5f36d17s2"
ActinideException-occupancyTag actinide-Np = "7s25f46d1"
ActinideException-occupancyTag actinide-Cm = "5f76d17s2"
ActinideException-occupancyTag actinide-Lr = "5f146d17s2"

------------------------------------------------------------------------
-- Actinide exception rows + finite list (cardinality 7)
------------------------------------------------------------------------

record ActinideExceptionRow : Set where
  constructor mkActinideExceptionRow
  field
    exception : ActinideException
    modality  : ActinideOccupancyModality

ActinideExceptionRow-z : ActinideExceptionRow → ℕ
ActinideExceptionRow-z row = ActinideException-z (ActinideExceptionRow.exception row)

ActinideExceptionRow-symbol : ActinideExceptionRow → String
ActinideExceptionRow-symbol row = ActinideException-symbol (ActinideExceptionRow.exception row)

ActinideExceptionRow-observedNotation : ActinideExceptionRow → String
ActinideExceptionRow-observedNotation row =
  ActinideException-observedNotation (ActinideExceptionRow.exception row)

ActinideExceptionRow-predictedNotation : ActinideExceptionRow → String
ActinideExceptionRow-predictedNotation row =
  ActinideException-predictedNotation (ActinideExceptionRow.exception row)

ActinideExceptionRow-occupancyTag : ActinideExceptionRow → String
ActinideExceptionRow-occupancyTag row =
  ActinideException-occupancyTag (ActinideExceptionRow.exception row)

actinideExceptionRow : ActinideException → ActinideExceptionRow
actinideExceptionRow ex = record
  { exception = ex
  ; modality  = actinideOccupancyModalityCurrent
  }

actinide-exception-row-z : ∀ (ex : ActinideException) →
  ActinideExceptionRow-z (actinideExceptionRow ex) ≡ ActinideException-z ex
actinide-exception-row-z ex = refl

actinide-exception-row-modality-unwired : ∀ (ex : ActinideException) →
  ActinideExceptionRow.modality (actinideExceptionRow ex) ≡ actinideOccupancyModalityCurrent
actinide-exception-row-modality-unwired ex = refl

actinideExceptionList : List ActinideException
actinideExceptionList =
  actinide-Ac ∷ actinide-Th ∷ actinide-Pa ∷ actinide-U ∷
  actinide-Np ∷ actinide-Cm ∷ actinide-Lr ∷ []

actinideExceptionCount : ℕ
actinideExceptionCount = length actinideExceptionList

actinide-exception-count-seven : actinideExceptionCount ≡ 7
actinide-exception-count-seven = refl

actinide-exception-list-length : length actinideExceptionList ≡ 7
actinide-exception-list-length = refl

------------------------------------------------------------------------
-- Observed ≢ predicted (six Madelung exceptions; Lr agrees — honest)
------------------------------------------------------------------------

private
  ac-observed-ne-predicted : ActinideException-observedNotation actinide-Ac ≢
    ActinideException-predictedNotation actinide-Ac
  ac-observed-ne-predicted eq with ActinideException-observedNotation actinide-Ac ≟ ActinideException-predictedNotation actinide-Ac
  ac-observed-ne-predicted eq | no ¬pq = ¬pq eq

  th-observed-ne-predicted : ActinideException-observedNotation actinide-Th ≢
    ActinideException-predictedNotation actinide-Th
  th-observed-ne-predicted eq with ActinideException-observedNotation actinide-Th ≟ ActinideException-predictedNotation actinide-Th
  th-observed-ne-predicted eq | no ¬pq = ¬pq eq

  pa-observed-ne-predicted : ActinideException-observedNotation actinide-Pa ≢
    ActinideException-predictedNotation actinide-Pa
  pa-observed-ne-predicted eq with ActinideException-observedNotation actinide-Pa ≟ ActinideException-predictedNotation actinide-Pa
  pa-observed-ne-predicted eq | no ¬pq = ¬pq eq

  u-observed-ne-predicted : ActinideException-observedNotation actinide-U ≢
    ActinideException-predictedNotation actinide-U
  u-observed-ne-predicted eq with ActinideException-observedNotation actinide-U ≟ ActinideException-predictedNotation actinide-U
  u-observed-ne-predicted eq | no ¬pq = ¬pq eq

  np-observed-ne-predicted : ActinideException-observedNotation actinide-Np ≢
    ActinideException-predictedNotation actinide-Np
  np-observed-ne-predicted eq with ActinideException-observedNotation actinide-Np ≟ ActinideException-predictedNotation actinide-Np
  np-observed-ne-predicted eq | no ¬pq = ¬pq eq

  cm-observed-ne-predicted : ActinideException-observedNotation actinide-Cm ≢
    ActinideException-predictedNotation actinide-Cm
  cm-observed-ne-predicted eq with ActinideException-observedNotation actinide-Cm ≟ ActinideException-predictedNotation actinide-Cm
  cm-observed-ne-predicted eq | no ¬pq = ¬pq eq

actinideExceptionIsMadelungException : ActinideException → Set
actinideExceptionIsMadelungException ex =
  ActinideException-observedNotation ex ≢ ActinideException-predictedNotation ex

actinide-exception-ac-is-madelung-exception :
  actinideExceptionIsMadelungException actinide-Ac
actinide-exception-ac-is-madelung-exception = ac-observed-ne-predicted

actinide-exception-th-is-madelung-exception :
  actinideExceptionIsMadelungException actinide-Th
actinide-exception-th-is-madelung-exception = th-observed-ne-predicted

actinide-exception-pa-is-madelung-exception :
  actinideExceptionIsMadelungException actinide-Pa
actinide-exception-pa-is-madelung-exception = pa-observed-ne-predicted

actinide-exception-u-is-madelung-exception :
  actinideExceptionIsMadelungException actinide-U
actinide-exception-u-is-madelung-exception = u-observed-ne-predicted

actinide-exception-np-is-madelung-exception :
  actinideExceptionIsMadelungException actinide-Np
actinide-exception-np-is-madelung-exception = np-observed-ne-predicted

actinide-exception-cm-is-madelung-exception :
  actinideExceptionIsMadelungException actinide-Cm
actinide-exception-cm-is-madelung-exception = cm-observed-ne-predicted

lr-named-override-observed-eq-predicted :
  ActinideException-observedNotation actinide-Lr ≡
  ActinideException-predictedNotation actinide-Lr
lr-named-override-observed-eq-predicted = refl

lr-named-override-in-observed-override-config :
  ActinideException-observedNotation actinide-Lr ≢ ""
lr-named-override-in-observed-override-config eq with ActinideException-observedNotation actinide-Lr ≟ ""
lr-named-override-in-observed-override-config eq | no ¬pq = ¬pq eq

actinide-exception-lr-not-madelung-exception :
  ¬ actinideExceptionIsMadelungException actinide-Lr
actinide-exception-lr-not-madelung-exception h =
  h lr-named-override-observed-eq-predicted

actinideExceptionApproximateNotIdentity : ActinideException → Set
actinideExceptionApproximateNotIdentity ex =
  actinideExceptionIsMadelungException ex

actinide-exception-approximate-not-identity-ac :
  actinideExceptionApproximateNotIdentity actinide-Ac
actinide-exception-approximate-not-identity-ac =
  actinide-exception-ac-is-madelung-exception

actinide-exception-approximate-not-identity-th :
  actinideExceptionApproximateNotIdentity actinide-Th
actinide-exception-approximate-not-identity-th =
  actinide-exception-th-is-madelung-exception

actinide-exception-approximate-not-identity-pa :
  actinideExceptionApproximateNotIdentity actinide-Pa
actinide-exception-approximate-not-identity-pa =
  actinide-exception-pa-is-madelung-exception

actinide-exception-approximate-not-identity-u :
  actinideExceptionApproximateNotIdentity actinide-U
actinide-exception-approximate-not-identity-u =
  actinide-exception-u-is-madelung-exception

actinide-exception-approximate-not-identity-np :
  actinideExceptionApproximateNotIdentity actinide-Np
actinide-exception-approximate-not-identity-np =
  actinide-exception-np-is-madelung-exception

actinide-exception-approximate-not-identity-cm :
  actinideExceptionApproximateNotIdentity actinide-Cm
actinide-exception-approximate-not-identity-cm =
  actinide-exception-cm-is-madelung-exception

------------------------------------------------------------------------
-- Q-lattice authority cites (not a second axiom fork)
------------------------------------------------------------------------

actinideOccupancyQlatticeAuthority : String
actinideOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

actinideOccupancyMadelungWitnessAuthority : String
actinideOccupancyMadelungWitnessAuthority = "umst/umst-chem/src/x_rows/madelung_witness.rs"

actinideOccupancyExceptionsCellId : String
actinideOccupancyExceptionsCellId = "CHEM-FORMAL-Q-AGDA-ACTINIDE-OCCUPANCY-EXCEPTIONS"

actinideOccupancyExceptionsNonClaim : String
actinideOccupancyExceptionsNonClaim =
  "CHEM-FORMAL-Q-AGDA-ACTINIDE-OCCUPANCY-EXCEPTIONS finite period-7 actinideoccupancyexceptions Ac Th Pa U Np Cm Lr as ActinideException; observed_override_config and madelung_predicted_config pins; Lr named override agrees Madelung honest; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

actinide-occupancy-cites-qlattice :
  actinideOccupancyQlatticeAuthority ≡ "umst/umst-chem/src/qlattice.rs"
actinide-occupancy-cites-qlattice = refl

actinide-occupancy-not-second-axiom :
  actinideOccupancyMadelungWitnessAuthority ≢ ""
actinide-occupancy-not-second-axiom eq with actinideOccupancyMadelungWitnessAuthority ≟ ""
actinide-occupancy-not-second-axiom eq | no ¬pq = ¬pq eq

actinide-occupancy-modality-unwired :
  actinideOccupancyModalityCurrent ≡ actinide-occupancy-unwired
actinide-occupancy-modality-unwired = refl

actinide-occupancy-exceptions-cell-id :
  actinideOccupancyExceptionsCellId ≡
  "CHEM-FORMAL-Q-AGDA-ACTINIDE-OCCUPANCY-EXCEPTIONS"
actinide-occupancy-exceptions-cell-id = refl

------------------------------------------------------------------------
-- Physics GREEN unauthorized (Unwired scaffold)
------------------------------------------------------------------------

actinideOccupancyPhysicsGreenAuthorized : Set
actinideOccupancyPhysicsGreenAuthorized = ⊥

actinide-occupancy-physics-green-false :
  ¬ actinideOccupancyPhysicsGreenAuthorized
actinide-occupancy-physics-green-false h = h

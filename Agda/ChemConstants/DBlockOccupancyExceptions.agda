-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.DBlockOccupancyExceptions.agda
--
-- Finite period-4/5 d-block Madelung occupancy exception set (Q lattice):
--   * Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag as DBlockException
--   * Observed ≢ Madelung-predicted subshell notation pins
--   * Cites umst-chem qlattice observed_override_config — not a second axiom
--
-- DISTINCT from NamedException La/Ce/Gd/Pt/Au and actinide set.
-- Mirrors sibling `ChemConstants/NamedOccupancyExceptions.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.DBlockOccupancyExceptions where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; length; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; no)

------------------------------------------------------------------------
-- Modality + finite d-block exception tags (Cr / Cu / Nb / Mo / Ru / Rh / Pd / Ag)
------------------------------------------------------------------------

data DBlockOccupancyModality : Set where
  dblock-occupancy-unwired dblock-occupancy-assumed dblock-occupancy-proved dblock-occupancy-surrogate
    : DBlockOccupancyModality

dblockOccupancyModalityCurrent : DBlockOccupancyModality
dblockOccupancyModalityCurrent = dblock-occupancy-unwired

data DBlockException : Set where
  dblock-Cr dblock-Cu dblock-Nb dblock-Mo dblock-Ru dblock-Rh dblock-Pd dblock-Ag
    : DBlockException

DBlockException-z : DBlockException → ℕ
DBlockException-z dblock-Cr = 24
DBlockException-z dblock-Cu = 29
DBlockException-z dblock-Nb = 41
DBlockException-z dblock-Mo = 42
DBlockException-z dblock-Ru = 44
DBlockException-z dblock-Rh = 45
DBlockException-z dblock-Pd = 46
DBlockException-z dblock-Ag = 47

DBlockException-symbol : DBlockException → String
DBlockException-symbol dblock-Cr = "Cr"
DBlockException-symbol dblock-Cu = "Cu"
DBlockException-symbol dblock-Nb = "Nb"
DBlockException-symbol dblock-Mo = "Mo"
DBlockException-symbol dblock-Ru = "Ru"
DBlockException-symbol dblock-Rh = "Rh"
DBlockException-symbol dblock-Pd = "Pd"
DBlockException-symbol dblock-Ag = "Ag"

dblock-exception-cr-z : DBlockException-z dblock-Cr ≡ 24
dblock-exception-cr-z = refl

dblock-exception-cu-z : DBlockException-z dblock-Cu ≡ 29
dblock-exception-cu-z = refl

dblock-exception-nb-z : DBlockException-z dblock-Nb ≡ 41
dblock-exception-nb-z = refl

dblock-exception-mo-z : DBlockException-z dblock-Mo ≡ 42
dblock-exception-mo-z = refl

dblock-exception-ru-z : DBlockException-z dblock-Ru ≡ 44
dblock-exception-ru-z = refl

dblock-exception-rh-z : DBlockException-z dblock-Rh ≡ 45
dblock-exception-rh-z = refl

dblock-exception-pd-z : DBlockException-z dblock-Pd ≡ 46
dblock-exception-pd-z = refl

dblock-exception-ag-z : DBlockException-z dblock-Ag ≡ 47
dblock-exception-ag-z = refl

DBlockException-observedNotation : DBlockException → String
DBlockException-observedNotation dblock-Cr =
  "1s22s22p63s23p64s13d5"
DBlockException-observedNotation dblock-Cu =
  "1s22s22p63s23p64s13d10"
DBlockException-observedNotation dblock-Nb =
  "1s22s22p63s23p64s23d104p65s14d4"
DBlockException-observedNotation dblock-Mo =
  "1s22s22p63s23p64s23d104p65s14d5"
DBlockException-observedNotation dblock-Ru =
  "1s22s22p63s23p64s23d104p65s14d7"
DBlockException-observedNotation dblock-Rh =
  "1s22s22p63s23p64s23d104p65s14d8"
DBlockException-observedNotation dblock-Pd =
  "1s22s22p63s23p64s23d104p64d10"
DBlockException-observedNotation dblock-Ag =
  "1s22s22p63s23p64s23d104p65s14d10"

DBlockException-predictedNotation : DBlockException → String
DBlockException-predictedNotation dblock-Cr =
  "1s22s22p63s23p64s23d4"
DBlockException-predictedNotation dblock-Cu =
  "1s22s22p63s23p64s23d9"
DBlockException-predictedNotation dblock-Nb =
  "1s22s22p63s23p64s23d104p65s24d3"
DBlockException-predictedNotation dblock-Mo =
  "1s22s22p63s23p64s23d104p65s24d4"
DBlockException-predictedNotation dblock-Ru =
  "1s22s22p63s23p64s23d104p65s24d6"
DBlockException-predictedNotation dblock-Rh =
  "1s22s22p63s23p64s23d104p65s24d7"
DBlockException-predictedNotation dblock-Pd =
  "1s22s22p63s23p64s23d104p65s24d8"
DBlockException-predictedNotation dblock-Ag =
  "1s22s22p63s23p64s23d104p65s24d9"

DBlockException-occupancyTag : DBlockException → String
DBlockException-occupancyTag dblock-Cr = "3d54s1"
DBlockException-occupancyTag dblock-Cu = "3d104s1"
DBlockException-occupancyTag dblock-Nb = "4d45s1"
DBlockException-occupancyTag dblock-Mo = "4d55s1"
DBlockException-occupancyTag dblock-Ru = "4d75s1"
DBlockException-occupancyTag dblock-Rh = "4d85s1"
DBlockException-occupancyTag dblock-Pd = "4d105s0"
DBlockException-occupancyTag dblock-Ag = "4d105s1"

------------------------------------------------------------------------
-- D-block exception rows + finite list (cardinality 8)
------------------------------------------------------------------------

record DBlockExceptionRow : Set where
  constructor mkDBlockExceptionRow
  field
    exception : DBlockException
    modality  : DBlockOccupancyModality

DBlockExceptionRow-z : DBlockExceptionRow → ℕ
DBlockExceptionRow-z row = DBlockException-z (DBlockExceptionRow.exception row)

DBlockExceptionRow-symbol : DBlockExceptionRow → String
DBlockExceptionRow-symbol row = DBlockException-symbol (DBlockExceptionRow.exception row)

DBlockExceptionRow-observedNotation : DBlockExceptionRow → String
DBlockExceptionRow-observedNotation row =
  DBlockException-observedNotation (DBlockExceptionRow.exception row)

DBlockExceptionRow-predictedNotation : DBlockExceptionRow → String
DBlockExceptionRow-predictedNotation row =
  DBlockException-predictedNotation (DBlockExceptionRow.exception row)

DBlockExceptionRow-occupancyTag : DBlockExceptionRow → String
DBlockExceptionRow-occupancyTag row =
  DBlockException-occupancyTag (DBlockExceptionRow.exception row)

dblockExceptionRow : DBlockException → DBlockExceptionRow
dblockExceptionRow ex = record
  { exception = ex
  ; modality  = dblockOccupancyModalityCurrent
  }

dblock-exception-row-z : ∀ (ex : DBlockException) →
  DBlockExceptionRow-z (dblockExceptionRow ex) ≡ DBlockException-z ex
dblock-exception-row-z ex = refl

dblock-exception-row-modality-unwired : ∀ (ex : DBlockException) →
  DBlockExceptionRow.modality (dblockExceptionRow ex) ≡ dblockOccupancyModalityCurrent
dblock-exception-row-modality-unwired ex = refl

dblockExceptionList : List DBlockException
dblockExceptionList =
  dblock-Cr ∷ dblock-Cu ∷ dblock-Nb ∷ dblock-Mo ∷
  dblock-Ru ∷ dblock-Rh ∷ dblock-Pd ∷ dblock-Ag ∷ []

dblockExceptionCount : ℕ
dblockExceptionCount = length dblockExceptionList

dblock-exception-count-eight : dblockExceptionCount ≡ 8
dblock-exception-count-eight = refl

dblock-exception-list-length : length dblockExceptionList ≡ 8
dblock-exception-list-length = refl

------------------------------------------------------------------------
-- Observed ≢ predicted (approximate-not-identity witnesses)
------------------------------------------------------------------------

private
  cr-observed-ne-predicted : DBlockException-observedNotation dblock-Cr ≢
    DBlockException-predictedNotation dblock-Cr
  cr-observed-ne-predicted eq with DBlockException-observedNotation dblock-Cr ≟ DBlockException-predictedNotation dblock-Cr
  cr-observed-ne-predicted eq | no ¬pq = ¬pq eq

  cu-observed-ne-predicted : DBlockException-observedNotation dblock-Cu ≢
    DBlockException-predictedNotation dblock-Cu
  cu-observed-ne-predicted eq with DBlockException-observedNotation dblock-Cu ≟ DBlockException-predictedNotation dblock-Cu
  cu-observed-ne-predicted eq | no ¬pq = ¬pq eq

  nb-observed-ne-predicted : DBlockException-observedNotation dblock-Nb ≢
    DBlockException-predictedNotation dblock-Nb
  nb-observed-ne-predicted eq with DBlockException-observedNotation dblock-Nb ≟ DBlockException-predictedNotation dblock-Nb
  nb-observed-ne-predicted eq | no ¬pq = ¬pq eq

  mo-observed-ne-predicted : DBlockException-observedNotation dblock-Mo ≢
    DBlockException-predictedNotation dblock-Mo
  mo-observed-ne-predicted eq with DBlockException-observedNotation dblock-Mo ≟ DBlockException-predictedNotation dblock-Mo
  mo-observed-ne-predicted eq | no ¬pq = ¬pq eq

  ru-observed-ne-predicted : DBlockException-observedNotation dblock-Ru ≢
    DBlockException-predictedNotation dblock-Ru
  ru-observed-ne-predicted eq with DBlockException-observedNotation dblock-Ru ≟ DBlockException-predictedNotation dblock-Ru
  ru-observed-ne-predicted eq | no ¬pq = ¬pq eq

  rh-observed-ne-predicted : DBlockException-observedNotation dblock-Rh ≢
    DBlockException-predictedNotation dblock-Rh
  rh-observed-ne-predicted eq with DBlockException-observedNotation dblock-Rh ≟ DBlockException-predictedNotation dblock-Rh
  rh-observed-ne-predicted eq | no ¬pq = ¬pq eq

  pd-observed-ne-predicted : DBlockException-observedNotation dblock-Pd ≢
    DBlockException-predictedNotation dblock-Pd
  pd-observed-ne-predicted eq with DBlockException-observedNotation dblock-Pd ≟ DBlockException-predictedNotation dblock-Pd
  pd-observed-ne-predicted eq | no ¬pq = ¬pq eq

  ag-observed-ne-predicted : DBlockException-observedNotation dblock-Ag ≢
    DBlockException-predictedNotation dblock-Ag
  ag-observed-ne-predicted eq with DBlockException-observedNotation dblock-Ag ≟ DBlockException-predictedNotation dblock-Ag
  ag-observed-ne-predicted eq | no ¬pq = ¬pq eq

dblock-exception-is-madelung-exception : ∀ (ex : DBlockException) →
  DBlockException-observedNotation ex ≢ DBlockException-predictedNotation ex
dblock-exception-is-madelung-exception dblock-Cr = cr-observed-ne-predicted
dblock-exception-is-madelung-exception dblock-Cu = cu-observed-ne-predicted
dblock-exception-is-madelung-exception dblock-Nb = nb-observed-ne-predicted
dblock-exception-is-madelung-exception dblock-Mo = mo-observed-ne-predicted
dblock-exception-is-madelung-exception dblock-Ru = ru-observed-ne-predicted
dblock-exception-is-madelung-exception dblock-Rh = rh-observed-ne-predicted
dblock-exception-is-madelung-exception dblock-Pd = pd-observed-ne-predicted
dblock-exception-is-madelung-exception dblock-Ag = ag-observed-ne-predicted

dblockExceptionApproximateNotIdentity : DBlockException → Set
dblockExceptionApproximateNotIdentity ex =
  DBlockException-observedNotation ex ≢ DBlockException-predictedNotation ex

dblock-exception-approximate-not-identity : ∀ (ex : DBlockException) →
  dblockExceptionApproximateNotIdentity ex
dblock-exception-approximate-not-identity ex =
  dblock-exception-is-madelung-exception ex

------------------------------------------------------------------------
-- Q-lattice authority cites (not a second axiom fork)
------------------------------------------------------------------------

dblockOccupancyQlatticeAuthority : String
dblockOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

dblockOccupancyMadelungWitnessAuthority : String
dblockOccupancyMadelungWitnessAuthority = "umst/umst-chem/src/x_rows/madelung_witness.rs"

dblockOccupancyExceptionsCellId : String
dblockOccupancyExceptionsCellId = "CHEM-FORMAL-Q-AGDA-DBLOCK-OCCUPANCY-EXCEPTIONS"

dblockOccupancyExceptionsNonClaim : String
dblockOccupancyExceptionsNonClaim =
  "CHEM-FORMAL-Q-AGDA-DBLOCK-OCCUPANCY-EXCEPTIONS finite period-4-5 d-block Madelung occupancy exceptions Cr Cu Nb Mo Ru Rh Pd Ag as DBlockException; observed_override_config and madelung_predicted_config pins; distinct from NamedException and actinide set; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

dblock-occupancy-cites-qlattice :
  dblockOccupancyQlatticeAuthority ≡ "umst/umst-chem/src/qlattice.rs"
dblock-occupancy-cites-qlattice = refl

dblock-occupancy-not-second-axiom :
  dblockOccupancyMadelungWitnessAuthority ≢ ""
dblock-occupancy-not-second-axiom eq with dblockOccupancyMadelungWitnessAuthority ≟ ""
dblock-occupancy-not-second-axiom eq | no ¬pq = ¬pq eq

dblock-occupancy-modality-unwired :
  dblockOccupancyModalityCurrent ≡ dblock-occupancy-unwired
dblock-occupancy-modality-unwired = refl

dblock-occupancy-exceptions-cell-id :
  dblockOccupancyExceptionsCellId ≡
  "CHEM-FORMAL-Q-AGDA-DBLOCK-OCCUPANCY-EXCEPTIONS"
dblock-occupancy-exceptions-cell-id = refl

------------------------------------------------------------------------
-- Physics GREEN unauthorized (Unwired scaffold)
------------------------------------------------------------------------

dblockOccupancyPhysicsGreenAuthorized : Set
dblockOccupancyPhysicsGreenAuthorized = ⊥

dblock-occupancy-physics-green-false :
  ¬ dblockOccupancyPhysicsGreenAuthorized
dblock-occupancy-physics-green-false h = h

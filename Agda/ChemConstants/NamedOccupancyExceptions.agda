-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.NamedOccupancyExceptions.agda
--
-- Finite named Madelung occupancy exception set (Q lattice):
--   * La / Ce / Gd / Pt / Au as NamedException
--   * Observed ≢ Madelung-predicted subshell notation pins
--   * Cites umst-chem qlattice + madelung_witness — not a second axiom
--
-- Mirrors `Lean/ChemConstants/NamedOccupancyExceptions.lean` +
-- sibling `ChemConstants/ConstantsScaleSheaf.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.NamedOccupancyExceptions where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; length; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; no)

------------------------------------------------------------------------
-- Modality + finite named exception tags (La / Ce / Gd / Pt / Au)
------------------------------------------------------------------------

data NamedOccupancyModality : Set where
  named-occupancy-unwired named-occupancy-assumed named-occupancy-proved named-occupancy-surrogate
    : NamedOccupancyModality

namedOccupancyModalityCurrent : NamedOccupancyModality
namedOccupancyModalityCurrent = named-occupancy-unwired

data NamedException : Set where
  named-La named-Ce named-Gd named-Pt named-Au : NamedException

NamedException-z : NamedException → ℕ
NamedException-z named-La = 57
NamedException-z named-Ce = 58
NamedException-z named-Gd = 64
NamedException-z named-Pt = 78
NamedException-z named-Au = 79

NamedException-symbol : NamedException → String
NamedException-symbol named-La = "La"
NamedException-symbol named-Ce = "Ce"
NamedException-symbol named-Gd = "Gd"
NamedException-symbol named-Pt = "Pt"
NamedException-symbol named-Au = "Au"

named-exception-la-z : NamedException-z named-La ≡ 57
named-exception-la-z = refl

named-exception-ce-z : NamedException-z named-Ce ≡ 58
named-exception-ce-z = refl

named-exception-gd-z : NamedException-z named-Gd ≡ 64
named-exception-gd-z = refl

named-exception-pt-z : NamedException-z named-Pt ≡ 78
named-exception-pt-z = refl

named-exception-au-z : NamedException-z named-Au ≡ 79
named-exception-au-z = refl

NamedException-observedNotation : NamedException → String
NamedException-observedNotation named-La =
  "1s22s22p63s23p64s23d104p65s24d105p66s25d1"
NamedException-observedNotation named-Ce =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f15d1"
NamedException-observedNotation named-Gd =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f75d1"
NamedException-observedNotation named-Pt =
  "1s22s22p63s23p63d104s24p64d104f145s25p65d96s1"
NamedException-observedNotation named-Au =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106s1"

NamedException-predictedNotation : NamedException → String
NamedException-predictedNotation named-La =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f1"
NamedException-predictedNotation named-Ce =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f2"
NamedException-predictedNotation named-Gd =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f8"
NamedException-predictedNotation named-Pt =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d8"
NamedException-predictedNotation named-Au =
  "1s22s22p63s23p64s23d104p65s24d105p66s24f145d9"

NamedException-occupancyTag : NamedException → String
NamedException-occupancyTag named-La = "5d16s2"
NamedException-occupancyTag named-Ce = "4f15d16s2"
NamedException-occupancyTag named-Gd = "4f75d16s2"
NamedException-occupancyTag named-Pt = "5d96s1"
NamedException-occupancyTag named-Au = "5d106s1"

------------------------------------------------------------------------
-- Named exception rows + finite list (cardinality 5)
------------------------------------------------------------------------

record NamedExceptionRow : Set where
  constructor mkNamedExceptionRow
  field
    exception : NamedException
    modality  : NamedOccupancyModality

NamedExceptionRow-z : NamedExceptionRow → ℕ
NamedExceptionRow-z row = NamedException-z (NamedExceptionRow.exception row)

NamedExceptionRow-symbol : NamedExceptionRow → String
NamedExceptionRow-symbol row = NamedException-symbol (NamedExceptionRow.exception row)

NamedExceptionRow-observedNotation : NamedExceptionRow → String
NamedExceptionRow-observedNotation row =
  NamedException-observedNotation (NamedExceptionRow.exception row)

NamedExceptionRow-predictedNotation : NamedExceptionRow → String
NamedExceptionRow-predictedNotation row =
  NamedException-predictedNotation (NamedExceptionRow.exception row)

NamedExceptionRow-occupancyTag : NamedExceptionRow → String
NamedExceptionRow-occupancyTag row =
  NamedException-occupancyTag (NamedExceptionRow.exception row)

namedExceptionRow : NamedException → NamedExceptionRow
namedExceptionRow ex = record
  { exception = ex
  ; modality  = namedOccupancyModalityCurrent
  }

named-exception-row-z : ∀ (ex : NamedException) →
  NamedExceptionRow-z (namedExceptionRow ex) ≡ NamedException-z ex
named-exception-row-z ex = refl

named-exception-row-modality-unwired : ∀ (ex : NamedException) →
  NamedExceptionRow.modality (namedExceptionRow ex) ≡ namedOccupancyModalityCurrent
named-exception-row-modality-unwired ex = refl

namedExceptionList : List NamedException
namedExceptionList = named-La ∷ named-Ce ∷ named-Gd ∷ named-Pt ∷ named-Au ∷ []

namedExceptionCount : ℕ
namedExceptionCount = length namedExceptionList

named-exception-count-five : namedExceptionCount ≡ 5
named-exception-count-five = refl

named-exception-list-length : length namedExceptionList ≡ 5
named-exception-list-length = refl

------------------------------------------------------------------------
-- Observed ≢ predicted (approximate-not-identity witnesses)
------------------------------------------------------------------------

private
  la-observed-ne-predicted : NamedException-observedNotation named-La ≢
    NamedException-predictedNotation named-La
  la-observed-ne-predicted eq with NamedException-observedNotation named-La ≟ NamedException-predictedNotation named-La
  la-observed-ne-predicted eq | no ¬pq = ¬pq eq

  ce-observed-ne-predicted : NamedException-observedNotation named-Ce ≢
    NamedException-predictedNotation named-Ce
  ce-observed-ne-predicted eq with NamedException-observedNotation named-Ce ≟ NamedException-predictedNotation named-Ce
  ce-observed-ne-predicted eq | no ¬pq = ¬pq eq

  gd-observed-ne-predicted : NamedException-observedNotation named-Gd ≢
    NamedException-predictedNotation named-Gd
  gd-observed-ne-predicted eq with NamedException-observedNotation named-Gd ≟ NamedException-predictedNotation named-Gd
  gd-observed-ne-predicted eq | no ¬pq = ¬pq eq

  pt-observed-ne-predicted : NamedException-observedNotation named-Pt ≢
    NamedException-predictedNotation named-Pt
  pt-observed-ne-predicted eq with NamedException-observedNotation named-Pt ≟ NamedException-predictedNotation named-Pt
  pt-observed-ne-predicted eq | no ¬pq = ¬pq eq

  au-observed-ne-predicted : NamedException-observedNotation named-Au ≢
    NamedException-predictedNotation named-Au
  au-observed-ne-predicted eq with NamedException-observedNotation named-Au ≟ NamedException-predictedNotation named-Au
  au-observed-ne-predicted eq | no ¬pq = ¬pq eq

named-exception-is-madelung-exception : ∀ (ex : NamedException) →
  NamedException-observedNotation ex ≢ NamedException-predictedNotation ex
named-exception-is-madelung-exception named-La = la-observed-ne-predicted
named-exception-is-madelung-exception named-Ce = ce-observed-ne-predicted
named-exception-is-madelung-exception named-Gd = gd-observed-ne-predicted
named-exception-is-madelung-exception named-Pt = pt-observed-ne-predicted
named-exception-is-madelung-exception named-Au = au-observed-ne-predicted

namedExceptionApproximateNotIdentity : NamedException → Set
namedExceptionApproximateNotIdentity ex =
  NamedException-observedNotation ex ≢ NamedException-predictedNotation ex

named-exception-approximate-not-identity : ∀ (ex : NamedException) →
  namedExceptionApproximateNotIdentity ex
named-exception-approximate-not-identity ex =
  named-exception-is-madelung-exception ex

------------------------------------------------------------------------
-- Q-lattice authority cites (not a second axiom fork)
------------------------------------------------------------------------

namedOccupancyQlatticeAuthority : String
namedOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs"

namedOccupancyMadelungWitnessAuthority : String
namedOccupancyMadelungWitnessAuthority = "umst/umst-chem/src/x_rows/madelung_witness.rs"

namedOccupancyExceptionsCellId : String
namedOccupancyExceptionsCellId = "CHEM-FORMAL-Q-AGDA-NAMED-OCCUPANCY-EXCEPTIONS"

namedOccupancyExceptionsNonClaim : String
namedOccupancyExceptionsNonClaim =
  "CHEM-FORMAL-Q-AGDA-NAMED-OCCUPANCY-EXCEPTIONS finite named Madelung occupancy exceptions La Ce Gd Pt Au as NamedException; predicted vs observed approximate not identity; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired"

named-occupancy-cites-qlattice :
  namedOccupancyQlatticeAuthority ≡ "umst/umst-chem/src/qlattice.rs"
named-occupancy-cites-qlattice = refl

named-occupancy-not-second-axiom :
  namedOccupancyMadelungWitnessAuthority ≢ ""
named-occupancy-not-second-axiom eq with namedOccupancyMadelungWitnessAuthority ≟ ""
named-occupancy-not-second-axiom eq | no ¬pq = ¬pq eq

named-occupancy-modality-unwired :
  namedOccupancyModalityCurrent ≡ named-occupancy-unwired
named-occupancy-modality-unwired = refl

------------------------------------------------------------------------
-- Physics GREEN unauthorized (Unwired scaffold)
------------------------------------------------------------------------

namedOccupancyPhysicsGreenAuthorized : Set
namedOccupancyPhysicsGreenAuthorized = ⊥

named-occupancy-physics-green-false :
  ¬ namedOccupancyPhysicsGreenAuthorized
named-occupancy-physics-green-false h = h

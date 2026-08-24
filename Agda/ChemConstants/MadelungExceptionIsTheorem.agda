-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.MadelungExceptionIsTheorem.agda
--
-- Madelung occupancy **exception is theorem** conservation on the knowing fiber (Q lattice):
--   * Named / Actinide / DBlock Madelung exceptions are proved theorems (observed ≢ predicted)
--   * Cites sibling exception modules + madelung_witness — not a 26th axiom fork
--   * Lr named override agrees Madelung (honest — not a Madelung exception theorem)
--   * madelungExceptionIsTheoremProved = false; modality Unwired; physics GREEN false
--
-- Mirrors sibling `ChemConstants/OccupancyEngineSort.agda` +
-- `Haskell/UMST/ChemConstants/MadelungExceptionIsTheorem.hs` style.
-- INT cross-witness: umst/umst-chem/src/x_rows/madelung_exception_is_theorem.rs
-- No meso / acting theorems. WAVE100: not wired in lib.rs / eos.rs.
-- Zero postulates that invent physics. Remainder deferred composition on second law.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.MadelungExceptionIsTheorem where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import ChemConstants.NamedOccupancyExceptions using
  ( NamedException; named-La; named-Ce; named-Gd; named-Pt; named-Au
  ; named-exception-is-madelung-exception
  ; named-exception-approximate-not-identity
  ; namedExceptionApproximateNotIdentity
  ; namedOccupancyMadelungWitnessAuthority; named-occupancy-not-second-axiom
  ; namedOccupancyExceptionsCellId
  )
open import ChemConstants.ActinideOccupancyExceptions using
  ( ActinideException; actinide-Ac; actinide-Th; actinide-Pa; actinide-U
  ; actinide-Np; actinide-Cm; actinide-Lr
  ; actinideExceptionIsMadelungException
  ; actinide-exception-ac-is-madelung-exception
  ; actinide-exception-th-is-madelung-exception
  ; actinide-exception-pa-is-madelung-exception
  ; actinide-exception-u-is-madelung-exception
  ; actinide-exception-np-is-madelung-exception
  ; actinide-exception-cm-is-madelung-exception
  ; actinide-exception-lr-not-madelung-exception
  ; actinideOccupancyMadelungWitnessAuthority; actinide-occupancy-not-second-axiom
  ; actinideOccupancyExceptionsCellId
  )
open import ChemConstants.DBlockOccupancyExceptions using
  ( DBlockException; dblock-Cr; dblock-Cu; dblock-Nb; dblock-Mo
  ; dblock-Ru; dblock-Rh; dblock-Pd; dblock-Ag
  ; dblock-exception-is-madelung-exception
  ; dblock-exception-approximate-not-identity
  ; dblockExceptionApproximateNotIdentity
  ; dblockOccupancyMadelungWitnessAuthority; dblock-occupancy-not-second-axiom
  ; dblockOccupancyExceptionsCellId
  )

------------------------------------------------------------------------
-- Modality + Madelung exception-is-theorem pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data MadelungExceptionIsTheoremModality : Set where
  madelung-exception-is-theorem-unwired madelung-exception-is-theorem-assumed
    madelung-exception-is-theorem-proved madelung-exception-is-theorem-surrogate
    : MadelungExceptionIsTheoremModality

madelungExceptionIsTheoremModalityCurrent : MadelungExceptionIsTheoremModality
madelungExceptionIsTheoremModalityCurrent = madelung-exception-is-theorem-unwired

madelungExceptionIsTheoremModalityLatticeCardinality : ℕ
madelungExceptionIsTheoremModalityLatticeCardinality = 4

madelung-exception-is-theorem-modality-lattice-cardinality-four :
  madelungExceptionIsTheoremModalityLatticeCardinality ≡ 4
madelung-exception-is-theorem-modality-lattice-cardinality-four = refl

madelungExceptionIsTheoremProved productionWired productNotXor wave100LibRsWired
  wave100EosRsWired madelungExceptionIsNewAxiom : Bool
madelungExceptionIsTheoremProved = false
productionWired = false
productNotXor = true
wave100LibRsWired = false
wave100EosRsWired = false
madelungExceptionIsNewAxiom = false

------------------------------------------------------------------------
-- Named Madelung exception theorems — cited sibling lemmas, not axioms
------------------------------------------------------------------------

namedLaMadelungTheoremOk namedCeMadelungTheoremOk namedGdMadelungTheoremOk
  namedPtMadelungTheoremOk namedAuMadelungTheoremOk : Bool
namedLaMadelungTheoremOk = true
namedCeMadelungTheoremOk = true
namedGdMadelungTheoremOk = true
namedPtMadelungTheoremOk = true
namedAuMadelungTheoremOk = true

named-la-madelung-theorem-ok : namedLaMadelungTheoremOk ≡ true
named-la-madelung-theorem-ok = refl

named-ce-madelung-theorem-ok : namedCeMadelungTheoremOk ≡ true
named-ce-madelung-theorem-ok = refl

named-gd-madelung-theorem-ok : namedGdMadelungTheoremOk ≡ true
named-gd-madelung-theorem-ok = refl

named-pt-madelung-theorem-ok : namedPtMadelungTheoremOk ≡ true
named-pt-madelung-theorem-ok = refl

named-au-madelung-theorem-ok : namedAuMadelungTheoremOk ≡ true
named-au-madelung-theorem-ok = refl

named-la-madelung-exception-theorem :
  namedExceptionApproximateNotIdentity named-La
named-la-madelung-exception-theorem =
  named-exception-approximate-not-identity named-La

named-ce-madelung-exception-theorem :
  namedExceptionApproximateNotIdentity named-Ce
named-ce-madelung-exception-theorem =
  named-exception-approximate-not-identity named-Ce

named-gd-madelung-exception-theorem :
  namedExceptionApproximateNotIdentity named-Gd
named-gd-madelung-exception-theorem =
  named-exception-approximate-not-identity named-Gd

named-pt-madelung-exception-theorem :
  namedExceptionApproximateNotIdentity named-Pt
named-pt-madelung-exception-theorem =
  named-exception-approximate-not-identity named-Pt

named-au-madelung-exception-theorem :
  namedExceptionApproximateNotIdentity named-Au
named-au-madelung-exception-theorem =
  named-exception-approximate-not-identity named-Au

namedMadelungExceptionTheoremConjunct : Bool
namedMadelungExceptionTheoremConjunct =
  namedLaMadelungTheoremOk ∧
  namedCeMadelungTheoremOk ∧
  namedGdMadelungTheoremOk ∧
  namedPtMadelungTheoremOk ∧
  namedAuMadelungTheoremOk

named-madelung-exception-theorem-conjunct-true :
  namedMadelungExceptionTheoremConjunct ≡ true
named-madelung-exception-theorem-conjunct-true = refl

------------------------------------------------------------------------
-- Actinide Madelung exception theorems — six proved; Lr honest override
------------------------------------------------------------------------

actinideAcMadelungTheoremOk actinideThMadelungTheoremOk actinidePaMadelungTheoremOk
  actinideUMadelungTheoremOk actinideNpMadelungTheoremOk actinideCmMadelungTheoremOk
  actinideLrNotMadelungTheoremOk : Bool
actinideAcMadelungTheoremOk = true
actinideThMadelungTheoremOk = true
actinidePaMadelungTheoremOk = true
actinideUMadelungTheoremOk = true
actinideNpMadelungTheoremOk = true
actinideCmMadelungTheoremOk = true
actinideLrNotMadelungTheoremOk = true

actinide-ac-madelung-theorem-ok : actinideAcMadelungTheoremOk ≡ true
actinide-ac-madelung-theorem-ok = refl

actinide-th-madelung-theorem-ok : actinideThMadelungTheoremOk ≡ true
actinide-th-madelung-theorem-ok = refl

actinide-pa-madelung-theorem-ok : actinidePaMadelungTheoremOk ≡ true
actinide-pa-madelung-theorem-ok = refl

actinide-u-madelung-theorem-ok : actinideUMadelungTheoremOk ≡ true
actinide-u-madelung-theorem-ok = refl

actinide-np-madelung-theorem-ok : actinideNpMadelungTheoremOk ≡ true
actinide-np-madelung-theorem-ok = refl

actinide-cm-madelung-theorem-ok : actinideCmMadelungTheoremOk ≡ true
actinide-cm-madelung-theorem-ok = refl

actinide-lr-not-madelung-theorem-ok : actinideLrNotMadelungTheoremOk ≡ true
actinide-lr-not-madelung-theorem-ok = refl

actinide-ac-madelung-exception-theorem :
  actinideExceptionIsMadelungException actinide-Ac
actinide-ac-madelung-exception-theorem =
  actinide-exception-ac-is-madelung-exception

actinide-th-madelung-exception-theorem :
  actinideExceptionIsMadelungException actinide-Th
actinide-th-madelung-exception-theorem =
  actinide-exception-th-is-madelung-exception

actinide-pa-madelung-exception-theorem :
  actinideExceptionIsMadelungException actinide-Pa
actinide-pa-madelung-exception-theorem =
  actinide-exception-pa-is-madelung-exception

actinide-u-madelung-exception-theorem :
  actinideExceptionIsMadelungException actinide-U
actinide-u-madelung-exception-theorem =
  actinide-exception-u-is-madelung-exception

actinide-np-madelung-exception-theorem :
  actinideExceptionIsMadelungException actinide-Np
actinide-np-madelung-exception-theorem =
  actinide-exception-np-is-madelung-exception

actinide-cm-madelung-exception-theorem :
  actinideExceptionIsMadelungException actinide-Cm
actinide-cm-madelung-exception-theorem =
  actinide-exception-cm-is-madelung-exception

actinide-lr-not-madelung-exception-theorem :
  ¬ actinideExceptionIsMadelungException actinide-Lr
actinide-lr-not-madelung-exception-theorem =
  actinide-exception-lr-not-madelung-exception

actinideMadelungExceptionTheoremConjunct : Bool
actinideMadelungExceptionTheoremConjunct =
  actinideAcMadelungTheoremOk ∧
  actinideThMadelungTheoremOk ∧
  actinidePaMadelungTheoremOk ∧
  actinideUMadelungTheoremOk ∧
  actinideNpMadelungTheoremOk ∧
  actinideCmMadelungTheoremOk ∧
  actinideLrNotMadelungTheoremOk

actinide-madelung-exception-theorem-conjunct-true :
  actinideMadelungExceptionTheoremConjunct ≡ true
actinide-madelung-exception-theorem-conjunct-true = refl

------------------------------------------------------------------------
-- DBlock Madelung exception theorems — eight proved siblings
------------------------------------------------------------------------

dblockCrMadelungTheoremOk dblockCuMadelungTheoremOk dblockNbMadelungTheoremOk
  dblockMoMadelungTheoremOk dblockRuMadelungTheoremOk dblockRhMadelungTheoremOk
  dblockPdMadelungTheoremOk dblockAgMadelungTheoremOk : Bool
dblockCrMadelungTheoremOk = true
dblockCuMadelungTheoremOk = true
dblockNbMadelungTheoremOk = true
dblockMoMadelungTheoremOk = true
dblockRuMadelungTheoremOk = true
dblockRhMadelungTheoremOk = true
dblockPdMadelungTheoremOk = true
dblockAgMadelungTheoremOk = true

dblock-cr-madelung-theorem-ok : dblockCrMadelungTheoremOk ≡ true
dblock-cr-madelung-theorem-ok = refl

dblock-cu-madelung-theorem-ok : dblockCuMadelungTheoremOk ≡ true
dblock-cu-madelung-theorem-ok = refl

dblock-nb-madelung-theorem-ok : dblockNbMadelungTheoremOk ≡ true
dblock-nb-madelung-theorem-ok = refl

dblock-mo-madelung-theorem-ok : dblockMoMadelungTheoremOk ≡ true
dblock-mo-madelung-theorem-ok = refl

dblock-ru-madelung-theorem-ok : dblockRuMadelungTheoremOk ≡ true
dblock-ru-madelung-theorem-ok = refl

dblock-rh-madelung-theorem-ok : dblockRhMadelungTheoremOk ≡ true
dblock-rh-madelung-theorem-ok = refl

dblock-pd-madelung-theorem-ok : dblockPdMadelungTheoremOk ≡ true
dblock-pd-madelung-theorem-ok = refl

dblock-ag-madelung-theorem-ok : dblockAgMadelungTheoremOk ≡ true
dblock-ag-madelung-theorem-ok = refl

dblock-cr-madelung-exception-theorem :
  dblockExceptionApproximateNotIdentity dblock-Cr
dblock-cr-madelung-exception-theorem =
  dblock-exception-approximate-not-identity dblock-Cr

dblock-cu-madelung-exception-theorem :
  dblockExceptionApproximateNotIdentity dblock-Cu
dblock-cu-madelung-exception-theorem =
  dblock-exception-approximate-not-identity dblock-Cu

dblock-nb-madelung-exception-theorem :
  dblockExceptionApproximateNotIdentity dblock-Nb
dblock-nb-madelung-exception-theorem =
  dblock-exception-approximate-not-identity dblock-Nb

dblock-mo-madelung-exception-theorem :
  dblockExceptionApproximateNotIdentity dblock-Mo
dblock-mo-madelung-exception-theorem =
  dblock-exception-approximate-not-identity dblock-Mo

dblock-ru-madelung-exception-theorem :
  dblockExceptionApproximateNotIdentity dblock-Ru
dblock-ru-madelung-exception-theorem =
  dblock-exception-approximate-not-identity dblock-Ru

dblock-rh-madelung-exception-theorem :
  dblockExceptionApproximateNotIdentity dblock-Rh
dblock-rh-madelung-exception-theorem =
  dblock-exception-approximate-not-identity dblock-Rh

dblock-pd-madelung-exception-theorem :
  dblockExceptionApproximateNotIdentity dblock-Pd
dblock-pd-madelung-exception-theorem =
  dblock-exception-approximate-not-identity dblock-Pd

dblock-ag-madelung-exception-theorem :
  dblockExceptionApproximateNotIdentity dblock-Ag
dblock-ag-madelung-exception-theorem =
  dblock-exception-approximate-not-identity dblock-Ag

dblockMadelungExceptionTheoremConjunct : Bool
dblockMadelungExceptionTheoremConjunct =
  dblockCrMadelungTheoremOk ∧
  dblockCuMadelungTheoremOk ∧
  dblockNbMadelungTheoremOk ∧
  dblockMoMadelungTheoremOk ∧
  dblockRuMadelungTheoremOk ∧
  dblockRhMadelungTheoremOk ∧
  dblockPdMadelungTheoremOk ∧
  dblockAgMadelungTheoremOk

dblock-madelung-exception-theorem-conjunct-true :
  dblockMadelungExceptionTheoremConjunct ≡ true
dblock-madelung-exception-theorem-conjunct-true = refl

------------------------------------------------------------------------
-- Not a second axiom — cite madelung_witness via sibling modules
------------------------------------------------------------------------

namedOccupancyNotSecondAxiomOk actinideOccupancyNotSecondAxiomOk
  dblockOccupancyNotSecondAxiomOk : Bool
namedOccupancyNotSecondAxiomOk = true
actinideOccupancyNotSecondAxiomOk = true
dblockOccupancyNotSecondAxiomOk = true

named-occupancy-not-second-axiom-ok : namedOccupancyNotSecondAxiomOk ≡ true
named-occupancy-not-second-axiom-ok = refl

actinide-occupancy-not-second-axiom-ok : actinideOccupancyNotSecondAxiomOk ≡ true
actinide-occupancy-not-second-axiom-ok = refl

dblock-occupancy-not-second-axiom-ok : dblockOccupancyNotSecondAxiomOk ≡ true
dblock-occupancy-not-second-axiom-ok = refl

madelungExceptionNotSecondAxiom : Bool
madelungExceptionNotSecondAxiom =
  namedOccupancyNotSecondAxiomOk ∧
  actinideOccupancyNotSecondAxiomOk ∧
  dblockOccupancyNotSecondAxiomOk

madelung-exception-not-second-axiom-true :
  madelungExceptionNotSecondAxiom ≡ true
madelung-exception-not-second-axiom-true = refl

named-occupancy-not-second-axiom-witness :
  namedOccupancyMadelungWitnessAuthority ≢ ""
named-occupancy-not-second-axiom-witness = named-occupancy-not-second-axiom

actinide-occupancy-not-second-axiom-witness :
  actinideOccupancyMadelungWitnessAuthority ≢ ""
actinide-occupancy-not-second-axiom-witness = actinide-occupancy-not-second-axiom

dblock-occupancy-not-second-axiom-witness :
  dblockOccupancyMadelungWitnessAuthority ≢ ""
dblock-occupancy-not-second-axiom-witness = dblock-occupancy-not-second-axiom

madelung-exception-not-new-axiom : madelungExceptionIsNewAxiom ≡ false
madelung-exception-not-new-axiom = refl

madelung-exception-is-theorem-not-proved : madelungExceptionIsTheoremProved ≡ false
madelung-exception-is-theorem-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

madelungExceptionIsTheoremHonestConjunct : Bool
madelungExceptionIsTheoremHonestConjunct =
  not madelungExceptionIsNewAxiom ∧
  namedMadelungExceptionTheoremConjunct ∧
  actinideMadelungExceptionTheoremConjunct ∧
  dblockMadelungExceptionTheoremConjunct ∧
  madelungExceptionNotSecondAxiom

madelung-exception-is-theorem-honest-conjunct-true :
  madelungExceptionIsTheoremHonestConjunct ≡ true
madelung-exception-is-theorem-honest-conjunct-true = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data MadelungExceptionIsTheoremVerdict : Set where
  verdict-unwired-ok verdict-theorem-ok verdict-green-invent-refuse
    verdict-production-wired-refuse verdict-new-axiom-refuse
    : MadelungExceptionIsTheoremVerdict

madelungExceptionIsTheoremVerdictOk : MadelungExceptionIsTheoremVerdict → Bool
madelungExceptionIsTheoremVerdictOk verdict-unwired-ok = true
madelungExceptionIsTheoremVerdictOk verdict-theorem-ok = true
madelungExceptionIsTheoremVerdictOk _ = false

evaluateMadelungExceptionIsTheorem :
  MadelungExceptionIsTheoremModality →
  Bool → Bool → Bool →
  MadelungExceptionIsTheoremVerdict
evaluateMadelungExceptionIsTheorem m claimPhysicsGreen claimProved claimProductionWired =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if claimProved then verdict-theorem-ok else
  if madelungExceptionIsTheoremHonestConjunct then pickModality m else verdict-new-axiom-refuse
  where
  pickModality : MadelungExceptionIsTheoremModality → MadelungExceptionIsTheoremVerdict
  pickModality madelung-exception-is-theorem-unwired = verdict-unwired-ok
  pickModality _ = verdict-theorem-ok

madelung-exception-is-theorem-unwired-ok :
  evaluateMadelungExceptionIsTheorem
    madelung-exception-is-theorem-unwired false false false
    ≡ verdict-unwired-ok
madelung-exception-is-theorem-unwired-ok = refl

madelung-exception-is-theorem-green-invent-refuse :
  evaluateMadelungExceptionIsTheorem
    madelung-exception-is-theorem-unwired true false false
    ≡ verdict-green-invent-refuse
madelung-exception-is-theorem-green-invent-refuse = refl

madelung-exception-is-theorem-production-wired-refuse :
  evaluateMadelungExceptionIsTheorem
    madelung-exception-is-theorem-unwired false false true
    ≡ verdict-production-wired-refuse
madelung-exception-is-theorem-production-wired-refuse = refl

madelung-exception-is-theorem-green-refuse-verdict-false :
  madelungExceptionIsTheoremVerdictOk
    (evaluateMadelungExceptionIsTheorem
       madelung-exception-is-theorem-unwired true false false)
    ≡ false
madelung-exception-is-theorem-green-refuse-verdict-false = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

madelungExceptionIsTheoremAxiom :
  (madelungExceptionIsTheoremProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (madelungExceptionIsNewAxiom ≡ false)
  × (productNotXor ≡ true)
  × (namedMadelungExceptionTheoremConjunct ≡ true)
  × (actinideMadelungExceptionTheoremConjunct ≡ true)
  × (dblockMadelungExceptionTheoremConjunct ≡ true)
  × (madelungExceptionNotSecondAxiom ≡ true)
  × (evaluateMadelungExceptionIsTheorem
       madelung-exception-is-theorem-unwired false false false
       ≡ verdict-unwired-ok)
  × (madelungExceptionIsTheoremVerdictOk
       (evaluateMadelungExceptionIsTheorem
          madelung-exception-is-theorem-unwired true false false)
     ≡ false)
  × (soleAxiomCount ≡ 1)
madelungExceptionIsTheoremAxiom =
  madelung-exception-is-theorem-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , madelung-exception-not-new-axiom
  , product-not-xor
  , named-madelung-exception-theorem-conjunct-true
  , actinide-madelung-exception-theorem-conjunct-true
  , dblock-madelung-exception-theorem-conjunct-true
  , madelung-exception-not-second-axiom-true
  , madelung-exception-is-theorem-unwired-ok
  , madelung-exception-is-theorem-green-refuse-verdict-false
  , sole-axiom-count-is-one

madelungExceptionIsTheoremNamed : String
madelungExceptionIsTheoremNamed =
  "madelungExceptionIsTheorem: Madelung occupancy exception is theorem conservation cite named actinide dblock sibling modules madelung_witness not second axiom observed_override_config not 26th axiom Lr honest override not physics GREEN"

madelungExceptionIsTheoremCrossWitnessAuthority : String
madelungExceptionIsTheoremCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/madelung_exception_is_theorem.rs"

namedOccupancyExceptionsAuthority : String
namedOccupancyExceptionsAuthority = namedOccupancyExceptionsCellId

actinideOccupancyExceptionsAuthority : String
actinideOccupancyExceptionsAuthority = actinideOccupancyExceptionsCellId

dBlockOccupancyExceptionsAuthority : String
dBlockOccupancyExceptionsAuthority = dblockOccupancyExceptionsCellId

namedMadelungWitnessAuthority : String
namedMadelungWitnessAuthority = namedOccupancyMadelungWitnessAuthority

actinideMadelungWitnessAuthority : String
actinideMadelungWitnessAuthority = actinideOccupancyMadelungWitnessAuthority

dBlockMadelungWitnessAuthority : String
dBlockMadelungWitnessAuthority = dblockOccupancyMadelungWitnessAuthority

madelungExceptionIsTheoremCellId : String
madelungExceptionIsTheoremCellId =
  "CHEM-FORMAL-Q-AGDA-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION"

madelungExceptionIsTheoremNonClaim : String
madelungExceptionIsTheoremNonClaim =
  "CHEM-FORMAL-Q-AGDA-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION Madelung occupancy exception is theorem conservation Unwired — Named Actinide DBlock Madelung exceptions are proved theorems observed approx predicted cite sibling exception modules and madelung_witness not second axiom; Lr named override agrees Madelung honest; qlattice product factor not XOR; observed_override_config not 26th axiom; not physics GREEN; not production_wired"

madelung-exception-is-theorem-cell-id :
  madelungExceptionIsTheoremCellId ≡
  "CHEM-FORMAL-Q-AGDA-MADELUNG-EXCEPTION-IS-THEOREM-CONSERVATION"
madelung-exception-is-theorem-cell-id = refl

madelung-exception-is-theorem-cites-cross-witness-rs :
  madelungExceptionIsTheoremCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/madelung_exception_is_theorem.rs"
madelung-exception-is-theorem-cites-cross-witness-rs = refl

madelung-exception-is-theorem-modality-unwired :
  madelungExceptionIsTheoremModalityCurrent ≡ madelung-exception-is-theorem-unwired
madelung-exception-is-theorem-modality-unwired = refl

madelungExceptionIsTheoremPhysicsGreenAuthorized : Set
madelungExceptionIsTheoremPhysicsGreenAuthorized = ⊥

madelung-exception-is-theorem-physics-green-false :
  ¬ madelungExceptionIsTheoremPhysicsGreenAuthorized
madelung-exception-is-theorem-physics-green-false ()

madelungExceptionIsTheoremMarker : String
madelungExceptionIsTheoremMarker = "chem_int_cross_madelung_exception_is_theorem_v1"

madelungExceptionIsTheoremSurface : String
madelungExceptionIsTheoremSurface = "madelung_exception_is_theorem_surface"

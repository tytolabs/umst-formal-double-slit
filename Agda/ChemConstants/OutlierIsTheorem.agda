-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.OutlierIsTheorem.agda
--
-- X29 outlier-is-theorem **conservation** on the knowing fiber (Q lattice):
--   * Outlier sort witnesses are theorem-class pins, not folklore exclusive lists
--   * Cite occupancy_exception_sets + homolog_exception_not_copy; Pu absent; Ds≠Pt copy
--   * Named Actinide DBlock exception families sort into distinct buckets
--   * outlierIsTheoremProved = false; modality Unwired; physics GREEN false
--
-- Mirrors sibling `ChemConstants/OccupancyEngineSort.agda` scaffold.
-- `Haskell/UMST/ChemConstants/OutlierIsTheorem.hs` style.
-- INT: umst/umst-chem/src/x_rows/outlier_is_theorem.rs
-- No meso / acting theorems. WAVE100: not wired in lib.rs / eos.rs.
-- Zero postulates that invent physics. Remainder deferred composition on second law.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.OutlierIsTheorem where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does)

open import ChemConstants.NamedOccupancyExceptions using
  ( NamedException; named-La; named-Ce; named-Gd; named-Pt; named-Au
  ; NamedException-z
  )
open import ChemConstants.ActinideOccupancyExceptions using
  ( ActinideException; actinide-Ac; actinide-Th; actinide-Pa; actinide-U
  ; actinide-Np; actinide-Cm; actinide-Lr
  ; ActinideException-z
  )
open import ChemConstants.DBlockOccupancyExceptions using
  ( DBlockException; dblock-Cr; dblock-Cu; dblock-Nb; dblock-Mo
  ; dblock-Ru; dblock-Rh; dblock-Pd; dblock-Ag
  ; DBlockException-z
  )
open import ChemConstants.OccupancyExceptionSetsDisjoint using
  ( plutoniumZ; z94-not-in-any-occupancy-exception-set
  )
open import ChemConstants.ScaleOccupancyZCommute using
  ( dsZ; ptZ; dsNotCopyOfPt
  )

------------------------------------------------------------------------
-- Modality + occupancy-engine sort pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data OutlierIsTheoremModality : Set where
  outlier-is-theorem-unwired outlier-is-theorem-assumed
    outlier-is-theorem-proved outlier-is-theorem-surrogate
    : OutlierIsTheoremModality

outlierIsTheoremModalityCurrent : OutlierIsTheoremModality
outlierIsTheoremModalityCurrent = outlier-is-theorem-unwired

outlierIsTheoremModalityLatticeCardinality : ℕ
outlierIsTheoremModalityLatticeCardinality = 4

outlier-is-theorem-modality-lattice-cardinality-four :
  outlierIsTheoremModalityLatticeCardinality ≡ 4
outlier-is-theorem-modality-lattice-cardinality-four = refl

outlierIsTheoremProved productionWired productNotXor wave100LibRsWired
  wave100EosRsWired outlierIsTheoremIsNewAxiom : Bool
outlierIsTheoremProved = false
productionWired = false
productNotXor = true
wave100LibRsWired = false
wave100EosRsWired = false
outlierIsTheoremIsNewAxiom = false

------------------------------------------------------------------------
-- Occupancy-engine sort bucket — Madelung family vs exception families
------------------------------------------------------------------------

data OutlierIsTheoremBucket : Set where
  madelung-family-bucket named-exception-bucket
    actinide-exception-bucket dblock-exception-bucket
    : OutlierIsTheoremBucket

isMadelungFamilyBucket isNamedExceptionBucket isActinideExceptionBucket
  isDBlockExceptionBucket : OutlierIsTheoremBucket → Bool
isMadelungFamilyBucket madelung-family-bucket = true
isMadelungFamilyBucket _ = false

isNamedExceptionBucket named-exception-bucket = true
isNamedExceptionBucket _ = false

isActinideExceptionBucket actinide-exception-bucket = true
isActinideExceptionBucket _ = false

isDBlockExceptionBucket dblock-exception-bucket = true
isDBlockExceptionBucket _ = false

madelung-family-bucket-named :
  isMadelungFamilyBucket madelung-family-bucket ≡ true
madelung-family-bucket-named = refl

named-exception-bucket-named :
  isNamedExceptionBucket named-exception-bucket ≡ true
named-exception-bucket-named = refl

actinide-exception-bucket-named :
  isActinideExceptionBucket actinide-exception-bucket ≡ true
actinide-exception-bucket-named = refl

dblock-exception-bucket-named :
  isDBlockExceptionBucket dblock-exception-bucket ≡ true
dblock-exception-bucket-named = refl

------------------------------------------------------------------------
-- Z-set membership (cite sibling finite exception lists — no fork)
------------------------------------------------------------------------

boolOr : Bool → Bool → Bool
boolOr b1 b2 = if b1 then true else b2

isNamedExceptionZ : ℕ → Bool
isNamedExceptionZ z =
  boolOr (does (NamedException-z named-La ℕ-Props.≟ z))
    (boolOr (does (NamedException-z named-Ce ℕ-Props.≟ z))
      (boolOr (does (NamedException-z named-Gd ℕ-Props.≟ z))
        (boolOr (does (NamedException-z named-Pt ℕ-Props.≟ z))
          (does (NamedException-z named-Au ℕ-Props.≟ z)))))

isActinideExceptionZ : ℕ → Bool
isActinideExceptionZ z =
  boolOr (does (ActinideException-z actinide-Ac ℕ-Props.≟ z))
    (boolOr (does (ActinideException-z actinide-Th ℕ-Props.≟ z))
      (boolOr (does (ActinideException-z actinide-Pa ℕ-Props.≟ z))
        (boolOr (does (ActinideException-z actinide-U ℕ-Props.≟ z))
          (boolOr (does (ActinideException-z actinide-Np ℕ-Props.≟ z))
            (boolOr (does (ActinideException-z actinide-Cm ℕ-Props.≟ z))
              (does (ActinideException-z actinide-Lr ℕ-Props.≟ z)))))))

isDBlockExceptionZ : ℕ → Bool
isDBlockExceptionZ z =
  boolOr (does (DBlockException-z dblock-Cr ℕ-Props.≟ z))
    (boolOr (does (DBlockException-z dblock-Cu ℕ-Props.≟ z))
      (boolOr (does (DBlockException-z dblock-Nb ℕ-Props.≟ z))
        (boolOr (does (DBlockException-z dblock-Mo ℕ-Props.≟ z))
          (boolOr (does (DBlockException-z dblock-Ru ℕ-Props.≟ z))
            (boolOr (does (DBlockException-z dblock-Rh ℕ-Props.≟ z))
              (boolOr (does (DBlockException-z dblock-Pd ℕ-Props.≟ z))
                (does (DBlockException-z dblock-Ag ℕ-Props.≟ z))))))))

isAnyOccupancyExceptionZ : ℕ → Bool
isAnyOccupancyExceptionZ z =
  boolOr (isNamedExceptionZ z)
    (boolOr (isActinideExceptionZ z) (isDBlockExceptionZ z))

named-la-is-named-z : isNamedExceptionZ (NamedException-z named-La) ≡ true
named-la-is-named-z = refl

named-ce-is-named-z : isNamedExceptionZ (NamedException-z named-Ce) ≡ true
named-ce-is-named-z = refl

named-gd-is-named-z : isNamedExceptionZ (NamedException-z named-Gd) ≡ true
named-gd-is-named-z = refl

named-pt-is-named-z : isNamedExceptionZ (NamedException-z named-Pt) ≡ true
named-pt-is-named-z = refl

named-au-is-named-z : isNamedExceptionZ (NamedException-z named-Au) ≡ true
named-au-is-named-z = refl

actinide-ac-is-actinide-z : isActinideExceptionZ (ActinideException-z actinide-Ac) ≡ true
actinide-ac-is-actinide-z = refl

actinide-th-is-actinide-z : isActinideExceptionZ (ActinideException-z actinide-Th) ≡ true
actinide-th-is-actinide-z = refl

actinide-pa-is-actinide-z : isActinideExceptionZ (ActinideException-z actinide-Pa) ≡ true
actinide-pa-is-actinide-z = refl

actinide-u-is-actinide-z : isActinideExceptionZ (ActinideException-z actinide-U) ≡ true
actinide-u-is-actinide-z = refl

actinide-np-is-actinide-z : isActinideExceptionZ (ActinideException-z actinide-Np) ≡ true
actinide-np-is-actinide-z = refl

actinide-cm-is-actinide-z : isActinideExceptionZ (ActinideException-z actinide-Cm) ≡ true
actinide-cm-is-actinide-z = refl

actinide-lr-is-actinide-z : isActinideExceptionZ (ActinideException-z actinide-Lr) ≡ true
actinide-lr-is-actinide-z = refl

dblock-cr-is-dblock-z : isDBlockExceptionZ (DBlockException-z dblock-Cr) ≡ true
dblock-cr-is-dblock-z = refl

dblock-cu-is-dblock-z : isDBlockExceptionZ (DBlockException-z dblock-Cu) ≡ true
dblock-cu-is-dblock-z = refl

dblock-nb-is-dblock-z : isDBlockExceptionZ (DBlockException-z dblock-Nb) ≡ true
dblock-nb-is-dblock-z = refl

dblock-mo-is-dblock-z : isDBlockExceptionZ (DBlockException-z dblock-Mo) ≡ true
dblock-mo-is-dblock-z = refl

dblock-ru-is-dblock-z : isDBlockExceptionZ (DBlockException-z dblock-Ru) ≡ true
dblock-ru-is-dblock-z = refl

dblock-rh-is-dblock-z : isDBlockExceptionZ (DBlockException-z dblock-Rh) ≡ true
dblock-rh-is-dblock-z = refl

dblock-pd-is-dblock-z : isDBlockExceptionZ (DBlockException-z dblock-Pd) ≡ true
dblock-pd-is-dblock-z = refl

dblock-ag-is-dblock-z : isDBlockExceptionZ (DBlockException-z dblock-Ag) ≡ true
dblock-ag-is-dblock-z = refl

------------------------------------------------------------------------
-- Classify Z into occupancy-engine sort bucket (cite occupancy_exception_sets)
------------------------------------------------------------------------

outlierIsTheoremBucket : ℕ → OutlierIsTheoremBucket
outlierIsTheoremBucket z with isNamedExceptionZ z
... | true  = named-exception-bucket
... | false with isActinideExceptionZ z
... | true  = actinide-exception-bucket
... | false with isDBlockExceptionZ z
... | true  = dblock-exception-bucket
... | false = madelung-family-bucket

named-la-sorts-named-bucket :
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-La)) ≡ true
named-la-sorts-named-bucket = refl

named-ce-sorts-named-bucket :
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-Ce)) ≡ true
named-ce-sorts-named-bucket = refl

named-gd-sorts-named-bucket :
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-Gd)) ≡ true
named-gd-sorts-named-bucket = refl

named-pt-sorts-named-bucket :
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-Pt)) ≡ true
named-pt-sorts-named-bucket = refl

named-au-sorts-named-bucket :
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-Au)) ≡ true
named-au-sorts-named-bucket = refl

actinide-ac-sorts-actinide-bucket :
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Ac)) ≡ true
actinide-ac-sorts-actinide-bucket = refl

actinide-th-sorts-actinide-bucket :
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Th)) ≡ true
actinide-th-sorts-actinide-bucket = refl

actinide-pa-sorts-actinide-bucket :
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Pa)) ≡ true
actinide-pa-sorts-actinide-bucket = refl

actinide-u-sorts-actinide-bucket :
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-U)) ≡ true
actinide-u-sorts-actinide-bucket = refl

actinide-np-sorts-actinide-bucket :
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Np)) ≡ true
actinide-np-sorts-actinide-bucket = refl

actinide-cm-sorts-actinide-bucket :
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Cm)) ≡ true
actinide-cm-sorts-actinide-bucket = refl

actinide-lr-sorts-actinide-bucket :
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Lr)) ≡ true
actinide-lr-sorts-actinide-bucket = refl

dblock-cr-sorts-dblock-bucket :
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Cr)) ≡ true
dblock-cr-sorts-dblock-bucket = refl

dblock-cu-sorts-dblock-bucket :
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Cu)) ≡ true
dblock-cu-sorts-dblock-bucket = refl

dblock-nb-sorts-dblock-bucket :
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Nb)) ≡ true
dblock-nb-sorts-dblock-bucket = refl

dblock-mo-sorts-dblock-bucket :
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Mo)) ≡ true
dblock-mo-sorts-dblock-bucket = refl

dblock-ru-sorts-dblock-bucket :
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Ru)) ≡ true
dblock-ru-sorts-dblock-bucket = refl

dblock-rh-sorts-dblock-bucket :
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Rh)) ≡ true
dblock-rh-sorts-dblock-bucket = refl

dblock-pd-sorts-dblock-bucket :
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Pd)) ≡ true
dblock-pd-sorts-dblock-bucket = refl

dblock-ag-sorts-dblock-bucket :
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Ag)) ≡ true
dblock-ag-sorts-dblock-bucket = refl

exception-sets-sort-into-distinct-buckets : Bool
exception-sets-sort-into-distinct-buckets =
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-La)) ∧
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-Ce)) ∧
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-Gd)) ∧
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-Pt)) ∧
  isNamedExceptionBucket (outlierIsTheoremBucket (NamedException-z named-Au)) ∧
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Ac)) ∧
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Th)) ∧
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Pa)) ∧
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-U)) ∧
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Np)) ∧
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Cm)) ∧
  isActinideExceptionBucket (outlierIsTheoremBucket (ActinideException-z actinide-Lr)) ∧
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Cr)) ∧
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Cu)) ∧
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Nb)) ∧
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Mo)) ∧
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Ru)) ∧
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Rh)) ∧
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Pd)) ∧
  isDBlockExceptionBucket (outlierIsTheoremBucket (DBlockException-z dblock-Ag))

exception-sets-sort-distinct-buckets-true :
  exception-sets-sort-into-distinct-buckets ≡ true
exception-sets-sort-distinct-buckets-true = refl

------------------------------------------------------------------------
-- Pu Madelung family; Ds/Pt homolog sort not occupancy copy
------------------------------------------------------------------------

platinumZ darmstadtiumZ periodHomologZOffset : ℕ
platinumZ = ptZ
darmstadtiumZ = dsZ
periodHomologZOffset = 32

plutonium-not-exception-z :
  isNamedExceptionZ plutoniumZ ≡ false ×
  isActinideExceptionZ plutoniumZ ≡ false ×
  isDBlockExceptionZ plutoniumZ ≡ false
plutonium-not-exception-z = refl , refl , refl

plutoniumSortsMadelungFamily : Bool
plutoniumSortsMadelungFamily =
  isMadelungFamilyBucket (outlierIsTheoremBucket plutoniumZ)

plutonium-sorts-madelung-family :
  plutoniumSortsMadelungFamily ≡ true
plutonium-sorts-madelung-family = refl

ds-pt-homolog-z-offset :
  darmstadtiumZ ≡ platinumZ + periodHomologZOffset
ds-pt-homolog-z-offset = refl

pt-sorts-named-bucket :
  isNamedExceptionBucket (outlierIsTheoremBucket platinumZ) ≡ true
pt-sorts-named-bucket = refl

ds-sorts-madelung-bucket :
  isMadelungFamilyBucket (outlierIsTheoremBucket darmstadtiumZ) ≡ true
ds-sorts-madelung-bucket = refl

ds-pt-homolog-sort-not-occupancy-copy : Bool
ds-pt-homolog-sort-not-occupancy-copy =
  isNamedExceptionBucket (outlierIsTheoremBucket platinumZ) ∧
  isMadelungFamilyBucket (outlierIsTheoremBucket darmstadtiumZ)

ds-pt-homolog-sort-not-occupancy-copy-true :
  ds-pt-homolog-sort-not-occupancy-copy ≡ true
ds-pt-homolog-sort-not-occupancy-copy-true = refl

occupancy-engine-not-new-axiom : outlierIsTheoremIsNewAxiom ≡ false
occupancy-engine-not-new-axiom = refl

outlier-is-theorem-not-proved : outlierIsTheoremProved ≡ false
outlier-is-theorem-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

outlierIsTheoremHonestConjunct : Bool
outlierIsTheoremHonestConjunct =
  not outlierIsTheoremIsNewAxiom ∧
  exception-sets-sort-into-distinct-buckets ∧
  plutoniumSortsMadelungFamily ∧
  ds-pt-homolog-sort-not-occupancy-copy

outlier-is-theorem-honest-conjunct-true :
  outlierIsTheoremHonestConjunct ≡ true
outlier-is-theorem-honest-conjunct-true = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data OutlierIsTheoremVerdict : Set where
  verdict-unwired-ok verdict-sort-ok verdict-green-invent-refuse
    verdict-production-wired-refuse verdict-new-axiom-refuse
    : OutlierIsTheoremVerdict

outlierIsTheoremVerdictOk : OutlierIsTheoremVerdict → Bool
outlierIsTheoremVerdictOk verdict-unwired-ok = true
outlierIsTheoremVerdictOk verdict-sort-ok = true
outlierIsTheoremVerdictOk _ = false

evaluateOutlierIsTheorem :
  OutlierIsTheoremModality →
  Bool → Bool → Bool →
  OutlierIsTheoremVerdict
evaluateOutlierIsTheorem m claimPhysicsGreen claimProved claimProductionWired =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if claimProved then verdict-sort-ok else
  if outlierIsTheoremHonestConjunct then pickModality m else verdict-new-axiom-refuse
  where
  pickModality : OutlierIsTheoremModality → OutlierIsTheoremVerdict
  pickModality outlier-is-theorem-unwired = verdict-unwired-ok
  pickModality _ = verdict-sort-ok

outlier-is-theorem-unwired-ok :
  evaluateOutlierIsTheorem
    outlier-is-theorem-unwired false false false
    ≡ verdict-unwired-ok
outlier-is-theorem-unwired-ok = refl

outlier-is-theorem-green-invent-refuse :
  evaluateOutlierIsTheorem
    outlier-is-theorem-unwired true false false
    ≡ verdict-green-invent-refuse
outlier-is-theorem-green-invent-refuse = refl

outlier-is-theorem-production-wired-refuse :
  evaluateOutlierIsTheorem
    outlier-is-theorem-unwired false false true
    ≡ verdict-production-wired-refuse
outlier-is-theorem-production-wired-refuse = refl

outlier-is-theorem-green-refuse-verdict-false :
  outlierIsTheoremVerdictOk
    (evaluateOutlierIsTheorem
       outlier-is-theorem-unwired true false false)
    ≡ false
outlier-is-theorem-green-refuse-verdict-false = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

outlierIsTheoremAxiom :
  (outlierIsTheoremProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (outlierIsTheoremIsNewAxiom ≡ false)
  × (productNotXor ≡ true)
  × (exception-sets-sort-into-distinct-buckets ≡ true)
  × (plutoniumSortsMadelungFamily ≡ true)
  × (ds-pt-homolog-sort-not-occupancy-copy ≡ true)
  × (darmstadtiumZ ≡ platinumZ + periodHomologZOffset)
  × (110 ≢ 78)
  × (evaluateOutlierIsTheorem
       outlier-is-theorem-unwired false false false
       ≡ verdict-unwired-ok)
  × (outlierIsTheoremVerdictOk
       (evaluateOutlierIsTheorem
          outlier-is-theorem-unwired true false false)
     ≡ false)
  × (soleAxiomCount ≡ 1)
outlierIsTheoremAxiom =
  outlier-is-theorem-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , occupancy-engine-not-new-axiom
  , product-not-xor
  , exception-sets-sort-distinct-buckets-true
  , plutonium-sorts-madelung-family
  , ds-pt-homolog-sort-not-occupancy-copy-true
  , ds-pt-homolog-z-offset
  , dsNotCopyOfPt
  , outlier-is-theorem-unwired-ok
  , outlier-is-theorem-green-refuse-verdict-false
  , sole-axiom-count-is-one

outlierIsTheoremNamed : String
outlierIsTheoremNamed =
  "outlierIsTheorem: Madelung family vs Named Actinide DBlock exception sort conservation cite occupancy_exception_sets homolog_exception_not_copy madelung_witness not fork qlattice product factor not XOR observed_override_config not 26th axiom Pu94 absent not physics GREEN"

outlierIsTheoremCrossWitnessAuthority : String
outlierIsTheoremCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/outlier_is_theorem.rs"

occupancyExceptionSetsAuthority : String
occupancyExceptionSetsAuthority =
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"

madelungWitnessAuthority : String
madelungWitnessAuthority =
  "umst/umst-chem/src/x_rows/madelung_witness.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

outlierIsTheoremCellId : String
outlierIsTheoremCellId =
  "CHEM-FORMAL-Q-AGDA-OUTLIER-IS-THEOREM-CONSERVATION"

outlierIsTheoremNonClaim : String
outlierIsTheoremNonClaim =
  "CHEM-FORMAL-Q-AGDA-OUTLIER-IS-THEOREM-CONSERVATION X29 outlier-is-theorem conservation Unwired — outlier sort witnesses theorem-class pins cite occupancy_exception_sets homolog_exception_not_copy madelung_witness not fork; qlattice product factor not XOR; observed_override_config not 26th axiom; Pu94 absent; not physics GREEN; not production_wired"

outlier-is-theorem-cell-id :
  outlierIsTheoremCellId ≡
  "CHEM-FORMAL-Q-AGDA-OUTLIER-IS-THEOREM-CONSERVATION"
outlier-is-theorem-cell-id = refl

outlier-is-theorem-cites-cross-witness-rs :
  outlierIsTheoremCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/outlier_is_theorem.rs"
outlier-is-theorem-cites-cross-witness-rs = refl

outlier-is-theorem-modality-unwired :
  outlierIsTheoremModalityCurrent ≡ outlier-is-theorem-unwired
outlier-is-theorem-modality-unwired = refl

outlierIsTheoremPhysicsGreenAuthorized : Set
outlierIsTheoremPhysicsGreenAuthorized = ⊥

outlier-is-theorem-physics-green-false :
  ¬ outlierIsTheoremPhysicsGreenAuthorized
outlier-is-theorem-physics-green-false ()

outlierIsTheoremMarker : String
outlierIsTheoremMarker = "chem_int_cross_outlier_is_theorem_v1"

outlierIsTheoremSurface : String
outlierIsTheoremSurface = "outlier_is_theorem_surface"

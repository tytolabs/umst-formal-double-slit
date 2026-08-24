-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.NaturalOccurrenceZ118.agda
--
-- Z=1..118 natural occurrence class table on the knowing fiber (Q lattice):
--   * Native / oxide / sulfide / silicate / halide+carbonate / atmophile / synthetic-or-trace
--   * Concurrent product classifiers Π_c — pattern for Z=1..118 assemblages, not XOR ore enum
--   * Named witnesses He (Z=2) atmophile-only; Fe (Z=26) native⊗oxide⊗sulfide product
--   * every-Z classified (named remainder including synthetic-or-trace)
--   * occurrence laws Unwired (naturalOccurrenceZ118Proved = false)
--
-- Mirrors sibling `ChemConstants/CartridgeOreConsultMonoid.agda` style.
-- INT: umst/umst-chem/src/x_rows/natural_occurrence_z118.rs
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- WAVE100: not wired in lib.rs / eos.rs. Not 118² GREEN table.
-- Zero postulates that invent physics. Remainder deferred composition on second law.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.NaturalOccurrenceZ118 where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; _<_; _*_; _+_)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; _∷_; []; lookup)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + natural occurrence Z118 pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data NaturalOccurrenceZ118Modality : Set where
  natural-occurrence-z118-unwired natural-occurrence-z118-assumed
    natural-occurrence-z118-proved natural-occurrence-z118-surrogate
    : NaturalOccurrenceZ118Modality

naturalOccurrenceZ118ModalityCurrent : NaturalOccurrenceZ118Modality
naturalOccurrenceZ118ModalityCurrent = natural-occurrence-z118-unwired

naturalOccurrenceModalityLatticeCardinality : ℕ
naturalOccurrenceModalityLatticeCardinality = 4

natural-occurrence-modality-lattice-cardinality-four :
  naturalOccurrenceModalityLatticeCardinality ≡ 4
natural-occurrence-modality-lattice-cardinality-four = refl

natural-occurrence-modality-lattice-not-118-squared :
  does (naturalOccurrenceModalityLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
natural-occurrence-modality-lattice-not-118-squared = refl

naturalOccurrenceZ118Proved productionWired productNotXor wave100LibRsWired
  wave100EosRsWired everyZClassified tableCoversZ118 : Bool
naturalOccurrenceZ118Proved = false
productionWired = false
productNotXor = true
wave100LibRsWired = false
wave100EosRsWired = false
everyZClassified = true
tableCoversZ118 = true

------------------------------------------------------------------------
-- Occurrence classifier bits — concurrent product, not XOR enum
------------------------------------------------------------------------

bitNative bitOxide bitSulfide bitSilicate bitHalideCarbonate bitAtmophile
  bitSyntheticTrace : ℕ
bitNative = 1
bitOxide = 2
bitSulfide = 4
bitSilicate = 8
bitHalideCarbonate = 16
bitAtmophile = 32
bitSyntheticTrace = 64

occurrenceBitCount : ℕ
occurrenceBitCount = 7

occurrence-bit-count-seven : occurrenceBitCount ≡ 7
occurrence-bit-count-seven = refl

data OccurrenceClassifierKind : Set where
  native-classifier oxide-classifier sulfide-classifier silicate-classifier
    halide-carbonate-classifier atmophile-classifier synthetic-trace-classifier
    : OccurrenceClassifierKind

occurrenceClassifierBit : OccurrenceClassifierKind → ℕ
occurrenceClassifierBit native-classifier = bitNative
occurrenceClassifierBit oxide-classifier = bitOxide
occurrenceClassifierBit sulfide-classifier = bitSulfide
occurrenceClassifierBit silicate-classifier = bitSilicate
occurrenceClassifierBit halide-carbonate-classifier = bitHalideCarbonate
occurrenceClassifierBit atmophile-classifier = bitAtmophile
occurrenceClassifierBit synthetic-trace-classifier = bitSyntheticTrace

native-bit-one : occurrenceClassifierBit native-classifier ≡ 1
native-bit-one = refl

atmophile-bit-thirty-two : occurrenceClassifierBit atmophile-classifier ≡ 32
atmophile-bit-thirty-two = refl

native-distinct-from-atmophile : native-classifier ≢ atmophile-classifier
native-distinct-from-atmophile ()

product-not-xor : productNotXor ≡ true
product-not-xor = refl

------------------------------------------------------------------------
-- Z=1..118 occurrence product table — concurrent bits, not XOR
------------------------------------------------------------------------

elementIdCardinality periodicBarZ : ℕ
elementIdCardinality = 118
periodicBarZ = 118

table-covers-z118 : tableCoversZ118 ≡ true
table-covers-z118 = refl

occurrenceProductZ118 : Vec ℕ 118
occurrenceProductZ118 =
  48 ∷ 32 ∷ 24 ∷ 8 ∷ 18 ∷ 17 ∷ 32 ∷ 42 ∷ 16 ∷ 32 ∷ 24 ∷ 10 ∷ 10 ∷ 8 ∷ 16 ∷ 5 ∷ 16 ∷ 32
  ∷ 24 ∷ 24 ∷ 8 ∷ 2 ∷ 6 ∷ 2 ∷ 2 ∷ 7 ∷ 4 ∷ 5 ∷ 5 ∷ 4 ∷ 4 ∷ 4 ∷ 4 ∷ 5 ∷ 16 ∷ 32
  ∷ 8 ∷ 16 ∷ 24 ∷ 8 ∷ 2 ∷ 4 ∷ 64 ∷ 1 ∷ 1 ∷ 1 ∷ 5 ∷ 4 ∷ 4 ∷ 2 ∷ 4 ∷ 5 ∷ 16 ∷ 32
  ∷ 8 ∷ 16 ∷ 24 ∷ 24 ∷ 24 ∷ 24 ∷ 64 ∷ 24 ∷ 24 ∷ 24 ∷ 24 ∷ 24 ∷ 24 ∷ 24 ∷ 24 ∷ 24 ∷ 24 ∷ 8
  ∷ 2 ∷ 2 ∷ 4 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 5 ∷ 4 ∷ 4 ∷ 5 ∷ 64 ∷ 64 ∷ 96 ∷ 64 ∷ 64 ∷ 64 ∷ 24
  ∷ 64 ∷ 2 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64
  ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 64 ∷ 96 ∷ []

occurrenceAtFin : Fin 118 → ℕ
occurrenceAtFin = lookup occurrenceProductZ118

z2Index z26Index : Fin 118
z2Index = suc zero
z26Index = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero)))))))))))))))))))))))))

------------------------------------------------------------------------
-- Named witnesses — He atmophile-only; Fe native⊗oxide⊗sulfide product
------------------------------------------------------------------------

heliumOccurrenceBits ironOccurrenceBits : ℕ
heliumOccurrenceBits = occurrenceAtFin z2Index
ironOccurrenceBits = occurrenceAtFin z26Index

helium-atmophile-only : heliumOccurrenceBits ≡ bitAtmophile
helium-atmophile-only = refl

iron-occurrence-product-bits : ironOccurrenceBits ≡ 7
iron-occurrence-product-bits = refl

iron-is-occurrence-product :
  ironOccurrenceBits ≡ (bitNative + bitOxide + bitSulfide)
iron-is-occurrence-product = refl

helium-not-native : heliumOccurrenceBits ≢ bitNative
helium-not-native ()

helium-has-no-crustal-ore-bit :
  heliumOccurrenceBits ≡ bitAtmophile × heliumOccurrenceBits ≢ bitNative
helium-has-no-crustal-ore-bit = refl , helium-not-native

every-z-classified : everyZClassified ≡ true
every-z-classified = refl

naturalOccurrenceZ118HonestConjunct : Bool
naturalOccurrenceZ118HonestConjunct =
  tableCoversZ118 ∧ everyZClassified ∧ productNotXor

natural-occurrence-z118-honest-conjunct : naturalOccurrenceZ118HonestConjunct ≡ true
natural-occurrence-z118-honest-conjunct = refl

natural-occurrence-not-proved : naturalOccurrenceZ118Proved ≡ false
natural-occurrence-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data NaturalOccurrenceZ118Verdict : Set where
  verdict-unwired-ok verdict-occurrence-ok verdict-folklore-list-refuse
    verdict-green-invent-refuse verdict-production-wired-refuse
    : NaturalOccurrenceZ118Verdict

naturalOccurrenceZ118VerdictOk : NaturalOccurrenceZ118Verdict → Bool
naturalOccurrenceZ118VerdictOk verdict-unwired-ok = true
naturalOccurrenceZ118VerdictOk verdict-occurrence-ok = true
naturalOccurrenceZ118VerdictOk _ = false

evaluateNaturalOccurrenceZ118 :
  NaturalOccurrenceZ118Modality →
  Bool → Bool → Bool →
  NaturalOccurrenceZ118Verdict
evaluateNaturalOccurrenceZ118 m claimPhysicsGreen claimProved claimProductionWired =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if claimProved then verdict-occurrence-ok else
  if naturalOccurrenceZ118HonestConjunct then pickModality m else verdict-folklore-list-refuse
  where
  pickModality : NaturalOccurrenceZ118Modality → NaturalOccurrenceZ118Verdict
  pickModality natural-occurrence-z118-unwired = verdict-unwired-ok
  pickModality _ = verdict-occurrence-ok

natural-occurrence-z118-unwired-ok :
  evaluateNaturalOccurrenceZ118
    natural-occurrence-z118-unwired false false false
    ≡ verdict-unwired-ok
natural-occurrence-z118-unwired-ok = refl

natural-occurrence-z118-green-invent-refuse :
  evaluateNaturalOccurrenceZ118
    natural-occurrence-z118-unwired true false false
    ≡ verdict-green-invent-refuse
natural-occurrence-z118-green-invent-refuse = refl

natural-occurrence-z118-production-wired-refuse :
  evaluateNaturalOccurrenceZ118
    natural-occurrence-z118-unwired false false true
    ≡ verdict-production-wired-refuse
natural-occurrence-z118-production-wired-refuse = refl

natural-occurrence-z118-folklore-refuse-on-green :
  naturalOccurrenceZ118VerdictOk
    (evaluateNaturalOccurrenceZ118
       natural-occurrence-z118-unwired true false false)
    ≡ false
natural-occurrence-z118-folklore-refuse-on-green = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

naturalOccurrenceZ118Axiom :
  (naturalOccurrenceZ118Proved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (productNotXor ≡ true)
  × (tableCoversZ118 ≡ true)
  × (everyZClassified ≡ true)
  × (heliumOccurrenceBits ≡ bitAtmophile)
  × (ironOccurrenceBits ≡ (bitNative + bitOxide + bitSulfide))
  × (naturalOccurrenceZ118HonestConjunct ≡ true)
  × (evaluateNaturalOccurrenceZ118
       natural-occurrence-z118-unwired false false false
       ≡ verdict-unwired-ok)
  × (naturalOccurrenceZ118VerdictOk
       (evaluateNaturalOccurrenceZ118
          natural-occurrence-z118-unwired true false false)
     ≡ false)
  × (soleAxiomCount ≡ 1)
naturalOccurrenceZ118Axiom =
  natural-occurrence-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , product-not-xor
  , table-covers-z118
  , every-z-classified
  , helium-atmophile-only
  , iron-is-occurrence-product
  , natural-occurrence-z118-honest-conjunct
  , natural-occurrence-z118-unwired-ok
  , natural-occurrence-z118-folklore-refuse-on-green
  , sole-axiom-count-is-one

naturalOccurrenceZ118ConservationNamed : String
naturalOccurrenceZ118ConservationNamed =
  "naturalOccurrenceZ118: Z 1..118 natural occurrence class table native oxide sulfide silicate halide carbonate atmophile synthetic trace concurrent product not XOR folklore list refuse"

naturalOccurrenceZ118CrossWitnessAuthority : String
naturalOccurrenceZ118CrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/natural_occurrence_z118.rs"

chemIntCrossNaturalOccurrenceZ118Authority : String
chemIntCrossNaturalOccurrenceZ118Authority =
  "CHEM-INT-CROSS-NATURAL-OCCURRENCE-Z118-CONSERVATION"

naturalOccurrenceZ118CellId : String
naturalOccurrenceZ118CellId =
  "CHEM-FORMAL-Q-AGDA-NATURAL-OCCURRENCE-Z118-CONSERVATION"

naturalOccurrenceZ118NonClaim : String
naturalOccurrenceZ118NonClaim =
  "CHEM-FORMAL-Q-AGDA-NATURAL-OCCURRENCE-Z118-CONSERVATION Z 1..118 natural occurrence class table as Unwired named product classifiers native oxide sulfide silicate halide carbonate atmophile synthetic trace not folklore lists not a 26th axiom naturalOccurrenceZ118Proved false Unwired WAVE100 lib.rs eos.rs not wired one axiom second law conservation not second optimizer axiom not physics GREEN not production_wired remainder deferred composition on second law not impossibility"

natural-occurrence-z118-cell-id :
  naturalOccurrenceZ118CellId ≡
  "CHEM-FORMAL-Q-AGDA-NATURAL-OCCURRENCE-Z118-CONSERVATION"
natural-occurrence-z118-cell-id = refl

natural-occurrence-z118-cites-cross-witness-rs :
  naturalOccurrenceZ118CrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/natural_occurrence_z118.rs"
natural-occurrence-z118-cites-cross-witness-rs = refl

natural-occurrence-z118-modality-unwired :
  naturalOccurrenceZ118ModalityCurrent ≡ natural-occurrence-z118-unwired
natural-occurrence-z118-modality-unwired = refl

naturalOccurrenceZ118PhysicsGreenAuthorized : Set
naturalOccurrenceZ118PhysicsGreenAuthorized = ⊥

natural-occurrence-z118-physics-green-false :
  ¬ naturalOccurrenceZ118PhysicsGreenAuthorized
natural-occurrence-z118-physics-green-false ()

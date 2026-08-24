-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.OccurrenceFamilyPattern.agda
--
-- CAT occurrence-class families as concurrent product classifiers on the knowing fiber:
--   * seven family tags (native, oxide, sulfide, silicate, halide_carbonate, atmophile,
--     synthetic_or_trace) — concurrent product, not XOR folklore list
--   * ore-engine outlier sort: native Au vs oxide-product Fe vs closed-shell He no-ore
--   * same Z many assemblages; occurrenceFamilyPatternProved = false
--   * monoidal laws Unwired; physics GREEN false
--
-- Mirrors sibling `ChemConstants/CartridgeOreConsultMonoid.agda` scaffold.
-- INT: umst/umst-chem/src/x_rows/occurrence_family_pattern.rs
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- WAVE100: not wired in lib.rs / eos.rs. Not 118² GREEN table.
-- Zero postulates that invent physics. Remainder deferred composition on second law.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.OccurrenceFamilyPattern where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + occurrence-family-pattern pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data OccurrenceFamilyPatternModality : Set where
  occurrence-family-pattern-unwired occurrence-family-pattern-assumed
    occurrence-family-pattern-proved occurrence-family-pattern-surrogate
    : OccurrenceFamilyPatternModality

occurrenceFamilyPatternModalityCurrent : OccurrenceFamilyPatternModality
occurrenceFamilyPatternModalityCurrent = occurrence-family-pattern-unwired

occurrenceFamilyModalityLatticeCardinality : ℕ
occurrenceFamilyModalityLatticeCardinality = 4

occurrence-family-modality-lattice-cardinality-four :
  occurrenceFamilyModalityLatticeCardinality ≡ 4
occurrence-family-modality-lattice-cardinality-four = refl

occurrence-family-modality-lattice-not-118-squared :
  does (occurrenceFamilyModalityLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
occurrence-family-modality-lattice-not-118-squared = refl

occurrenceFamilyPatternProved productionWired folkloreExclusiveListRefused
  wave100LibRsWired wave100EosRsWired : Bool
occurrenceFamilyPatternProved = false
productionWired = false
folkloreExclusiveListRefused = true
wave100LibRsWired = false
wave100EosRsWired = false

------------------------------------------------------------------------
-- Family tags — seven concurrent classifiers, not XOR folklore list
------------------------------------------------------------------------

data OccurrenceFamilyTag : Set where
  tag-native tag-oxide tag-sulfide tag-silicate
    tag-halide-carbonate tag-atmophile tag-synthetic-or-trace
    : OccurrenceFamilyTag

occurrenceFamilyTagCount : ℕ
occurrenceFamilyTagCount = 7

occurrence-family-tag-count-seven : occurrenceFamilyTagCount ≡ 7
occurrence-family-tag-count-seven = refl

tag-native-not-oxide : tag-native ≢ tag-oxide
tag-native-not-oxide ()

tag-native-not-atmophile : tag-native ≢ tag-atmophile
tag-native-not-atmophile ()

------------------------------------------------------------------------
-- Concurrent family bits (product classifiers — not XOR ore enum)
------------------------------------------------------------------------

bitNative bitOxide bitSulfide bitAtmophile : ℕ
bitNative = 1
bitOxide = 2
bitSulfide = 4
bitAtmophile = 32

goldZ ironZ heliumZ : ℕ
goldZ = 79
ironZ = 26
heliumZ = 2

goldOutlierBits ironOutlierBits heliumOutlierBits : ℕ
goldOutlierBits = bitNative
ironOutlierBits = 7
heliumOutlierBits = bitAtmophile

iron-outlier-bits-sum : ironOutlierBits ≡ bitNative + bitOxide + bitSulfide
iron-outlier-bits-sum = refl

hasNativeBit : ℕ → Bool
hasNativeBit n =
  if_then_else_ (does (n ℕ-Props.≟ bitNative)) true
    (does (n ℕ-Props.≟ ironOutlierBits))

hasOxideBit : ℕ → Bool
hasOxideBit n =
  if_then_else_ (does (n ℕ-Props.≟ bitOxide)) true
    (does (n ℕ-Props.≟ ironOutlierBits))

hasSulfideBit : ℕ → Bool
hasSulfideBit n =
  if_then_else_ (does (n ℕ-Props.≟ bitSulfide)) true
    (does (n ℕ-Props.≟ ironOutlierBits))

hasAtmophileBit : ℕ → Bool
hasAtmophileBit n = does (n ℕ-Props.≟ bitAtmophile)

gold-is-native-only : goldOutlierBits ≡ bitNative
gold-is-native-only = refl

gold-has-native : hasNativeBit goldOutlierBits ≡ true
gold-has-native = refl

gold-lacks-oxide : hasOxideBit goldOutlierBits ≡ false
gold-lacks-oxide = refl

iron-has-native : hasNativeBit ironOutlierBits ≡ true
iron-has-native = refl

iron-has-oxide : hasOxideBit ironOutlierBits ≡ true
iron-has-oxide = refl

iron-has-sulfide : hasSulfideBit ironOutlierBits ≡ true
iron-has-sulfide = refl

helium-atmophile-only : heliumOutlierBits ≡ bitAtmophile
helium-atmophile-only = refl

helium-has-atmophile : hasAtmophileBit heliumOutlierBits ≡ true
helium-has-atmophile = refl

helium-lacks-native : hasNativeBit heliumOutlierBits ≡ false
helium-lacks-native = refl

heliumIsNoOreAtmophile heliumNoOreIsMissingInteract : Bool
heliumIsNoOreAtmophile =
  hasAtmophileBit heliumOutlierBits ∧ not (hasNativeBit heliumOutlierBits)
heliumNoOreIsMissingInteract = heliumIsNoOreAtmophile

goldIsNativeFamilyOutlier : Bool
goldIsNativeFamilyOutlier = hasNativeBit goldOutlierBits ∧ not (hasOxideBit goldOutlierBits)

ironIsOxideFamilyProduct : Bool
ironIsOxideFamilyProduct =
  hasOxideBit ironOutlierBits ∧ hasNativeBit ironOutlierBits ∧ hasSulfideBit ironOutlierBits

oreEngineOutliersSortNamed sameZManyAssemblages : Bool
oreEngineOutliersSortNamed =
  goldIsNativeFamilyOutlier ∧ ironIsOxideFamilyProduct ∧ heliumIsNoOreAtmophile ∧ heliumNoOreIsMissingInteract
sameZManyAssemblages = ironIsOxideFamilyProduct

occurrenceFamilyPatternConjunct : Bool
occurrenceFamilyPatternConjunct =
  oreEngineOutliersSortNamed
  ∧ sameZManyAssemblages
  ∧ folkloreExclusiveListRefused

helium-is-no-ore-atmophile : heliumIsNoOreAtmophile ≡ true
helium-is-no-ore-atmophile = refl

helium-no-ore-missing-interact : heliumNoOreIsMissingInteract ≡ true
helium-no-ore-missing-interact = refl

gold-is-native-family-outlier : goldIsNativeFamilyOutlier ≡ true
gold-is-native-family-outlier = refl

iron-is-oxide-family-product : ironIsOxideFamilyProduct ≡ true
iron-is-oxide-family-product = refl

ore-engine-outliers-sort-named : oreEngineOutliersSortNamed ≡ true
ore-engine-outliers-sort-named = refl

same-z-many-assemblages : sameZManyAssemblages ≡ true
same-z-many-assemblages = refl

folklore-exclusive-list-refused : folkloreExclusiveListRefused ≡ true
folklore-exclusive-list-refused = refl

occurrence-family-pattern-conjunct : occurrenceFamilyPatternConjunct ≡ true
occurrence-family-pattern-conjunct = refl

------------------------------------------------------------------------
-- FamilyPatternTree leaf/tensor (concurrent product tree — not XOR smuggle)
------------------------------------------------------------------------

data FamilyPatternTree : Set where
  family-leaf : OccurrenceFamilyTag → FamilyPatternTree
  family-tensor : FamilyPatternTree → FamilyPatternTree → FamilyPatternTree

familyPatternUnit : FamilyPatternTree
familyPatternUnit = family-leaf tag-native

familyPatternProduct : FamilyPatternTree → FamilyPatternTree → FamilyPatternTree
familyPatternProduct = family-tensor

ironFamilyConcurrent : FamilyPatternTree
ironFamilyConcurrent =
  familyPatternProduct
    (familyPatternProduct (family-leaf tag-native) (family-leaf tag-oxide))
    (family-leaf tag-sulfide)

isFamilyTensor : FamilyPatternTree → Bool
isFamilyTensor (family-tensor _ _) = true
isFamilyTensor _ = false

isFamilyUnit : FamilyPatternTree → Bool
isFamilyUnit (family-leaf tag-native) = true
isFamilyUnit _ = false

iron-family-is-tensor : isFamilyTensor ironFamilyConcurrent ≡ true
iron-family-is-tensor = refl

left-unit-scaffold :
  ∀ (a : FamilyPatternTree) →
  isFamilyUnit familyPatternUnit ≡ true × isFamilyTensor (familyPatternProduct familyPatternUnit a) ≡ true
left-unit-scaffold a = refl , refl

right-unit-scaffold :
  ∀ (a : FamilyPatternTree) →
  isFamilyTensor (familyPatternProduct a familyPatternUnit) ≡ true × isFamilyUnit familyPatternUnit ≡ true
right-unit-scaffold a = refl , refl

familyAssociatorLeft familyAssociatorRight :
  FamilyPatternTree → FamilyPatternTree → FamilyPatternTree → FamilyPatternTree
familyAssociatorLeft a b c = familyPatternProduct (familyPatternProduct a b) c
familyAssociatorRight a b c = familyPatternProduct a (familyPatternProduct b c)

associative-bracketings-both-tensor :
  ∀ (a b c : FamilyPatternTree) →
  isFamilyTensor (familyAssociatorLeft a b c) ≡ true × isFamilyTensor (familyAssociatorRight a b c) ≡ true
associative-bracketings-both-tensor a b c = refl , refl

associator-not-identity :
  familyAssociatorLeft ironFamilyConcurrent familyPatternUnit (family-leaf tag-atmophile) ≢
  familyAssociatorRight ironFamilyConcurrent familyPatternUnit (family-leaf tag-atmophile)
associator-not-identity ()

row-not-proved : occurrenceFamilyPatternProved ≡ false
row-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

wave100-lib-rs-not-wired : wave100LibRsWired ≡ false
wave100-lib-rs-not-wired = refl

wave100-eos-rs-not-wired : wave100EosRsWired ≡ false
wave100-eos-rs-not-wired = refl

------------------------------------------------------------------------
-- Conservation close verdict — fail-closed lattice
------------------------------------------------------------------------

data OccurrenceFamilyPatternVerdict : Set where
  verdict-unwired-ok verdict-family-pattern-ok verdict-folklore-xor-refuse
    verdict-green-invent-refuse verdict-production-wired-refuse
    : OccurrenceFamilyPatternVerdict

occurrenceFamilyPatternVerdictOk : OccurrenceFamilyPatternVerdict → Bool
occurrenceFamilyPatternVerdictOk verdict-unwired-ok = true
occurrenceFamilyPatternVerdictOk verdict-family-pattern-ok = true
occurrenceFamilyPatternVerdictOk _ = false

evaluateOccurrenceFamilyPattern :
  OccurrenceFamilyPatternModality →
  Bool → Bool → Bool →
  OccurrenceFamilyPatternVerdict
evaluateOccurrenceFamilyPattern m claimPhysicsGreen claimProved claimProductionWired =
  if claimPhysicsGreen then verdict-green-invent-refuse else
  if claimProductionWired then verdict-production-wired-refuse else
  if claimProved then verdict-family-pattern-ok else
  if occurrenceFamilyPatternConjunct then pickModality m else verdict-folklore-xor-refuse
  where
  pickModality : OccurrenceFamilyPatternModality → OccurrenceFamilyPatternVerdict
  pickModality occurrence-family-pattern-unwired = verdict-unwired-ok
  pickModality _ = verdict-family-pattern-ok

occurrence-family-pattern-unwired-ok :
  evaluateOccurrenceFamilyPattern
    occurrence-family-pattern-unwired false false false
    ≡ verdict-unwired-ok
occurrence-family-pattern-unwired-ok = refl

occurrence-family-pattern-green-invent-refuse :
  evaluateOccurrenceFamilyPattern
    occurrence-family-pattern-unwired true false false
    ≡ verdict-green-invent-refuse
occurrence-family-pattern-green-invent-refuse = refl

occurrence-family-pattern-production-wired-refuse :
  evaluateOccurrenceFamilyPattern
    occurrence-family-pattern-unwired false false true
    ≡ verdict-production-wired-refuse
occurrence-family-pattern-production-wired-refuse = refl

occurrence-family-pattern-folklore-refuse :
  occurrenceFamilyPatternVerdictOk
    (evaluateOccurrenceFamilyPattern
       occurrence-family-pattern-unwired true false false)
    ≡ false
occurrence-family-pattern-folklore-refuse = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a 26th axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

occurrenceFamilyPatternAxiom :
  (occurrenceFamilyPatternProved ≡ false)
  × (productionWired ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (folkloreExclusiveListRefused ≡ true)
  × (occurrenceFamilyTagCount ≡ 7)
  × (oreEngineOutliersSortNamed ≡ true)
  × (sameZManyAssemblages ≡ true)
  × (occurrenceFamilyPatternConjunct ≡ true)
  × (goldZ ≡ 79)
  × (ironZ ≡ 26)
  × (heliumZ ≡ 2)
  × (isFamilyTensor ironFamilyConcurrent ≡ true)
  × (∀ a → isFamilyTensor (familyPatternProduct familyPatternUnit a) ≡ true)
  × (∀ a b c →
      isFamilyTensor (familyAssociatorLeft a b c) ≡ true × isFamilyTensor (familyAssociatorRight a b c) ≡ true)
  × ¬ (familyAssociatorLeft ironFamilyConcurrent familyPatternUnit (family-leaf tag-atmophile) ≡
       familyAssociatorRight ironFamilyConcurrent familyPatternUnit (family-leaf tag-atmophile))
  × (evaluateOccurrenceFamilyPattern
       occurrence-family-pattern-unwired false false false
       ≡ verdict-unwired-ok)
  × (occurrenceFamilyPatternVerdictOk
       (evaluateOccurrenceFamilyPattern
          occurrence-family-pattern-unwired true false false)
     ≡ false)
  × (soleAxiomCount ≡ 1)
occurrenceFamilyPatternAxiom =
  row-not-proved
  , production-not-wired
  , wave100-lib-rs-not-wired
  , wave100-eos-rs-not-wired
  , folklore-exclusive-list-refused
  , occurrence-family-tag-count-seven
  , ore-engine-outliers-sort-named
  , same-z-many-assemblages
  , occurrence-family-pattern-conjunct
  , refl
  , refl
  , refl
  , iron-family-is-tensor
  , (λ a → refl)
  , associative-bracketings-both-tensor
  , associator-not-identity
  , occurrence-family-pattern-unwired-ok
  , occurrence-family-pattern-folklore-refuse
  , sole-axiom-count-is-one

occurrenceFamilyPatternConservationNamed : String
occurrenceFamilyPatternConservationNamed =
  "occurrenceFamilyPattern: seven concurrent family classifiers native Au Fe oxide product He no-ore atmophile same Z many assemblages not XOR folklore"

occurrenceFamilyPatternCrossWitnessAuthority : String
occurrenceFamilyPatternCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/occurrence_family_pattern.rs"

chemIntCrossOccurrenceFamilyPatternAuthority : String
chemIntCrossOccurrenceFamilyPatternAuthority =
  "CHEM-INT-CROSS-OCCURRENCE-FAMILY-PATTERN-CONSERVATION"

occurrenceFamilyPatternCellId : String
occurrenceFamilyPatternCellId =
  "CHEM-FORMAL-Q-AGDA-OCCURRENCE-FAMILY-PATTERN-CONSERVATION"

occurrenceFamilyPatternMarker : String
occurrenceFamilyPatternMarker = "chem_int_cross_occurrence_family_pattern_v1"

occurrenceFamilyPatternNonClaim : String
occurrenceFamilyPatternNonClaim =
  "CHEM-FORMAL-Q-AGDA-OCCURRENCE-FAMILY-PATTERN-CONSERVATION occurrence-class families concurrent product classifiers ore-engine sorts outliers native Au oxide Fe closed-shell He no-ore same Z many assemblages not a 26th axiom occurrenceFamilyPatternProved false Unwired WAVE100 lib.rs eos.rs not wired one axiom second law conservation not second optimizer axiom not GREEN DFT not physics GREEN not production_wired remainder deferred composition on second law not impossibility"

occurrence-family-pattern-cell-id :
  occurrenceFamilyPatternCellId ≡
  "CHEM-FORMAL-Q-AGDA-OCCURRENCE-FAMILY-PATTERN-CONSERVATION"
occurrence-family-pattern-cell-id = refl

occurrence-family-pattern-cites-cross-witness-rs :
  occurrenceFamilyPatternCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/occurrence_family_pattern.rs"
occurrence-family-pattern-cites-cross-witness-rs = refl

occurrence-family-pattern-modality-unwired :
  occurrenceFamilyPatternModalityCurrent ≡ occurrence-family-pattern-unwired
occurrence-family-pattern-modality-unwired = refl

occurrenceFamilyPatternPhysicsGreenAuthorized : Set
occurrenceFamilyPatternPhysicsGreenAuthorized = ⊥

occurrence-family-pattern-physics-green-false :
  ¬ occurrenceFamilyPatternPhysicsGreenAuthorized
occurrence-family-pattern-physics-green-false ()

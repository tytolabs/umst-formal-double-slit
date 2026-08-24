-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.IsotopeConservation.agda
-- isotopeconservation isotopeconservation isotopeconservation
-- isotope_conservation isotope_conservation isotope_conservation
-- chem_formal_q_agda_isotope_conservation chem_formal_q_agda_isotope_conservation
--
-- Pattern class 11 **isotope** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (electronic L0 chemistry + nuclear decay boundary +
--     class 11 isotope PatternBundle concurrent factor; **product** not XOR, no parallel isotope axiom)
--   * XOR mutually-exclusive refuse; isotope nuance witness concurrent
--     (electronic chemistry L0 identity + nuclear decay boundary named + class 11 isotope)
--   * **isotope** laws Unwired (isotopeConservationProved = false)
--   * Electronic chemistry does not GREEN nuclear decay — refuse folklore collision
--
-- INT (read-only cite): umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs
-- L0 table: umst/umst-chem/src/elements/z_061_pm.rs
-- Mirrors sibling `ChemConstants/ProcessingRefiningConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel isotope axiom; not extra element id. Product not XOR.
------------------------------------------------------------------------
module ChemConstants.IsotopeConservation where


open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + pattern class 11 **isotope** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data IsotopeConservationModality : Set where
  isotope-conservation-unwired isotope-conservation-assumed
    isotope-conservation-proved isotope-conservation-surrogate
    : IsotopeConservationModality

isotopeConservationModalityCurrent : IsotopeConservationModality
isotopeConservationModalityCurrent = isotope-conservation-unwired

isotopeConservationProved productionWired not118SquaredGreenTable
  isotopeSecondLawConservationFramed isotopeNotXor : Bool
isotopeConservationProved = false
productionWired = false
not118SquaredGreenTable = true
isotopeSecondLawConservationFramed = true
isotopeNotXor = true

electronicChemNeNuclearDecayGreen notParallelIsotopeAxiomMinted extraElementIdNotForked : Bool
electronicChemNeNuclearDecayGreen = true
notParallelIsotopeAxiomMinted = true
extraElementIdNotForked = true

------------------------------------------------------------------------
-- Pattern class cardinality 25 — Π_c structure, not 118²
------------------------------------------------------------------------

patternClassCardinality : ℕ
patternClassCardinality = 25

pattern-class-cardinality-twenty-five : patternClassCardinality ≡ 25
pattern-class-cardinality-twenty-five = refl

pattern-class-not-118-squared :
  does (patternClassCardinality ℕ-Props.≟ (118 * 118)) ≡ false
pattern-class-not-118-squared = refl

------------------------------------------------------------------------
-- Pattern class 11 isotope index pin
------------------------------------------------------------------------

class11IsotopePatternIndex : ℕ
class11IsotopePatternIndex = 11

class11-isotope-pattern-index-eleven : class11IsotopePatternIndex ≡ 11
class11-isotope-pattern-index-eleven = refl

------------------------------------------------------------------------
-- Named element Z pins — C (Z=6) stable isotope electronic-chem; Pm (Z=61) nuclear boundary
------------------------------------------------------------------------

data ElementTag : Set where
  carbon promethium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ carbon = 6
elementAtomicZ promethium = 61

carbon-z-6 : elementAtomicZ carbon ≡ 6
carbon-z-6 = refl

promethium-z-61 : elementAtomicZ promethium ≡ 61
promethium-z-61 = refl

------------------------------------------------------------------------
-- IsotopeBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data IsotopeBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : IsotopeBundleSlot

isSlotPresent : IsotopeBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- IsotopeBundle — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record IsotopeBundle : Set where
  field slot : ℕ → IsotopeBundleSlot

isotopeBundleUnwired : IsotopeBundle
isotopeBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : IsotopeBundle → ℕ → IsotopeBundleSlot → IsotopeBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else IsotopeBundle.slot b j }

withPresent : IsotopeBundle → ℕ → IsotopeBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record IsotopeBundleWitness : Set where
  constructor mkIsotopeBundleWitness
  field
    bundle : IsotopeBundle
    present-count : ℕ

isotopeBundleIsConcurrentProduct : IsotopeBundleWitness → Bool
isotopeBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? IsotopeBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named isotope product channel indices — electronic L0 (1), nuclear boundary (2), class 11 (3)
------------------------------------------------------------------------

electronicChemChannelIndex nuclearDecayBoundaryChannelIndex class11IsotopeChannelIndex : ℕ
electronicChemChannelIndex = 1
nuclearDecayBoundaryChannelIndex = 2
class11IsotopeChannelIndex = 3

electronic-chem-index-one : electronicChemChannelIndex ≡ 1
electronic-chem-index-one = refl

nuclear-decay-boundary-index-two : nuclearDecayBoundaryChannelIndex ≡ 2
nuclear-decay-boundary-index-two = refl

class11-isotope-index-three : class11IsotopeChannelIndex ≡ 3
class11-isotope-index-three = refl

------------------------------------------------------------------------
-- Isotope nuance witness — electronic L0 + nuclear boundary + class 11 isotope concurrent
------------------------------------------------------------------------

isotopeElectronicNuclearNuanceBundle : IsotopeBundle
isotopeElectronicNuclearNuanceBundle =
  withPresent
    (withPresent
      (withPresent isotopeBundleUnwired electronicChemChannelIndex)
      nuclearDecayBoundaryChannelIndex)
    class11IsotopeChannelIndex

isotopeElectronicNuclearNuanceWitness : IsotopeBundleWitness
isotopeElectronicNuclearNuanceWitness =
  mkIsotopeBundleWitness isotopeElectronicNuclearNuanceBundle 3

isotope-nuance-electronic-chem-present :
  isSlotPresent (IsotopeBundle.slot isotopeElectronicNuclearNuanceBundle electronicChemChannelIndex) ≡ true
isotope-nuance-electronic-chem-present = refl

isotope-nuance-nuclear-decay-boundary-present :
  isSlotPresent (IsotopeBundle.slot isotopeElectronicNuclearNuanceBundle nuclearDecayBoundaryChannelIndex) ≡ true
isotope-nuance-nuclear-decay-boundary-present = refl

isotope-nuance-class11-isotope-present :
  isSlotPresent (IsotopeBundle.slot isotopeElectronicNuclearNuanceBundle class11IsotopeChannelIndex) ≡ true
isotope-nuance-class11-isotope-present = refl

isotope-nuance-present-count : IsotopeBundleWitness.present-count isotopeElectronicNuclearNuanceWitness ≡ 3
isotope-nuance-present-count = refl

isotope-nuance-concurrent-product :
  isotopeBundleIsConcurrentProduct isotopeElectronicNuclearNuanceWitness ≡ true
isotope-nuance-concurrent-product = refl

isotope-nuance-three-factors-concurrent :
  isSlotPresent (IsotopeBundle.slot isotopeElectronicNuclearNuanceBundle electronicChemChannelIndex) ≡ true
  × isSlotPresent (IsotopeBundle.slot isotopeElectronicNuclearNuanceBundle nuclearDecayBoundaryChannelIndex) ≡ true
  × isSlotPresent (IsotopeBundle.slot isotopeElectronicNuclearNuanceBundle class11IsotopeChannelIndex) ≡ true
  × IsotopeBundleWitness.present-count isotopeElectronicNuclearNuanceWitness ≡ 3
isotope-nuance-three-factors-concurrent =
  isotope-nuance-electronic-chem-present
  , isotope-nuance-nuclear-decay-boundary-present
  , isotope-nuance-class11-isotope-present
  , isotope-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : IsotopeBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if isotopeBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = IsotopeBundleWitness.bundle w
       in if isSlotPresent (IsotopeBundle.slot b i)
          then if isSlotPresent (IsotopeBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : IsotopeBundleWitness
unwiredWitness = mkIsotopeBundleWitness isotopeBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

isotope-nuance-xor-product-ok :
  evaluateXorRefuse isotopeElectronicNuclearNuanceWitness electronicChemChannelIndex nuclearDecayBoundaryChannelIndex ≡ xor-product-ok
isotope-nuance-xor-product-ok = refl

isotope-not-xor : isotopeNotXor ≡ true
isotope-not-xor = refl

------------------------------------------------------------------------
-- ClassifierIsotopeStep scaffold — IsotopeBundle **conservation**
------------------------------------------------------------------------

data ClassifierIsotopeStep : Set where
  isotope-identity : ClassifierIsotopeStep
  slot-leaf : ℕ → ClassifierIsotopeStep
  product-concurrent : ClassifierIsotopeStep → ClassifierIsotopeStep → ClassifierIsotopeStep
  xor-mutually-exclusive : ClassifierIsotopeStep → ClassifierIsotopeStep → ClassifierIsotopeStep

isotopeIdentity : ClassifierIsotopeStep
isotopeIdentity = isotope-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierIsotopeStep → ClassifierIsotopeStep → ClassifierIsotopeStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

electronicChemLeaf nuclearDecayBoundaryLeaf class11IsotopeLeaf : ClassifierIsotopeStep
electronicChemLeaf = slot-leaf electronicChemChannelIndex
nuclearDecayBoundaryLeaf = slot-leaf nuclearDecayBoundaryChannelIndex
class11IsotopeLeaf = slot-leaf class11IsotopeChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierIsotopeStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isIsotopeIdentity : ClassifierIsotopeStep → Bool
isIsotopeIdentity isotope-identity = true
isIsotopeIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at isotope-identity
------------------------------------------------------------------------

isotope-left-identity :
  ∀ (a : ClassifierIsotopeStep) →
  isIsotopeIdentity isotopeIdentity ≡ true
  × isProductConcurrent (productConcurrentOp isotopeIdentity a) ≡ true
isotope-left-identity a = refl , refl

isotope-right-identity :
  ∀ (a : ClassifierIsotopeStep) →
  isProductConcurrent (productConcurrentOp a isotopeIdentity) ≡ true
  × isIsotopeIdentity isotopeIdentity ≡ true
isotope-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-isotope :
  (∀ a → isProductConcurrent (productConcurrentOp isotopeIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a isotopeIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-isotope =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named isotope nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedIsotopeNuanceProduct : ClassifierIsotopeStep
namedIsotopeNuanceProduct =
  productConcurrentOp
    (productConcurrentOp electronicChemLeaf nuclearDecayBoundaryLeaf)
    class11IsotopeLeaf

named-isotope-nuance-product-concurrent :
  isProductConcurrent namedIsotopeNuanceProduct ≡ true
  × isotopeBundleIsConcurrentProduct isotopeElectronicNuclearNuanceWitness ≡ true
named-isotope-nuance-product-concurrent = refl , isotope-nuance-concurrent-product

------------------------------------------------------------------------
-- IsotopeBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data IsotopeAdmissibility : Set where
  isotope-admissible isotope-xor-refuse : IsotopeAdmissibility

isIsotopePreserving : ClassifierIsotopeStep → Bool
isIsotopePreserving isotope-identity = true
isIsotopePreserving (slot-leaf _) = true
isIsotopePreserving (product-concurrent a b) =
  isIsotopePreserving a ∧ isIsotopePreserving b
isIsotopePreserving (xor-mutually-exclusive _ _) = false

isIsotopeAdmissible : ClassifierIsotopeStep → Bool
isIsotopeAdmissible step = isIsotopePreserving step

electronic-chem-leaf-admissible : isIsotopeAdmissible electronicChemLeaf ≡ true
electronic-chem-leaf-admissible = refl

nuclear-decay-boundary-leaf-admissible : isIsotopeAdmissible nuclearDecayBoundaryLeaf ≡ true
nuclear-decay-boundary-leaf-admissible = refl

class11-isotope-leaf-admissible : isIsotopeAdmissible class11IsotopeLeaf ≡ true
class11-isotope-leaf-admissible = refl

named-isotope-nuance-admissible : isIsotopeAdmissible namedIsotopeNuanceProduct ≡ true
named-isotope-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isIsotopeAdmissible (xorMutuallyExclusiveOp electronicChemLeaf nuclearDecayBoundaryLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class11-isotope-refuse :
  isIsotopeAdmissible (xorMutuallyExclusiveOp nuclearDecayBoundaryLeaf class11IsotopeLeaf) ≡ false
xor-mutually-exclusive-class11-isotope-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data IsotopeWitnessPresence : Set where
  isotope-witness-absent isotope-witness-present : IsotopeWitnessPresence

record ClassifierIsotopeWitness : Set where
  constructor mkClassifierIsotopeWitness
  field
    witness-presence : IsotopeWitnessPresence
    isotope-gap-total : ℕ

isotopeWitnessAbsent : ClassifierIsotopeWitness
isotopeWitnessAbsent = mkClassifierIsotopeWitness isotope-witness-absent zero

isotopeWitnessPresentZeroGap : ClassifierIsotopeWitness
isotopeWitnessPresentZeroGap = mkClassifierIsotopeWitness isotope-witness-present zero

isotopeWitnessPresentWithGaps : ℕ → ClassifierIsotopeWitness
isotopeWitnessPresentWithGaps n = mkClassifierIsotopeWitness isotope-witness-present n

isotopeWitnessGapFree : ClassifierIsotopeWitness → Bool
isotopeWitnessGapFree (mkClassifierIsotopeWitness isotope-witness-absent _) = false
isotopeWitnessGapFree (mkClassifierIsotopeWitness isotope-witness-present n) =
  does (n ℕ-Props.≟ zero)

isotope-witness-present-zero-gap-free :
  isotopeWitnessGapFree isotopeWitnessPresentZeroGap ≡ true
isotope-witness-present-zero-gap-free = refl

isotope-witness-absent-not-gap-free :
  isotopeWitnessGapFree isotopeWitnessAbsent ≡ false
isotope-witness-absent-not-gap-free = refl

isotope-witness-with-gaps-not-gap-free :
  ∀ n → isotopeWitnessGapFree (isotopeWitnessPresentWithGaps (suc n)) ≡ false
isotope-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-isotope **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data IsotopeConservationVerdict : Set where
  verdict-unwired-ok verdict-isotope-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    verdict-nuclear-decay-chem-green-refuse verdict-parallel-isotope-axiom-refuse
    : IsotopeConservationVerdict

isotopeConservationVerdictOk : IsotopeConservationVerdict → Bool
isotopeConservationVerdictOk verdict-unwired-ok = true
isotopeConservationVerdictOk verdict-isotope-admissible-ok = true
isotopeConservationVerdictOk verdict-concurrent-product-ok = true
isotopeConservationVerdictOk _ = false

evaluateIsotopeConservationClose :
  IsotopeConservationModality → ClassifierIsotopeStep → ClassifierIsotopeWitness
  → IsotopeBundleWitness → Bool → Bool → Bool → IsotopeConservationVerdict
evaluateIsotopeConservationClose _ _ _ _ true _ _ = verdict-green-invent-refuse
evaluateIsotopeConservationClose _ _ _ _ false true _ = verdict-nuclear-decay-chem-green-refuse
evaluateIsotopeConservationClose _ _ _ _ false false true = verdict-parallel-isotope-axiom-refuse
evaluateIsotopeConservationClose isotope-conservation-unwired _ _ _ false false false = verdict-unwired-ok
evaluateIsotopeConservationClose isotope-conservation-assumed _ _ _ false false false = verdict-unwired-ok
evaluateIsotopeConservationClose isotope-conservation-surrogate _ _ _ false false false = verdict-unwired-ok
evaluateIsotopeConservationClose isotope-conservation-proved _ (mkClassifierIsotopeWitness isotope-witness-absent _) _ false false false =
  verdict-total-claim-refuse
evaluateIsotopeConservationClose isotope-conservation-proved (xor-mutually-exclusive _ _) _ _ false false false =
  verdict-xor-mutually-exclusive-refuse
evaluateIsotopeConservationClose isotope-conservation-proved _ (mkClassifierIsotopeWitness isotope-witness-present _) w false false false
  with isotopeBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-isotope-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without isotope witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateIsotopeConservationClose
    isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateIsotopeConservationClose
    isotope-conservation-assumed namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateIsotopeConservationClose
    isotope-conservation-surrogate namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false)
    ≡ true
  × isotopeConservationVerdictOk
      (evaluateIsotopeConservationClose isotope-conservation-assumed namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false)
      ≡ true
  × isotopeConservationVerdictOk
      (evaluateIsotopeConservationClose isotope-conservation-surrogate namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without isotope witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateIsotopeConservationClose
    isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose
       isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateIsotopeConservationClose
    isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false ≡
  verdict-isotope-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateIsotopeConservationClose
    isotope-conservation-proved
    (xorMutuallyExclusiveOp electronicChemLeaf nuclearDecayBoundaryLeaf)
    isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose
       isotope-conservation-proved
       (xorMutuallyExclusiveOp electronicChemLeaf nuclearDecayBoundaryLeaf)
       isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateIsotopeConservationClose
    isotope-conservation-proved
    (xorMutuallyExclusiveOp electronicChemLeaf nuclearDecayBoundaryLeaf)
    isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-isotope — nuance **product** closed
------------------------------------------------------------------------

isotope-admissible-ok :
  evaluateIsotopeConservationClose
    isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap unwiredWitness false false false ≡
  verdict-isotope-admissible-ok
isotope-admissible-ok = refl

isotope-admissible-verdict-ok :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose
       isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap unwiredWitness false false false)
    ≡ true
isotope-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — isotope nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateIsotopeConservationClose
    isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose
       isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-isotope-conservation-proved :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose
       isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false false)
    ≡ true
  × isotopeConservationProved ≡ false
concurrent-product-ok-still-not-isotope-conservation-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateIsotopeConservationClose
    isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness true false false ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose
       isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness true false false)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Nuclear decay chem GREEN refuse — electronic chemistry does not GREEN nuclear decay
------------------------------------------------------------------------

nuclear-decay-chem-green-refuse :
  evaluateIsotopeConservationClose
    isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false true false ≡
  verdict-nuclear-decay-chem-green-refuse
nuclear-decay-chem-green-refuse = refl

nuclear-decay-chem-green-always-refuse :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose
       isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false true false)
    ≡ false
nuclear-decay-chem-green-always-refuse = refl

electronic-chem-ne-nuclear-decay-green-pin : electronicChemNeNuclearDecayGreen ≡ true
electronic-chem-ne-nuclear-decay-green-pin = refl

------------------------------------------------------------------------
-- Parallel isotope axiom refuse — second law + conservation only, not 26th axiom
------------------------------------------------------------------------

parallel-isotope-axiom-refuse :
  evaluateIsotopeConservationClose
    isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false true ≡
  verdict-parallel-isotope-axiom-refuse
parallel-isotope-axiom-refuse = refl

parallel-isotope-axiom-always-refuse :
  isotopeConservationVerdictOk
    (evaluateIsotopeConservationClose
       isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false true)
    ≡ false
parallel-isotope-axiom-always-refuse = refl

not-parallel-isotope-axiom-minted-pin : notParallelIsotopeAxiomMinted ≡ true
not-parallel-isotope-axiom-minted-pin = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

isotopeConservationFiberOk : FormalFiber → Bool
isotopeConservationFiberOk fiber-quantum-knowing = true
isotopeConservationFiberOk fiber-meso-acting = false

isotope-conservation-knowing-fiber-ok :
  isotopeConservationFiberOk fiber-quantum-knowing ≡ true
isotope-conservation-knowing-fiber-ok = refl

isotope-conservation-meso-acting-not-ok :
  isotopeConservationFiberOk fiber-meso-acting ≡ false
isotope-conservation-meso-acting-not-ok = refl

isotope-conservation-routes-knowing-not-meso :
  isotopeConservationFiberOk fiber-quantum-knowing ≡ true ×
  isotopeConservationFiberOk fiber-meso-acting ≡ false
isotope-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  isotopeConservationFiberOk fiber-quantum-knowing ∧
  not (isotopeConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 11 isotope Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

isotope-conservation-not-proved : isotopeConservationProved ≡ false
isotope-conservation-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

isotope-second-law-conservation-framed : isotopeSecondLawConservationFramed ≡ true
isotope-second-law-conservation-framed = refl

isotope-not-xor-pin : isotopeNotXor ≡ true
isotope-not-xor-pin = isotope-not-xor

extra-element-id-not-forked-pin : extraElementIdNotForked ≡ true
extra-element-id-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel isotope axiom fork)
------------------------------------------------------------------------

isotopeConservationAxiom :
  (isotopeConservationProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (isotopeSecondLawConservationFramed ≡ true)
  × (isotopeNotXor ≡ true)
  × (electronicChemNeNuclearDecayGreen ≡ true)
  × (notParallelIsotopeAxiomMinted ≡ true)
  × (extraElementIdNotForked ≡ true)
  × (evaluateIsotopeConservationClose isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false ≡ verdict-unwired-ok)
  × (evaluateIsotopeConservationClose isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessAbsent isotopeElectronicNuclearNuanceWitness false false false ≡ verdict-total-claim-refuse)
  × (evaluateIsotopeConservationClose isotope-conservation-proved (xorMutuallyExclusiveOp electronicChemLeaf nuclearDecayBoundaryLeaf) isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateIsotopeConservationClose isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap unwiredWitness false false false ≡ verdict-isotope-admissible-ok)
  × (evaluateIsotopeConservationClose isotope-conservation-proved namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false false ≡ verdict-concurrent-product-ok)
  × (evaluateIsotopeConservationClose isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false true false ≡ verdict-nuclear-decay-chem-green-refuse)
  × (evaluateIsotopeConservationClose isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness false false true ≡ verdict-parallel-isotope-axiom-refuse)
  × (isotopeConservationFiberOk fiber-quantum-knowing ≡ true)
  × (isotopeConservationFiberOk fiber-meso-acting ≡ false)
  × (isotopeConservationVerdictOk (evaluateIsotopeConservationClose isotope-conservation-unwired namedIsotopeNuanceProduct isotopeWitnessPresentZeroGap isotopeElectronicNuclearNuanceWitness true false false) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp isotopeIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a isotopeIdentity) ≡ true)
  × (isIsotopeAdmissible (xorMutuallyExclusiveOp electronicChemLeaf nuclearDecayBoundaryLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (class11IsotopePatternIndex ≡ 11)
  × (IsotopeBundleWitness.present-count isotopeElectronicNuclearNuanceWitness ≡ 3)
  × (elementAtomicZ carbon ≡ 6)
  × (elementAtomicZ promethium ≡ 61)
isotopeConservationAxiom =
  isotope-conservation-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , isotope-second-law-conservation-framed
  , isotope-not-xor-pin
  , electronic-chem-ne-nuclear-decay-green-pin
  , not-parallel-isotope-axiom-minted-pin
  , extra-element-id-not-forked-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , isotope-admissible-ok
  , concurrent-product-ok
  , nuclear-decay-chem-green-refuse
  , parallel-isotope-axiom-refuse
  , isotope-conservation-knowing-fiber-ok
  , isotope-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , class11-isotope-pattern-index-eleven
  , isotope-nuance-present-count
  , carbon-z-6
  , promethium-z-61

isotopeConservationNamed : String
isotopeConservationNamed =
  "isotopeConservation: pattern class 11 isotope conservation concurrent Pi_c identity conserved electronic chemistry L0 identity nuclear decay boundary named class 11 isotope concurrent product identity conserved present ge 2 product not XOR electronic nuclear witness concurrent xor mutually exclusive refuse parallel isotope axiom refuse electronic chem ne nuclear decay green refuse not extra element id"

isotopeConservationCrossWitnessAuthority : String
isotopeConservationCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"

isotopeConservationTableAuthority : String
isotopeConservationTableAuthority =
  "umst/umst-chem/src/elements/z_061_pm.rs"

nuclearDecayBoundaryAuthority : String
nuclearDecayBoundaryAuthority =
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"

patternProductConservationAuthority : String
patternProductConservationAuthority =
  "umst/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

isotopeConservationCellId : String
isotopeConservationCellId = "CHEM-FORMAL-Q-AGDA-ISOTOPE-CONSERVATION"

isotopeConservationNonClaim : String
isotopeConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-ISOTOPE-CONSERVATION pattern class 11 isotope conservation concurrent Pi_c identity conserved electronic chemistry L0 identity nuclear decay boundary named class 11 isotope product not XOR electronic nuclear witness concurrent xor mutually exclusive refuse parallel isotope axiom refuse electronic chem ne nuclear decay green refuse not extra element id isotopeConservationProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite chem_physics_chart_isomorphism.rs z_061_pm not fork not physics GREEN not production_wired"

isotope-conservation-cell-id :
  isotopeConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-ISOTOPE-CONSERVATION"
isotope-conservation-cell-id = refl

isotope-conservation-cites-chem-physics-chart-rs :
  isotopeConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"
isotope-conservation-cites-chem-physics-chart-rs = refl

isotope-conservation-cites-z-061-pm-rs :
  isotopeConservationTableAuthority ≡
  "umst/umst-chem/src/elements/z_061_pm.rs"
isotope-conservation-cites-z-061-pm-rs = refl

isotope-conservation-modality-unwired :
  isotopeConservationModalityCurrent ≡ isotope-conservation-unwired
isotope-conservation-modality-unwired = refl

isotopeConservationPhysicsGreenAuthorized : Set
isotopeConservationPhysicsGreenAuthorized = ⊥

isotope-conservation-physics-green-false : ¬ isotopeConservationPhysicsGreenAuthorized
isotope-conservation-physics-green-false ()

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.IsotopeNuclearBoundaryConservation.agda
--
-- Pattern class 11 **isotope nuclear boundary** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (electronic L0 chemistry + nuclear boundary channel +
--     class 11 isotope PatternBundle concurrent factor; **product** not XOR, no parallel isotope axiom)
--   * XOR mutually-exclusive refuse; isotope nuclear boundary nuance witness concurrent
--     (electronic chemistry L0 identity + nuclear boundary named + class 11 isotope)
--   * **isotope nuclear boundary** laws Unwired (isotopeNuclearBoundaryProved = false)
--   * Nuclear≠electronic — refuse nuclear GREEN smuggle into electronic chemistry
--   * Isotope not 119th ElementId — same-Z nuance not new element
--
-- INT (read-only cite): umst/umst-chem/src/isotope_nuclear_electronic_boundary.rs
-- L0 table: umst/umst-chem/src/elements/z_061_pm.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel isotope axiom; not extra element id. Product not XOR.
------------------------------------------------------------------------
module ChemConstants.IsotopeNuclearBoundaryConservation where


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
-- Modality + pattern class 14 **catalysis** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data IsotopeNuclearBoundaryConservationModality : Set where
  isotope-nuclear-boundary-conservation-unwired isotope-nuclear-boundary-conservation-assumed
    isotope-nuclear-boundary-conservation-proved isotope-nuclear-boundary-conservation-surrogate
    : IsotopeNuclearBoundaryConservationModality

isotopeNuclearBoundaryConservationModalityCurrent : IsotopeNuclearBoundaryConservationModality
isotopeNuclearBoundaryConservationModalityCurrent = isotope-nuclear-boundary-conservation-unwired

isotopeNuclearBoundaryProved productionWired not118SquaredGreenTable
  isotopeNuclearBoundarySecondLawConservationFramed isotopeNuclearBoundaryNotXor : Bool
isotopeNuclearBoundaryProved = false
productionWired = false
not118SquaredGreenTable = true
isotopeNuclearBoundarySecondLawConservationFramed = true
isotopeNuclearBoundaryNotXor = true

nuclearNeElectronic notParallelIsotopeAxiomMinted isotopeNot119thElementId : Bool
nuclearNeElectronic = true
notParallelIsotopeAxiomMinted = true
isotopeNot119thElementId = true

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
-- Pattern class 14 Catalysis index pin
------------------------------------------------------------------------

class11IsotopeNuclearBoundaryIndex : ℕ
class11IsotopeNuclearBoundaryIndex = 11

class11-isotope-nuclear-boundary-index-eleven : class11IsotopeNuclearBoundaryIndex ≡ 11
class11-isotope-nuclear-boundary-index-eleven = refl

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
-- IsotopeNuclearBoundaryBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data IsotopeNuclearBoundaryBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : IsotopeNuclearBoundaryBundleSlot

isSlotPresent : IsotopeNuclearBoundaryBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- IsotopeNuclearBoundaryBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record IsotopeNuclearBoundaryBundle : Set where
  field slot : ℕ → IsotopeNuclearBoundaryBundleSlot

isotopeNuclearBoundaryBundleUnwired : IsotopeNuclearBoundaryBundle
isotopeNuclearBoundaryBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : IsotopeNuclearBoundaryBundle → ℕ → IsotopeNuclearBoundaryBundleSlot → IsotopeNuclearBoundaryBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else IsotopeNuclearBoundaryBundle.slot b j }

withPresent : IsotopeNuclearBoundaryBundle → ℕ → IsotopeNuclearBoundaryBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record IsotopeNuclearBoundaryBundleWitness : Set where
  constructor mkIsotopeNuclearBoundaryBundleWitness
  field
    bundle : IsotopeNuclearBoundaryBundle
    present-count : ℕ

isotopeNuclearBoundaryBundleIsConcurrentProduct : IsotopeNuclearBoundaryBundleWitness → Bool
isotopeNuclearBoundaryBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? IsotopeNuclearBoundaryBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named catalysis channel indices — interact restriction (1), nuclear boundary (2), class 11 isotope (3)
------------------------------------------------------------------------

electronicChemChannelIndex nuclearBoundaryChannelIndex class11IsotopeChannelIndex : ℕ
electronicChemChannelIndex = 1
nuclearBoundaryChannelIndex = 2
class11IsotopeChannelIndex = 3

electronic-chem-index-one : electronicChemChannelIndex ≡ 1
electronic-chem-index-one = refl

nuclear-boundary-index-two : nuclearBoundaryChannelIndex ≡ 2
nuclear-boundary-index-two = refl

class11-isotope-index-three : class11IsotopeChannelIndex ≡ 3
class11-isotope-index-three = refl

------------------------------------------------------------------------
-- Catalysis nuance witness — interact restriction + nuclear boundary + class 11 isotope concurrent
------------------------------------------------------------------------

isotopeNuclearBoundaryNuanceBundle : IsotopeNuclearBoundaryBundle
isotopeNuclearBoundaryNuanceBundle =
  withPresent
    (withPresent
      (withPresent isotopeNuclearBoundaryBundleUnwired electronicChemChannelIndex)
      nuclearBoundaryChannelIndex)
    class11IsotopeChannelIndex

isotopeNuclearBoundaryNuanceWitness : IsotopeNuclearBoundaryBundleWitness
isotopeNuclearBoundaryNuanceWitness =
  mkIsotopeNuclearBoundaryBundleWitness isotopeNuclearBoundaryNuanceBundle 3

isotope-nuclear-boundary-nuance-electronic-chem-present :
  isSlotPresent (IsotopeNuclearBoundaryBundle.slot isotopeNuclearBoundaryNuanceBundle electronicChemChannelIndex) ≡ true
isotope-nuclear-boundary-nuance-electronic-chem-present = refl

isotope-nuclear-boundary-nuance-nuclear-boundary-present :
  isSlotPresent (IsotopeNuclearBoundaryBundle.slot isotopeNuclearBoundaryNuanceBundle nuclearBoundaryChannelIndex) ≡ true
isotope-nuclear-boundary-nuance-nuclear-boundary-present = refl

isotope-nuclear-boundary-nuance-class11-isotope-present :
  isSlotPresent (IsotopeNuclearBoundaryBundle.slot isotopeNuclearBoundaryNuanceBundle class11IsotopeChannelIndex) ≡ true
isotope-nuclear-boundary-nuance-class11-isotope-present = refl

isotope-nuclear-boundary-nuance-present-count : IsotopeNuclearBoundaryBundleWitness.present-count isotopeNuclearBoundaryNuanceWitness ≡ 3
isotope-nuclear-boundary-nuance-present-count = refl

isotope-nuclear-boundary-nuance-concurrent-product :
  isotopeNuclearBoundaryBundleIsConcurrentProduct isotopeNuclearBoundaryNuanceWitness ≡ true
isotope-nuclear-boundary-nuance-concurrent-product = refl

isotope-nuclear-boundary-nuance-three-factors-concurrent :
  isSlotPresent (IsotopeNuclearBoundaryBundle.slot isotopeNuclearBoundaryNuanceBundle electronicChemChannelIndex) ≡ true
  × isSlotPresent (IsotopeNuclearBoundaryBundle.slot isotopeNuclearBoundaryNuanceBundle nuclearBoundaryChannelIndex) ≡ true
  × isSlotPresent (IsotopeNuclearBoundaryBundle.slot isotopeNuclearBoundaryNuanceBundle class11IsotopeChannelIndex) ≡ true
  × IsotopeNuclearBoundaryBundleWitness.present-count isotopeNuclearBoundaryNuanceWitness ≡ 3
isotope-nuclear-boundary-nuance-three-factors-concurrent =
  isotope-nuclear-boundary-nuance-electronic-chem-present
  , isotope-nuclear-boundary-nuance-nuclear-boundary-present
  , isotope-nuclear-boundary-nuance-class11-isotope-present
  , isotope-nuclear-boundary-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : IsotopeNuclearBoundaryBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if isotopeNuclearBoundaryBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = IsotopeNuclearBoundaryBundleWitness.bundle w
       in if isSlotPresent (IsotopeNuclearBoundaryBundle.slot b i)
          then if isSlotPresent (IsotopeNuclearBoundaryBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : IsotopeNuclearBoundaryBundleWitness
unwiredWitness = mkIsotopeNuclearBoundaryBundleWitness isotopeNuclearBoundaryBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

isotope-nuclear-boundary-nuance-xor-product-ok :
  evaluateXorRefuse isotopeNuclearBoundaryNuanceWitness electronicChemChannelIndex nuclearBoundaryChannelIndex ≡ xor-product-ok
isotope-nuclear-boundary-nuance-xor-product-ok = refl

isotope-nuclear-boundary-not-xor : isotopeNuclearBoundaryNotXor ≡ true
isotope-nuclear-boundary-not-xor = refl

------------------------------------------------------------------------
-- ClassifierIsotopeNuclearBoundaryStep scaffold — IsotopeNuclearBoundaryBundle **conservation**
------------------------------------------------------------------------

data ClassifierIsotopeNuclearBoundaryStep : Set where
  isotope-nuclear-boundary-identity : ClassifierIsotopeNuclearBoundaryStep
  slot-leaf : ℕ → ClassifierIsotopeNuclearBoundaryStep
  product-concurrent : ClassifierIsotopeNuclearBoundaryStep → ClassifierIsotopeNuclearBoundaryStep → ClassifierIsotopeNuclearBoundaryStep
  xor-mutually-exclusive : ClassifierIsotopeNuclearBoundaryStep → ClassifierIsotopeNuclearBoundaryStep → ClassifierIsotopeNuclearBoundaryStep

isotopeNuclearBoundaryIdentity : ClassifierIsotopeNuclearBoundaryStep
isotopeNuclearBoundaryIdentity = isotope-nuclear-boundary-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierIsotopeNuclearBoundaryStep → ClassifierIsotopeNuclearBoundaryStep → ClassifierIsotopeNuclearBoundaryStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

electronicChemLeaf nuclearBoundaryLeaf class11IsotopeLeaf : ClassifierIsotopeNuclearBoundaryStep
electronicChemLeaf = slot-leaf electronicChemChannelIndex
nuclearBoundaryLeaf = slot-leaf nuclearBoundaryChannelIndex
class11IsotopeLeaf = slot-leaf class11IsotopeChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierIsotopeNuclearBoundaryStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isIsotopeNuclearBoundaryIdentity : ClassifierIsotopeNuclearBoundaryStep → Bool
isIsotopeNuclearBoundaryIdentity isotope-nuclear-boundary-identity = true
isIsotopeNuclearBoundaryIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at isotope-nuclear-boundary-identity
------------------------------------------------------------------------

isotope-nuclear-boundary-left-identity :
  ∀ (a : ClassifierIsotopeNuclearBoundaryStep) →
  isIsotopeNuclearBoundaryIdentity isotopeNuclearBoundaryIdentity ≡ true
  × isProductConcurrent (productConcurrentOp isotopeNuclearBoundaryIdentity a) ≡ true
isotope-nuclear-boundary-left-identity a = refl , refl

isotope-nuclear-boundary-right-identity :
  ∀ (a : ClassifierIsotopeNuclearBoundaryStep) →
  isProductConcurrent (productConcurrentOp a isotopeNuclearBoundaryIdentity) ≡ true
  × isIsotopeNuclearBoundaryIdentity isotopeNuclearBoundaryIdentity ≡ true
isotope-nuclear-boundary-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-isotope-nuclear-boundary :
  (∀ a → isProductConcurrent (productConcurrentOp isotopeNuclearBoundaryIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a isotopeNuclearBoundaryIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-isotope-nuclear-boundary =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named catalysis nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedIsotopeNuclearBoundaryNuanceProduct : ClassifierIsotopeNuclearBoundaryStep
namedIsotopeNuclearBoundaryNuanceProduct =
  productConcurrentOp
    (productConcurrentOp electronicChemLeaf nuclearBoundaryLeaf)
    class11IsotopeLeaf

named-isotope-nuclear-boundary-nuance-product-concurrent :
  isProductConcurrent namedIsotopeNuclearBoundaryNuanceProduct ≡ true
  × isotopeNuclearBoundaryBundleIsConcurrentProduct isotopeNuclearBoundaryNuanceWitness ≡ true
named-isotope-nuclear-boundary-nuance-product-concurrent = refl , isotope-nuclear-boundary-nuance-concurrent-product

------------------------------------------------------------------------
-- IsotopeNuclearBoundaryBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data IsotopeNuclearBoundaryAdmissibility : Set where
  isotope-nuclear-boundary-admissible isotope-nuclear-boundary-xor-refuse : IsotopeNuclearBoundaryAdmissibility

isIsotopeNuclearBoundaryPreserving : ClassifierIsotopeNuclearBoundaryStep → Bool
isIsotopeNuclearBoundaryPreserving isotope-nuclear-boundary-identity = true
isIsotopeNuclearBoundaryPreserving (slot-leaf _) = true
isIsotopeNuclearBoundaryPreserving (product-concurrent a b) =
  isIsotopeNuclearBoundaryPreserving a ∧ isIsotopeNuclearBoundaryPreserving b
isIsotopeNuclearBoundaryPreserving (xor-mutually-exclusive _ _) = false

isIsotopeNuclearBoundaryAdmissible : ClassifierIsotopeNuclearBoundaryStep → Bool
isIsotopeNuclearBoundaryAdmissible step = isIsotopeNuclearBoundaryPreserving step

electronic-chem-leaf-admissible : isIsotopeNuclearBoundaryAdmissible electronicChemLeaf ≡ true
electronic-chem-leaf-admissible = refl

nuclear-boundary-leaf-admissible : isIsotopeNuclearBoundaryAdmissible nuclearBoundaryLeaf ≡ true
nuclear-boundary-leaf-admissible = refl

class11-isotope-leaf-admissible : isIsotopeNuclearBoundaryAdmissible class11IsotopeLeaf ≡ true
class11-isotope-leaf-admissible = refl

named-isotope-nuclear-boundary-nuance-admissible : isIsotopeNuclearBoundaryAdmissible namedIsotopeNuclearBoundaryNuanceProduct ≡ true
named-isotope-nuclear-boundary-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isIsotopeNuclearBoundaryAdmissible (xorMutuallyExclusiveOp electronicChemLeaf nuclearBoundaryLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class11-isotope-refuse :
  isIsotopeNuclearBoundaryAdmissible (xorMutuallyExclusiveOp nuclearBoundaryLeaf class11IsotopeLeaf) ≡ false
xor-mutually-exclusive-class11-isotope-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data IsotopeNuclearBoundaryWitnessPresence : Set where
  isotope-nuclear-boundary-witness-absent isotope-nuclear-boundary-witness-present : IsotopeNuclearBoundaryWitnessPresence

record ClassifierIsotopeNuclearBoundaryWitness : Set where
  constructor mkClassifierIsotopeNuclearBoundaryWitness
  field
    witness-presence : IsotopeNuclearBoundaryWitnessPresence
    isotope-nuclear-boundary-gap-total : ℕ

isotopeNuclearBoundaryWitnessAbsent : ClassifierIsotopeNuclearBoundaryWitness
isotopeNuclearBoundaryWitnessAbsent = mkClassifierIsotopeNuclearBoundaryWitness isotope-nuclear-boundary-witness-absent zero

isotopeNuclearBoundaryWitnessPresentZeroGap : ClassifierIsotopeNuclearBoundaryWitness
isotopeNuclearBoundaryWitnessPresentZeroGap = mkClassifierIsotopeNuclearBoundaryWitness isotope-nuclear-boundary-witness-present zero

isotopeNuclearBoundaryWitnessPresentWithGaps : ℕ → ClassifierIsotopeNuclearBoundaryWitness
isotopeNuclearBoundaryWitnessPresentWithGaps n = mkClassifierIsotopeNuclearBoundaryWitness isotope-nuclear-boundary-witness-present n

isotopeNuclearBoundaryWitnessGapFree : ClassifierIsotopeNuclearBoundaryWitness → Bool
isotopeNuclearBoundaryWitnessGapFree (mkClassifierIsotopeNuclearBoundaryWitness isotope-nuclear-boundary-witness-absent _) = false
isotopeNuclearBoundaryWitnessGapFree (mkClassifierIsotopeNuclearBoundaryWitness isotope-nuclear-boundary-witness-present n) =
  does (n ℕ-Props.≟ zero)

isotope-nuclear-boundary-witness-present-zero-gap-free :
  isotopeNuclearBoundaryWitnessGapFree isotopeNuclearBoundaryWitnessPresentZeroGap ≡ true
isotope-nuclear-boundary-witness-present-zero-gap-free = refl

isotope-nuclear-boundary-witness-absent-not-gap-free :
  isotopeNuclearBoundaryWitnessGapFree isotopeNuclearBoundaryWitnessAbsent ≡ false
isotope-nuclear-boundary-witness-absent-not-gap-free = refl

isotope-nuclear-boundary-witness-with-gaps-not-gap-free :
  ∀ n → isotopeNuclearBoundaryWitnessGapFree (isotopeNuclearBoundaryWitnessPresentWithGaps (suc n)) ≡ false
isotope-nuclear-boundary-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Catalysis **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data IsotopeNuclearBoundaryConservationVerdict : Set where
  verdict-unwired-ok verdict-isotope-nuclear-boundary-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    verdict-nuclear-ne-electronic-refuse verdict-element-119-refuse
    verdict-parallel-isotope-axiom-refuse
    : IsotopeNuclearBoundaryConservationVerdict

isotopeNuclearBoundaryConservationVerdictOk : IsotopeNuclearBoundaryConservationVerdict → Bool
isotopeNuclearBoundaryConservationVerdictOk verdict-unwired-ok = true
isotopeNuclearBoundaryConservationVerdictOk verdict-isotope-nuclear-boundary-admissible-ok = true
isotopeNuclearBoundaryConservationVerdictOk verdict-concurrent-product-ok = true
isotopeNuclearBoundaryConservationVerdictOk _ = false

evaluateIsotopeNuclearBoundaryConservationClose :
  IsotopeNuclearBoundaryConservationModality → ClassifierIsotopeNuclearBoundaryStep → ClassifierIsotopeNuclearBoundaryWitness
  → IsotopeNuclearBoundaryBundleWitness → Bool → Bool → Bool → Bool → IsotopeNuclearBoundaryConservationVerdict
evaluateIsotopeNuclearBoundaryConservationClose _ _ _ _ true _ _ _ = verdict-green-invent-refuse
evaluateIsotopeNuclearBoundaryConservationClose _ _ _ _ false true _ _ = verdict-nuclear-ne-electronic-refuse
evaluateIsotopeNuclearBoundaryConservationClose _ _ _ _ false false true _ = verdict-element-119-refuse
evaluateIsotopeNuclearBoundaryConservationClose _ _ _ _ false false false true = verdict-parallel-isotope-axiom-refuse
evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-unwired _ _ _ false false false false = verdict-unwired-ok
evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-assumed _ _ _ false false false false = verdict-unwired-ok
evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-surrogate _ _ _ false false false false = verdict-unwired-ok
evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-proved _ (mkClassifierIsotopeNuclearBoundaryWitness isotope-nuclear-boundary-witness-absent _) _ false false false false =
  verdict-total-claim-refuse
evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-proved (xor-mutually-exclusive _ _) _ _ false false false false =
  verdict-xor-mutually-exclusive-refuse
evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-proved _ (mkClassifierIsotopeNuclearBoundaryWitness isotope-nuclear-boundary-witness-present _) w false false false false
  with isotopeNuclearBoundaryBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-isotope-nuclear-boundary-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-assumed namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-surrogate namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false)
    ≡ true
  × isotopeNuclearBoundaryConservationVerdictOk
      (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-assumed namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false)
      ≡ true
  × isotopeNuclearBoundaryConservationVerdictOk
      (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-surrogate namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false ≡
  verdict-isotope-nuclear-boundary-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-proved
    (xorMutuallyExclusiveOp electronicChemLeaf nuclearBoundaryLeaf)
    isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-proved
       (xorMutuallyExclusiveOp electronicChemLeaf nuclearBoundaryLeaf)
       isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-proved
    (xorMutuallyExclusiveOp electronicChemLeaf nuclearBoundaryLeaf)
    isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

isotope-nuclear-boundary-admissible-ok :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap unwiredWitness false false false false ≡
  verdict-isotope-nuclear-boundary-admissible-ok
isotope-nuclear-boundary-admissible-ok = refl

isotope-nuclear-boundary-admissible-verdict-ok :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap unwiredWitness false false false false)
    ≡ true
isotope-nuclear-boundary-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-isotope-nuclear-boundary-proved :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false false)
    ≡ true
  × isotopeNuclearBoundaryProved ≡ false
concurrent-product-ok-still-not-isotope-nuclear-boundary-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness true false false false ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness true false false false)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

isotopeNuclearBoundaryConservationFiberOk : FormalFiber → Bool
isotopeNuclearBoundaryConservationFiberOk fiber-quantum-knowing = true
isotopeNuclearBoundaryConservationFiberOk fiber-meso-acting = false

isotope-nuclear-boundary-conservation-knowing-fiber-ok :
  isotopeNuclearBoundaryConservationFiberOk fiber-quantum-knowing ≡ true
isotope-nuclear-boundary-conservation-knowing-fiber-ok = refl

isotope-nuclear-boundary-conservation-meso-acting-not-ok :
  isotopeNuclearBoundaryConservationFiberOk fiber-meso-acting ≡ false
isotope-nuclear-boundary-conservation-meso-acting-not-ok = refl

isotope-nuclear-boundary-conservation-routes-knowing-not-meso :
  isotopeNuclearBoundaryConservationFiberOk fiber-quantum-knowing ≡ true ×
  isotopeNuclearBoundaryConservationFiberOk fiber-meso-acting ≡ false
isotope-nuclear-boundary-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  isotopeNuclearBoundaryConservationFiberOk fiber-quantum-knowing ∧
  not (isotopeNuclearBoundaryConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl


------------------------------------------------------------------------
-- Out-of-bar Z=119 refuse — isotope same-Z nuance not 119th ElementId
------------------------------------------------------------------------

outOfBarZ119 : ℕ
outOfBarZ119 = 119

out-of-bar-z-119 : outOfBarZ119 ≡ 119
out-of-bar-z-119 = refl

element-119-refused :
  does (outOfBarZ119 ℕ-Props.≟ 119) ≡ true
  × isotopeNot119thElementId ≡ true
element-119-refused = refl , refl

------------------------------------------------------------------------
-- Nuclear≠electronic refuse — nuclear decay is not chem GREEN
------------------------------------------------------------------------

nuclear-ne-electronic-refuse :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false true false false ≡
  verdict-nuclear-ne-electronic-refuse
nuclear-ne-electronic-refuse = refl

nuclear-ne-electronic-always-refuse :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false true false false)
    ≡ false
nuclear-ne-electronic-always-refuse = refl

------------------------------------------------------------------------
-- Element 119 refuse — isotope not 119th ElementId
------------------------------------------------------------------------

element-119-refuse-verdict :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false true false ≡
  verdict-element-119-refuse
element-119-refuse-verdict = refl

element-119-refuse-always-refuse :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false true false)
    ≡ false
element-119-refuse-always-refuse = refl

------------------------------------------------------------------------
-- Parallel isotope axiom refuse — second law + conservation only, not 26th axiom
------------------------------------------------------------------------

parallel-isotope-axiom-refuse :
  evaluateIsotopeNuclearBoundaryConservationClose
    isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false true ≡
  verdict-parallel-isotope-axiom-refuse
parallel-isotope-axiom-refuse = refl

parallel-isotope-axiom-always-refuse :
  isotopeNuclearBoundaryConservationVerdictOk
    (evaluateIsotopeNuclearBoundaryConservationClose
       isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false true)
    ≡ false
parallel-isotope-axiom-always-refuse = refl

------------------------------------------------------------------------
-- Honest pins — not class 11 isotope nuclear boundary Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

isotope-nuclear-boundary-not-proved : isotopeNuclearBoundaryProved ≡ false
isotope-nuclear-boundary-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

isotope-nuclear-boundary-second-law-conservation-framed : isotopeNuclearBoundarySecondLawConservationFramed ≡ true
isotope-nuclear-boundary-second-law-conservation-framed = refl

isotope-nuclear-boundary-not-xor-pin : isotopeNuclearBoundaryNotXor ≡ true
isotope-nuclear-boundary-not-xor-pin = isotope-nuclear-boundary-not-xor

nuclear-ne-electronic-pin : nuclearNeElectronic ≡ true
nuclear-ne-electronic-pin = refl

not-parallel-isotope-axiom-minted-pin : notParallelIsotopeAxiomMinted ≡ true
not-parallel-isotope-axiom-minted-pin = refl

isotope-not-119th-element-id-pin : isotopeNot119thElementId ≡ true
isotope-not-119th-element-id-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel isotope axiom fork)
------------------------------------------------------------------------

isotopeNuclearBoundaryConservationAxiom :
  (isotopeNuclearBoundaryProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (isotopeNuclearBoundarySecondLawConservationFramed ≡ true)
  × (isotopeNuclearBoundaryNotXor ≡ true)
  × (nuclearNeElectronic ≡ true)
  × (notParallelIsotopeAxiomMinted ≡ true)
  × (isotopeNot119thElementId ≡ true)
  × (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false ≡ verdict-unwired-ok)
  × (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessAbsent isotopeNuclearBoundaryNuanceWitness false false false false ≡ verdict-total-claim-refuse)
  × (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-proved (xorMutuallyExclusiveOp electronicChemLeaf nuclearBoundaryLeaf) isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap unwiredWitness false false false false ≡ verdict-isotope-nuclear-boundary-admissible-ok)
  × (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-proved namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false false ≡ verdict-concurrent-product-ok)
  × (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false true false false ≡ verdict-nuclear-ne-electronic-refuse)
  × (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false true false ≡ verdict-element-119-refuse)
  × (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness false false false true ≡ verdict-parallel-isotope-axiom-refuse)
  × (isotopeNuclearBoundaryConservationFiberOk fiber-quantum-knowing ≡ true)
  × (isotopeNuclearBoundaryConservationFiberOk fiber-meso-acting ≡ false)
  × (isotopeNuclearBoundaryConservationVerdictOk (evaluateIsotopeNuclearBoundaryConservationClose isotope-nuclear-boundary-conservation-unwired namedIsotopeNuclearBoundaryNuanceProduct isotopeNuclearBoundaryWitnessPresentZeroGap isotopeNuclearBoundaryNuanceWitness true false false false) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp isotopeNuclearBoundaryIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a isotopeNuclearBoundaryIdentity) ≡ true)
  × (isIsotopeNuclearBoundaryAdmissible (xorMutuallyExclusiveOp electronicChemLeaf nuclearBoundaryLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (class11IsotopeNuclearBoundaryIndex ≡ 11)
  × (IsotopeNuclearBoundaryBundleWitness.present-count isotopeNuclearBoundaryNuanceWitness ≡ 3)
  × (elementAtomicZ carbon ≡ 6)
  × (elementAtomicZ promethium ≡ 61)
isotopeNuclearBoundaryConservationAxiom =
  isotope-nuclear-boundary-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , isotope-nuclear-boundary-second-law-conservation-framed
  , isotope-nuclear-boundary-not-xor-pin
  , nuclear-ne-electronic-pin
  , not-parallel-isotope-axiom-minted-pin
  , isotope-not-119th-element-id-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , isotope-nuclear-boundary-admissible-ok
  , concurrent-product-ok
  , nuclear-ne-electronic-refuse
  , element-119-refuse-verdict
  , parallel-isotope-axiom-refuse
  , isotope-nuclear-boundary-conservation-knowing-fiber-ok
  , isotope-nuclear-boundary-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , class11-isotope-nuclear-boundary-index-eleven
  , isotope-nuclear-boundary-nuance-present-count
  , carbon-z-6
  , promethium-z-61

isotopeNuclearBoundaryConservationNamed : String
isotopeNuclearBoundaryConservationNamed =
  "isotopeNuclearBoundaryConservation: pattern class 11 isotope nuclear boundary conservation concurrent Pi_c identity conserved Electronic chemistry L0 identity nuclear boundary class 11 isotope concurrent product identity conserved present ge 2 product not XOR nuclear ne electronic no parallel isotope axiom nuclear boundary"

isotopeNuclearBoundaryConservationCrossWitnessAuthority : String
isotopeNuclearBoundaryConservationCrossWitnessAuthority =
  "umst/umst-chem/src/isotope_nuclear_electronic_boundary.rs"

isotopeNuclearBoundaryTableAuthority : String
isotopeNuclearBoundaryTableAuthority =
  "umst/umst-chem/src/elements/z_061_pm.rs"

nuclearDecayBoundaryAuthority : String
nuclearDecayBoundaryAuthority =
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"

patternProductConservationAuthority : String
patternProductConservationAuthority =
  "umst/umst-chem/src/umst-formal-double-slit/Haskell/UMST/ChemConstants/PatternProductConservation.hs"

isotopeNuclearBoundaryConservationCellId : String
isotopeNuclearBoundaryConservationCellId = "CHEM-FORMAL-Q-AGDA-ISOTOPE-NUCLEAR-BOUNDARY-CONSERVATION"

isotopeNuclearBoundaryConservationNonClaim : String
isotopeNuclearBoundaryConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-ISOTOPE-NUCLEAR-BOUNDARY-CONSERVATION pattern class 11 isotope nuclear boundary conservation nuclear ne electronic isotope not 119th ElementId concurrent Pi_c identity conserved Electronic chemistry L0 identity nuclear boundary class 11 isotope product not XOR nuclear ne electronic no parallel isotope axiom nuclear boundary XOR mutually exclusive refuse catalysis nuance witness concurrent isotopeNuclearBoundaryProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite isotope_nuclear_electronic_boundary.rs l0_tables catalysis not fork not physics GREEN not production_wired"

isotope-nuclear-boundary-conservation-cell-id :
  isotopeNuclearBoundaryConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-ISOTOPE-NUCLEAR-BOUNDARY-CONSERVATION"
isotope-nuclear-boundary-conservation-cell-id = refl

isotope-nuclear-boundary-conservation-cites-catalysis-barrier-rs :
  isotopeNuclearBoundaryConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/isotope_nuclear_electronic_boundary.rs"
isotope-nuclear-boundary-conservation-cites-catalysis-barrier-rs = refl

isotope-nuclear-boundary-conservation-cites-l0-table-rs :
  isotopeNuclearBoundaryTableAuthority ≡
  "umst/umst-chem/src/elements/z_061_pm.rs"
isotope-nuclear-boundary-conservation-cites-l0-table-rs = refl

isotope-nuclear-boundary-conservation-modality-unwired :
  isotopeNuclearBoundaryConservationModalityCurrent ≡ isotope-nuclear-boundary-conservation-unwired
isotope-nuclear-boundary-conservation-modality-unwired = refl

isotopeNuclearBoundaryConservationPhysicsGreenAuthorized : Set
isotopeNuclearBoundaryConservationPhysicsGreenAuthorized = ⊥

isotope-nuclear-boundary-conservation-physics-green-false : ¬ isotopeNuclearBoundaryConservationPhysicsGreenAuthorized
isotope-nuclear-boundary-conservation-physics-green-false ()

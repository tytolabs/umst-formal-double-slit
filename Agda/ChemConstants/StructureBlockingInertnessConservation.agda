-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.StructureBlockingInertnessConservation.agda
--
-- CLASS-05 structure-blocking / inertness **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (He 1s²; structure_blocking + closed_shell product not XOR)
--   * He no-ore = missing Interact class 5 — not atmophile nobility magic
--   * InteractKind::StructureBlocking partiality typed — not bond-forming folklore
--   * **structure-blocking** laws Unwired (structureBlockingInertnessProved = false)
--
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- INT (read-only): umst/umst-chem/src/x_rows/structure_blocking_inertness_conservation.rs
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.StructureBlockingInertnessConservation where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + class-5 structure-blocking / inertness **conservation** pins (Unwired)
------------------------------------------------------------------------

data StructureBlockingInertnessConservationModality : Set where
  structure-blocking-inertness-conservation-unwired structure-blocking-inertness-conservation-assumed
    structure-blocking-inertness-conservation-proved structure-blocking-inertness-conservation-surrogate
    : StructureBlockingInertnessConservationModality

structureBlockingInertnessConservationModalityCurrent : StructureBlockingInertnessConservationModality
structureBlockingInertnessConservationModalityCurrent = structure-blocking-inertness-conservation-unwired

structureBlockingInertnessProved productionWired not118SquaredGreenTable
  structureBlockingSecondLawConservationFramed productNotXor
  heNoOreMissingInteract missingInteractNotNobilityMagic : Bool
structureBlockingInertnessProved = false
productionWired = false
not118SquaredGreenTable = true
structureBlockingSecondLawConservationFramed = true
productNotXor = true
heNoOreMissingInteract = true
missingInteractNotNobilityMagic = true

------------------------------------------------------------------------
-- PatternBundle class cardinality 25 — Π_c structure, not 118²
------------------------------------------------------------------------

patternClassCardinality : ℕ
patternClassCardinality = 25

pattern-class-cardinality-twenty-five : patternClassCardinality ≡ 25
pattern-class-cardinality-twenty-five = refl

pattern-class-not-118-squared :
  does (patternClassCardinality ℕ-Props.≟ (118 * 118)) ≡ false
pattern-class-not-118-squared = refl

------------------------------------------------------------------------
-- North-star §2 class 5 — structure_blocking_inertness authority pin
------------------------------------------------------------------------

structureBlockingClassIndex closedShellNamedFactorClassIndex : ℕ
structureBlockingClassIndex = 5
closedShellNamedFactorClassIndex = 24

structure-blocking-class-index-five :
  structureBlockingClassIndex ≡ 5
structure-blocking-class-index-five = refl

closed-shell-named-factor-class-index-twenty-four :
  closedShellNamedFactorClassIndex ≡ 24
closed-shell-named-factor-class-index-twenty-four = refl

interactKindStructureBlockingTag patternBundleStructureBlockingFactorTag : String
interactKindStructureBlockingTag = "InteractKind::StructureBlocking"
patternBundleStructureBlockingFactorTag = "structure_blocking_inertness"

namedFactorClosedShellTag heliumNotationTag : String
namedFactorClosedShellTag = "closed_shell"
heliumNotationTag = "1s²"

------------------------------------------------------------------------
-- Named element Z pins — helium (Z=2), oganesson (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  helium oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ helium = 2
elementAtomicZ oganesson = 118

helium-z-2 : elementAtomicZ helium ≡ 2
helium-z-2 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- He no-ore = missing Interact class 5 — not atmophile nobility GREEN
------------------------------------------------------------------------

heNoOreMissingInteractClass5 : Bool
heNoOreMissingInteractClass5 = true

he-no-ore-missing-interact-class5 :
  heNoOreMissingInteractClass5 ≡ true
he-no-ore-missing-interact-class5 = refl

he-no-ore-missing-interact-pinned :
  (elementAtomicZ helium ≡ 2) × (structureBlockingClassIndex ≡ 5)
he-no-ore-missing-interact-pinned = helium-z-2 , structure-blocking-class-index-five

he-no-ore-not-nobility-magic :
  heNoOreMissingInteract ≡ true × missingInteractNotNobilityMagic ≡ true
he-no-ore-not-nobility-magic = refl , refl

------------------------------------------------------------------------
-- PatternBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PatternBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PatternBundleSlot

isSlotPresent : PatternBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

record PatternBundle : Set where
  field slot : ℕ → PatternBundleSlot

patternBundleUnwired : PatternBundle
patternBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : PatternBundle → ℕ → PatternBundleSlot → PatternBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else PatternBundle.slot b j }

withPresent : PatternBundle → ℕ → PatternBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- NamedFactors slot — closed_shell concurrent Π_c factor (class 24)
------------------------------------------------------------------------

data NamedFactorSlot : Set where
  named-unwired named-absent named-present : NamedFactorSlot

isNamedPresent : NamedFactorSlot → Bool
isNamedPresent named-present = true
isNamedPresent _ = false

record NamedFactorsBundle : Set where
  field named-slot : ℕ → NamedFactorSlot

namedFactorsUnwired : NamedFactorsBundle
namedFactorsUnwired = record { named-slot = λ _ → named-unwired }

namedSlotEq : ℕ → ℕ → Bool
namedSlotEq zero zero = true
namedSlotEq (suc m) (suc n) = namedSlotEq m n
namedSlotEq _ _ = false

withNamedSlot : NamedFactorsBundle → ℕ → NamedFactorSlot → NamedFactorsBundle
withNamedSlot b i s = record
  { named-slot = λ j → if namedSlotEq j i then s else NamedFactorsBundle.named-slot b j }

withNamedPresent : NamedFactorsBundle → ℕ → NamedFactorsBundle
withNamedPresent b i = withNamedSlot b i named-present

closedShellNamedFactorIndex : ℕ
closedShellNamedFactorIndex = 8

closed-shell-named-factor-index-eight : closedShellNamedFactorIndex ≡ 8
closed-shell-named-factor-index-eight = refl

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PatternBundleWitness : Set where
  constructor mkPatternBundleWitness
  field
    bundle : PatternBundle
    present-count : ℕ

patternBundleIsConcurrentProduct : PatternBundleWitness → Bool
patternBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PatternBundleWitness.present-count w)

record NamedFactorsWitness : Set where
  constructor mkNamedFactorsWitness
  field
    named-bundle : NamedFactorsBundle
    named-present-count : ℕ

namedFactorsIsConcurrentProduct : NamedFactorsWitness → Bool
namedFactorsIsConcurrentProduct w =
  does ((suc zero) ℕ-Props.≤? NamedFactorsWitness.named-present-count w)

------------------------------------------------------------------------
-- Helium 1s² nuance witness — structure_blocking + closed_shell concurrent
------------------------------------------------------------------------

helium1s2PatternBundle : PatternBundle
helium1s2PatternBundle =
  withPresent
    (withPresent patternBundleUnwired structureBlockingClassIndex)
    closedShellNamedFactorClassIndex

helium1s2NamedFactors : NamedFactorsBundle
helium1s2NamedFactors = withNamedPresent namedFactorsUnwired closedShellNamedFactorIndex

helium1s2PatternWitness : PatternBundleWitness
helium1s2PatternWitness = mkPatternBundleWitness helium1s2PatternBundle 2

helium1s2NamedWitness : NamedFactorsWitness
helium1s2NamedWitness = mkNamedFactorsWitness helium1s2NamedFactors 1

helium-structure-blocking-present :
  isSlotPresent (PatternBundle.slot helium1s2PatternBundle structureBlockingClassIndex) ≡ true
helium-structure-blocking-present = refl

helium-closed-shell-pattern-present :
  isSlotPresent (PatternBundle.slot helium1s2PatternBundle closedShellNamedFactorClassIndex) ≡ true
helium-closed-shell-pattern-present = refl

helium-closed-shell-named-present :
  isNamedPresent (NamedFactorsBundle.named-slot helium1s2NamedFactors closedShellNamedFactorIndex) ≡ true
helium-closed-shell-named-present = refl

helium-1s2-pattern-present-count :
  PatternBundleWitness.present-count helium1s2PatternWitness ≡ 2
helium-1s2-pattern-present-count = refl

helium-1s2-named-present-count :
  NamedFactorsWitness.named-present-count helium1s2NamedWitness ≡ 1
helium-1s2-named-present-count = refl

helium-1s2-concurrent-product :
  patternBundleIsConcurrentProduct helium1s2PatternWitness ≡ true
helium-1s2-concurrent-product = refl

helium-1s2-concurrent-product-factors :
  isSlotPresent (PatternBundle.slot helium1s2PatternBundle structureBlockingClassIndex) ≡ true
  × isSlotPresent (PatternBundle.slot helium1s2PatternBundle closedShellNamedFactorClassIndex) ≡ true
  × isNamedPresent (NamedFactorsBundle.named-slot helium1s2NamedFactors closedShellNamedFactorIndex) ≡ true
  × (elementAtomicZ helium ≡ 2)
  × PatternBundleWitness.present-count helium1s2PatternWitness ≡ 2
helium-1s2-concurrent-product-factors =
  helium-structure-blocking-present
  , helium-closed-shell-pattern-present
  , helium-closed-shell-named-present
  , helium-z-2
  , helium-1s2-pattern-present-count

------------------------------------------------------------------------
-- InteractKind partiality scaffold — StructureBlocking not folklore
------------------------------------------------------------------------

data InteractKind : Set where
  structure-blocking-kind bond-forming-folklore-kind : InteractKind

isStructureBlockingKind isBondFormingFolkloreKind : InteractKind → Bool
isStructureBlockingKind structure-blocking-kind = true
isStructureBlockingKind _ = false

isBondFormingFolkloreKind bond-forming-folklore-kind = true
isBondFormingFolkloreKind _ = false

structure-blocking-kind-pinned :
  isStructureBlockingKind structure-blocking-kind ≡ true ×
  isBondFormingFolkloreKind structure-blocking-kind ≡ false
structure-blocking-kind-pinned = refl , refl

structure-blocking-distinct-from-folklore :
  structure-blocking-kind ≢ bond-forming-folklore-kind
structure-blocking-distinct-from-folklore ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PatternBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if patternBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = PatternBundleWitness.bundle w
       in if isSlotPresent (PatternBundle.slot b i)
          then if isSlotPresent (PatternBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PatternBundleWitness
unwiredWitness = mkPatternBundleWitness patternBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

helium-1s2-xor-product-ok :
  evaluateXorRefuse helium1s2PatternWitness structureBlockingClassIndex closedShellNamedFactorClassIndex ≡ xor-product-ok
helium-1s2-xor-product-ok = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

------------------------------------------------------------------------
-- ClassifierStructureBlockingStep scaffold — Π_c **conservation**
------------------------------------------------------------------------

data ClassifierStructureBlockingStep : Set where
  structure-identity : ClassifierStructureBlockingStep
  slot-leaf : ℕ → ClassifierStructureBlockingStep
  product-concurrent : ClassifierStructureBlockingStep → ClassifierStructureBlockingStep → ClassifierStructureBlockingStep
  xor-mutually-exclusive : ClassifierStructureBlockingStep → ClassifierStructureBlockingStep → ClassifierStructureBlockingStep

structureIdentity : ClassifierStructureBlockingStep
structureIdentity = structure-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierStructureBlockingStep → ClassifierStructureBlockingStep → ClassifierStructureBlockingStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

structureBlockingLeaf closedShellLeaf : ClassifierStructureBlockingStep
structureBlockingLeaf = slot-leaf structureBlockingClassIndex
closedShellLeaf = slot-leaf closedShellNamedFactorClassIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierStructureBlockingStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isStructureIdentity : ClassifierStructureBlockingStep → Bool
isStructureIdentity structure-identity = true
isStructureIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at structure-identity
------------------------------------------------------------------------

structure-left-identity :
  ∀ (a : ClassifierStructureBlockingStep) →
  isStructureIdentity structureIdentity ≡ true
  × isProductConcurrent (productConcurrentOp structureIdentity a) ≡ true
structure-left-identity a = refl , refl

structure-right-identity :
  ∀ (a : ClassifierStructureBlockingStep) →
  isProductConcurrent (productConcurrentOp a structureIdentity) ≡ true
  × isStructureIdentity structureIdentity ≡ true
structure-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-structure :
  (∀ a → isProductConcurrent (productConcurrentOp structureIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a structureIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-structure =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named helium 1s² **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedHelium1s2Product : ClassifierStructureBlockingStep
namedHelium1s2Product =
  productConcurrentOp structureBlockingLeaf closedShellLeaf

named-helium-1s2-product-concurrent :
  isProductConcurrent namedHelium1s2Product ≡ true
  × patternBundleIsConcurrentProduct helium1s2PatternWitness ≡ true
named-helium-1s2-product-concurrent = refl , helium-1s2-concurrent-product

------------------------------------------------------------------------
-- Structure-blocking admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data StructureBlockingAdmissibility : Set where
  structure-blocking-admissible structure-xor-refuse : StructureBlockingAdmissibility

isStructurePreserving : ClassifierStructureBlockingStep → Bool
isStructurePreserving structure-identity = true
isStructurePreserving (slot-leaf _) = true
isStructurePreserving (product-concurrent a b) =
  isStructurePreserving a ∧ isStructurePreserving b
isStructurePreserving (xor-mutually-exclusive _ _) = false

isStructureBlockingAdmissible : ClassifierStructureBlockingStep → Bool
isStructureBlockingAdmissible step = isStructurePreserving step

structure-blocking-leaf-admissible : isStructureBlockingAdmissible structureBlockingLeaf ≡ true
structure-blocking-leaf-admissible = refl

closed-shell-leaf-admissible : isStructureBlockingAdmissible closedShellLeaf ≡ true
closed-shell-leaf-admissible = refl

named-helium-1s2-admissible : isStructureBlockingAdmissible namedHelium1s2Product ≡ true
named-helium-1s2-admissible = refl

xor-mutually-exclusive-refuse :
  isStructureBlockingAdmissible (xorMutuallyExclusiveOp structureBlockingLeaf closedShellLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

------------------------------------------------------------------------
-- Classifier witness — total-claim refuse without witness
------------------------------------------------------------------------

data StructureWitnessPresence : Set where
  structure-witness-absent structure-witness-present : StructureWitnessPresence

record ClassifierStructureWitness : Set where
  constructor mkClassifierStructureWitness
  field
    witness-presence : StructureWitnessPresence
    structure-gap-total : ℕ

structureWitnessAbsent : ClassifierStructureWitness
structureWitnessAbsent = mkClassifierStructureWitness structure-witness-absent zero

structureWitnessPresentZeroGap : ClassifierStructureWitness
structureWitnessPresentZeroGap = mkClassifierStructureWitness structure-witness-present zero

structureWitnessGapFree : ClassifierStructureWitness → Bool
structureWitnessGapFree (mkClassifierStructureWitness structure-witness-absent _) = false
structureWitnessGapFree (mkClassifierStructureWitness structure-witness-present n) =
  does (n ℕ-Props.≟ zero)

structure-witness-present-zero-gap-free :
  structureWitnessGapFree structureWitnessPresentZeroGap ≡ true
structure-witness-present-zero-gap-free = refl

structure-witness-absent-not-gap-free :
  structureWitnessGapFree structureWitnessAbsent ≡ false
structure-witness-absent-not-gap-free = refl

------------------------------------------------------------------------
-- Classifier-CLASS-05 **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data StructureBlockingInertnessConservationVerdict : Set where
  verdict-unwired-ok verdict-structure-blocking-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : StructureBlockingInertnessConservationVerdict

structureBlockingInertnessConservationVerdictOk : StructureBlockingInertnessConservationVerdict → Bool
structureBlockingInertnessConservationVerdictOk verdict-unwired-ok = true
structureBlockingInertnessConservationVerdictOk verdict-structure-blocking-admissible-ok = true
structureBlockingInertnessConservationVerdictOk verdict-concurrent-product-ok = true
structureBlockingInertnessConservationVerdictOk _ = false

evaluateStructureBlockingInertnessConservationClose :
  StructureBlockingInertnessConservationModality → ClassifierStructureBlockingStep → ClassifierStructureWitness
  → PatternBundleWitness → Bool → StructureBlockingInertnessConservationVerdict
evaluateStructureBlockingInertnessConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-proved _ (mkClassifierStructureWitness structure-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-proved _ (mkClassifierStructureWitness structure-witness-present _) w false
  with patternBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-structure-blocking-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without structure witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-unwired namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-assumed namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-surrogate namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  structureBlockingInertnessConservationVerdictOk
    (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-unwired namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false)
    ≡ true
  × structureBlockingInertnessConservationVerdictOk
      (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-assumed namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false)
      ≡ true
  × structureBlockingInertnessConservationVerdictOk
      (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-surrogate namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without structure witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  structureBlockingInertnessConservationVerdictOk
    (evaluateStructureBlockingInertnessConservationClose
       structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false ≡
  verdict-structure-blocking-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-proved
    (xorMutuallyExclusiveOp structureBlockingLeaf closedShellLeaf)
    structureWitnessPresentZeroGap helium1s2PatternWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  structureBlockingInertnessConservationVerdictOk
    (evaluateStructureBlockingInertnessConservationClose
       structure-blocking-inertness-conservation-proved
       (xorMutuallyExclusiveOp structureBlockingLeaf closedShellLeaf)
       structureWitnessPresentZeroGap helium1s2PatternWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

------------------------------------------------------------------------
-- Admissible classifier — helium 1s² **product** closed
------------------------------------------------------------------------

structure-blocking-admissible-ok :
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessPresentZeroGap unwiredWitness false ≡
  verdict-structure-blocking-admissible-ok
structure-blocking-admissible-ok = refl

structure-blocking-admissible-verdict-ok :
  structureBlockingInertnessConservationVerdictOk
    (evaluateStructureBlockingInertnessConservationClose
       structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessPresentZeroGap unwiredWitness false)
    ≡ true
structure-blocking-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — helium witness with structure-blocking present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessPresentZeroGap helium1s2PatternWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  structureBlockingInertnessConservationVerdictOk
    (evaluateStructureBlockingInertnessConservationClose
       structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessPresentZeroGap helium1s2PatternWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-structure-blocking-proved :
  structureBlockingInertnessConservationVerdictOk
    (evaluateStructureBlockingInertnessConservationClose
       structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessPresentZeroGap helium1s2PatternWitness false)
    ≡ true
  × structureBlockingInertnessProved ≡ false
concurrent-product-ok-still-not-structure-blocking-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateStructureBlockingInertnessConservationClose
    structure-blocking-inertness-conservation-unwired namedHelium1s2Product structureWitnessPresentZeroGap helium1s2PatternWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  structureBlockingInertnessConservationVerdictOk
    (evaluateStructureBlockingInertnessConservationClose
       structure-blocking-inertness-conservation-unwired namedHelium1s2Product structureWitnessPresentZeroGap helium1s2PatternWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

structureBlockingInertnessConservationFiberOk : FormalFiber → Bool
structureBlockingInertnessConservationFiberOk fiber-quantum-knowing = true
structureBlockingInertnessConservationFiberOk fiber-meso-acting = false

structure-blocking-inertness-conservation-knowing-fiber-ok :
  structureBlockingInertnessConservationFiberOk fiber-quantum-knowing ≡ true
structure-blocking-inertness-conservation-knowing-fiber-ok = refl

structure-blocking-inertness-conservation-meso-acting-not-ok :
  structureBlockingInertnessConservationFiberOk fiber-meso-acting ≡ false
structure-blocking-inertness-conservation-meso-acting-not-ok = refl

structure-blocking-inertness-conservation-routes-knowing-not-meso :
  structureBlockingInertnessConservationFiberOk fiber-quantum-knowing ≡ true ×
  structureBlockingInertnessConservationFiberOk fiber-meso-acting ≡ false
structure-blocking-inertness-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  structureBlockingInertnessConservationFiberOk fiber-quantum-knowing ∧
  not (structureBlockingInertnessConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class-5 Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

structure-blocking-inertness-not-proved : structureBlockingInertnessProved ≡ false
structure-blocking-inertness-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

structure-blocking-second-law-conservation-framed :
  structureBlockingSecondLawConservationFramed ≡ true
structure-blocking-second-law-conservation-framed = refl

product-not-xor-pin : productNotXor ≡ true
product-not-xor-pin = product-not-xor

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second class-5 axiom fork)
------------------------------------------------------------------------

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-is-one : soleAxiomCount ≡ 1
sole-axiom-count-is-one = refl

structureBlockingInertnessConservationAxiom :
  (structureBlockingInertnessProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (structureBlockingSecondLawConservationFramed ≡ true)
  × (productNotXor ≡ true)
  × (heNoOreMissingInteract ≡ true)
  × (missingInteractNotNobilityMagic ≡ true)
  × (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-unwired namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false ≡ verdict-unwired-ok)
  × (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessAbsent helium1s2PatternWitness false ≡ verdict-total-claim-refuse)
  × (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-proved (xorMutuallyExclusiveOp structureBlockingLeaf closedShellLeaf) structureWitnessPresentZeroGap helium1s2PatternWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessPresentZeroGap unwiredWitness false ≡ verdict-structure-blocking-admissible-ok)
  × (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-proved namedHelium1s2Product structureWitnessPresentZeroGap helium1s2PatternWitness false ≡ verdict-concurrent-product-ok)
  × (structureBlockingInertnessConservationFiberOk fiber-quantum-knowing ≡ true)
  × (structureBlockingInertnessConservationFiberOk fiber-meso-acting ≡ false)
  × (structureBlockingInertnessConservationVerdictOk (evaluateStructureBlockingInertnessConservationClose structure-blocking-inertness-conservation-unwired namedHelium1s2Product structureWitnessPresentZeroGap helium1s2PatternWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp structureIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a structureIdentity) ≡ true)
  × (isStructureBlockingAdmissible (xorMutuallyExclusiveOp structureBlockingLeaf closedShellLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (structureBlockingClassIndex ≡ 5)
  × (elementAtomicZ helium ≡ 2)
  × (structure-blocking-kind ≢ bond-forming-folklore-kind)
  × (soleAxiomCount ≡ 1)
structureBlockingInertnessConservationAxiom =
  structure-blocking-inertness-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , structure-blocking-second-law-conservation-framed
  , product-not-xor-pin
  , he-no-ore-not-nobility-magic . proj₁
  , he-no-ore-not-nobility-magic . proj₂
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , structure-blocking-admissible-ok
  , concurrent-product-ok
  , structure-blocking-inertness-conservation-knowing-fiber-ok
  , structure-blocking-inertness-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , structure-blocking-class-index-five
  , helium-z-2
  , structure-blocking-distinct-from-folklore
  , sole-axiom-count-is-one

structureBlockingInertnessConservationNamed : String
structureBlockingInertnessConservationNamed =
  "structureBlockingInertnessConservation: class 5 structure-blocking inertness conservation concurrent Pi_c identity conserved He 1s2 missing Interact not nobility magic XOR refuse"

structureBlockingInertnessConservationCrossWitnessAuthority : String
structureBlockingInertnessConservationCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/structure_blocking_inertness_conservation.rs"

structureBlockingInertnessConservationL0TableAuthority : String
structureBlockingInertnessConservationL0TableAuthority =
  "umst/umst-chem/src/l0_tables/structure_blocking_inertness.rs"

chemIntCrossStructureBlockingInertnessConservationAuthority : String
chemIntCrossStructureBlockingInertnessConservationAuthority =
  "CHEM-INT-CROSS-STRUCTURE-BLOCKING-INERTNESS-CONSERVATION"

structureBlockingInertnessConservationCellId : String
structureBlockingInertnessConservationCellId =
  "CHEM-FORMAL-Q-AGDA-STRUCTURE-BLOCKING-INERTNESS-CONSERVATION"

structureBlockingInertnessConservationNonClaim : String
structureBlockingInertnessConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-STRUCTURE-BLOCKING-INERTNESS-CONSERVATION class 5 structure-blocking inertness conservation concurrent Pi_c identity conserved He 1s2 structure_blocking closed_shell product not XOR He no-ore missing Interact class 5 not atmophile nobility GREEN InteractKind StructureBlocking not bond-forming folklore structureBlockingInertnessProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second class-5 axiom not physics GREEN not production_wired"

structure-blocking-inertness-conservation-cell-id :
  structureBlockingInertnessConservationCellId ≡
  "CHEM-FORMAL-Q-AGDA-STRUCTURE-BLOCKING-INERTNESS-CONSERVATION"
structure-blocking-inertness-conservation-cell-id = refl

structure-blocking-inertness-conservation-cites-cross-witness-rs :
  structureBlockingInertnessConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/structure_blocking_inertness_conservation.rs"
structure-blocking-inertness-conservation-cites-cross-witness-rs = refl

structure-blocking-inertness-conservation-cites-l0-table-rs :
  structureBlockingInertnessConservationL0TableAuthority ≡
  "umst/umst-chem/src/l0_tables/structure_blocking_inertness.rs"
structure-blocking-inertness-conservation-cites-l0-table-rs = refl

structure-blocking-inertness-conservation-modality-unwired :
  structureBlockingInertnessConservationModalityCurrent ≡ structure-blocking-inertness-conservation-unwired
structure-blocking-inertness-conservation-modality-unwired = refl

structureBlockingInertnessConservationPhysicsGreenAuthorized : Set
structureBlockingInertnessConservationPhysicsGreenAuthorized = ⊥

structure-blocking-inertness-conservation-physics-green-false :
  ¬ structureBlockingInertnessConservationPhysicsGreenAuthorized
structure-blocking-inertness-conservation-physics-green-false ()

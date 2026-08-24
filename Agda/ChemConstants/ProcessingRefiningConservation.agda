-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ProcessingRefiningConservation.agda
--
-- Pattern class 9 **processing_refining** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (dissipative Refine Kleisli + second-law Gmin + class 9 processing_refining;
--     **product** not XOR, no parallel processing_refining axiom)
--   * XOR mutually-exclusive refuse; processing-refining nuance witness concurrent
--     (dissipative refine + second-law Gmin + class 9 processing_refining)
--   * **processing_refining** laws Unwired (processingRefining09Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/refine_process.rs
-- L0 table: umst/umst-chem/src/l0_tables/processing_refining.rs
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel processing_refining axiom; not extra element id. Product not XOR.
------------------------------------------------------------------------
module ChemConstants.ProcessingRefiningConservation where


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
-- Modality + pattern class 9 **processing_refining** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ProcessingRefiningConservationModality : Set where
  processing-refining-conservation-unwired processing-refining-conservation-assumed
    processing-refining-conservation-proved processing-refining-conservation-surrogate
    : ProcessingRefiningConservationModality

processingRefiningConservationModalityCurrent : ProcessingRefiningConservationModality
processingRefiningConservationModalityCurrent = processing-refining-conservation-unwired

processingRefining09Proved productionWired not118SquaredGreenTable
  processingRefiningSecondLawConservationFramed processingRefiningNotXor : Bool
processingRefining09Proved = false
productionWired = false
not118SquaredGreenTable = true
processingRefiningSecondLawConservationFramed = true
processingRefiningNotXor = true

refineIsDissipative notParallelProcessingRefiningAxiomMinted extraElementIdNotForked : Bool
refineIsDissipative = true
notParallelProcessingRefiningAxiomMinted = true
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
-- Pattern class 9 Processing-refining index pin
------------------------------------------------------------------------

processingRefiningClassIndex : ℕ
processingRefiningClassIndex = 9

processing-refining-class-index-nine : processingRefiningClassIndex ≡ 9
processing-refining-class-index-nine = refl

------------------------------------------------------------------------
-- Named element Z pins — Fe (Z=26), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  iron oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ iron = 26
elementAtomicZ oganesson = 118

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- ProcessingRefiningBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data ProcessingRefiningBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : ProcessingRefiningBundleSlot

isSlotPresent : ProcessingRefiningBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- ProcessingRefiningBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record ProcessingRefiningBundle : Set where
  field slot : ℕ → ProcessingRefiningBundleSlot

processingRefiningBundleUnwired : ProcessingRefiningBundle
processingRefiningBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : ProcessingRefiningBundle → ℕ → ProcessingRefiningBundleSlot → ProcessingRefiningBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else ProcessingRefiningBundle.slot b j }

withPresent : ProcessingRefiningBundle → ℕ → ProcessingRefiningBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record ProcessingRefiningBundleWitness : Set where
  constructor mkProcessingRefiningBundleWitness
  field
    bundle : ProcessingRefiningBundle
    present-count : ℕ

processingRefiningBundleIsConcurrentProduct : ProcessingRefiningBundleWitness → Bool
processingRefiningBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? ProcessingRefiningBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named processing-refining channel indices — dissipative refine (1), second-law Gmin (2), class 9 processing_refining (3)
------------------------------------------------------------------------

dissipativeRefineChannelIndex secondLawGminChannelIndex class9ProcessingRefiningChannelIndex : ℕ
dissipativeRefineChannelIndex = 1
secondLawGminChannelIndex = 2
class9ProcessingRefiningChannelIndex = 3

dissipative-refine-index-one : dissipativeRefineChannelIndex ≡ 1
dissipative-refine-index-one = refl

second-law-gmin-index-two : secondLawGminChannelIndex ≡ 2
second-law-gmin-index-two = refl

class9-processing-refining-index-three : class9ProcessingRefiningChannelIndex ≡ 3
class9-processing-refining-index-three = refl

------------------------------------------------------------------------
-- Assemblage-stability-why nuance witness — dissipative refine + second-law Gmin + class 9 processing_refining concurrent
------------------------------------------------------------------------

processingRefiningNuanceBundle : ProcessingRefiningBundle
processingRefiningNuanceBundle =
  withPresent
    (withPresent
      (withPresent processingRefiningBundleUnwired dissipativeRefineChannelIndex)
      secondLawGminChannelIndex)
    class9ProcessingRefiningChannelIndex

processingRefiningNuanceWitness : ProcessingRefiningBundleWitness
processingRefiningNuanceWitness =
  mkProcessingRefiningBundleWitness processingRefiningNuanceBundle 3

processing-refining-nuance-dissipative-refine-present :
  isSlotPresent (ProcessingRefiningBundle.slot processingRefiningNuanceBundle dissipativeRefineChannelIndex) ≡ true
processing-refining-nuance-dissipative-refine-present = refl

processing-refining-nuance-second-law-gmin-present :
  isSlotPresent (ProcessingRefiningBundle.slot processingRefiningNuanceBundle secondLawGminChannelIndex) ≡ true
processing-refining-nuance-second-law-gmin-present = refl

processing-refining-nuance-class9-processing-refining-present :
  isSlotPresent (ProcessingRefiningBundle.slot processingRefiningNuanceBundle class9ProcessingRefiningChannelIndex) ≡ true
processing-refining-nuance-class9-processing-refining-present = refl

processing-refining-nuance-present-count : ProcessingRefiningBundleWitness.present-count processingRefiningNuanceWitness ≡ 3
processing-refining-nuance-present-count = refl

processing-refining-nuance-concurrent-product :
  processingRefiningBundleIsConcurrentProduct processingRefiningNuanceWitness ≡ true
processing-refining-nuance-concurrent-product = refl

processing-refining-nuance-three-factors-concurrent :
  isSlotPresent (ProcessingRefiningBundle.slot processingRefiningNuanceBundle dissipativeRefineChannelIndex) ≡ true
  × isSlotPresent (ProcessingRefiningBundle.slot processingRefiningNuanceBundle secondLawGminChannelIndex) ≡ true
  × isSlotPresent (ProcessingRefiningBundle.slot processingRefiningNuanceBundle class9ProcessingRefiningChannelIndex) ≡ true
  × ProcessingRefiningBundleWitness.present-count processingRefiningNuanceWitness ≡ 3
processing-refining-nuance-three-factors-concurrent =
  processing-refining-nuance-dissipative-refine-present
  , processing-refining-nuance-second-law-gmin-present
  , processing-refining-nuance-class9-processing-refining-present
  , processing-refining-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : ProcessingRefiningBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if processingRefiningBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = ProcessingRefiningBundleWitness.bundle w
       in if isSlotPresent (ProcessingRefiningBundle.slot b i)
          then if isSlotPresent (ProcessingRefiningBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : ProcessingRefiningBundleWitness
unwiredWitness = mkProcessingRefiningBundleWitness processingRefiningBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

processing-refining-nuance-xor-product-ok :
  evaluateXorRefuse processingRefiningNuanceWitness dissipativeRefineChannelIndex secondLawGminChannelIndex ≡ xor-product-ok
processing-refining-nuance-xor-product-ok = refl

processing-refining-not-xor : processingRefiningNotXor ≡ true
processing-refining-not-xor = refl

------------------------------------------------------------------------
-- ClassifierProcessingRefiningStep scaffold — ProcessingRefiningBundle **conservation**
------------------------------------------------------------------------

data ClassifierProcessingRefiningStep : Set where
  processing-refining-identity : ClassifierProcessingRefiningStep
  slot-leaf : ℕ → ClassifierProcessingRefiningStep
  product-concurrent : ClassifierProcessingRefiningStep → ClassifierProcessingRefiningStep → ClassifierProcessingRefiningStep
  xor-mutually-exclusive : ClassifierProcessingRefiningStep → ClassifierProcessingRefiningStep → ClassifierProcessingRefiningStep

processingRefiningIdentity : ClassifierProcessingRefiningStep
processingRefiningIdentity = processing-refining-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierProcessingRefiningStep → ClassifierProcessingRefiningStep → ClassifierProcessingRefiningStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

dissipativeRefineLeaf secondLawGminLeaf class9ProcessingRefiningLeaf : ClassifierProcessingRefiningStep
dissipativeRefineLeaf = slot-leaf dissipativeRefineChannelIndex
secondLawGminLeaf = slot-leaf secondLawGminChannelIndex
class9ProcessingRefiningLeaf = slot-leaf class9ProcessingRefiningChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierProcessingRefiningStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isProcessingRefiningIdentity : ClassifierProcessingRefiningStep → Bool
isProcessingRefiningIdentity processing-refining-identity = true
isProcessingRefiningIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at processing-refining-identity
------------------------------------------------------------------------

processing-refining-left-identity :
  ∀ (a : ClassifierProcessingRefiningStep) →
  isProcessingRefiningIdentity processingRefiningIdentity ≡ true
  × isProductConcurrent (productConcurrentOp processingRefiningIdentity a) ≡ true
processing-refining-left-identity a = refl , refl

processing-refining-right-identity :
  ∀ (a : ClassifierProcessingRefiningStep) →
  isProductConcurrent (productConcurrentOp a processingRefiningIdentity) ≡ true
  × isProcessingRefiningIdentity processingRefiningIdentity ≡ true
processing-refining-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-processing-refining :
  (∀ a → isProductConcurrent (productConcurrentOp processingRefiningIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a processingRefiningIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-processing-refining =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named processing-refining nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedProcessingRefiningNuanceProduct : ClassifierProcessingRefiningStep
namedProcessingRefiningNuanceProduct =
  productConcurrentOp
    (productConcurrentOp dissipativeRefineLeaf secondLawGminLeaf)
    class9ProcessingRefiningLeaf

named-processing-refining-nuance-product-concurrent :
  isProductConcurrent namedProcessingRefiningNuanceProduct ≡ true
  × processingRefiningBundleIsConcurrentProduct processingRefiningNuanceWitness ≡ true
named-processing-refining-nuance-product-concurrent = refl , processing-refining-nuance-concurrent-product

------------------------------------------------------------------------
-- ProcessingRefiningBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data ProcessingRefiningAdmissibility : Set where
  processing-refining-admissible processing-refining-xor-refuse : ProcessingRefiningAdmissibility

isProcessingRefiningPreserving : ClassifierProcessingRefiningStep → Bool
isProcessingRefiningPreserving processing-refining-identity = true
isProcessingRefiningPreserving (slot-leaf _) = true
isProcessingRefiningPreserving (product-concurrent a b) =
  isProcessingRefiningPreserving a ∧ isProcessingRefiningPreserving b
isProcessingRefiningPreserving (xor-mutually-exclusive _ _) = false

isProcessingRefiningAdmissible : ClassifierProcessingRefiningStep → Bool
isProcessingRefiningAdmissible step = isProcessingRefiningPreserving step

dissipative-refine-leaf-admissible : isProcessingRefiningAdmissible dissipativeRefineLeaf ≡ true
dissipative-refine-leaf-admissible = refl

second-law-gmin-leaf-admissible : isProcessingRefiningAdmissible secondLawGminLeaf ≡ true
second-law-gmin-leaf-admissible = refl

class9-processing-refining-leaf-admissible : isProcessingRefiningAdmissible class9ProcessingRefiningLeaf ≡ true
class9-processing-refining-leaf-admissible = refl

named-processing-refining-nuance-admissible : isProcessingRefiningAdmissible namedProcessingRefiningNuanceProduct ≡ true
named-processing-refining-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isProcessingRefiningAdmissible (xorMutuallyExclusiveOp dissipativeRefineLeaf secondLawGminLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class9-processing-refining-refuse :
  isProcessingRefiningAdmissible (xorMutuallyExclusiveOp secondLawGminLeaf class9ProcessingRefiningLeaf) ≡ false
xor-mutually-exclusive-class9-processing-refining-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data ProcessingRefiningWitnessPresence : Set where
  processing-refining-witness-absent processing-refining-witness-present : ProcessingRefiningWitnessPresence

record ClassifierProcessingRefiningWitness : Set where
  constructor mkClassifierProcessingRefiningWitness
  field
    witness-presence : ProcessingRefiningWitnessPresence
    processing-refining-gap-total : ℕ

processingRefiningWitnessAbsent : ClassifierProcessingRefiningWitness
processingRefiningWitnessAbsent = mkClassifierProcessingRefiningWitness processing-refining-witness-absent zero

processingRefiningWitnessPresentZeroGap : ClassifierProcessingRefiningWitness
processingRefiningWitnessPresentZeroGap = mkClassifierProcessingRefiningWitness processing-refining-witness-present zero

processingRefiningWitnessPresentWithGaps : ℕ → ClassifierProcessingRefiningWitness
processingRefiningWitnessPresentWithGaps n = mkClassifierProcessingRefiningWitness processing-refining-witness-present n

processingRefiningWitnessGapFree : ClassifierProcessingRefiningWitness → Bool
processingRefiningWitnessGapFree (mkClassifierProcessingRefiningWitness processing-refining-witness-absent _) = false
processingRefiningWitnessGapFree (mkClassifierProcessingRefiningWitness processing-refining-witness-present n) =
  does (n ℕ-Props.≟ zero)

processing-refining-witness-present-zero-gap-free :
  processingRefiningWitnessGapFree processingRefiningWitnessPresentZeroGap ≡ true
processing-refining-witness-present-zero-gap-free = refl

processing-refining-witness-absent-not-gap-free :
  processingRefiningWitnessGapFree processingRefiningWitnessAbsent ≡ false
processing-refining-witness-absent-not-gap-free = refl

processing-refining-witness-with-gaps-not-gap-free :
  ∀ n → processingRefiningWitnessGapFree (processingRefiningWitnessPresentWithGaps (suc n)) ≡ false
processing-refining-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Processing-refining **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data ProcessingRefiningConservationVerdict : Set where
  verdict-unwired-ok verdict-processing-refining-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : ProcessingRefiningConservationVerdict

processingRefiningConservationVerdictOk : ProcessingRefiningConservationVerdict → Bool
processingRefiningConservationVerdictOk verdict-unwired-ok = true
processingRefiningConservationVerdictOk verdict-processing-refining-admissible-ok = true
processingRefiningConservationVerdictOk verdict-concurrent-product-ok = true
processingRefiningConservationVerdictOk _ = false

evaluateProcessingRefiningConservationClose :
  ProcessingRefiningConservationModality → ClassifierProcessingRefiningStep → ClassifierProcessingRefiningWitness
  → ProcessingRefiningBundleWitness → Bool → ProcessingRefiningConservationVerdict
evaluateProcessingRefiningConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateProcessingRefiningConservationClose processing-refining-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateProcessingRefiningConservationClose processing-refining-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateProcessingRefiningConservationClose processing-refining-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateProcessingRefiningConservationClose processing-refining-conservation-proved _ (mkClassifierProcessingRefiningWitness processing-refining-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateProcessingRefiningConservationClose processing-refining-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateProcessingRefiningConservationClose processing-refining-conservation-proved _ (mkClassifierProcessingRefiningWitness processing-refining-witness-present _) w false
  with processingRefiningBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-processing-refining-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without processing-refining witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-unwired namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-assumed namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-surrogate namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  processingRefiningConservationVerdictOk
    (evaluateProcessingRefiningConservationClose processing-refining-conservation-unwired namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false)
    ≡ true
  × processingRefiningConservationVerdictOk
      (evaluateProcessingRefiningConservationClose processing-refining-conservation-assumed namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false)
      ≡ true
  × processingRefiningConservationVerdictOk
      (evaluateProcessingRefiningConservationClose processing-refining-conservation-surrogate namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without processing-refining witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  processingRefiningConservationVerdictOk
    (evaluateProcessingRefiningConservationClose
       processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false ≡
  verdict-processing-refining-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-proved
    (xorMutuallyExclusiveOp dissipativeRefineLeaf secondLawGminLeaf)
    processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  processingRefiningConservationVerdictOk
    (evaluateProcessingRefiningConservationClose
       processing-refining-conservation-proved
       (xorMutuallyExclusiveOp dissipativeRefineLeaf secondLawGminLeaf)
       processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-proved
    (xorMutuallyExclusiveOp dissipativeRefineLeaf secondLawGminLeaf)
    processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-processing-refining — nuance **product** closed
------------------------------------------------------------------------

processing-refining-admissible-ok :
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap unwiredWitness false ≡
  verdict-processing-refining-admissible-ok
processing-refining-admissible-ok = refl

processing-refining-admissible-verdict-ok :
  processingRefiningConservationVerdictOk
    (evaluateProcessingRefiningConservationClose
       processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap unwiredWitness false)
    ≡ true
processing-refining-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — processing-refining nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  processingRefiningConservationVerdictOk
    (evaluateProcessingRefiningConservationClose
       processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-processing-refining09-proved :
  processingRefiningConservationVerdictOk
    (evaluateProcessingRefiningConservationClose
       processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness false)
    ≡ true
  × processingRefining09Proved ≡ false
concurrent-product-ok-still-not-processing-refining09-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateProcessingRefiningConservationClose
    processing-refining-conservation-unwired namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  processingRefiningConservationVerdictOk
    (evaluateProcessingRefiningConservationClose
       processing-refining-conservation-unwired namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

processingRefiningConservationFiberOk : FormalFiber → Bool
processingRefiningConservationFiberOk fiber-quantum-knowing = true
processingRefiningConservationFiberOk fiber-meso-acting = false

processing-refining-conservation-knowing-fiber-ok :
  processingRefiningConservationFiberOk fiber-quantum-knowing ≡ true
processing-refining-conservation-knowing-fiber-ok = refl

processing-refining-conservation-meso-acting-not-ok :
  processingRefiningConservationFiberOk fiber-meso-acting ≡ false
processing-refining-conservation-meso-acting-not-ok = refl

processing-refining-conservation-routes-knowing-not-meso :
  processingRefiningConservationFiberOk fiber-quantum-knowing ≡ true ×
  processingRefiningConservationFiberOk fiber-meso-acting ≡ false
processing-refining-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  processingRefiningConservationFiberOk fiber-quantum-knowing ∧
  not (processingRefiningConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 9 processing_refining Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

processing-refining-09-not-proved : processingRefining09Proved ≡ false
processing-refining-09-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

processing-refining-second-law-conservation-framed : processingRefiningSecondLawConservationFramed ≡ true
processing-refining-second-law-conservation-framed = refl

processing-refining-not-xor-pin : processingRefiningNotXor ≡ true
processing-refining-not-xor-pin = processing-refining-not-xor

refine-is-dissipative-pin : refineIsDissipative ≡ true
refine-is-dissipative-pin = refl

not-parallel-processing-refining-axiom-minted-pin : notParallelProcessingRefiningAxiomMinted ≡ true
not-parallel-processing-refining-axiom-minted-pin = refl

extra-element-id-not-forked-pin : extraElementIdNotForked ≡ true
extra-element-id-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel processing_refining axiom fork)
------------------------------------------------------------------------

processingRefiningConservationAxiom :
  (processingRefining09Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (processingRefiningSecondLawConservationFramed ≡ true)
  × (processingRefiningNotXor ≡ true)
  × (evaluateProcessingRefiningConservationClose processing-refining-conservation-unwired namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateProcessingRefiningConservationClose processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessAbsent processingRefiningNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateProcessingRefiningConservationClose processing-refining-conservation-proved (xorMutuallyExclusiveOp dissipativeRefineLeaf secondLawGminLeaf) processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateProcessingRefiningConservationClose processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap unwiredWitness false ≡ verdict-processing-refining-admissible-ok)
  × (evaluateProcessingRefiningConservationClose processing-refining-conservation-proved namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (processingRefiningConservationFiberOk fiber-quantum-knowing ≡ true)
  × (processingRefiningConservationFiberOk fiber-meso-acting ≡ false)
  × (processingRefiningConservationVerdictOk (evaluateProcessingRefiningConservationClose processing-refining-conservation-unwired namedProcessingRefiningNuanceProduct processingRefiningWitnessPresentZeroGap processingRefiningNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp processingRefiningIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a processingRefiningIdentity) ≡ true)
  × (isProcessingRefiningAdmissible (xorMutuallyExclusiveOp dissipativeRefineLeaf secondLawGminLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (processingRefiningClassIndex ≡ 9)
  × (ProcessingRefiningBundleWitness.present-count processingRefiningNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
processingRefiningConservationAxiom =
  processing-refining-09-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , processing-refining-second-law-conservation-framed
  , processing-refining-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , processing-refining-admissible-ok
  , concurrent-product-ok
  , processing-refining-conservation-knowing-fiber-ok
  , processing-refining-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , processing-refining-class-index-nine
  , processing-refining-nuance-present-count
  , iron-z-26
  , oganesson-z-118

processingRefiningConservationNamed : String
processingRefiningConservationNamed =
  "processingRefiningConservation: pattern class 9 processing_refining conservation concurrent Pi_c identity conserved dissipative refine Kleisli second law Gmin class 9 processing_refining concurrent product identity conserved present ge 2 product not XOR refine is dissipative no parallel processing_refining axiom not extra element id"

processingRefiningConservationCrossWitnessAuthority : String
processingRefiningConservationCrossWitnessAuthority =
  "umst/umst-chem/src/processing_refining.rs"

processingRefiningTableAuthority : String
processingRefiningTableAuthority =
  "umst/umst-chem/src/l0_tables/processing_refining.rs"

refiningGraphCutsAuthority : String
refiningGraphCutsAuthority =
  "umst/umst-chem/src/refining_graph_cuts.rs"

refineEffectTypesAuthority : String
refineEffectTypesAuthority =
  "umst/umst-chem/src/theorem_import/refine_effect_types.rs"

processingRefiningConservationCellId : String
processingRefiningConservationCellId = "CHEM-FORMAL-Q-AGDA-PROCESSING-REFINING-CONSERVATION"

processingRefiningConservationNonClaim : String
processingRefiningConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-PROCESSING-REFINING-CONSERVATION pattern class 9 processing_refining conservation concurrent Pi_c identity conserved dissipative refine Kleisli second law Gmin class 9 processing_refining product not XOR refine is dissipative no parallel processing_refining axiom not extra element id XOR mutually exclusive refuse processing refining nuance witness concurrent processingRefining09Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite processing_refining.rs l0_tables processing_refining not fork not physics GREEN not production_wired"

processing-refining-conservation-cell-id :
  processingRefiningConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-PROCESSING-REFINING-CONSERVATION"
processing-refining-conservation-cell-id = refl

processing-refining-conservation-cites-processing-refining-rs :
  processingRefiningConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/processing_refining.rs"
processing-refining-conservation-cites-processing-refining-rs = refl

processing-refining-conservation-cites-l0-table-rs :
  processingRefiningTableAuthority ≡
  "umst/umst-chem/src/l0_tables/processing_refining.rs"
processing-refining-conservation-cites-l0-table-rs = refl

processing-refining-conservation-modality-unwired :
  processingRefiningConservationModalityCurrent ≡ processing-refining-conservation-unwired
processing-refining-conservation-modality-unwired = refl

processingRefiningConservationPhysicsGreenAuthorized : Set
processingRefiningConservationPhysicsGreenAuthorized = ⊥

processing-refining-conservation-physics-green-false : ¬ processingRefiningConservationPhysicsGreenAuthorized
processing-refining-conservation-physics-green-false ()

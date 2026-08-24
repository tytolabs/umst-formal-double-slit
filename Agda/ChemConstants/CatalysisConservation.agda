-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.CatalysisConservation.agda
--
-- Pattern class 14 **catalysis** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (Interact restriction + not extra force + class 14 catalysis;
--     **product** not XOR, no parallel catalysis axiom)
--   * XOR mutually-exclusive refuse; catalysis nuance witness concurrent
--     (Interact restriction + not extra force + class 14 catalysis)
--   * **catalysis** laws Unwired (catalysis14Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/catalysis_barrier.rs
-- L0 table: umst/umst-chem/src/l0_tables/catalysis.rs
-- Mirrors sibling `ChemConstants/ProcessingRefiningConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel catalysis axiom; not extra force. Product not XOR.
-- Class 14 catalysis as Interact restriction, not extra force.
------------------------------------------------------------------------
module ChemConstants.CatalysisConservation where


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

data CatalysisConservationModality : Set where
  catalysis-conservation-unwired catalysis-conservation-assumed
    catalysis-conservation-proved catalysis-conservation-surrogate
    : CatalysisConservationModality

catalysisConservationModalityCurrent : CatalysisConservationModality
catalysisConservationModalityCurrent = catalysis-conservation-unwired

catalysis14Proved productionWired not118SquaredGreenTable
  catalysisSecondLawConservationFramed catalysisNotXor : Bool
catalysis14Proved = false
productionWired = false
not118SquaredGreenTable = true
catalysisSecondLawConservationFramed = true
catalysisNotXor = true

interactRestrictionTyped notParallelCatalysisAxiomMinted extraForceNotForked : Bool
interactRestrictionTyped = true
notParallelCatalysisAxiomMinted = true
extraForceNotForked = true

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

catalysisClassIndex : ℕ
catalysisClassIndex = 14

catalysis-class-index-fourteen : catalysisClassIndex ≡ 14
catalysis-class-index-fourteen = refl

------------------------------------------------------------------------
-- Named element Z pins — Pt (Z=78), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  platinum oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ platinum = 78
elementAtomicZ oganesson = 118

platinum-z-78 : elementAtomicZ platinum ≡ 78
platinum-z-78 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- CatalysisBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data CatalysisBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : CatalysisBundleSlot

isSlotPresent : CatalysisBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- CatalysisBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record CatalysisBundle : Set where
  field slot : ℕ → CatalysisBundleSlot

catalysisBundleUnwired : CatalysisBundle
catalysisBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : CatalysisBundle → ℕ → CatalysisBundleSlot → CatalysisBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else CatalysisBundle.slot b j }

withPresent : CatalysisBundle → ℕ → CatalysisBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record CatalysisBundleWitness : Set where
  constructor mkCatalysisBundleWitness
  field
    bundle : CatalysisBundle
    present-count : ℕ

catalysisBundleIsConcurrentProduct : CatalysisBundleWitness → Bool
catalysisBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? CatalysisBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named catalysis channel indices — interact restriction (1), not extra force (2), class 14 catalysis (3)
------------------------------------------------------------------------

interactRestrictionChannelIndex notExtraForceChannelIndex class14CatalysisChannelIndex : ℕ
interactRestrictionChannelIndex = 1
notExtraForceChannelIndex = 2
class14CatalysisChannelIndex = 3

interact-restriction-index-one : interactRestrictionChannelIndex ≡ 1
interact-restriction-index-one = refl

not-extra-force-index-two : notExtraForceChannelIndex ≡ 2
not-extra-force-index-two = refl

class14-catalysis-index-three : class14CatalysisChannelIndex ≡ 3
class14-catalysis-index-three = refl

------------------------------------------------------------------------
-- Catalysis nuance witness — interact restriction + not extra force + class 14 catalysis concurrent
------------------------------------------------------------------------

catalysisNuanceBundle : CatalysisBundle
catalysisNuanceBundle =
  withPresent
    (withPresent
      (withPresent catalysisBundleUnwired interactRestrictionChannelIndex)
      notExtraForceChannelIndex)
    class14CatalysisChannelIndex

catalysisNuanceWitness : CatalysisBundleWitness
catalysisNuanceWitness =
  mkCatalysisBundleWitness catalysisNuanceBundle 3

catalysis-nuance-interact-restriction-present :
  isSlotPresent (CatalysisBundle.slot catalysisNuanceBundle interactRestrictionChannelIndex) ≡ true
catalysis-nuance-interact-restriction-present = refl

catalysis-nuance-not-extra-force-present :
  isSlotPresent (CatalysisBundle.slot catalysisNuanceBundle notExtraForceChannelIndex) ≡ true
catalysis-nuance-not-extra-force-present = refl

catalysis-nuance-class14-catalysis-present :
  isSlotPresent (CatalysisBundle.slot catalysisNuanceBundle class14CatalysisChannelIndex) ≡ true
catalysis-nuance-class14-catalysis-present = refl

catalysis-nuance-present-count : CatalysisBundleWitness.present-count catalysisNuanceWitness ≡ 3
catalysis-nuance-present-count = refl

catalysis-nuance-concurrent-product :
  catalysisBundleIsConcurrentProduct catalysisNuanceWitness ≡ true
catalysis-nuance-concurrent-product = refl

catalysis-nuance-three-factors-concurrent :
  isSlotPresent (CatalysisBundle.slot catalysisNuanceBundle interactRestrictionChannelIndex) ≡ true
  × isSlotPresent (CatalysisBundle.slot catalysisNuanceBundle notExtraForceChannelIndex) ≡ true
  × isSlotPresent (CatalysisBundle.slot catalysisNuanceBundle class14CatalysisChannelIndex) ≡ true
  × CatalysisBundleWitness.present-count catalysisNuanceWitness ≡ 3
catalysis-nuance-three-factors-concurrent =
  catalysis-nuance-interact-restriction-present
  , catalysis-nuance-not-extra-force-present
  , catalysis-nuance-class14-catalysis-present
  , catalysis-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : CatalysisBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if catalysisBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = CatalysisBundleWitness.bundle w
       in if isSlotPresent (CatalysisBundle.slot b i)
          then if isSlotPresent (CatalysisBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : CatalysisBundleWitness
unwiredWitness = mkCatalysisBundleWitness catalysisBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

catalysis-nuance-xor-product-ok :
  evaluateXorRefuse catalysisNuanceWitness interactRestrictionChannelIndex notExtraForceChannelIndex ≡ xor-product-ok
catalysis-nuance-xor-product-ok = refl

catalysis-not-xor : catalysisNotXor ≡ true
catalysis-not-xor = refl

------------------------------------------------------------------------
-- ClassifierCatalysisStep scaffold — CatalysisBundle **conservation**
------------------------------------------------------------------------

data ClassifierCatalysisStep : Set where
  catalysis-identity : ClassifierCatalysisStep
  slot-leaf : ℕ → ClassifierCatalysisStep
  product-concurrent : ClassifierCatalysisStep → ClassifierCatalysisStep → ClassifierCatalysisStep
  xor-mutually-exclusive : ClassifierCatalysisStep → ClassifierCatalysisStep → ClassifierCatalysisStep

catalysisIdentity : ClassifierCatalysisStep
catalysisIdentity = catalysis-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierCatalysisStep → ClassifierCatalysisStep → ClassifierCatalysisStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

interactRestrictionLeaf notExtraForceLeaf class14CatalysisLeaf : ClassifierCatalysisStep
interactRestrictionLeaf = slot-leaf interactRestrictionChannelIndex
notExtraForceLeaf = slot-leaf notExtraForceChannelIndex
class14CatalysisLeaf = slot-leaf class14CatalysisChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierCatalysisStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isCatalysisIdentity : ClassifierCatalysisStep → Bool
isCatalysisIdentity catalysis-identity = true
isCatalysisIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at catalysis-identity
------------------------------------------------------------------------

catalysis-left-identity :
  ∀ (a : ClassifierCatalysisStep) →
  isCatalysisIdentity catalysisIdentity ≡ true
  × isProductConcurrent (productConcurrentOp catalysisIdentity a) ≡ true
catalysis-left-identity a = refl , refl

catalysis-right-identity :
  ∀ (a : ClassifierCatalysisStep) →
  isProductConcurrent (productConcurrentOp a catalysisIdentity) ≡ true
  × isCatalysisIdentity catalysisIdentity ≡ true
catalysis-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-catalysis :
  (∀ a → isProductConcurrent (productConcurrentOp catalysisIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a catalysisIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-catalysis =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named catalysis nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedCatalysisNuanceProduct : ClassifierCatalysisStep
namedCatalysisNuanceProduct =
  productConcurrentOp
    (productConcurrentOp interactRestrictionLeaf notExtraForceLeaf)
    class14CatalysisLeaf

named-catalysis-nuance-product-concurrent :
  isProductConcurrent namedCatalysisNuanceProduct ≡ true
  × catalysisBundleIsConcurrentProduct catalysisNuanceWitness ≡ true
named-catalysis-nuance-product-concurrent = refl , catalysis-nuance-concurrent-product

------------------------------------------------------------------------
-- CatalysisBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data CatalysisAdmissibility : Set where
  catalysis-admissible catalysis-xor-refuse : CatalysisAdmissibility

isCatalysisPreserving : ClassifierCatalysisStep → Bool
isCatalysisPreserving catalysis-identity = true
isCatalysisPreserving (slot-leaf _) = true
isCatalysisPreserving (product-concurrent a b) =
  isCatalysisPreserving a ∧ isCatalysisPreserving b
isCatalysisPreserving (xor-mutually-exclusive _ _) = false

isCatalysisAdmissible : ClassifierCatalysisStep → Bool
isCatalysisAdmissible step = isCatalysisPreserving step

interact-restriction-leaf-admissible : isCatalysisAdmissible interactRestrictionLeaf ≡ true
interact-restriction-leaf-admissible = refl

not-extra-force-leaf-admissible : isCatalysisAdmissible notExtraForceLeaf ≡ true
not-extra-force-leaf-admissible = refl

class14-catalysis-leaf-admissible : isCatalysisAdmissible class14CatalysisLeaf ≡ true
class14-catalysis-leaf-admissible = refl

named-catalysis-nuance-admissible : isCatalysisAdmissible namedCatalysisNuanceProduct ≡ true
named-catalysis-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isCatalysisAdmissible (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class14-catalysis-refuse :
  isCatalysisAdmissible (xorMutuallyExclusiveOp notExtraForceLeaf class14CatalysisLeaf) ≡ false
xor-mutually-exclusive-class14-catalysis-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data CatalysisWitnessPresence : Set where
  catalysis-witness-absent catalysis-witness-present : CatalysisWitnessPresence

record ClassifierCatalysisWitness : Set where
  constructor mkClassifierCatalysisWitness
  field
    witness-presence : CatalysisWitnessPresence
    catalysis-gap-total : ℕ

catalysisWitnessAbsent : ClassifierCatalysisWitness
catalysisWitnessAbsent = mkClassifierCatalysisWitness catalysis-witness-absent zero

catalysisWitnessPresentZeroGap : ClassifierCatalysisWitness
catalysisWitnessPresentZeroGap = mkClassifierCatalysisWitness catalysis-witness-present zero

catalysisWitnessPresentWithGaps : ℕ → ClassifierCatalysisWitness
catalysisWitnessPresentWithGaps n = mkClassifierCatalysisWitness catalysis-witness-present n

catalysisWitnessGapFree : ClassifierCatalysisWitness → Bool
catalysisWitnessGapFree (mkClassifierCatalysisWitness catalysis-witness-absent _) = false
catalysisWitnessGapFree (mkClassifierCatalysisWitness catalysis-witness-present n) =
  does (n ℕ-Props.≟ zero)

catalysis-witness-present-zero-gap-free :
  catalysisWitnessGapFree catalysisWitnessPresentZeroGap ≡ true
catalysis-witness-present-zero-gap-free = refl

catalysis-witness-absent-not-gap-free :
  catalysisWitnessGapFree catalysisWitnessAbsent ≡ false
catalysis-witness-absent-not-gap-free = refl

catalysis-witness-with-gaps-not-gap-free :
  ∀ n → catalysisWitnessGapFree (catalysisWitnessPresentWithGaps (suc n)) ≡ false
catalysis-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Catalysis **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data CatalysisConservationVerdict : Set where
  verdict-unwired-ok verdict-catalysis-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : CatalysisConservationVerdict

catalysisConservationVerdictOk : CatalysisConservationVerdict → Bool
catalysisConservationVerdictOk verdict-unwired-ok = true
catalysisConservationVerdictOk verdict-catalysis-admissible-ok = true
catalysisConservationVerdictOk verdict-concurrent-product-ok = true
catalysisConservationVerdictOk _ = false

evaluateCatalysisConservationClose :
  CatalysisConservationModality → ClassifierCatalysisStep → ClassifierCatalysisWitness
  → CatalysisBundleWitness → Bool → CatalysisConservationVerdict
evaluateCatalysisConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateCatalysisConservationClose catalysis-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateCatalysisConservationClose catalysis-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateCatalysisConservationClose catalysis-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateCatalysisConservationClose catalysis-conservation-proved _ (mkClassifierCatalysisWitness catalysis-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateCatalysisConservationClose catalysis-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateCatalysisConservationClose catalysis-conservation-proved _ (mkClassifierCatalysisWitness catalysis-witness-present _) w false
  with catalysisBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-catalysis-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateCatalysisConservationClose
    catalysis-conservation-unwired namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateCatalysisConservationClose
    catalysis-conservation-assumed namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateCatalysisConservationClose
    catalysis-conservation-surrogate namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  catalysisConservationVerdictOk
    (evaluateCatalysisConservationClose catalysis-conservation-unwired namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false)
    ≡ true
  × catalysisConservationVerdictOk
      (evaluateCatalysisConservationClose catalysis-conservation-assumed namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false)
      ≡ true
  × catalysisConservationVerdictOk
      (evaluateCatalysisConservationClose catalysis-conservation-surrogate namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateCatalysisConservationClose
    catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  catalysisConservationVerdictOk
    (evaluateCatalysisConservationClose
       catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateCatalysisConservationClose
    catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false ≡
  verdict-catalysis-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateCatalysisConservationClose
    catalysis-conservation-proved
    (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf)
    catalysisWitnessPresentZeroGap catalysisNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  catalysisConservationVerdictOk
    (evaluateCatalysisConservationClose
       catalysis-conservation-proved
       (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf)
       catalysisWitnessPresentZeroGap catalysisNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateCatalysisConservationClose
    catalysis-conservation-proved
    (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf)
    catalysisWitnessPresentZeroGap catalysisNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

catalysis-admissible-ok :
  evaluateCatalysisConservationClose
    catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap unwiredWitness false ≡
  verdict-catalysis-admissible-ok
catalysis-admissible-ok = refl

catalysis-admissible-verdict-ok :
  catalysisConservationVerdictOk
    (evaluateCatalysisConservationClose
       catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap unwiredWitness false)
    ≡ true
catalysis-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateCatalysisConservationClose
    catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap catalysisNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  catalysisConservationVerdictOk
    (evaluateCatalysisConservationClose
       catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap catalysisNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-catalysis14-proved :
  catalysisConservationVerdictOk
    (evaluateCatalysisConservationClose
       catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap catalysisNuanceWitness false)
    ≡ true
  × catalysis14Proved ≡ false
concurrent-product-ok-still-not-catalysis14-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateCatalysisConservationClose
    catalysis-conservation-unwired namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap catalysisNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  catalysisConservationVerdictOk
    (evaluateCatalysisConservationClose
       catalysis-conservation-unwired namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap catalysisNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

catalysisConservationFiberOk : FormalFiber → Bool
catalysisConservationFiberOk fiber-quantum-knowing = true
catalysisConservationFiberOk fiber-meso-acting = false

catalysis-conservation-knowing-fiber-ok :
  catalysisConservationFiberOk fiber-quantum-knowing ≡ true
catalysis-conservation-knowing-fiber-ok = refl

catalysis-conservation-meso-acting-not-ok :
  catalysisConservationFiberOk fiber-meso-acting ≡ false
catalysis-conservation-meso-acting-not-ok = refl

catalysis-conservation-routes-knowing-not-meso :
  catalysisConservationFiberOk fiber-quantum-knowing ≡ true ×
  catalysisConservationFiberOk fiber-meso-acting ≡ false
catalysis-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  catalysisConservationFiberOk fiber-quantum-knowing ∧
  not (catalysisConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 14 catalysis Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

catalysis-14-not-proved : catalysis14Proved ≡ false
catalysis-14-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

catalysis-second-law-conservation-framed : catalysisSecondLawConservationFramed ≡ true
catalysis-second-law-conservation-framed = refl

catalysis-not-xor-pin : catalysisNotXor ≡ true
catalysis-not-xor-pin = catalysis-not-xor

interact-restriction-typed-pin : interactRestrictionTyped ≡ true
interact-restriction-typed-pin = refl

not-parallel-catalysis-axiom-minted-pin : notParallelCatalysisAxiomMinted ≡ true
not-parallel-catalysis-axiom-minted-pin = refl

extra-force-not-forked-pin : extraForceNotForked ≡ true
extra-force-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel catalysis axiom fork)
------------------------------------------------------------------------

catalysisConservationAxiom :
  (catalysis14Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (catalysisSecondLawConservationFramed ≡ true)
  × (catalysisNotXor ≡ true)
  × (evaluateCatalysisConservationClose catalysis-conservation-unwired namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateCatalysisConservationClose catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessAbsent catalysisNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateCatalysisConservationClose catalysis-conservation-proved (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf) catalysisWitnessPresentZeroGap catalysisNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateCatalysisConservationClose catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap unwiredWitness false ≡ verdict-catalysis-admissible-ok)
  × (evaluateCatalysisConservationClose catalysis-conservation-proved namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap catalysisNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (catalysisConservationFiberOk fiber-quantum-knowing ≡ true)
  × (catalysisConservationFiberOk fiber-meso-acting ≡ false)
  × (catalysisConservationVerdictOk (evaluateCatalysisConservationClose catalysis-conservation-unwired namedCatalysisNuanceProduct catalysisWitnessPresentZeroGap catalysisNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp catalysisIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a catalysisIdentity) ≡ true)
  × (isCatalysisAdmissible (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (catalysisClassIndex ≡ 14)
  × (CatalysisBundleWitness.present-count catalysisNuanceWitness ≡ 3)
  × (elementAtomicZ platinum ≡ 78)
  × (elementAtomicZ oganesson ≡ 118)
catalysisConservationAxiom =
  catalysis-14-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , catalysis-second-law-conservation-framed
  , catalysis-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , catalysis-admissible-ok
  , concurrent-product-ok
  , catalysis-conservation-knowing-fiber-ok
  , catalysis-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , catalysis-class-index-fourteen
  , catalysis-nuance-present-count
  , platinum-z-78
  , oganesson-z-118

catalysisConservationNamed : String
catalysisConservationNamed =
  "catalysisConservation: pattern class 14 catalysis conservation concurrent Pi_c identity conserved Interact restriction not extra force class 14 catalysis concurrent product identity conserved present ge 2 product not XOR interact restriction typed no parallel catalysis axiom not extra force"

catalysisConservationCrossWitnessAuthority : String
catalysisConservationCrossWitnessAuthority =
  "umst/umst-chem/src/catalysis_barrier.rs"

catalysisTableAuthority : String
catalysisTableAuthority =
  "umst/umst-chem/src/l0_tables/catalysis.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

catalysisConservationCellId : String
catalysisConservationCellId = "CHEM-FORMAL-Q-AGDA-CATALYSIS-CONSERVATION"

catalysisConservationNonClaim : String
catalysisConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-CATALYSIS-CONSERVATION pattern class 14 catalysis conservation concurrent Pi_c identity conserved Interact restriction not extra force class 14 catalysis product not XOR interact restriction typed no parallel catalysis axiom not extra force XOR mutually exclusive refuse catalysis nuance witness concurrent catalysis14Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite catalysis_barrier.rs l0_tables catalysis not fork not physics GREEN not production_wired"

catalysis-conservation-cell-id :
  catalysisConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-CATALYSIS-CONSERVATION"
catalysis-conservation-cell-id = refl

catalysis-conservation-cites-catalysis-barrier-rs :
  catalysisConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/catalysis_barrier.rs"
catalysis-conservation-cites-catalysis-barrier-rs = refl

catalysis-conservation-cites-l0-table-rs :
  catalysisTableAuthority ≡
  "umst/umst-chem/src/l0_tables/catalysis.rs"
catalysis-conservation-cites-l0-table-rs = refl

catalysis-conservation-modality-unwired :
  catalysisConservationModalityCurrent ≡ catalysis-conservation-unwired
catalysis-conservation-modality-unwired = refl

catalysisConservationPhysicsGreenAuthorized : Set
catalysisConservationPhysicsGreenAuthorized = ⊥

catalysis-conservation-physics-green-false : ¬ catalysisConservationPhysicsGreenAuthorized
catalysis-conservation-physics-green-false ()

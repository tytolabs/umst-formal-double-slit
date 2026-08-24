-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.AqueousVsMineralConservation.agda
--
-- CHEM-FORMAL-Q-AGDA-AQUEOUS-VS-MINERAL-CONSERVATION
-- CHEM-FORMAL-Q-AGDA-AQUEOUS-VS-MINERAL-CONSERVATION pattern class 16 aqueous_vs_mineral conservation
--
-- Pattern class 16 **aqueous_vs_mineral** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (aqueous messy/pore Env section + mineral contained section +
--     class 16 aqueous_vs_mineral; **product** not XOR, no parallel aqueous axiom)
--   * XOR mutually-exclusive refuse; aqueous-vs-mineral nuance witness concurrent
--     (aqueous messy/pore section + mineral contained section + class 16 aqueous_vs_mineral)
--   * **aqueous_vs_mineral** laws Unwired (aqueousVsMineral16Proved = false; conservationProved = false)
--   * L1 hydrate SpeciesId tags stay L1 — not aliased into L0 ElementId rows
--   * PHREEQC / Pitzer-SIT prior art framed Assumed — not Proved on this cell
--   * T / P are Interact graph functions — not bare 298.15 K / 1 atm float pins
--
-- INT (read-only cite): umst/umst-chem/src/aqueous_mineral_is_environment_restriction.rs
-- L0 table: umst/umst-chem/src/l0_tables/aqueous_vs_mineral.rs
-- L0 edge: umst/umst-chem/src/aqueous_mineral_regime.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel aqueous axiom; Env restriction not XOR chemistries. Product not XOR.
-- Class 16 aqueous_vs_mineral as Env restriction along sample sections, not extra chemistry.
-- WAVE100: no cabal/lakefile/lib.rs wiring.
------------------------------------------------------------------------
module ChemConstants.AqueousVsMineralConservation where

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
-- Modality + pattern class 16 **aqueous_vs_mineral** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data AqueousVsMineralConservationModality : Set where
  aqueous-vs-mineral-conservation-unwired aqueous-vs-mineral-conservation-assumed
    aqueous-vs-mineral-conservation-proved aqueous-vs-mineral-conservation-surrogate
    : AqueousVsMineralConservationModality

aqueousVsMineralConservationModalityCurrent : AqueousVsMineralConservationModality
aqueousVsMineralConservationModalityCurrent = aqueous-vs-mineral-conservation-unwired

aqueousVsMineral16Proved productionWired not118SquaredGreenTable
  aqueousVsMineralSecondLawConservationFramed aqueousVsMineralNotXor
  conservationProved : Bool
aqueousVsMineral16Proved = false
productionWired = false
not118SquaredGreenTable = true
aqueousVsMineralSecondLawConservationFramed = true
aqueousVsMineralNotXor = true
conservationProved = false

envRestrictionTyped notParallelAqueousAxiomMinted l1HydratesStayL1NotElementId
  phreeqcPitzerPriorArtFramed tpGraphFunctionNotFloatPin : Bool
envRestrictionTyped = true
notParallelAqueousAxiomMinted = true
l1HydratesStayL1NotElementId = true
phreeqcPitzerPriorArtFramed = true
tpGraphFunctionNotFloatPin = true

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
-- Pattern class 16 AqueousVsMineral index pin
------------------------------------------------------------------------

aqueousVsMineralClassIndex : ℕ
aqueousVsMineralClassIndex = 16

aqueous-vs-mineral-class-index-sixteen : aqueousVsMineralClassIndex ≡ 16
aqueous-vs-mineral-class-index-sixteen = refl

------------------------------------------------------------------------
-- Named element Z pins — Ca (Z=20), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  calcium oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ calcium = 20
elementAtomicZ oganesson = 118

calcium-z-20 : elementAtomicZ calcium ≡ 20
calcium-z-20 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- AqueousVsMineralBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data AqueousVsMineralBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : AqueousVsMineralBundleSlot

isSlotPresent : AqueousVsMineralBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- AqueousVsMineralBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record AqueousVsMineralBundle : Set where
  field slot : ℕ → AqueousVsMineralBundleSlot

aqueousVsMineralBundleUnwired : AqueousVsMineralBundle
aqueousVsMineralBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : AqueousVsMineralBundle → ℕ → AqueousVsMineralBundleSlot → AqueousVsMineralBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else AqueousVsMineralBundle.slot b j }

withPresent : AqueousVsMineralBundle → ℕ → AqueousVsMineralBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record AqueousVsMineralBundleWitness : Set where
  constructor mkAqueousVsMineralBundleWitness
  field
    bundle : AqueousVsMineralBundle
    present-count : ℕ

aqueousVsMineralBundleIsConcurrentProduct : AqueousVsMineralBundleWitness → Bool
aqueousVsMineralBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? AqueousVsMineralBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named aqueous_vs_mineral channel indices — aqueous messy/pore section (1), mineral contained section (2), class 16 aqueous_vs_mineral (3)
------------------------------------------------------------------------

aqueousMessySectionChannelIndex mineralContainedSectionChannelIndex class16AqueousVsMineralChannelIndex : ℕ
aqueousMessySectionChannelIndex = 1
mineralContainedSectionChannelIndex = 2
class16AqueousVsMineralChannelIndex = 3

aqueous-messy-section-index-one : aqueousMessySectionChannelIndex ≡ 1
aqueous-messy-section-index-one = refl

mineral-contained-section-index-two : mineralContainedSectionChannelIndex ≡ 2
mineral-contained-section-index-two = refl

class16-aqueous-vs-mineral-index-three : class16AqueousVsMineralChannelIndex ≡ 3
class16-aqueous-vs-mineral-index-three = refl

------------------------------------------------------------------------
-- AqueousVsMineral nuance witness — aqueous messy/pore section + mineral contained section + class 16 aqueous_vs_mineral concurrent
------------------------------------------------------------------------

aqueousVsMineralNuanceBundle : AqueousVsMineralBundle
aqueousVsMineralNuanceBundle =
  withPresent
    (withPresent
      (withPresent aqueousVsMineralBundleUnwired aqueousMessySectionChannelIndex)
      mineralContainedSectionChannelIndex)
    class16AqueousVsMineralChannelIndex

aqueousVsMineralNuanceWitness : AqueousVsMineralBundleWitness
aqueousVsMineralNuanceWitness =
  mkAqueousVsMineralBundleWitness aqueousVsMineralNuanceBundle 3

aqueous-vs-mineral-nuance-aqueous-messy-section-present :
  isSlotPresent (AqueousVsMineralBundle.slot aqueousVsMineralNuanceBundle aqueousMessySectionChannelIndex) ≡ true
aqueous-vs-mineral-nuance-aqueous-messy-section-present = refl

aqueous-vs-mineral-nuance-mineral-contained-section-present :
  isSlotPresent (AqueousVsMineralBundle.slot aqueousVsMineralNuanceBundle mineralContainedSectionChannelIndex) ≡ true
aqueous-vs-mineral-nuance-mineral-contained-section-present = refl

aqueous-vs-mineral-nuance-class16-aqueous-vs-mineral-present :
  isSlotPresent (AqueousVsMineralBundle.slot aqueousVsMineralNuanceBundle class16AqueousVsMineralChannelIndex) ≡ true
aqueous-vs-mineral-nuance-class16-aqueous-vs-mineral-present = refl

aqueous-vs-mineral-nuance-present-count : AqueousVsMineralBundleWitness.present-count aqueousVsMineralNuanceWitness ≡ 3
aqueous-vs-mineral-nuance-present-count = refl

aqueous-vs-mineral-nuance-concurrent-product :
  aqueousVsMineralBundleIsConcurrentProduct aqueousVsMineralNuanceWitness ≡ true
aqueous-vs-mineral-nuance-concurrent-product = refl

aqueous-vs-mineral-nuance-three-factors-concurrent :
  isSlotPresent (AqueousVsMineralBundle.slot aqueousVsMineralNuanceBundle aqueousMessySectionChannelIndex) ≡ true
  × isSlotPresent (AqueousVsMineralBundle.slot aqueousVsMineralNuanceBundle mineralContainedSectionChannelIndex) ≡ true
  × isSlotPresent (AqueousVsMineralBundle.slot aqueousVsMineralNuanceBundle class16AqueousVsMineralChannelIndex) ≡ true
  × AqueousVsMineralBundleWitness.present-count aqueousVsMineralNuanceWitness ≡ 3
aqueous-vs-mineral-nuance-three-factors-concurrent =
  aqueous-vs-mineral-nuance-aqueous-messy-section-present
  , aqueous-vs-mineral-nuance-mineral-contained-section-present
  , aqueous-vs-mineral-nuance-class16-aqueous-vs-mineral-present
  , aqueous-vs-mineral-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : AqueousVsMineralBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if aqueousVsMineralBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = AqueousVsMineralBundleWitness.bundle w
       in if isSlotPresent (AqueousVsMineralBundle.slot b i)
          then if isSlotPresent (AqueousVsMineralBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : AqueousVsMineralBundleWitness
unwiredWitness = mkAqueousVsMineralBundleWitness aqueousVsMineralBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

aqueous-vs-mineral-nuance-xor-product-ok :
  evaluateXorRefuse aqueousVsMineralNuanceWitness aqueousMessySectionChannelIndex mineralContainedSectionChannelIndex ≡ xor-product-ok
aqueous-vs-mineral-nuance-xor-product-ok = refl

aqueous-vs-mineral-not-xor : aqueousVsMineralNotXor ≡ true
aqueous-vs-mineral-not-xor = refl

------------------------------------------------------------------------
-- ClassifierAqueousVsMineralStep scaffold — AqueousVsMineralBundle **conservation**
------------------------------------------------------------------------

data ClassifierAqueousVsMineralStep : Set where
  aqueous-vs-mineral-identity : ClassifierAqueousVsMineralStep
  slot-leaf : ℕ → ClassifierAqueousVsMineralStep
  product-concurrent : ClassifierAqueousVsMineralStep → ClassifierAqueousVsMineralStep → ClassifierAqueousVsMineralStep
  xor-mutually-exclusive : ClassifierAqueousVsMineralStep → ClassifierAqueousVsMineralStep → ClassifierAqueousVsMineralStep

aqueousVsMineralIdentity : ClassifierAqueousVsMineralStep
aqueousVsMineralIdentity = aqueous-vs-mineral-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierAqueousVsMineralStep → ClassifierAqueousVsMineralStep → ClassifierAqueousVsMineralStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

aqueousMessySectionLeaf mineralContainedSectionLeaf class16AqueousVsMineralLeaf : ClassifierAqueousVsMineralStep
aqueousMessySectionLeaf = slot-leaf aqueousMessySectionChannelIndex
mineralContainedSectionLeaf = slot-leaf mineralContainedSectionChannelIndex
class16AqueousVsMineralLeaf = slot-leaf class16AqueousVsMineralChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierAqueousVsMineralStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isAqueousVsMineralIdentity : ClassifierAqueousVsMineralStep → Bool
isAqueousVsMineralIdentity aqueous-vs-mineral-identity = true
isAqueousVsMineralIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at aqueous-vs-mineral-identity
------------------------------------------------------------------------

aqueous-vs-mineral-left-identity :
  ∀ (a : ClassifierAqueousVsMineralStep) →
  isAqueousVsMineralIdentity aqueousVsMineralIdentity ≡ true
  × isProductConcurrent (productConcurrentOp aqueousVsMineralIdentity a) ≡ true
aqueous-vs-mineral-left-identity a = refl , refl

aqueous-vs-mineral-right-identity :
  ∀ (a : ClassifierAqueousVsMineralStep) →
  isProductConcurrent (productConcurrentOp a aqueousVsMineralIdentity) ≡ true
  × isAqueousVsMineralIdentity aqueousVsMineralIdentity ≡ true
aqueous-vs-mineral-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-aqueous-vs-mineral :
  (∀ a → isProductConcurrent (productConcurrentOp aqueousVsMineralIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a aqueousVsMineralIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-aqueous-vs-mineral =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named aqueous_vs_mineral nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedAqueousVsMineralNuanceProduct : ClassifierAqueousVsMineralStep
namedAqueousVsMineralNuanceProduct =
  productConcurrentOp
    (productConcurrentOp aqueousMessySectionLeaf mineralContainedSectionLeaf)
    class16AqueousVsMineralLeaf

named-aqueous-vs-mineral-nuance-product-concurrent :
  isProductConcurrent namedAqueousVsMineralNuanceProduct ≡ true
  × aqueousVsMineralBundleIsConcurrentProduct aqueousVsMineralNuanceWitness ≡ true
named-aqueous-vs-mineral-nuance-product-concurrent = refl , aqueous-vs-mineral-nuance-concurrent-product

------------------------------------------------------------------------
-- AqueousVsMineralBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data AqueousVsMineralAdmissibility : Set where
  aqueous-vs-mineral-admissible aqueous-vs-mineral-xor-refuse : AqueousVsMineralAdmissibility

isAqueousVsMineralPreserving : ClassifierAqueousVsMineralStep → Bool
isAqueousVsMineralPreserving aqueous-vs-mineral-identity = true
isAqueousVsMineralPreserving (slot-leaf _) = true
isAqueousVsMineralPreserving (product-concurrent a b) =
  isAqueousVsMineralPreserving a ∧ isAqueousVsMineralPreserving b
isAqueousVsMineralPreserving (xor-mutually-exclusive _ _) = false

isAqueousVsMineralAdmissible : ClassifierAqueousVsMineralStep → Bool
isAqueousVsMineralAdmissible step = isAqueousVsMineralPreserving step

aqueous-messy-section-leaf-admissible : isAqueousVsMineralAdmissible aqueousMessySectionLeaf ≡ true
aqueous-messy-section-leaf-admissible = refl

mineral-contained-section-leaf-admissible : isAqueousVsMineralAdmissible mineralContainedSectionLeaf ≡ true
mineral-contained-section-leaf-admissible = refl

class16-aqueous-vs-mineral-leaf-admissible : isAqueousVsMineralAdmissible class16AqueousVsMineralLeaf ≡ true
class16-aqueous-vs-mineral-leaf-admissible = refl

named-aqueous-vs-mineral-nuance-admissible : isAqueousVsMineralAdmissible namedAqueousVsMineralNuanceProduct ≡ true
named-aqueous-vs-mineral-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isAqueousVsMineralAdmissible (xorMutuallyExclusiveOp aqueousMessySectionLeaf mineralContainedSectionLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class16-aqueous-vs-mineral-refuse :
  isAqueousVsMineralAdmissible (xorMutuallyExclusiveOp mineralContainedSectionLeaf class16AqueousVsMineralLeaf) ≡ false
xor-mutually-exclusive-class16-aqueous-vs-mineral-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data AqueousVsMineralWitnessPresence : Set where
  aqueous-vs-mineral-witness-absent aqueous-vs-mineral-witness-present : AqueousVsMineralWitnessPresence

record ClassifierAqueousVsMineralWitness : Set where
  constructor mkClassifierAqueousVsMineralWitness
  field
    witness-presence : AqueousVsMineralWitnessPresence
    aqueous-vs-mineral-gap-total : ℕ

aqueousVsMineralWitnessAbsent : ClassifierAqueousVsMineralWitness
aqueousVsMineralWitnessAbsent = mkClassifierAqueousVsMineralWitness aqueous-vs-mineral-witness-absent zero

aqueousVsMineralWitnessPresentZeroGap : ClassifierAqueousVsMineralWitness
aqueousVsMineralWitnessPresentZeroGap = mkClassifierAqueousVsMineralWitness aqueous-vs-mineral-witness-present zero

aqueousVsMineralWitnessPresentWithGaps : ℕ → ClassifierAqueousVsMineralWitness
aqueousVsMineralWitnessPresentWithGaps n = mkClassifierAqueousVsMineralWitness aqueous-vs-mineral-witness-present n

aqueousVsMineralWitnessGapFree : ClassifierAqueousVsMineralWitness → Bool
aqueousVsMineralWitnessGapFree (mkClassifierAqueousVsMineralWitness aqueous-vs-mineral-witness-absent _) = false
aqueousVsMineralWitnessGapFree (mkClassifierAqueousVsMineralWitness aqueous-vs-mineral-witness-present n) =
  does (n ℕ-Props.≟ zero)

aqueous-vs-mineral-witness-present-zero-gap-free :
  aqueousVsMineralWitnessGapFree aqueousVsMineralWitnessPresentZeroGap ≡ true
aqueous-vs-mineral-witness-present-zero-gap-free = refl

aqueous-vs-mineral-witness-absent-not-gap-free :
  aqueousVsMineralWitnessGapFree aqueousVsMineralWitnessAbsent ≡ false
aqueous-vs-mineral-witness-absent-not-gap-free = refl

aqueous-vs-mineral-witness-with-gaps-not-gap-free :
  ∀ n → aqueousVsMineralWitnessGapFree (aqueousVsMineralWitnessPresentWithGaps (suc n)) ≡ false
aqueous-vs-mineral-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-AqueousVsMineral **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data AqueousVsMineralConservationVerdict : Set where
  verdict-unwired-ok verdict-aqueous-vs-mineral-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : AqueousVsMineralConservationVerdict

aqueousVsMineralConservationVerdictOk : AqueousVsMineralConservationVerdict → Bool
aqueousVsMineralConservationVerdictOk verdict-unwired-ok = true
aqueousVsMineralConservationVerdictOk verdict-aqueous-vs-mineral-admissible-ok = true
aqueousVsMineralConservationVerdictOk verdict-concurrent-product-ok = true
aqueousVsMineralConservationVerdictOk _ = false

evaluateAqueousVsMineralConservationClose :
  AqueousVsMineralConservationModality → ClassifierAqueousVsMineralStep → ClassifierAqueousVsMineralWitness
  → AqueousVsMineralBundleWitness → Bool → AqueousVsMineralConservationVerdict
evaluateAqueousVsMineralConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-proved _ (mkClassifierAqueousVsMineralWitness aqueous-vs-mineral-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-proved _ (mkClassifierAqueousVsMineralWitness aqueous-vs-mineral-witness-present _) w false
  with aqueousVsMineralBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-aqueous-vs-mineral-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without aqueous_vs_mineral witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-unwired namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-assumed namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-surrogate namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  aqueousVsMineralConservationVerdictOk
    (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-unwired namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false)
    ≡ true
  × aqueousVsMineralConservationVerdictOk
      (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-assumed namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false)
      ≡ true
  × aqueousVsMineralConservationVerdictOk
      (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-surrogate namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without aqueous_vs_mineral witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  aqueousVsMineralConservationVerdictOk
    (evaluateAqueousVsMineralConservationClose
       aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false ≡
  verdict-aqueous-vs-mineral-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-proved
    (xorMutuallyExclusiveOp aqueousMessySectionLeaf mineralContainedSectionLeaf)
    aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  aqueousVsMineralConservationVerdictOk
    (evaluateAqueousVsMineralConservationClose
       aqueous-vs-mineral-conservation-proved
       (xorMutuallyExclusiveOp aqueousMessySectionLeaf mineralContainedSectionLeaf)
       aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-proved
    (xorMutuallyExclusiveOp aqueousMessySectionLeaf mineralContainedSectionLeaf)
    aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-aqueous_vs_mineral — nuance **product** closed
------------------------------------------------------------------------

aqueous-vs-mineral-admissible-ok :
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap unwiredWitness false ≡
  verdict-aqueous-vs-mineral-admissible-ok
aqueous-vs-mineral-admissible-ok = refl

aqueous-vs-mineral-admissible-verdict-ok :
  aqueousVsMineralConservationVerdictOk
    (evaluateAqueousVsMineralConservationClose
       aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap unwiredWitness false)
    ≡ true
aqueous-vs-mineral-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — aqueous_vs_mineral nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  aqueousVsMineralConservationVerdictOk
    (evaluateAqueousVsMineralConservationClose
       aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-aqueous-vs-mineral16-proved :
  aqueousVsMineralConservationVerdictOk
    (evaluateAqueousVsMineralConservationClose
       aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness false)
    ≡ true
  × aqueousVsMineral16Proved ≡ false
concurrent-product-ok-still-not-aqueous-vs-mineral16-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateAqueousVsMineralConservationClose
    aqueous-vs-mineral-conservation-unwired namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  aqueousVsMineralConservationVerdictOk
    (evaluateAqueousVsMineralConservationClose
       aqueous-vs-mineral-conservation-unwired namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

aqueousVsMineralConservationFiberOk : FormalFiber → Bool
aqueousVsMineralConservationFiberOk fiber-quantum-knowing = true
aqueousVsMineralConservationFiberOk fiber-meso-acting = false

aqueous-vs-mineral-conservation-knowing-fiber-ok :
  aqueousVsMineralConservationFiberOk fiber-quantum-knowing ≡ true
aqueous-vs-mineral-conservation-knowing-fiber-ok = refl

aqueous-vs-mineral-conservation-meso-acting-not-ok :
  aqueousVsMineralConservationFiberOk fiber-meso-acting ≡ false
aqueous-vs-mineral-conservation-meso-acting-not-ok = refl

aqueous-vs-mineral-conservation-routes-knowing-not-meso :
  aqueousVsMineralConservationFiberOk fiber-quantum-knowing ≡ true ×
  aqueousVsMineralConservationFiberOk fiber-meso-acting ≡ false
aqueous-vs-mineral-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  aqueousVsMineralConservationFiberOk fiber-quantum-knowing ∧
  not (aqueousVsMineralConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 16 aqueous_vs_mineral Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

aqueous-vs-mineral-16-not-proved : aqueousVsMineral16Proved ≡ false
aqueous-vs-mineral-16-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

aqueous-vs-mineral-second-law-conservation-framed : aqueousVsMineralSecondLawConservationFramed ≡ true
aqueous-vs-mineral-second-law-conservation-framed = refl

aqueous-vs-mineral-not-xor-pin : aqueousVsMineralNotXor ≡ true
aqueous-vs-mineral-not-xor-pin = aqueous-vs-mineral-not-xor

env-restriction-typed-pin : envRestrictionTyped ≡ true
env-restriction-typed-pin = refl

not-parallel-aqueous-axiom-minted-pin : notParallelAqueousAxiomMinted ≡ true
not-parallel-aqueous-axiom-minted-pin = refl

l1-hydrates-stay-l1-not-element-id-pin : l1HydratesStayL1NotElementId ≡ true
l1-hydrates-stay-l1-not-element-id-pin = refl


conservation-not-proved : conservationProved ≡ false
conservation-not-proved = refl

phreeqc-pitzer-prior-art-framed : phreeqcPitzerPriorArtFramed ≡ true
phreeqc-pitzer-prior-art-framed = refl

tp-graph-function-not-float-pin : tpGraphFunctionNotFloatPin ≡ true
tp-graph-function-not-float-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel aqueous_vs_mineral axiom fork)
------------------------------------------------------------------------

aqueousVsMineralConservationAxiom :
  (aqueousVsMineral16Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (aqueousVsMineralSecondLawConservationFramed ≡ true)
  × (aqueousVsMineralNotXor ≡ true)
  × (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-unwired namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessAbsent aqueousVsMineralNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-proved (xorMutuallyExclusiveOp aqueousMessySectionLeaf mineralContainedSectionLeaf) aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap unwiredWitness false ≡ verdict-aqueous-vs-mineral-admissible-ok)
  × (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-proved namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (aqueousVsMineralConservationFiberOk fiber-quantum-knowing ≡ true)
  × (aqueousVsMineralConservationFiberOk fiber-meso-acting ≡ false)
  × (aqueousVsMineralConservationVerdictOk (evaluateAqueousVsMineralConservationClose aqueous-vs-mineral-conservation-unwired namedAqueousVsMineralNuanceProduct aqueousVsMineralWitnessPresentZeroGap aqueousVsMineralNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp aqueousVsMineralIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a aqueousVsMineralIdentity) ≡ true)
  × (isAqueousVsMineralAdmissible (xorMutuallyExclusiveOp aqueousMessySectionLeaf mineralContainedSectionLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (aqueousVsMineralClassIndex ≡ 16)
  × (AqueousVsMineralBundleWitness.present-count aqueousVsMineralNuanceWitness ≡ 3)
  × (elementAtomicZ calcium ≡ 20)
  × (elementAtomicZ oganesson ≡ 118)
  × (conservationProved ≡ false)
  × (phreeqcPitzerPriorArtFramed ≡ true)
  × (tpGraphFunctionNotFloatPin ≡ true)
  × (l1HydratesStayL1NotElementId ≡ true)
aqueousVsMineralConservationAxiom =
  aqueous-vs-mineral-16-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , aqueous-vs-mineral-second-law-conservation-framed
  , aqueous-vs-mineral-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , aqueous-vs-mineral-admissible-ok
  , concurrent-product-ok
  , aqueous-vs-mineral-conservation-knowing-fiber-ok
  , aqueous-vs-mineral-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , aqueous-vs-mineral-class-index-sixteen
  , aqueous-vs-mineral-nuance-present-count
  , calcium-z-20
  , oganesson-z-118
  , conservation-not-proved
  , phreeqc-pitzer-prior-art-framed
  , tp-graph-function-not-float-pin
  , l1-hydrates-stay-l1-not-element-id-pin

aqueousVsMineralConservationNamed : String
aqueousVsMineralConservationNamed =
  "aqueousVsMineralConservation: pattern class 16 aqueous_vs_mineral conservation concurrent Pi_c identity conserved aqueous messy pore Env section mineral contained section class 16 aqueous_vs_mineral concurrent product identity conserved present ge 2 product not XOR env restriction typed no parallel aqueous axiom L1 hydrates stay L1 not ElementId PHREEQC Pitzer prior art T P graph functions not float pins conservationProved false"

aqueousVsMineralConservationCrossWitnessAuthority : String
aqueousVsMineralConservationCrossWitnessAuthority =
  "umst/umst-chem/src/aqueous_mineral_is_environment_restriction.rs"

aqueousVsMineralTableAuthority : String
aqueousVsMineralTableAuthority =
  "umst/umst-chem/src/l0_tables/aqueous_vs_mineral.rs"

aqueousMineralRegimeAuthority : String
aqueousMineralRegimeAuthority =
  "umst/umst-chem/src/aqueous_mineral_regime.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

aqueousVsMineralConservationCellId : String
aqueousVsMineralConservationCellId = "CHEM-FORMAL-Q-AGDA-AQUEOUS-VS-MINERAL-CONSERVATION"

aqueousVsMineralConservationNonClaim : String
aqueousVsMineralConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-AQUEOUS-VS-MINERAL-CONSERVATION pattern class 16 aqueous_vs_mineral conservation concurrent Pi_c identity conserved aqueous messy pore Env section mineral contained section class 16 aqueous_vs_mineral product not XOR env restriction typed no parallel aqueous axiom L1 hydrates stay L1 not ElementId PHREEQC Pitzer prior art T P graph functions not float pins XOR mutually exclusive refuse aqueous vs mineral nuance witness concurrent aqueousVsMineral16Proved false conservationProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite aqueous_mineral_is_environment_restriction.rs l0_tables aqueous_vs_mineral aqueous_mineral_regime not fork not physics GREEN not production_wired WAVE100 no lib.rs"

aqueous-vs-mineral-conservation-cell-id :
  aqueousVsMineralConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-AQUEOUS-VS-MINERAL-CONSERVATION"
aqueous-vs-mineral-conservation-cell-id = refl

aqueous-vs-mineral-conservation-cites-env-restriction-rs :
  aqueousVsMineralConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/aqueous_mineral_is_environment_restriction.rs"
aqueous-vs-mineral-conservation-cites-env-restriction-rs = refl

aqueous-vs-mineral-conservation-cites-l0-table-rs :
  aqueousVsMineralTableAuthority ≡
  "umst/umst-chem/src/l0_tables/aqueous_vs_mineral.rs"
aqueous-vs-mineral-conservation-cites-l0-table-rs = refl

aqueous-vs-mineral-conservation-modality-unwired :
  aqueousVsMineralConservationModalityCurrent ≡ aqueous-vs-mineral-conservation-unwired
aqueous-vs-mineral-conservation-modality-unwired = refl

aqueousVsMineralConservationPhysicsGreenAuthorized : Set
aqueousVsMineralConservationPhysicsGreenAuthorized = ⊥

aqueous-vs-mineral-conservation-physics-green-false : ¬ aqueousVsMineralConservationPhysicsGreenAuthorized
aqueous-vs-mineral-conservation-physics-green-false ()

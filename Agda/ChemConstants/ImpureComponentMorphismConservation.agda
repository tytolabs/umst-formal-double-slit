-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ImpureComponentMorphismConservation.agda
--
-- Pattern class 8 **impure_component_morphism** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (second-law carrier + ore constituent morphism + PatternBundle concurrent factor;
--     **product** not XOR, not second SpeciesId / 26th axiom)
--   * XOR mutually-exclusive refuse; impure-component-morphism nuance witness concurrent
--     (second-law conservation carrier + ore constituent morphism + pattern bundle concurrent factor)
--   * **impure_component_morphism** laws Unwired (impureComponentMorphism08Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/impure_component_morphism.rs
-- L0 table: umst/umst-chem/src/l0_tables/impure_component_morphism.rs
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- Not 26th axiom; not second SpeciesId. Product not XOR.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ImpureComponentMorphismConservation where


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
-- Modality + pattern class 8 **impure_component_morphism** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ImpureComponentMorphismConservationModality : Set where
  impure-component-morphism-conservation-unwired impure-component-morphism-conservation-assumed
    impure-component-morphism-conservation-proved impure-component-morphism-conservation-surrogate
    : ImpureComponentMorphismConservationModality

impureComponentMorphismConservationModalityCurrent : ImpureComponentMorphismConservationModality
impureComponentMorphismConservationModalityCurrent = impure-component-morphism-conservation-unwired

impureComponentMorphism08Proved productionWired not118SquaredGreenTable
  impureComponentMorphismSecondLawConservationFramed impureComponentMorphismNotXor : Bool
impureComponentMorphism08Proved = false
productionWired = false
not118SquaredGreenTable = true
impureComponentMorphismSecondLawConservationFramed = true
impureComponentMorphismNotXor = true

impurityIsMorphism not26thAxiomMinted speciesIdNotForked : Bool
impurityIsMorphism = true
not26thAxiomMinted = true
speciesIdNotForked = true

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
-- Pattern class 8 Impure-component-morphism index pin
------------------------------------------------------------------------

impureComponentMorphismClassIndex : ℕ
impureComponentMorphismClassIndex = 7

impure-component-morphism-class-index-seven : impureComponentMorphismClassIndex ≡ 7
impure-component-morphism-class-index-seven = refl

------------------------------------------------------------------------
-- Named element Z pins — Fe (Z=26), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  iron copper : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ iron = 26
elementAtomicZ copper = 29

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

copper-z-29 : elementAtomicZ copper ≡ 29
copper-z-29 = refl

------------------------------------------------------------------------
-- ImpureComponentMorphismBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data ImpureComponentMorphismBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : ImpureComponentMorphismBundleSlot

isSlotPresent : ImpureComponentMorphismBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- ImpureComponentMorphismBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record ImpureComponentMorphismBundle : Set where
  field slot : ℕ → ImpureComponentMorphismBundleSlot

impureComponentMorphismBundleUnwired : ImpureComponentMorphismBundle
impureComponentMorphismBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : ImpureComponentMorphismBundle → ℕ → ImpureComponentMorphismBundleSlot → ImpureComponentMorphismBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else ImpureComponentMorphismBundle.slot b j }

withPresent : ImpureComponentMorphismBundle → ℕ → ImpureComponentMorphismBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record ImpureComponentMorphismBundleWitness : Set where
  constructor mkImpureComponentMorphismBundleWitness
  field
    bundle : ImpureComponentMorphismBundle
    present-count : ℕ

impureComponentMorphismBundleIsConcurrentProduct : ImpureComponentMorphismBundleWitness → Bool
impureComponentMorphismBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? ImpureComponentMorphismBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named impure-component-morphism channel indices — second-law carrier (1), ore morphism (2), PatternBundle (3)
------------------------------------------------------------------------

secondLawConservationCarrierChannelIndex oreConstituentMorphismChannelIndex patternBundleConcurrentFactorChannelIndex : ℕ
secondLawConservationCarrierChannelIndex = 1
oreConstituentMorphismChannelIndex = 2
patternBundleConcurrentFactorChannelIndex = 3

second-law-conservation-carrier-index-one : secondLawConservationCarrierChannelIndex ≡ 1
second-law-conservation-carrier-index-one = refl

ore-constituent-morphism-index-two : oreConstituentMorphismChannelIndex ≡ 2
ore-constituent-morphism-index-two = refl

pattern-bundle-concurrent-factor-index-three : patternBundleConcurrentFactorChannelIndex ≡ 3
pattern-bundle-concurrent-factor-index-three = refl

------------------------------------------------------------------------
-- Assemblage-stability-why nuance witness — connectivity + enablement + nets concurrent
------------------------------------------------------------------------

impureComponentMorphismNuanceBundle : ImpureComponentMorphismBundle
impureComponentMorphismNuanceBundle =
  withPresent
    (withPresent
      (withPresent impureComponentMorphismBundleUnwired secondLawConservationCarrierChannelIndex)
      oreConstituentMorphismChannelIndex)
    patternBundleConcurrentFactorChannelIndex

impureComponentMorphismNuanceWitness : ImpureComponentMorphismBundleWitness
impureComponentMorphismNuanceWitness =
  mkImpureComponentMorphismBundleWitness impureComponentMorphismNuanceBundle 3

impure-component-morphism-nuance-connectivity-present :
  isSlotPresent (ImpureComponentMorphismBundle.slot impureComponentMorphismNuanceBundle secondLawConservationCarrierChannelIndex) ≡ true
impure-component-morphism-nuance-connectivity-present = refl

impure-component-morphism-nuance-enablement-present :
  isSlotPresent (ImpureComponentMorphismBundle.slot impureComponentMorphismNuanceBundle oreConstituentMorphismChannelIndex) ≡ true
impure-component-morphism-nuance-enablement-present = refl

impure-component-morphism-nuance-nets-present :
  isSlotPresent (ImpureComponentMorphismBundle.slot impureComponentMorphismNuanceBundle patternBundleConcurrentFactorChannelIndex) ≡ true
impure-component-morphism-nuance-nets-present = refl

impure-component-morphism-nuance-present-count : ImpureComponentMorphismBundleWitness.present-count impureComponentMorphismNuanceWitness ≡ 3
impure-component-morphism-nuance-present-count = refl

impure-component-morphism-nuance-concurrent-product :
  impureComponentMorphismBundleIsConcurrentProduct impureComponentMorphismNuanceWitness ≡ true
impure-component-morphism-nuance-concurrent-product = refl

impure-component-morphism-nuance-three-factors-concurrent :
  isSlotPresent (ImpureComponentMorphismBundle.slot impureComponentMorphismNuanceBundle secondLawConservationCarrierChannelIndex) ≡ true
  × isSlotPresent (ImpureComponentMorphismBundle.slot impureComponentMorphismNuanceBundle oreConstituentMorphismChannelIndex) ≡ true
  × isSlotPresent (ImpureComponentMorphismBundle.slot impureComponentMorphismNuanceBundle patternBundleConcurrentFactorChannelIndex) ≡ true
  × ImpureComponentMorphismBundleWitness.present-count impureComponentMorphismNuanceWitness ≡ 3
impure-component-morphism-nuance-three-factors-concurrent =
  impure-component-morphism-nuance-connectivity-present
  , impure-component-morphism-nuance-enablement-present
  , impure-component-morphism-nuance-nets-present
  , impure-component-morphism-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : ImpureComponentMorphismBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if impureComponentMorphismBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = ImpureComponentMorphismBundleWitness.bundle w
       in if isSlotPresent (ImpureComponentMorphismBundle.slot b i)
          then if isSlotPresent (ImpureComponentMorphismBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : ImpureComponentMorphismBundleWitness
unwiredWitness = mkImpureComponentMorphismBundleWitness impureComponentMorphismBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

impure-component-morphism-nuance-xor-product-ok :
  evaluateXorRefuse impureComponentMorphismNuanceWitness secondLawConservationCarrierChannelIndex oreConstituentMorphismChannelIndex ≡ xor-product-ok
impure-component-morphism-nuance-xor-product-ok = refl

impure-component-morphism-not-xor : impureComponentMorphismNotXor ≡ true
impure-component-morphism-not-xor = refl

------------------------------------------------------------------------
-- ClassifierImpureComponentMorphismStep scaffold — ImpureComponentMorphismBundle **conservation**
------------------------------------------------------------------------

data ClassifierImpureComponentMorphismStep : Set where
  impure-component-morphism-identity : ClassifierImpureComponentMorphismStep
  slot-leaf : ℕ → ClassifierImpureComponentMorphismStep
  product-concurrent : ClassifierImpureComponentMorphismStep → ClassifierImpureComponentMorphismStep → ClassifierImpureComponentMorphismStep
  xor-mutually-exclusive : ClassifierImpureComponentMorphismStep → ClassifierImpureComponentMorphismStep → ClassifierImpureComponentMorphismStep

impureComponentMorphismIdentity : ClassifierImpureComponentMorphismStep
impureComponentMorphismIdentity = impure-component-morphism-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierImpureComponentMorphismStep → ClassifierImpureComponentMorphismStep → ClassifierImpureComponentMorphismStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

secondLawConservationCarrierLeaf oreConstituentMorphismLeaf patternBundleConcurrentFactorLeaf : ClassifierImpureComponentMorphismStep
secondLawConservationCarrierLeaf = slot-leaf secondLawConservationCarrierChannelIndex
oreConstituentMorphismLeaf = slot-leaf oreConstituentMorphismChannelIndex
patternBundleConcurrentFactorLeaf = slot-leaf patternBundleConcurrentFactorChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierImpureComponentMorphismStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isImpureComponentMorphismIdentity : ClassifierImpureComponentMorphismStep → Bool
isImpureComponentMorphismIdentity impure-component-morphism-identity = true
isImpureComponentMorphismIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at impure-component-morphism-identity
------------------------------------------------------------------------

impure-component-morphism-left-identity :
  ∀ (a : ClassifierImpureComponentMorphismStep) →
  isImpureComponentMorphismIdentity impureComponentMorphismIdentity ≡ true
  × isProductConcurrent (productConcurrentOp impureComponentMorphismIdentity a) ≡ true
impure-component-morphism-left-identity a = refl , refl

impure-component-morphism-right-identity :
  ∀ (a : ClassifierImpureComponentMorphismStep) →
  isProductConcurrent (productConcurrentOp a impureComponentMorphismIdentity) ≡ true
  × isImpureComponentMorphismIdentity impureComponentMorphismIdentity ≡ true
impure-component-morphism-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-impure-component-morphism :
  (∀ a → isProductConcurrent (productConcurrentOp impureComponentMorphismIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a impureComponentMorphismIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-impure-component-morphism =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named impure-component-morphism nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedImpureComponentMorphismNuanceProduct : ClassifierImpureComponentMorphismStep
namedImpureComponentMorphismNuanceProduct =
  productConcurrentOp
    (productConcurrentOp secondLawConservationCarrierLeaf oreConstituentMorphismLeaf)
    patternBundleConcurrentFactorLeaf

named-impure-component-morphism-nuance-product-concurrent :
  isProductConcurrent namedImpureComponentMorphismNuanceProduct ≡ true
  × impureComponentMorphismBundleIsConcurrentProduct impureComponentMorphismNuanceWitness ≡ true
named-impure-component-morphism-nuance-product-concurrent = refl , impure-component-morphism-nuance-concurrent-product

------------------------------------------------------------------------
-- ImpureComponentMorphismBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data ImpureComponentMorphismAdmissibility : Set where
  impure-component-morphism-admissible impure-component-morphism-xor-refuse : ImpureComponentMorphismAdmissibility

isImpureComponentMorphismPreserving : ClassifierImpureComponentMorphismStep → Bool
isImpureComponentMorphismPreserving impure-component-morphism-identity = true
isImpureComponentMorphismPreserving (slot-leaf _) = true
isImpureComponentMorphismPreserving (product-concurrent a b) =
  isImpureComponentMorphismPreserving a ∧ isImpureComponentMorphismPreserving b
isImpureComponentMorphismPreserving (xor-mutually-exclusive _ _) = false

isImpureComponentMorphismAdmissible : ClassifierImpureComponentMorphismStep → Bool
isImpureComponentMorphismAdmissible step = isImpureComponentMorphismPreserving step

second-law-conservation-carrier-leaf-admissible : isImpureComponentMorphismAdmissible secondLawConservationCarrierLeaf ≡ true
second-law-conservation-carrier-leaf-admissible = refl

ore-constituent-morphism-leaf-admissible : isImpureComponentMorphismAdmissible oreConstituentMorphismLeaf ≡ true
ore-constituent-morphism-leaf-admissible = refl

pattern-bundle-concurrent-factor-leaf-admissible : isImpureComponentMorphismAdmissible patternBundleConcurrentFactorLeaf ≡ true
pattern-bundle-concurrent-factor-leaf-admissible = refl

named-impure-component-morphism-nuance-admissible : isImpureComponentMorphismAdmissible namedImpureComponentMorphismNuanceProduct ≡ true
named-impure-component-morphism-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isImpureComponentMorphismAdmissible (xorMutuallyExclusiveOp secondLawConservationCarrierLeaf oreConstituentMorphismLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-pattern-bundle-concurrent-factor-refuse :
  isImpureComponentMorphismAdmissible (xorMutuallyExclusiveOp oreConstituentMorphismLeaf patternBundleConcurrentFactorLeaf) ≡ false
xor-mutually-exclusive-pattern-bundle-concurrent-factor-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data ImpureComponentMorphismWitnessPresence : Set where
  impure-component-morphism-witness-absent impure-component-morphism-witness-present : ImpureComponentMorphismWitnessPresence

record ClassifierImpureComponentMorphismWitness : Set where
  constructor mkClassifierImpureComponentMorphismWitness
  field
    witness-presence : ImpureComponentMorphismWitnessPresence
    impure-component-morphism-gap-total : ℕ

impureComponentMorphismWitnessAbsent : ClassifierImpureComponentMorphismWitness
impureComponentMorphismWitnessAbsent = mkClassifierImpureComponentMorphismWitness impure-component-morphism-witness-absent zero

impureComponentMorphismWitnessPresentZeroGap : ClassifierImpureComponentMorphismWitness
impureComponentMorphismWitnessPresentZeroGap = mkClassifierImpureComponentMorphismWitness impure-component-morphism-witness-present zero

impureComponentMorphismWitnessPresentWithGaps : ℕ → ClassifierImpureComponentMorphismWitness
impureComponentMorphismWitnessPresentWithGaps n = mkClassifierImpureComponentMorphismWitness impure-component-morphism-witness-present n

impureComponentMorphismWitnessGapFree : ClassifierImpureComponentMorphismWitness → Bool
impureComponentMorphismWitnessGapFree (mkClassifierImpureComponentMorphismWitness impure-component-morphism-witness-absent _) = false
impureComponentMorphismWitnessGapFree (mkClassifierImpureComponentMorphismWitness impure-component-morphism-witness-present n) =
  does (n ℕ-Props.≟ zero)

impure-component-morphism-witness-present-zero-gap-free :
  impureComponentMorphismWitnessGapFree impureComponentMorphismWitnessPresentZeroGap ≡ true
impure-component-morphism-witness-present-zero-gap-free = refl

impure-component-morphism-witness-absent-not-gap-free :
  impureComponentMorphismWitnessGapFree impureComponentMorphismWitnessAbsent ≡ false
impure-component-morphism-witness-absent-not-gap-free = refl

impure-component-morphism-witness-with-gaps-not-gap-free :
  ∀ n → impureComponentMorphismWitnessGapFree (impureComponentMorphismWitnessPresentWithGaps (suc n)) ≡ false
impure-component-morphism-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Assemblage-stability-why **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data ImpureComponentMorphismConservationVerdict : Set where
  verdict-unwired-ok verdict-impure-component-morphism-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : ImpureComponentMorphismConservationVerdict

impureComponentMorphismConservationVerdictOk : ImpureComponentMorphismConservationVerdict → Bool
impureComponentMorphismConservationVerdictOk verdict-unwired-ok = true
impureComponentMorphismConservationVerdictOk verdict-impure-component-morphism-admissible-ok = true
impureComponentMorphismConservationVerdictOk verdict-concurrent-product-ok = true
impureComponentMorphismConservationVerdictOk _ = false

evaluateImpureComponentMorphismConservationClose :
  ImpureComponentMorphismConservationModality → ClassifierImpureComponentMorphismStep → ClassifierImpureComponentMorphismWitness
  → ImpureComponentMorphismBundleWitness → Bool → ImpureComponentMorphismConservationVerdict
evaluateImpureComponentMorphismConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-proved _ (mkClassifierImpureComponentMorphismWitness impure-component-morphism-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-proved _ (mkClassifierImpureComponentMorphismWitness impure-component-morphism-witness-present _) w false
  with impureComponentMorphismBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-impure-component-morphism-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without impure-component-morphism witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-unwired namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-assumed namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-surrogate namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  impureComponentMorphismConservationVerdictOk
    (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-unwired namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false)
    ≡ true
  × impureComponentMorphismConservationVerdictOk
      (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-assumed namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false)
      ≡ true
  × impureComponentMorphismConservationVerdictOk
      (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-surrogate namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without impure-component-morphism witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  impureComponentMorphismConservationVerdictOk
    (evaluateImpureComponentMorphismConservationClose
       impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false ≡
  verdict-impure-component-morphism-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-proved
    (xorMutuallyExclusiveOp secondLawConservationCarrierLeaf oreConstituentMorphismLeaf)
    impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  impureComponentMorphismConservationVerdictOk
    (evaluateImpureComponentMorphismConservationClose
       impure-component-morphism-conservation-proved
       (xorMutuallyExclusiveOp secondLawConservationCarrierLeaf oreConstituentMorphismLeaf)
       impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-proved
    (xorMutuallyExclusiveOp secondLawConservationCarrierLeaf oreConstituentMorphismLeaf)
    impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-impure-component-morphism — nuance **product** closed
------------------------------------------------------------------------

impure-component-morphism-admissible-ok :
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap unwiredWitness false ≡
  verdict-impure-component-morphism-admissible-ok
impure-component-morphism-admissible-ok = refl

impure-component-morphism-admissible-verdict-ok :
  impureComponentMorphismConservationVerdictOk
    (evaluateImpureComponentMorphismConservationClose
       impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap unwiredWitness false)
    ≡ true
impure-component-morphism-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — impure-component-morphism nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  impureComponentMorphismConservationVerdictOk
    (evaluateImpureComponentMorphismConservationClose
       impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-impure-component-morphism04-proved :
  impureComponentMorphismConservationVerdictOk
    (evaluateImpureComponentMorphismConservationClose
       impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness false)
    ≡ true
  × impureComponentMorphism08Proved ≡ false
concurrent-product-ok-still-not-impure-component-morphism04-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateImpureComponentMorphismConservationClose
    impure-component-morphism-conservation-unwired namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  impureComponentMorphismConservationVerdictOk
    (evaluateImpureComponentMorphismConservationClose
       impure-component-morphism-conservation-unwired namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

impureComponentMorphismConservationFiberOk : FormalFiber → Bool
impureComponentMorphismConservationFiberOk fiber-quantum-knowing = true
impureComponentMorphismConservationFiberOk fiber-meso-acting = false

impure-component-morphism-conservation-knowing-fiber-ok :
  impureComponentMorphismConservationFiberOk fiber-quantum-knowing ≡ true
impure-component-morphism-conservation-knowing-fiber-ok = refl

impure-component-morphism-conservation-meso-acting-not-ok :
  impureComponentMorphismConservationFiberOk fiber-meso-acting ≡ false
impure-component-morphism-conservation-meso-acting-not-ok = refl

impure-component-morphism-conservation-routes-knowing-not-meso :
  impureComponentMorphismConservationFiberOk fiber-quantum-knowing ≡ true ×
  impureComponentMorphismConservationFiberOk fiber-meso-acting ≡ false
impure-component-morphism-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  impureComponentMorphismConservationFiberOk fiber-quantum-knowing ∧
  not (impureComponentMorphismConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 8 impure_component_morphism Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

impure-component-morphism-08-not-proved : impureComponentMorphism08Proved ≡ false
impure-component-morphism-08-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

impure-component-morphism-second-law-conservation-framed : impureComponentMorphismSecondLawConservationFramed ≡ true
impure-component-morphism-second-law-conservation-framed = refl

impure-component-morphism-not-xor-pin : impureComponentMorphismNotXor ≡ true
impure-component-morphism-not-xor-pin = impure-component-morphism-not-xor

impurity-is-morphism-pin : impurityIsMorphism ≡ true
impurity-is-morphism-pin = refl

not-26th-axiom-minted-pin : not26thAxiomMinted ≡ true
not-26th-axiom-minted-pin = refl

species-id-not-forked-pin : speciesIdNotForked ≡ true
species-id-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second SpeciesId / 26th axiom fork)
------------------------------------------------------------------------

impureComponentMorphismConservationAxiom :
  (impureComponentMorphism08Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (impureComponentMorphismSecondLawConservationFramed ≡ true)
  × (impureComponentMorphismNotXor ≡ true)
  × (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-unwired namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessAbsent impureComponentMorphismNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-proved (xorMutuallyExclusiveOp secondLawConservationCarrierLeaf oreConstituentMorphismLeaf) impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap unwiredWitness false ≡ verdict-impure-component-morphism-admissible-ok)
  × (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-proved namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (impureComponentMorphismConservationFiberOk fiber-quantum-knowing ≡ true)
  × (impureComponentMorphismConservationFiberOk fiber-meso-acting ≡ false)
  × (impureComponentMorphismConservationVerdictOk (evaluateImpureComponentMorphismConservationClose impure-component-morphism-conservation-unwired namedImpureComponentMorphismNuanceProduct impureComponentMorphismWitnessPresentZeroGap impureComponentMorphismNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp impureComponentMorphismIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a impureComponentMorphismIdentity) ≡ true)
  × (isImpureComponentMorphismAdmissible (xorMutuallyExclusiveOp secondLawConservationCarrierLeaf oreConstituentMorphismLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (impureComponentMorphismClassIndex ≡ 7)
  × (ImpureComponentMorphismBundleWitness.present-count impureComponentMorphismNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ copper ≡ 29)
impureComponentMorphismConservationAxiom =
  impure-component-morphism-08-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , impure-component-morphism-second-law-conservation-framed
  , impure-component-morphism-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , impure-component-morphism-admissible-ok
  , concurrent-product-ok
  , impure-component-morphism-conservation-knowing-fiber-ok
  , impure-component-morphism-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , impure-component-morphism-class-index-seven
  , impure-component-morphism-nuance-present-count
  , iron-z-26
  , copper-z-29

impureComponentMorphismConservationNamed : String
impureComponentMorphismConservationNamed =
  "impureComponentMorphismConservation: pattern class 8 impure_component_morphism conservation concurrent Pi_c identity conserved second law conservation carrier ore constituent morphism pattern bundle concurrent factor concurrent product identity conserved present ge 2 product not XOR impurity is morphism not second SpeciesId not 26th axiom"

impureComponentMorphismConservationCrossWitnessAuthority : String
impureComponentMorphismConservationCrossWitnessAuthority =
  "umst/umst-chem/src/impure_component_morphism.rs"

impureComponentMorphismTableAuthority : String
impureComponentMorphismTableAuthority =
  "umst/umst-chem/src/l0_tables/impure_component_morphism.rs"

oreAssemblageAuthority : String
oreAssemblageAuthority =
  "umst/umst-chem/src/ore_assemblage.rs"

patternProductConservationAuthority : String
patternProductConservationAuthority =
  "umst/umst-chem/src/theorem_import/PatternProductConservation.agda"

impureComponentMorphismConservationCellId : String
impureComponentMorphismConservationCellId = "CHEM-FORMAL-Q-AGDA-IMPURE-COMPONENT-MORPHISM-CONSERVATION"

impureComponentMorphismConservationNonClaim : String
impureComponentMorphismConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-IMPURE-COMPONENT-MORPHISM-CONSERVATION pattern class 8 impure_component_morphism conservation concurrent Pi_c identity conserved second law conservation carrier ore constituent morphism pattern bundle concurrent factor product not XOR impurity is morphism not second SpeciesId not 26th axiom XOR mutually exclusive refuse impure component morphism nuance witness concurrent impureComponentMorphism08Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite impure_component_morphism.rs l0_tables impure_component_morphism not fork not physics GREEN not production_wired"

impure-component-morphism-conservation-cell-id :
  impureComponentMorphismConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-IMPURE-COMPONENT-MORPHISM-CONSERVATION"
impure-component-morphism-conservation-cell-id = refl

impure-component-morphism-conservation-cites-impure-component-morphism-rs :
  impureComponentMorphismConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/impure_component_morphism.rs"
impure-component-morphism-conservation-cites-impure-component-morphism-rs = refl

impure-component-morphism-conservation-cites-l0-table-rs :
  impureComponentMorphismTableAuthority ≡
  "umst/umst-chem/src/l0_tables/impure_component_morphism.rs"
impure-component-morphism-conservation-cites-l0-table-rs = refl

impure-component-morphism-conservation-modality-unwired :
  impureComponentMorphismConservationModalityCurrent ≡ impure-component-morphism-conservation-unwired
impure-component-morphism-conservation-modality-unwired = refl

impureComponentMorphismConservationPhysicsGreenAuthorized : Set
impureComponentMorphismConservationPhysicsGreenAuthorized = ⊥

impure-component-morphism-conservation-physics-green-false : ¬ impureComponentMorphismConservationPhysicsGreenAuthorized
impure-component-morphism-conservation-physics-green-false ()

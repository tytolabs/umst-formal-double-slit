-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PatternProductConservation.agda
--
-- PATTERN-00 PatternBundle **product** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (cardinality 25; ≥2 Present is **product** not XOR)
--   * XOR mutually-exclusive refuse; carbon nuance witness concurrent
--     (allotrope + catalysis + continuum-vs-discrete)
--   * **product** laws Unwired (pattern00ProductProved = false)
--
-- Mirrors sibling `ChemConstants/DissipConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.PatternProductConservation where

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
-- Modality + PATTERN-00 PatternBundle **product** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PatternProductConservationModality : Set where
  pattern-product-conservation-unwired pattern-product-conservation-assumed
    pattern-product-conservation-proved pattern-product-conservation-surrogate
    : PatternProductConservationModality

patternProductConservationModalityCurrent : PatternProductConservationModality
patternProductConservationModalityCurrent = pattern-product-conservation-unwired

pattern00ProductProved productionWired not118SquaredGreenTable
  patternSecondLawConservationFramed productNotXor : Bool
pattern00ProductProved = false
productionWired = false
not118SquaredGreenTable = true
patternSecondLawConservationFramed = true
productNotXor = true

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
-- Named element Z pins — carbon (Z=6), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  carbon oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ carbon = 6
elementAtomicZ oganesson = 118

carbon-z-6 : elementAtomicZ carbon ≡ 6
carbon-z-6 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- PatternBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PatternBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PatternBundleSlot

isSlotPresent : PatternBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- PatternBundle_25 — many classes may hold at once (Π_c **product**)
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Named pattern class indices — allotrope (10), catalysis (14), continuum (23)
------------------------------------------------------------------------

allotropeClassIndex catalysisClassIndex continuumClassIndex : ℕ
allotropeClassIndex = 10
catalysisClassIndex = 14
continuumClassIndex = 23

allotrope-index-ten : allotropeClassIndex ≡ 10
allotrope-index-ten = refl

catalysis-index-fourteen : catalysisClassIndex ≡ 14
catalysis-index-fourteen = refl

continuum-index-twenty-three : continuumClassIndex ≡ 23
continuum-index-twenty-three = refl

------------------------------------------------------------------------
-- Carbon nuance witness — allotrope + catalysis + continuum concurrent
------------------------------------------------------------------------

carbonNuanceBundle : PatternBundle
carbonNuanceBundle =
  withPresent
    (withPresent
      (withPresent patternBundleUnwired allotropeClassIndex)
      catalysisClassIndex)
    continuumClassIndex

carbonNuanceWitness : PatternBundleWitness
carbonNuanceWitness =
  mkPatternBundleWitness carbonNuanceBundle 3

carbon-nuance-allotrope-present :
  isSlotPresent (PatternBundle.slot carbonNuanceBundle allotropeClassIndex) ≡ true
carbon-nuance-allotrope-present = refl

carbon-nuance-catalysis-present :
  isSlotPresent (PatternBundle.slot carbonNuanceBundle catalysisClassIndex) ≡ true
carbon-nuance-catalysis-present = refl

carbon-nuance-continuum-present :
  isSlotPresent (PatternBundle.slot carbonNuanceBundle continuumClassIndex) ≡ true
carbon-nuance-continuum-present = refl

carbon-nuance-present-count : PatternBundleWitness.present-count carbonNuanceWitness ≡ 3
carbon-nuance-present-count = refl

carbon-nuance-concurrent-product :
  patternBundleIsConcurrentProduct carbonNuanceWitness ≡ true
carbon-nuance-concurrent-product = refl

carbon-nuance-three-factors-concurrent :
  isSlotPresent (PatternBundle.slot carbonNuanceBundle allotropeClassIndex) ≡ true
  × isSlotPresent (PatternBundle.slot carbonNuanceBundle catalysisClassIndex) ≡ true
  × isSlotPresent (PatternBundle.slot carbonNuanceBundle continuumClassIndex) ≡ true
  × PatternBundleWitness.present-count carbonNuanceWitness ≡ 3
carbon-nuance-three-factors-concurrent =
  carbon-nuance-allotrope-present
  , carbon-nuance-catalysis-present
  , carbon-nuance-continuum-present
  , carbon-nuance-present-count

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

carbon-nuance-xor-product-ok :
  evaluateXorRefuse carbonNuanceWitness allotropeClassIndex catalysisClassIndex ≡ xor-product-ok
carbon-nuance-xor-product-ok = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPatternStep scaffold — PatternBundle **product** **conservation**
------------------------------------------------------------------------

data ClassifierPatternStep : Set where
  pattern-identity : ClassifierPatternStep
  slot-leaf : ℕ → ClassifierPatternStep
  product-concurrent : ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep
  xor-mutually-exclusive : ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep

patternIdentity : ClassifierPatternStep
patternIdentity = pattern-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

allotropeLeaf catalysisLeaf continuumLeaf : ClassifierPatternStep
allotropeLeaf = slot-leaf allotropeClassIndex
catalysisLeaf = slot-leaf catalysisClassIndex
continuumLeaf = slot-leaf continuumClassIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierPatternStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isPatternIdentity : ClassifierPatternStep → Bool
isPatternIdentity pattern-identity = true
isPatternIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at pattern-identity
------------------------------------------------------------------------

pattern-left-identity :
  ∀ (a : ClassifierPatternStep) →
  isPatternIdentity patternIdentity ≡ true
  × isProductConcurrent (productConcurrentOp patternIdentity a) ≡ true
pattern-left-identity a = refl , refl

pattern-right-identity :
  ∀ (a : ClassifierPatternStep) →
  isProductConcurrent (productConcurrentOp a patternIdentity) ≡ true
  × isPatternIdentity patternIdentity ≡ true
pattern-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-pattern :
  (∀ a → isProductConcurrent (productConcurrentOp patternIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a patternIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-pattern =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named carbon nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedCarbonNuanceProduct : ClassifierPatternStep
namedCarbonNuanceProduct =
  productConcurrentOp
    (productConcurrentOp allotropeLeaf catalysisLeaf)
    continuumLeaf

named-carbon-nuance-product-concurrent :
  isProductConcurrent namedCarbonNuanceProduct ≡ true
  × patternBundleIsConcurrentProduct carbonNuanceWitness ≡ true
named-carbon-nuance-product-concurrent = refl , carbon-nuance-concurrent-product

------------------------------------------------------------------------
-- PatternBundle **product** admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data PatternProductAdmissibility : Set where
  pattern-product-admissible pattern-xor-refuse : PatternProductAdmissibility

isPatternPreserving : ClassifierPatternStep → Bool
isPatternPreserving pattern-identity = true
isPatternPreserving (slot-leaf _) = true
isPatternPreserving (product-concurrent a b) =
  isPatternPreserving a ∧ isPatternPreserving b
isPatternPreserving (xor-mutually-exclusive _ _) = false

isPatternProductAdmissible : ClassifierPatternStep → Bool
isPatternProductAdmissible step = isPatternPreserving step

allotrope-leaf-admissible : isPatternProductAdmissible allotropeLeaf ≡ true
allotrope-leaf-admissible = refl

catalysis-leaf-admissible : isPatternProductAdmissible catalysisLeaf ≡ true
catalysis-leaf-admissible = refl

continuum-leaf-admissible : isPatternProductAdmissible continuumLeaf ≡ true
continuum-leaf-admissible = refl

named-carbon-nuance-admissible : isPatternProductAdmissible namedCarbonNuanceProduct ≡ true
named-carbon-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isPatternProductAdmissible (xorMutuallyExclusiveOp allotropeLeaf catalysisLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-refuse :
  isPatternProductAdmissible (xorMutuallyExclusiveOp catalysisLeaf continuumLeaf) ≡ false
xor-mutually-exclusive-continuum-refuse = refl

------------------------------------------------------------------------
-- PatternBundle witness — total-claim refuse without witness
------------------------------------------------------------------------

data PatternWitnessPresence : Set where
  pattern-witness-absent pattern-witness-present : PatternWitnessPresence

record ClassifierPatternWitness : Set where
  constructor mkClassifierPatternWitness
  field
    witness-presence : PatternWitnessPresence
    pattern-gap-total : ℕ

patternWitnessAbsent : ClassifierPatternWitness
patternWitnessAbsent = mkClassifierPatternWitness pattern-witness-absent zero

patternWitnessPresentZeroGap : ClassifierPatternWitness
patternWitnessPresentZeroGap = mkClassifierPatternWitness pattern-witness-present zero

patternWitnessPresentWithGaps : ℕ → ClassifierPatternWitness
patternWitnessPresentWithGaps n = mkClassifierPatternWitness pattern-witness-present n

patternWitnessGapFree : ClassifierPatternWitness → Bool
patternWitnessGapFree (mkClassifierPatternWitness pattern-witness-absent _) = false
patternWitnessGapFree (mkClassifierPatternWitness pattern-witness-present n) =
  does (n ℕ-Props.≟ zero)

pattern-witness-present-zero-gap-free :
  patternWitnessGapFree patternWitnessPresentZeroGap ≡ true
pattern-witness-present-zero-gap-free = refl

pattern-witness-absent-not-gap-free :
  patternWitnessGapFree patternWitnessAbsent ≡ false
pattern-witness-absent-not-gap-free = refl

pattern-witness-with-gaps-not-gap-free :
  ∀ n → patternWitnessGapFree (patternWitnessPresentWithGaps (suc n)) ≡ false
pattern-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-PATTERN-00 **product** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PatternProductConservationVerdict : Set where
  verdict-unwired-ok verdict-pattern-product-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : PatternProductConservationVerdict

patternProductConservationVerdictOk : PatternProductConservationVerdict → Bool
patternProductConservationVerdictOk verdict-unwired-ok = true
patternProductConservationVerdictOk verdict-pattern-product-admissible-ok = true
patternProductConservationVerdictOk verdict-concurrent-product-ok = true
patternProductConservationVerdictOk _ = false

evaluatePatternProductConservationClose :
  PatternProductConservationModality → ClassifierPatternStep → ClassifierPatternWitness
  → PatternBundleWitness → Bool → PatternProductConservationVerdict
evaluatePatternProductConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluatePatternProductConservationClose pattern-product-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluatePatternProductConservationClose pattern-product-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluatePatternProductConservationClose pattern-product-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluatePatternProductConservationClose pattern-product-conservation-proved _ (mkClassifierPatternWitness pattern-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluatePatternProductConservationClose pattern-product-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluatePatternProductConservationClose pattern-product-conservation-proved _ (mkClassifierPatternWitness pattern-witness-present _) w false
  with patternBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-pattern-product-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without pattern witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePatternProductConservationClose
    pattern-product-conservation-unwired namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePatternProductConservationClose
    pattern-product-conservation-assumed namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePatternProductConservationClose
    pattern-product-conservation-surrogate namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  patternProductConservationVerdictOk
    (evaluatePatternProductConservationClose pattern-product-conservation-unwired namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false)
    ≡ true
  × patternProductConservationVerdictOk
      (evaluatePatternProductConservationClose pattern-product-conservation-assumed namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false)
      ≡ true
  × patternProductConservationVerdictOk
      (evaluatePatternProductConservationClose pattern-product-conservation-surrogate namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without pattern witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePatternProductConservationClose
    pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  patternProductConservationVerdictOk
    (evaluatePatternProductConservationClose
       pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluatePatternProductConservationClose
    pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-pattern-product-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluatePatternProductConservationClose
    pattern-product-conservation-proved
    (xorMutuallyExclusiveOp allotropeLeaf catalysisLeaf)
    patternWitnessPresentZeroGap carbonNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  patternProductConservationVerdictOk
    (evaluatePatternProductConservationClose
       pattern-product-conservation-proved
       (xorMutuallyExclusiveOp allotropeLeaf catalysisLeaf)
       patternWitnessPresentZeroGap carbonNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluatePatternProductConservationClose
    pattern-product-conservation-proved
    (xorMutuallyExclusiveOp allotropeLeaf catalysisLeaf)
    patternWitnessPresentZeroGap carbonNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-pattern — carbon nuance **product** closed
------------------------------------------------------------------------

pattern-product-admissible-ok :
  evaluatePatternProductConservationClose
    pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessPresentZeroGap unwiredWitness false ≡
  verdict-pattern-product-admissible-ok
pattern-product-admissible-ok = refl

pattern-product-admissible-verdict-ok :
  patternProductConservationVerdictOk
    (evaluatePatternProductConservationClose
       pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessPresentZeroGap unwiredWitness false)
    ≡ true
pattern-product-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — carbon nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluatePatternProductConservationClose
    pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  patternProductConservationVerdictOk
    (evaluatePatternProductConservationClose
       pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-pattern00-proved :
  patternProductConservationVerdictOk
    (evaluatePatternProductConservationClose
       pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness false)
    ≡ true
  × pattern00ProductProved ≡ false
concurrent-product-ok-still-not-pattern00-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePatternProductConservationClose
    pattern-product-conservation-unwired namedCarbonNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  patternProductConservationVerdictOk
    (evaluatePatternProductConservationClose
       pattern-product-conservation-unwired namedCarbonNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

patternProductConservationFiberOk : FormalFiber → Bool
patternProductConservationFiberOk fiber-quantum-knowing = true
patternProductConservationFiberOk fiber-meso-acting = false

pattern-product-conservation-knowing-fiber-ok :
  patternProductConservationFiberOk fiber-quantum-knowing ≡ true
pattern-product-conservation-knowing-fiber-ok = refl

pattern-product-conservation-meso-acting-not-ok :
  patternProductConservationFiberOk fiber-meso-acting ≡ false
pattern-product-conservation-meso-acting-not-ok = refl

pattern-product-conservation-routes-knowing-not-meso :
  patternProductConservationFiberOk fiber-quantum-knowing ≡ true ×
  patternProductConservationFiberOk fiber-meso-acting ≡ false
pattern-product-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  patternProductConservationFiberOk fiber-quantum-knowing ∧
  not (patternProductConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not PATTERN-00 Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

pattern00-product-not-proved : pattern00ProductProved ≡ false
pattern00-product-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

pattern-second-law-conservation-framed : patternSecondLawConservationFramed ≡ true
pattern-second-law-conservation-framed = refl

product-not-xor-pin : productNotXor ≡ true
product-not-xor-pin = product-not-xor

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second PATTERN-00 axiom fork)
------------------------------------------------------------------------

patternProductConservationAxiom :
  (pattern00ProductProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (patternSecondLawConservationFramed ≡ true)
  × (productNotXor ≡ true)
  × (evaluatePatternProductConservationClose pattern-product-conservation-unwired namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluatePatternProductConservationClose pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluatePatternProductConservationClose pattern-product-conservation-proved (xorMutuallyExclusiveOp allotropeLeaf catalysisLeaf) patternWitnessPresentZeroGap carbonNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluatePatternProductConservationClose pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessPresentZeroGap unwiredWitness false ≡ verdict-pattern-product-admissible-ok)
  × (evaluatePatternProductConservationClose pattern-product-conservation-proved namedCarbonNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (patternProductConservationFiberOk fiber-quantum-knowing ≡ true)
  × (patternProductConservationFiberOk fiber-meso-acting ≡ false)
  × (patternProductConservationVerdictOk (evaluatePatternProductConservationClose pattern-product-conservation-unwired namedCarbonNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp patternIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a patternIdentity) ≡ true)
  × (isPatternProductAdmissible (xorMutuallyExclusiveOp allotropeLeaf catalysisLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (PatternBundleWitness.present-count carbonNuanceWitness ≡ 3)
  × (elementAtomicZ carbon ≡ 6)
  × (elementAtomicZ oganesson ≡ 118)
patternProductConservationAxiom =
  pattern00-product-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , pattern-second-law-conservation-framed
  , product-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , pattern-product-admissible-ok
  , concurrent-product-ok
  , pattern-product-conservation-knowing-fiber-ok
  , pattern-product-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , carbon-nuance-present-count
  , carbon-z-6
  , oganesson-z-118

patternProductConservationNamed : String
patternProductConservationNamed =
  "patternProductConservation: PATTERN-00 PatternBundle product conservation concurrent Pi_c identity conserved XOR refuse carbon nuance witness concurrent"

patternProductConservationCellId : String
patternProductConservationCellId = "CHEM-FORMAL-Q-AGDA-PATTERN-PRODUCT-CONSERVATION"

patternProductConservationNonClaim : String
patternProductConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-PATTERN-PRODUCT-CONSERVATION PATTERN-00 PatternBundle product conservation concurrent Pi_c identity conserved cardinality 25 present product not XOR XOR mutually exclusive refuse carbon nuance witness concurrent allotrope catalysis continuum pattern00ProductProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second PATTERN axiom not physics GREEN not production_wired"

pattern-product-conservation-modality-unwired :
  patternProductConservationModalityCurrent ≡ pattern-product-conservation-unwired
pattern-product-conservation-modality-unwired = refl

patternProductConservationPhysicsGreenAuthorized : Set
patternProductConservationPhysicsGreenAuthorized = ⊥

pattern-product-conservation-physics-green-false : ¬ patternProductConservationPhysicsGreenAuthorized
pattern-product-conservation-physics-green-false ()

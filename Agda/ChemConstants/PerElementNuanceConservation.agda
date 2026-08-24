-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PerElementNuanceConservation.agda
--
-- PATTERN-00 class 0 Per-element nuance **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupied Q-lattice + G+T graph + PSP per Z product)
--   * XOR mutually-exclusive refuse; per-element nuance witness concurrent
--     (qlattice-occupied + thermo-graph-morphism + psp-per-z)
--   * homolog ≠ copy — Pt (Z=78) NamedException vs Ds (Z=110) period-7 homolog not occupancy copy
--   * **per-element-nuance** laws Unwired (perElementNuanceProved = false)
--
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- INT: umst/umst-chem/src/x_rows/per_element_nuance_conservation.rs
-- WAVE100: not wired in lib.rs / eos.rs / nano.
-- Zero postulates that invent physics.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.PerElementNuanceConservation where

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
-- Modality + PATTERN-00 class-0 per-element nuance **conservation** pins (Unwired)
------------------------------------------------------------------------

data PerElementNuanceConservationModality : Set where
  per-element-nuance-conservation-unwired per-element-nuance-conservation-assumed
    per-element-nuance-conservation-proved per-element-nuance-conservation-surrogate
    : PerElementNuanceConservationModality

perElementNuanceConservationModalityCurrent : PerElementNuanceConservationModality
perElementNuanceConservationModalityCurrent = per-element-nuance-conservation-unwired

perElementNuanceProved productionWired not118SquaredGreenTable
  perElementNuanceSecondLawConservationFramed productNotXor
  wave100LibRsWired wave100EosRsWired wave100NanoWired homologNotCopy : Bool
perElementNuanceProved = false
productionWired = false
not118SquaredGreenTable = true
perElementNuanceSecondLawConservationFramed = true
productNotXor = true
wave100LibRsWired = false
wave100EosRsWired = false
wave100NanoWired = false
homologNotCopy = true

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
-- North-star §2 class-0 per_element_nuance pattern index
------------------------------------------------------------------------

perElementNuanceClassIndex : ℕ
perElementNuanceClassIndex = 0

per-element-nuance-class-index-zero : perElementNuanceClassIndex ≡ 0
per-element-nuance-class-index-zero = refl

per-element-nuance-class-not-118 :
  does (perElementNuanceClassIndex ℕ-Props.≟ 118) ≡ false
per-element-nuance-class-not-118 = refl

------------------------------------------------------------------------
-- Named element Z pins — C (Z=6), Pt (Z=78), Ds (Z=110), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  carbon platinum darmstadtium oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ carbon = 6
elementAtomicZ platinum = 78
elementAtomicZ darmstadtium = 110
elementAtomicZ oganesson = 118

carbon-z-6 : elementAtomicZ carbon ≡ 6
carbon-z-6 = refl

platinum-z-78 : elementAtomicZ platinum ≡ 78
platinum-z-78 = refl

darmstadtium-z-110 : elementAtomicZ darmstadtium ≡ 110
darmstadtium-z-110 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

periodHomologZOffset : ℕ
periodHomologZOffset = 32

ds-pt-homolog-z-offset :
  elementAtomicZ darmstadtium ≡ elementAtomicZ platinum + periodHomologZOffset
ds-pt-homolog-z-offset = refl

------------------------------------------------------------------------
-- Per-element nuance domain slot — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PerElementNuanceDomain : Set where
  domain-qlattice-occupied domain-thermo-graph-morphism domain-psp-per-z
    : PerElementNuanceDomain

isDomainPresent : PerElementNuanceDomain → Bool
isDomainPresent domain-qlattice-occupied = true
isDomainPresent domain-thermo-graph-morphism = true
isDomainPresent domain-psp-per-z = true

------------------------------------------------------------------------
-- PerElementNuanceBundle — many domains may hold at once (Π_c **product**)
------------------------------------------------------------------------

record PerElementNuanceBundle : Set where
  field domain : PerElementNuanceDomain → Bool

perElementNuanceBundleUnwired : PerElementNuanceBundle
perElementNuanceBundleUnwired = record { domain = λ _ → false }

withDomain : PerElementNuanceBundle → PerElementNuanceDomain → PerElementNuanceBundle
withDomain b d = record
  { domain = λ d' →
      if domainEq d' d then true else PerElementNuanceBundle.domain b d'
  }
  where
    domainEq : PerElementNuanceDomain → PerElementNuanceDomain → Bool
    domainEq domain-qlattice-occupied domain-qlattice-occupied = true
    domainEq domain-thermo-graph-morphism domain-thermo-graph-morphism = true
    domainEq domain-psp-per-z domain-psp-per-z = true
    domainEq _ _ = false

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PerElementNuanceWitness : Set where
  constructor mkPerElementNuanceWitness
  field
    bundle : PerElementNuanceBundle
    present-count : ℕ

perElementNuanceIsConcurrentProduct : PerElementNuanceWitness → Bool
perElementNuanceIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PerElementNuanceWitness.present-count w)

------------------------------------------------------------------------
-- Carbon per-element nuance witness — qlattice + thermo + psp concurrent
------------------------------------------------------------------------

carbonNuanceBundle : PerElementNuanceBundle
carbonNuanceBundle =
  withDomain
    (withDomain
      (withDomain perElementNuanceBundleUnwired domain-qlattice-occupied)
      domain-thermo-graph-morphism)
    domain-psp-per-z

carbonNuanceWitness : PerElementNuanceWitness
carbonNuanceWitness =
  mkPerElementNuanceWitness carbonNuanceBundle 3

carbon-nuance-qlattice-present :
  PerElementNuanceBundle.domain carbonNuanceBundle domain-qlattice-occupied ≡ true
carbon-nuance-qlattice-present = refl

carbon-nuance-thermo-present :
  PerElementNuanceBundle.domain carbonNuanceBundle domain-thermo-graph-morphism ≡ true
carbon-nuance-thermo-present = refl

carbon-nuance-psp-present :
  PerElementNuanceBundle.domain carbonNuanceBundle domain-psp-per-z ≡ true
carbon-nuance-psp-present = refl

carbon-nuance-present-count : PerElementNuanceWitness.present-count carbonNuanceWitness ≡ 3
carbon-nuance-present-count = refl

carbon-nuance-concurrent-product :
  perElementNuanceIsConcurrentProduct carbonNuanceWitness ≡ true
carbon-nuance-concurrent-product = refl

carbon-nuance-three-domains-concurrent :
  PerElementNuanceBundle.domain carbonNuanceBundle domain-qlattice-occupied ≡ true
  × PerElementNuanceBundle.domain carbonNuanceBundle domain-thermo-graph-morphism ≡ true
  × PerElementNuanceBundle.domain carbonNuanceBundle domain-psp-per-z ≡ true
  × PerElementNuanceWitness.present-count carbonNuanceWitness ≡ 3
carbon-nuance-three-domains-concurrent =
  carbon-nuance-qlattice-present
  , carbon-nuance-thermo-present
  , carbon-nuance-psp-present
  , carbon-nuance-present-count

------------------------------------------------------------------------
-- Occupied Q-lattice — discrete identity scaffold (not 118² GREEN)
------------------------------------------------------------------------

data QLatticeOccupancy : Set where
  qlattice-occupied qlattice-unoccupied : QLatticeOccupancy

isQLatticeOccupied : QLatticeOccupancy → Bool
isQLatticeOccupied qlattice-occupied = true
isQLatticeOccupied _ = false

carbon-qlattice-occupied : isQLatticeOccupied qlattice-occupied ≡ true
carbon-qlattice-occupied = refl

qlattice-not-118-squared :
  does (elementAtomicZ carbon ℕ-Props.≟ (118 * 118)) ≡ false
qlattice-not-118-squared = refl

------------------------------------------------------------------------
-- homolog ≠ copy — Pt NamedException vs Ds period-7 homolog restriction
------------------------------------------------------------------------

data HomologCopyVerdict : Set where
  homolog-not-copy homolog-is-copy : HomologCopyVerdict

evaluateHomologCopy : ℕ → ℕ → HomologCopyVerdict
evaluateHomologCopy zHomolog zSource =
  if does (zHomolog ℕ-Props.≟ (zSource + periodHomologZOffset))
  then homolog-not-copy
  else homolog-is-copy

ds-pt-homolog-not-copy :
  evaluateHomologCopy (elementAtomicZ darmstadtium) (elementAtomicZ platinum) ≡ homolog-not-copy
ds-pt-homolog-not-copy = refl

carbon-ds-homolog-is-copy :
  evaluateHomologCopy (elementAtomicZ carbon) (elementAtomicZ platinum) ≡ homolog-is-copy
carbon-ds-homolog-is-copy = refl

homolog-not-copy-pin : homologNotCopy ≡ true
homolog-not-copy-pin = refl

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PerElementNuanceWitness → PerElementNuanceDomain → PerElementNuanceDomain → XorRefuseVerdict
evaluateXorRefuse w d1 d2 =
  if perElementNuanceIsConcurrentProduct w
  then xor-product-ok
  else let b = PerElementNuanceWitness.bundle w
       in if PerElementNuanceBundle.domain b d1
          then if PerElementNuanceBundle.domain b d2
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PerElementNuanceWitness
unwiredWitness = mkPerElementNuanceWitness perElementNuanceBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness domain-qlattice-occupied domain-thermo-graph-morphism ≡ xor-product-ok
xor-refuse-not-product-ok = refl

carbon-nuance-xor-product-ok :
  evaluateXorRefuse carbonNuanceWitness domain-qlattice-occupied domain-thermo-graph-morphism ≡ xor-product-ok
carbon-nuance-xor-product-ok = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPatternStep scaffold — per-element nuance **conservation**
------------------------------------------------------------------------

data ClassifierPatternStep : Set where
  pattern-identity : ClassifierPatternStep
  domain-leaf : PerElementNuanceDomain → ClassifierPatternStep
  product-concurrent : ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep
  xor-mutually-exclusive : ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep

patternIdentity : ClassifierPatternStep
patternIdentity = pattern-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

qlatticeLeaf thermoLeaf pspLeaf : ClassifierPatternStep
qlatticeLeaf = domain-leaf domain-qlattice-occupied
thermoLeaf = domain-leaf domain-thermo-graph-morphism
pspLeaf = domain-leaf domain-psp-per-z

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
-- Named carbon per-element nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedCarbonPerElementNuanceProduct : ClassifierPatternStep
namedCarbonPerElementNuanceProduct =
  productConcurrentOp
    (productConcurrentOp qlatticeLeaf thermoLeaf)
    pspLeaf

named-carbon-per-element-nuance-product-concurrent :
  isProductConcurrent namedCarbonPerElementNuanceProduct ≡ true
  × perElementNuanceIsConcurrentProduct carbonNuanceWitness ≡ true
named-carbon-per-element-nuance-product-concurrent = refl , carbon-nuance-concurrent-product

------------------------------------------------------------------------
-- Per-element nuance admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data PerElementNuanceAdmissibility : Set where
  per-element-nuance-admissible per-element-nuance-xor-refuse : PerElementNuanceAdmissibility

isPatternPreserving : ClassifierPatternStep → Bool
isPatternPreserving pattern-identity = true
isPatternPreserving (domain-leaf _) = true
isPatternPreserving (product-concurrent a b) =
  isPatternPreserving a ∧ isPatternPreserving b
isPatternPreserving (xor-mutually-exclusive _ _) = false

isPerElementNuanceAdmissible : ClassifierPatternStep → Bool
isPerElementNuanceAdmissible step = isPatternPreserving step

qlattice-leaf-admissible : isPerElementNuanceAdmissible qlatticeLeaf ≡ true
qlattice-leaf-admissible = refl

thermo-leaf-admissible : isPerElementNuanceAdmissible thermoLeaf ≡ true
thermo-leaf-admissible = refl

psp-leaf-admissible : isPerElementNuanceAdmissible pspLeaf ≡ true
psp-leaf-admissible = refl

named-carbon-nuance-admissible : isPerElementNuanceAdmissible namedCarbonPerElementNuanceProduct ≡ true
named-carbon-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isPerElementNuanceAdmissible (xorMutuallyExclusiveOp qlatticeLeaf thermoLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-psp-refuse :
  isPerElementNuanceAdmissible (xorMutuallyExclusiveOp thermoLeaf pspLeaf) ≡ false
xor-mutually-exclusive-psp-refuse = refl

------------------------------------------------------------------------
-- Classifier witness — total-claim refuse without witness
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

------------------------------------------------------------------------
-- Classifier-PATTERN-00 class-0 **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PerElementNuanceConservationVerdict : Set where
  verdict-unwired-ok verdict-per-element-nuance-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    verdict-homolog-copy-refuse
    : PerElementNuanceConservationVerdict

perElementNuanceConservationVerdictOk : PerElementNuanceConservationVerdict → Bool
perElementNuanceConservationVerdictOk verdict-unwired-ok = true
perElementNuanceConservationVerdictOk verdict-per-element-nuance-admissible-ok = true
perElementNuanceConservationVerdictOk verdict-concurrent-product-ok = true
perElementNuanceConservationVerdictOk _ = false

evaluatePerElementNuanceConservationClose :
  PerElementNuanceConservationModality → ClassifierPatternStep → ClassifierPatternWitness
  → PerElementNuanceWitness → Bool → PerElementNuanceConservationVerdict
evaluatePerElementNuanceConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluatePerElementNuanceConservationClose per-element-nuance-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluatePerElementNuanceConservationClose per-element-nuance-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluatePerElementNuanceConservationClose per-element-nuance-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluatePerElementNuanceConservationClose per-element-nuance-conservation-proved _ (mkClassifierPatternWitness pattern-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluatePerElementNuanceConservationClose per-element-nuance-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluatePerElementNuanceConservationClose per-element-nuance-conservation-proved _ (mkClassifierPatternWitness pattern-witness-present _) w false
  with perElementNuanceIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-per-element-nuance-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without pattern witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-unwired namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-assumed namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-surrogate namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  perElementNuanceConservationVerdictOk
    (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-unwired namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false)
    ≡ true
  × perElementNuanceConservationVerdictOk
      (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-assumed namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false)
      ≡ true
  × perElementNuanceConservationVerdictOk
      (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-surrogate namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without pattern witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  perElementNuanceConservationVerdictOk
    (evaluatePerElementNuanceConservationClose
       per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡
  verdict-per-element-nuance-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-proved
    (xorMutuallyExclusiveOp qlatticeLeaf thermoLeaf)
    patternWitnessPresentZeroGap carbonNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  perElementNuanceConservationVerdictOk
    (evaluatePerElementNuanceConservationClose
       per-element-nuance-conservation-proved
       (xorMutuallyExclusiveOp qlatticeLeaf thermoLeaf)
       patternWitnessPresentZeroGap carbonNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

------------------------------------------------------------------------
-- Admissible classifier-pattern — carbon per-element nuance **product** closed
------------------------------------------------------------------------

per-element-nuance-admissible-ok :
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap unwiredWitness false ≡
  verdict-per-element-nuance-admissible-ok
per-element-nuance-admissible-ok = refl

per-element-nuance-admissible-verdict-ok :
  perElementNuanceConservationVerdictOk
    (evaluatePerElementNuanceConservationClose
       per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap unwiredWitness false)
    ≡ true
per-element-nuance-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — carbon nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  perElementNuanceConservationVerdictOk
    (evaluatePerElementNuanceConservationClose
       per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-proved :
  perElementNuanceConservationVerdictOk
    (evaluatePerElementNuanceConservationClose
       per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness false)
    ≡ true
  × perElementNuanceProved ≡ false
concurrent-product-ok-still-not-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePerElementNuanceConservationClose
    per-element-nuance-conservation-unwired namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  perElementNuanceConservationVerdictOk
    (evaluatePerElementNuanceConservationClose
       per-element-nuance-conservation-unwired namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- WAVE100 freeze — lib.rs / eos.rs / nano not wired
------------------------------------------------------------------------

wave100-not-wired :
  wave100LibRsWired ≡ false
  × wave100EosRsWired ≡ false
  × wave100NanoWired ≡ false
wave100-not-wired = refl , refl , refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

perElementNuanceConservationFiberOk : FormalFiber → Bool
perElementNuanceConservationFiberOk fiber-quantum-knowing = true
perElementNuanceConservationFiberOk fiber-meso-acting = false

per-element-nuance-conservation-knowing-fiber-ok :
  perElementNuanceConservationFiberOk fiber-quantum-knowing ≡ true
per-element-nuance-conservation-knowing-fiber-ok = refl

per-element-nuance-conservation-meso-acting-not-ok :
  perElementNuanceConservationFiberOk fiber-meso-acting ≡ false
per-element-nuance-conservation-meso-acting-not-ok = refl

per-element-nuance-conservation-routes-knowing-not-meso :
  perElementNuanceConservationFiberOk fiber-quantum-knowing ≡ true ×
  perElementNuanceConservationFiberOk fiber-meso-acting ≡ false
per-element-nuance-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  perElementNuanceConservationFiberOk fiber-quantum-knowing ∧
  not (perElementNuanceConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class-0 Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

per-element-nuance-not-proved : perElementNuanceProved ≡ false
per-element-nuance-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

per-element-nuance-second-law-conservation-framed :
  perElementNuanceSecondLawConservationFramed ≡ true
per-element-nuance-second-law-conservation-framed = refl

product-not-xor-pin : productNotXor ≡ true
product-not-xor-pin = product-not-xor

------------------------------------------------------------------------
-- Authority cites — INT per_element_nuance_conservation.rs read-only
------------------------------------------------------------------------

perElementNuanceConservationAuthority : String
perElementNuanceConservationAuthority =
  "umst/umst-chem/src/x_rows/per_element_nuance_conservation.rs"

perElementNuanceTableAuthority : String
perElementNuanceTableAuthority =
  "umst/umst-chem/src/l0_tables/per_element_nuance.rs"

qlatticeTypeAuthority : String
qlatticeTypeAuthority =
  "umst/umst-chem/src/qlattice.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

per-element-nuance-conservation-cites-cross-witness-rs :
  perElementNuanceConservationAuthority ≡
  "umst/umst-chem/src/x_rows/per_element_nuance_conservation.rs"
per-element-nuance-conservation-cites-cross-witness-rs = refl

per-element-nuance-cites-l0-table :
  perElementNuanceTableAuthority ≡
  "umst/umst-chem/src/l0_tables/per_element_nuance.rs"
per-element-nuance-cites-l0-table = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second class-0 axiom fork)
------------------------------------------------------------------------

perElementNuanceConservationAxiom :
  (perElementNuanceProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (perElementNuanceSecondLawConservationFramed ≡ true)
  × (productNotXor ≡ true)
  × (homologNotCopy ≡ true)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (wave100NanoWired ≡ false)
  × (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-unwired namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessAbsent carbonNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-proved (xorMutuallyExclusiveOp qlatticeLeaf thermoLeaf) patternWitnessPresentZeroGap carbonNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap unwiredWitness false ≡ verdict-per-element-nuance-admissible-ok)
  × (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-proved namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (perElementNuanceConservationFiberOk fiber-quantum-knowing ≡ true)
  × (perElementNuanceConservationFiberOk fiber-meso-acting ≡ false)
  × (perElementNuanceConservationVerdictOk (evaluatePerElementNuanceConservationClose per-element-nuance-conservation-unwired namedCarbonPerElementNuanceProduct patternWitnessPresentZeroGap carbonNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp patternIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a patternIdentity) ≡ true)
  × (isPerElementNuanceAdmissible (xorMutuallyExclusiveOp qlatticeLeaf thermoLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (perElementNuanceClassIndex ≡ 0)
  × (PerElementNuanceWitness.present-count carbonNuanceWitness ≡ 3)
  × (elementAtomicZ carbon ≡ 6)
  × (elementAtomicZ platinum ≡ 78)
  × (elementAtomicZ darmstadtium ≡ 110)
  × (elementAtomicZ oganesson ≡ 118)
  × (evaluateHomologCopy (elementAtomicZ darmstadtium) (elementAtomicZ platinum) ≡ homolog-not-copy)
  × (isQLatticeOccupied qlattice-occupied ≡ true)
perElementNuanceConservationAxiom =
  per-element-nuance-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , per-element-nuance-second-law-conservation-framed
  , product-not-xor-pin
  , homolog-not-copy-pin
  , refl
  , refl
  , refl
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , per-element-nuance-admissible-ok
  , concurrent-product-ok
  , per-element-nuance-conservation-knowing-fiber-ok
  , per-element-nuance-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , per-element-nuance-class-index-zero
  , carbon-nuance-present-count
  , carbon-z-6
  , platinum-z-78
  , darmstadtium-z-110
  , oganesson-z-118
  , ds-pt-homolog-not-copy
  , carbon-qlattice-occupied

perElementNuanceConservationNamed : String
perElementNuanceConservationNamed =
  "perElementNuanceConservation: PATTERN-00 class 0 per-element nuance conservation concurrent Pi_c identity conserved XOR refuse occupied Q-lattice homolog not copy carbon nuance witness concurrent"

perElementNuanceConservationCellId : String
perElementNuanceConservationCellId = "CHEM-FORMAL-Q-AGDA-PER-ELEMENT-NUANCE-CONSERVATION"

perElementNuanceConservationNonClaim : String
perElementNuanceConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-PER-ELEMENT-NUANCE-CONSERVATION PATTERN-00 class 0 per-element nuance conservation concurrent Pi_c identity conserved cardinality 25 present product not XOR XOR mutually exclusive refuse occupied Q-lattice homolog not copy Pt Ds carbon nuance witness concurrent qlattice thermo psp perElementNuanceProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second PATTERN axiom not physics GREEN not production_wired WAVE100 not lib.rs eos.rs nano"

per-element-nuance-conservation-modality-unwired :
  perElementNuanceConservationModalityCurrent ≡ per-element-nuance-conservation-unwired
per-element-nuance-conservation-modality-unwired = refl

perElementNuanceConservationPhysicsGreenAuthorized : Set
perElementNuanceConservationPhysicsGreenAuthorized = ⊥

per-element-nuance-conservation-physics-green-false : ¬ perElementNuanceConservationPhysicsGreenAuthorized
per-element-nuance-conservation-physics-green-false ()

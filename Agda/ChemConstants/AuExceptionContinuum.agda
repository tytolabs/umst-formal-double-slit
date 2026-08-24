-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.AuExceptionContinuum.agda
--
-- Au Z=79 **occupancy-engine sort** exception **continuum** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort + dblock exception + continuum witness;
--     **product** not XOR, no parallel au-exception-continuum axiom)
--   * XOR mutually-exclusive refuse; au-exception nuance witness concurrent
--     (occupancy-engine sort + dblock exception + continuum witness)
--   * **occupancy-engine sort** laws Unwired (auExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_079_au.rs
-- Homolog Cu Z=29 / Ag Z=47 — not Cu d-block copy, not Ag chart copy.
-- Sibling: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel au-exception-continuum axiom; continuum not forked. Product not XOR.
-- Au Z=79 d-block Madelung exception as occupancy-engine sort theorem, not extra force.
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

module ChemConstants.AuExceptionContinuum where

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
-- Modality + Au Z=79 occupancy-engine sort exception continuum pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data AuExceptionContinuumModality : Set where
  au-exception-continuum-unwired au-exception-continuum-assumed
    au-exception-continuum-proved au-exception-continuum-surrogate
    : AuExceptionContinuumModality

auExceptionContinuumModalityCurrent : AuExceptionContinuumModality
auExceptionContinuumModalityCurrent = au-exception-continuum-unwired

auExceptionContinuumProved productionWired not118SquaredGreenTable
  auExceptionSecondLawConservationFramed auExceptionNotXor : Bool
auExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
auExceptionSecondLawConservationFramed = true
auExceptionNotXor = true

occupancyEngineSortTyped notParallelAuExceptionAxiomMinted continuumNotForked : Bool
occupancyEngineSortTyped = true
notParallelAuExceptionAxiomMinted = true
continuumNotForked = true

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
-- Occupancy-engine sort Au exception continuum index pin
------------------------------------------------------------------------

occupancyEngineSortTagIndex : ℕ
occupancyEngineSortTagIndex = 79

occupancy-engine-sort-tag-index : occupancyEngineSortTagIndex ≡ 79
occupancy-engine-sort-tag-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Au (Z=79), Pt (Z=78 homolog; not Cu/Ag copy)
------------------------------------------------------------------------

data ElementTag : Set where
  gold platinum : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ gold = 79
elementAtomicZ platinum = 78

gold-z-79 : elementAtomicZ gold ≡ 79
gold-z-79 = refl

platinum-z-78 : elementAtomicZ platinum ≡ 78
platinum-z-78 = refl

------------------------------------------------------------------------
-- AuExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data AuExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : AuExceptionBundleSlot

isSlotPresent : AuExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- AuExceptionBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record AuExceptionBundle : Set where
  field slot : ℕ → AuExceptionBundleSlot

auExceptionBundleUnwired : AuExceptionBundle
auExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : AuExceptionBundle → ℕ → AuExceptionBundleSlot → AuExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else AuExceptionBundle.slot b j }

withPresent : AuExceptionBundle → ℕ → AuExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record AuExceptionBundleWitness : Set where
  constructor mkAuExceptionBundleWitness
  field
    bundle : AuExceptionBundle
    present-count : ℕ

auExceptionBundleIsConcurrentProduct : AuExceptionBundleWitness → Bool
auExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? AuExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named au-exception-continuum channel indices — interact restriction (1), not extra force (2), occupancy-engine sort (3)
------------------------------------------------------------------------

occupancyEngineSortChannelIndex dBlockExceptionChannelIndex continuumWitnessChannelIndex : ℕ
occupancyEngineSortChannelIndex = 1
dBlockExceptionChannelIndex = 2
continuumWitnessChannelIndex = 3

occupancy-engine-sort-index-one : occupancyEngineSortChannelIndex ≡ 1
occupancy-engine-sort-index-one = refl

dblock-exception-index-two : dBlockExceptionChannelIndex ≡ 2
dblock-exception-index-two = refl

continuum-witness-index-three : continuumWitnessChannelIndex ≡ 3
continuum-witness-index-three = refl

------------------------------------------------------------------------
-- AuException nuance witness — interact restriction + not extra force + occupancy-engine sort concurrent
------------------------------------------------------------------------

auExceptionNuanceBundle : AuExceptionBundle
auExceptionNuanceBundle =
  withPresent
    (withPresent
      (withPresent auExceptionBundleUnwired occupancyEngineSortChannelIndex)
      dBlockExceptionChannelIndex)
    continuumWitnessChannelIndex

auExceptionNuanceWitness : AuExceptionBundleWitness
auExceptionNuanceWitness =
  mkAuExceptionBundleWitness auExceptionNuanceBundle 3

au-exception-nuance-occupancy-engine-sort-present :
  isSlotPresent (AuExceptionBundle.slot auExceptionNuanceBundle occupancyEngineSortChannelIndex) ≡ true
au-exception-nuance-occupancy-engine-sort-present = refl

au-exception-nuance-dblock-exception-present :
  isSlotPresent (AuExceptionBundle.slot auExceptionNuanceBundle dBlockExceptionChannelIndex) ≡ true
au-exception-nuance-dblock-exception-present = refl

au-exception-nuance-continuum-witness-present :
  isSlotPresent (AuExceptionBundle.slot auExceptionNuanceBundle continuumWitnessChannelIndex) ≡ true
au-exception-nuance-continuum-witness-present = refl

au-exception-nuance-present-count : AuExceptionBundleWitness.present-count auExceptionNuanceWitness ≡ 3
au-exception-nuance-present-count = refl

au-exception-nuance-concurrent-product :
  auExceptionBundleIsConcurrentProduct auExceptionNuanceWitness ≡ true
au-exception-nuance-concurrent-product = refl

au-exception-nuance-three-factors-concurrent :
  isSlotPresent (AuExceptionBundle.slot auExceptionNuanceBundle occupancyEngineSortChannelIndex) ≡ true
  × isSlotPresent (AuExceptionBundle.slot auExceptionNuanceBundle dBlockExceptionChannelIndex) ≡ true
  × isSlotPresent (AuExceptionBundle.slot auExceptionNuanceBundle continuumWitnessChannelIndex) ≡ true
  × AuExceptionBundleWitness.present-count auExceptionNuanceWitness ≡ 3
au-exception-nuance-three-factors-concurrent =
  au-exception-nuance-occupancy-engine-sort-present
  , au-exception-nuance-dblock-exception-present
  , au-exception-nuance-continuum-witness-present
  , au-exception-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : AuExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if auExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = AuExceptionBundleWitness.bundle w
       in if isSlotPresent (AuExceptionBundle.slot b i)
          then if isSlotPresent (AuExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : AuExceptionBundleWitness
unwiredWitness = mkAuExceptionBundleWitness auExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

au-exception-nuance-xor-product-ok :
  evaluateXorRefuse auExceptionNuanceWitness occupancyEngineSortChannelIndex dBlockExceptionChannelIndex ≡ xor-product-ok
au-exception-nuance-xor-product-ok = refl

au-exception-not-xor : auExceptionNotXor ≡ true
au-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierAuExceptionStep scaffold — AuExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierAuExceptionStep : Set where
  au-exception-identity : ClassifierAuExceptionStep
  slot-leaf : ℕ → ClassifierAuExceptionStep
  product-concurrent : ClassifierAuExceptionStep → ClassifierAuExceptionStep → ClassifierAuExceptionStep
  xor-mutually-exclusive : ClassifierAuExceptionStep → ClassifierAuExceptionStep → ClassifierAuExceptionStep

auExceptionIdentity : ClassifierAuExceptionStep
auExceptionIdentity = au-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierAuExceptionStep → ClassifierAuExceptionStep → ClassifierAuExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortLeaf dBlockExceptionLeaf continuumWitnessLeaf : ClassifierAuExceptionStep
occupancyEngineSortLeaf = slot-leaf occupancyEngineSortChannelIndex
dBlockExceptionLeaf = slot-leaf dBlockExceptionChannelIndex
continuumWitnessLeaf = slot-leaf continuumWitnessChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierAuExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isAuExceptionIdentity : ClassifierAuExceptionStep → Bool
isAuExceptionIdentity au-exception-identity = true
isAuExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at au-exception-identity
------------------------------------------------------------------------

au-exception-left-identity :
  ∀ (a : ClassifierAuExceptionStep) →
  isAuExceptionIdentity auExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp auExceptionIdentity a) ≡ true
au-exception-left-identity a = refl , refl

au-exception-right-identity :
  ∀ (a : ClassifierAuExceptionStep) →
  isProductConcurrent (productConcurrentOp a auExceptionIdentity) ≡ true
  × isAuExceptionIdentity auExceptionIdentity ≡ true
au-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-au-exception :
  (∀ a → isProductConcurrent (productConcurrentOp auExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a auExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-au-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named au-exception-continuum nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedAuExceptionNuanceProduct : ClassifierAuExceptionStep
namedAuExceptionNuanceProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    continuumWitnessLeaf

named-au-exception-nuance-product-concurrent :
  isProductConcurrent namedAuExceptionNuanceProduct ≡ true
  × auExceptionBundleIsConcurrentProduct auExceptionNuanceWitness ≡ true
named-au-exception-nuance-product-concurrent = refl , au-exception-nuance-concurrent-product

------------------------------------------------------------------------
-- AuExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data AuExceptionAdmissibility : Set where
  au-exception-admissible au-exception-xor-refuse : AuExceptionAdmissibility

isAuExceptionPreserving : ClassifierAuExceptionStep → Bool
isAuExceptionPreserving au-exception-identity = true
isAuExceptionPreserving (slot-leaf _) = true
isAuExceptionPreserving (product-concurrent a b) =
  isAuExceptionPreserving a ∧ isAuExceptionPreserving b
isAuExceptionPreserving (xor-mutually-exclusive _ _) = false

isAuExceptionAdmissible : ClassifierAuExceptionStep → Bool
isAuExceptionAdmissible step = isAuExceptionPreserving step

occupancy-engine-sort-leaf-admissible : isAuExceptionAdmissible occupancyEngineSortLeaf ≡ true
occupancy-engine-sort-leaf-admissible = refl

dblock-exception-leaf-admissible : isAuExceptionAdmissible dBlockExceptionLeaf ≡ true
dblock-exception-leaf-admissible = refl

continuum-witness-leaf-admissible : isAuExceptionAdmissible continuumWitnessLeaf ≡ true
continuum-witness-leaf-admissible = refl

named-au-exception-nuance-admissible : isAuExceptionAdmissible namedAuExceptionNuanceProduct ≡ true
named-au-exception-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isAuExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-witness-refuse :
  isAuExceptionAdmissible (xorMutuallyExclusiveOp dBlockExceptionLeaf continuumWitnessLeaf) ≡ false
xor-mutually-exclusive-continuum-witness-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data AuExceptionWitnessPresence : Set where
  au-exception-witness-absent au-exception-witness-present : AuExceptionWitnessPresence

record ClassifierAuExceptionWitness : Set where
  constructor mkClassifierAuExceptionWitness
  field
    witness-presence : AuExceptionWitnessPresence
    au-exception-gap-total : ℕ

auExceptionWitnessAbsent : ClassifierAuExceptionWitness
auExceptionWitnessAbsent = mkClassifierAuExceptionWitness au-exception-witness-absent zero

auExceptionWitnessPresentZeroGap : ClassifierAuExceptionWitness
auExceptionWitnessPresentZeroGap = mkClassifierAuExceptionWitness au-exception-witness-present zero

auExceptionWitnessPresentWithGaps : ℕ → ClassifierAuExceptionWitness
auExceptionWitnessPresentWithGaps n = mkClassifierAuExceptionWitness au-exception-witness-present n

auExceptionWitnessGapFree : ClassifierAuExceptionWitness → Bool
auExceptionWitnessGapFree (mkClassifierAuExceptionWitness au-exception-witness-absent _) = false
auExceptionWitnessGapFree (mkClassifierAuExceptionWitness au-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

au-exception-witness-present-zero-gap-free :
  auExceptionWitnessGapFree auExceptionWitnessPresentZeroGap ≡ true
au-exception-witness-present-zero-gap-free = refl

au-exception-witness-absent-not-gap-free :
  auExceptionWitnessGapFree auExceptionWitnessAbsent ≡ false
au-exception-witness-absent-not-gap-free = refl

au-exception-witness-with-gaps-not-gap-free :
  ∀ n → auExceptionWitnessGapFree (auExceptionWitnessPresentWithGaps (suc n)) ≡ false
au-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-AuException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data AuExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-au-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : AuExceptionContinuumVerdict

auExceptionContinuumVerdictOk : AuExceptionContinuumVerdict → Bool
auExceptionContinuumVerdictOk verdict-unwired-ok = true
auExceptionContinuumVerdictOk verdict-au-exception-admissible-ok = true
auExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
auExceptionContinuumVerdictOk _ = false

evaluateAuExceptionContinuumClose :
  AuExceptionContinuumModality → ClassifierAuExceptionStep → ClassifierAuExceptionWitness
  → AuExceptionBundleWitness → Bool → AuExceptionContinuumVerdict
evaluateAuExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateAuExceptionContinuumClose au-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateAuExceptionContinuumClose au-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateAuExceptionContinuumClose au-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateAuExceptionContinuumClose au-exception-continuum-proved _ (mkClassifierAuExceptionWitness au-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateAuExceptionContinuumClose au-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateAuExceptionContinuumClose au-exception-continuum-proved _ (mkClassifierAuExceptionWitness au-exception-witness-present _) w false
  with auExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-au-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without au-exception-continuum witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateAuExceptionContinuumClose
    au-exception-continuum-unwired namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateAuExceptionContinuumClose
    au-exception-continuum-assumed namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateAuExceptionContinuumClose
    au-exception-continuum-surrogate namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  auExceptionContinuumVerdictOk
    (evaluateAuExceptionContinuumClose au-exception-continuum-unwired namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false)
    ≡ true
  × auExceptionContinuumVerdictOk
      (evaluateAuExceptionContinuumClose au-exception-continuum-assumed namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false)
      ≡ true
  × auExceptionContinuumVerdictOk
      (evaluateAuExceptionContinuumClose au-exception-continuum-surrogate namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without au-exception-continuum witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateAuExceptionContinuumClose
    au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  auExceptionContinuumVerdictOk
    (evaluateAuExceptionContinuumClose
       au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateAuExceptionContinuumClose
    au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false ≡
  verdict-au-exception-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateAuExceptionContinuumClose
    au-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    auExceptionWitnessPresentZeroGap auExceptionNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  auExceptionContinuumVerdictOk
    (evaluateAuExceptionContinuumClose
       au-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
       auExceptionWitnessPresentZeroGap auExceptionNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateAuExceptionContinuumClose
    au-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    auExceptionWitnessPresentZeroGap auExceptionNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-au-exception-continuum — nuance **product** closed
------------------------------------------------------------------------

au-exception-admissible-ok :
  evaluateAuExceptionContinuumClose
    au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-au-exception-admissible-ok
au-exception-admissible-ok = refl

au-exception-admissible-verdict-ok :
  auExceptionContinuumVerdictOk
    (evaluateAuExceptionContinuumClose
       au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
au-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — au-exception-continuum nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateAuExceptionContinuumClose
    au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap auExceptionNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  auExceptionContinuumVerdictOk
    (evaluateAuExceptionContinuumClose
       au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap auExceptionNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-auExceptionContinuum-proved :
  auExceptionContinuumVerdictOk
    (evaluateAuExceptionContinuumClose
       au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap auExceptionNuanceWitness false)
    ≡ true
  × auExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-auExceptionContinuum-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateAuExceptionContinuumClose
    au-exception-continuum-unwired namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap auExceptionNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  auExceptionContinuumVerdictOk
    (evaluateAuExceptionContinuumClose
       au-exception-continuum-unwired namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap auExceptionNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

auExceptionContinuumFiberOk : FormalFiber → Bool
auExceptionContinuumFiberOk fiber-quantum-knowing = true
auExceptionContinuumFiberOk fiber-meso-acting = false

au-exception-continuum-knowing-fiber-ok :
  auExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
au-exception-continuum-knowing-fiber-ok = refl

au-exception-continuum-meso-acting-not-ok :
  auExceptionContinuumFiberOk fiber-meso-acting ≡ false
au-exception-continuum-meso-acting-not-ok = refl

au-exception-continuum-routes-knowing-not-meso :
  auExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  auExceptionContinuumFiberOk fiber-meso-acting ≡ false
au-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  auExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (auExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not occupancy-engine sort Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

au-exception-continuum-not-proved : auExceptionContinuumProved ≡ false
au-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

au-exception-second-law-conservation-framed : auExceptionSecondLawConservationFramed ≡ true
au-exception-second-law-conservation-framed = refl

au-exception-not-xor-pin : auExceptionNotXor ≡ true
au-exception-not-xor-pin = au-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-au-exception-axiom-minted-pin : notParallelAuExceptionAxiomMinted ≡ true
not-parallel-au-exception-axiom-minted-pin = refl

continuum-not-forked-pin : continuumNotForked ≡ true
continuum-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel au-exception-continuum axiom fork)
------------------------------------------------------------------------

auExceptionContinuumAxiom :
  (auExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (auExceptionSecondLawConservationFramed ≡ true)
  × (auExceptionNotXor ≡ true)
  × (evaluateAuExceptionContinuumClose au-exception-continuum-unwired namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateAuExceptionContinuumClose au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessAbsent auExceptionNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateAuExceptionContinuumClose au-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) auExceptionWitnessPresentZeroGap auExceptionNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateAuExceptionContinuumClose au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-au-exception-admissible-ok)
  × (evaluateAuExceptionContinuumClose au-exception-continuum-proved namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap auExceptionNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (auExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (auExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (auExceptionContinuumVerdictOk (evaluateAuExceptionContinuumClose au-exception-continuum-unwired namedAuExceptionNuanceProduct auExceptionWitnessPresentZeroGap auExceptionNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp auExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a auExceptionIdentity) ≡ true)
  × (isAuExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (occupancyEngineSortTagIndex ≡ 79)
  × (AuExceptionBundleWitness.present-count auExceptionNuanceWitness ≡ 3)
  × (elementAtomicZ gold ≡ 79)
  × (elementAtomicZ platinum ≡ 78)
auExceptionContinuumAxiom =
  au-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , au-exception-second-law-conservation-framed
  , au-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , au-exception-admissible-ok
  , concurrent-product-ok
  , au-exception-continuum-knowing-fiber-ok
  , au-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , occupancy-engine-sort-tag-index
  , au-exception-nuance-present-count
  , gold-z-79
  , platinum-z-78

auExceptionContinuumNamed : String
auExceptionContinuumNamed =
  "auExceptionContinuum: Au Z=79 occupancy-engine sort exception continuum conservation concurrent Pi_c identity conserved Interact restriction not extra force occupancy-engine sort concurrent product identity conserved present ge 2 product not XOR interact restriction typed no parallel au-exception-continuum axiom not extra force"

auExceptionContinuumCrossWitnessAuthority : String
auExceptionContinuumCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

z079AuAuthority : String
z079AuAuthority =
  "umst/umst-chem/src/elements/z_079_au.rs"

occupancyExceptionSetsAuthority : String
occupancyExceptionSetsAuthority =
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"

auExceptionContinuumCellId : String
auExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-AU-EXCEPTION-CONTINUUM"

auExceptionContinuumNonClaim : String
auExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-AU-EXCEPTION-CONTINUUM Au Z=79 occupancy-engine sort exception continuum conservation concurrent Pi_c identity conserved Interact restriction not extra force occupancy-engine sort product not XOR interact restriction typed no parallel au-exception-continuum axiom not extra force XOR mutually exclusive refuse au-exception-continuum nuance witness concurrent auExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite occupancy_engine_sort.rs l0_tables au-exception-continuum not fork not physics GREEN not production_wired"

au-exception-continuum-cell-id :
  auExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-AU-EXCEPTION-CONTINUUM"
au-exception-continuum-cell-id = refl

au-exception-continuum-cites-occupancy-engine-sort-rs :
  auExceptionContinuumCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
au-exception-continuum-cites-occupancy-engine-sort-rs = refl

au-exception-continuum-cites-z079-au-rs :
  z079AuAuthority ≡
  "umst/umst-chem/src/elements/z_079_au.rs"
au-exception-continuum-cites-z079-au-rs = refl

au-exception-continuum-modality-unwired :
  auExceptionContinuumModalityCurrent ≡ au-exception-continuum-unwired
au-exception-continuum-modality-unwired = refl

auExceptionContinuumPhysicsGreenAuthorized : Set
auExceptionContinuumPhysicsGreenAuthorized = ⊥

au-exception-continuum-physics-green-false : ¬ auExceptionContinuumPhysicsGreenAuthorized
au-exception-continuum-physics-green-false ()

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.NbExceptionContinuum.agda
--
-- Nb Z=41 **occupancy-engine sort** exception **continuum** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort + dblock exception + continuum witness;
--     **product** not XOR, no parallel nb-exception-continuum axiom)
--   * XOR mutually-exclusive refuse; cu-exception nuance witness concurrent
--     (occupancy-engine sort + dblock exception + continuum witness)
--   * **occupancy-engine sort** laws Unwired (nbExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_041_nb.rs
-- Sibling: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel nb-exception-continuum axiom; continuum not forked. Product not XOR.
-- Nb Z=41 d-block Madelung exception as occupancy-engine sort theorem, not extra force.
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

module ChemConstants.NbExceptionContinuum where

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
-- Modality + pattern class 14 **occupancy-engine sort** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data NbExceptionContinuumModality : Set where
  nb-exception-continuum-unwired nb-exception-continuum-assumed
    nb-exception-continuum-proved nb-exception-continuum-surrogate
    : NbExceptionContinuumModality

nbExceptionContinuumModalityCurrent : NbExceptionContinuumModality
nbExceptionContinuumModalityCurrent = nb-exception-continuum-unwired

nbExceptionContinuumProved productionWired not118SquaredGreenTable
  nbExceptionSecondLawConservationFramed nbExceptionNotXor : Bool
nbExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
nbExceptionSecondLawConservationFramed = true
nbExceptionNotXor = true

occupancyEngineSortTyped notParallelNbExceptionAxiomMinted continuumNotForked : Bool
occupancyEngineSortTyped = true
notParallelNbExceptionAxiomMinted = true
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
-- Occupancy-engine sort Cu exception continuum index pin
------------------------------------------------------------------------

occupancyEngineSortTagIndex : ℕ
occupancyEngineSortTagIndex = 41

occupancy-engine-sort-tag-index : occupancyEngineSortTagIndex ≡ 41
occupancy-engine-sort-tag-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Pt (Z=78), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  niobium tantalum : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ niobium = 41
elementAtomicZ tantalum = 73

niobium-z-41 : elementAtomicZ niobium ≡ 41
niobium-z-41 = refl

tantalum-z-73 : elementAtomicZ tantalum ≡ 73
tantalum-z-73 = refl

------------------------------------------------------------------------
-- NbExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data NbExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : NbExceptionBundleSlot

isSlotPresent : NbExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- NbExceptionBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record NbExceptionBundle : Set where
  field slot : ℕ → NbExceptionBundleSlot

nbExceptionBundleUnwired : NbExceptionBundle
nbExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : NbExceptionBundle → ℕ → NbExceptionBundleSlot → NbExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else NbExceptionBundle.slot b j }

withPresent : NbExceptionBundle → ℕ → NbExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record NbExceptionBundleWitness : Set where
  constructor mkNbExceptionBundleWitness
  field
    bundle : NbExceptionBundle
    present-count : ℕ

nbExceptionBundleIsConcurrentProduct : NbExceptionBundleWitness → Bool
nbExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? NbExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named nb-exception-continuum channel indices — interact restriction (1), not extra force (2), occupancy-engine sort (3)
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
-- NbException nuance witness — interact restriction + not extra force + occupancy-engine sort concurrent
------------------------------------------------------------------------

nbExceptionNuanceBundle : NbExceptionBundle
nbExceptionNuanceBundle =
  withPresent
    (withPresent
      (withPresent nbExceptionBundleUnwired occupancyEngineSortChannelIndex)
      dBlockExceptionChannelIndex)
    continuumWitnessChannelIndex

nbExceptionNuanceWitness : NbExceptionBundleWitness
nbExceptionNuanceWitness =
  mkNbExceptionBundleWitness nbExceptionNuanceBundle 3

cu-exception-nuance-occupancy-engine-sort-present :
  isSlotPresent (NbExceptionBundle.slot nbExceptionNuanceBundle occupancyEngineSortChannelIndex) ≡ true
cu-exception-nuance-occupancy-engine-sort-present = refl

cu-exception-nuance-dblock-exception-present :
  isSlotPresent (NbExceptionBundle.slot nbExceptionNuanceBundle dBlockExceptionChannelIndex) ≡ true
cu-exception-nuance-dblock-exception-present = refl

cu-exception-nuance-continuum-witness-present :
  isSlotPresent (NbExceptionBundle.slot nbExceptionNuanceBundle continuumWitnessChannelIndex) ≡ true
cu-exception-nuance-continuum-witness-present = refl

cu-exception-nuance-present-count : NbExceptionBundleWitness.present-count nbExceptionNuanceWitness ≡ 3
cu-exception-nuance-present-count = refl

cu-exception-nuance-concurrent-product :
  nbExceptionBundleIsConcurrentProduct nbExceptionNuanceWitness ≡ true
cu-exception-nuance-concurrent-product = refl

cu-exception-nuance-three-factors-concurrent :
  isSlotPresent (NbExceptionBundle.slot nbExceptionNuanceBundle occupancyEngineSortChannelIndex) ≡ true
  × isSlotPresent (NbExceptionBundle.slot nbExceptionNuanceBundle dBlockExceptionChannelIndex) ≡ true
  × isSlotPresent (NbExceptionBundle.slot nbExceptionNuanceBundle continuumWitnessChannelIndex) ≡ true
  × NbExceptionBundleWitness.present-count nbExceptionNuanceWitness ≡ 3
cu-exception-nuance-three-factors-concurrent =
  cu-exception-nuance-occupancy-engine-sort-present
  , cu-exception-nuance-dblock-exception-present
  , cu-exception-nuance-continuum-witness-present
  , cu-exception-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : NbExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if nbExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = NbExceptionBundleWitness.bundle w
       in if isSlotPresent (NbExceptionBundle.slot b i)
          then if isSlotPresent (NbExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : NbExceptionBundleWitness
unwiredWitness = mkNbExceptionBundleWitness nbExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

cu-exception-nuance-xor-product-ok :
  evaluateXorRefuse nbExceptionNuanceWitness occupancyEngineSortChannelIndex dBlockExceptionChannelIndex ≡ xor-product-ok
cu-exception-nuance-xor-product-ok = refl

cu-exception-not-xor : nbExceptionNotXor ≡ true
cu-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierNbExceptionStep scaffold — NbExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierNbExceptionStep : Set where
  cu-exception-identity : ClassifierNbExceptionStep
  slot-leaf : ℕ → ClassifierNbExceptionStep
  product-concurrent : ClassifierNbExceptionStep → ClassifierNbExceptionStep → ClassifierNbExceptionStep
  xor-mutually-exclusive : ClassifierNbExceptionStep → ClassifierNbExceptionStep → ClassifierNbExceptionStep

nbExceptionIdentity : ClassifierNbExceptionStep
nbExceptionIdentity = cu-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierNbExceptionStep → ClassifierNbExceptionStep → ClassifierNbExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortLeaf dBlockExceptionLeaf continuumWitnessLeaf : ClassifierNbExceptionStep
occupancyEngineSortLeaf = slot-leaf occupancyEngineSortChannelIndex
dBlockExceptionLeaf = slot-leaf dBlockExceptionChannelIndex
continuumWitnessLeaf = slot-leaf continuumWitnessChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierNbExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isNbExceptionIdentity : ClassifierNbExceptionStep → Bool
isNbExceptionIdentity cu-exception-identity = true
isNbExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at cu-exception-identity
------------------------------------------------------------------------

cu-exception-left-identity :
  ∀ (a : ClassifierNbExceptionStep) →
  isNbExceptionIdentity nbExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp nbExceptionIdentity a) ≡ true
cu-exception-left-identity a = refl , refl

cu-exception-right-identity :
  ∀ (a : ClassifierNbExceptionStep) →
  isProductConcurrent (productConcurrentOp a nbExceptionIdentity) ≡ true
  × isNbExceptionIdentity nbExceptionIdentity ≡ true
cu-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-cu-exception :
  (∀ a → isProductConcurrent (productConcurrentOp nbExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a nbExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-cu-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named nb-exception-continuum nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedNbExceptionNuanceProduct : ClassifierNbExceptionStep
namedNbExceptionNuanceProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    continuumWitnessLeaf

named-cu-exception-nuance-product-concurrent :
  isProductConcurrent namedNbExceptionNuanceProduct ≡ true
  × nbExceptionBundleIsConcurrentProduct nbExceptionNuanceWitness ≡ true
named-cu-exception-nuance-product-concurrent = refl , cu-exception-nuance-concurrent-product

------------------------------------------------------------------------
-- NbExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data NbExceptionAdmissibility : Set where
  cu-exception-admissible cu-exception-xor-refuse : NbExceptionAdmissibility

isNbExceptionPreserving : ClassifierNbExceptionStep → Bool
isNbExceptionPreserving cu-exception-identity = true
isNbExceptionPreserving (slot-leaf _) = true
isNbExceptionPreserving (product-concurrent a b) =
  isNbExceptionPreserving a ∧ isNbExceptionPreserving b
isNbExceptionPreserving (xor-mutually-exclusive _ _) = false

isNbExceptionAdmissible : ClassifierNbExceptionStep → Bool
isNbExceptionAdmissible step = isNbExceptionPreserving step

occupancy-engine-sort-leaf-admissible : isNbExceptionAdmissible occupancyEngineSortLeaf ≡ true
occupancy-engine-sort-leaf-admissible = refl

dblock-exception-leaf-admissible : isNbExceptionAdmissible dBlockExceptionLeaf ≡ true
dblock-exception-leaf-admissible = refl

continuum-witness-leaf-admissible : isNbExceptionAdmissible continuumWitnessLeaf ≡ true
continuum-witness-leaf-admissible = refl

named-cu-exception-nuance-admissible : isNbExceptionAdmissible namedNbExceptionNuanceProduct ≡ true
named-cu-exception-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isNbExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-witness-refuse :
  isNbExceptionAdmissible (xorMutuallyExclusiveOp dBlockExceptionLeaf continuumWitnessLeaf) ≡ false
xor-mutually-exclusive-continuum-witness-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data NbExceptionWitnessPresence : Set where
  cu-exception-witness-absent cu-exception-witness-present : NbExceptionWitnessPresence

record ClassifierNbExceptionWitness : Set where
  constructor mkClassifierNbExceptionWitness
  field
    witness-presence : NbExceptionWitnessPresence
    catalysis-gap-total : ℕ

nbExceptionWitnessAbsent : ClassifierNbExceptionWitness
nbExceptionWitnessAbsent = mkClassifierNbExceptionWitness cu-exception-witness-absent zero

nbExceptionWitnessPresentZeroGap : ClassifierNbExceptionWitness
nbExceptionWitnessPresentZeroGap = mkClassifierNbExceptionWitness cu-exception-witness-present zero

nbExceptionWitnessPresentWithGaps : ℕ → ClassifierNbExceptionWitness
nbExceptionWitnessPresentWithGaps n = mkClassifierNbExceptionWitness cu-exception-witness-present n

nbExceptionWitnessGapFree : ClassifierNbExceptionWitness → Bool
nbExceptionWitnessGapFree (mkClassifierNbExceptionWitness cu-exception-witness-absent _) = false
nbExceptionWitnessGapFree (mkClassifierNbExceptionWitness cu-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

cu-exception-witness-present-zero-gap-free :
  nbExceptionWitnessGapFree nbExceptionWitnessPresentZeroGap ≡ true
cu-exception-witness-present-zero-gap-free = refl

cu-exception-witness-absent-not-gap-free :
  nbExceptionWitnessGapFree nbExceptionWitnessAbsent ≡ false
cu-exception-witness-absent-not-gap-free = refl

cu-exception-witness-with-gaps-not-gap-free :
  ∀ n → nbExceptionWitnessGapFree (nbExceptionWitnessPresentWithGaps (suc n)) ≡ false
cu-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-NbException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data NbExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-cu-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : NbExceptionContinuumVerdict

nbExceptionContinuumVerdictOk : NbExceptionContinuumVerdict → Bool
nbExceptionContinuumVerdictOk verdict-unwired-ok = true
nbExceptionContinuumVerdictOk verdict-cu-exception-admissible-ok = true
nbExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
nbExceptionContinuumVerdictOk _ = false

evaluateNbExceptionContinuumClose :
  NbExceptionContinuumModality → ClassifierNbExceptionStep → ClassifierNbExceptionWitness
  → NbExceptionBundleWitness → Bool → NbExceptionContinuumVerdict
evaluateNbExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateNbExceptionContinuumClose nb-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateNbExceptionContinuumClose nb-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateNbExceptionContinuumClose nb-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateNbExceptionContinuumClose nb-exception-continuum-proved _ (mkClassifierNbExceptionWitness cu-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateNbExceptionContinuumClose nb-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateNbExceptionContinuumClose nb-exception-continuum-proved _ (mkClassifierNbExceptionWitness cu-exception-witness-present _) w false
  with nbExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-cu-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without nb-exception-continuum witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-unwired namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-assumed namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-surrogate namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  nbExceptionContinuumVerdictOk
    (evaluateNbExceptionContinuumClose nb-exception-continuum-unwired namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false)
    ≡ true
  × nbExceptionContinuumVerdictOk
      (evaluateNbExceptionContinuumClose nb-exception-continuum-assumed namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false)
      ≡ true
  × nbExceptionContinuumVerdictOk
      (evaluateNbExceptionContinuumClose nb-exception-continuum-surrogate namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without nb-exception-continuum witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  nbExceptionContinuumVerdictOk
    (evaluateNbExceptionContinuumClose
       nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false ≡
  verdict-cu-exception-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  nbExceptionContinuumVerdictOk
    (evaluateNbExceptionContinuumClose
       nb-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
       nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-nb-exception-continuum — nuance **product** closed
------------------------------------------------------------------------

cu-exception-admissible-ok :
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-cu-exception-admissible-ok
cu-exception-admissible-ok = refl

cu-exception-admissible-verdict-ok :
  nbExceptionContinuumVerdictOk
    (evaluateNbExceptionContinuumClose
       nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
cu-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — nb-exception-continuum nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  nbExceptionContinuumVerdictOk
    (evaluateNbExceptionContinuumClose
       nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-nbExceptionContinuum-proved :
  nbExceptionContinuumVerdictOk
    (evaluateNbExceptionContinuumClose
       nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness false)
    ≡ true
  × nbExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-nbExceptionContinuum-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateNbExceptionContinuumClose
    nb-exception-continuum-unwired namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  nbExceptionContinuumVerdictOk
    (evaluateNbExceptionContinuumClose
       nb-exception-continuum-unwired namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

nbExceptionContinuumFiberOk : FormalFiber → Bool
nbExceptionContinuumFiberOk fiber-quantum-knowing = true
nbExceptionContinuumFiberOk fiber-meso-acting = false

nb-exception-continuum-knowing-fiber-ok :
  nbExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
nb-exception-continuum-knowing-fiber-ok = refl

nb-exception-continuum-meso-acting-not-ok :
  nbExceptionContinuumFiberOk fiber-meso-acting ≡ false
nb-exception-continuum-meso-acting-not-ok = refl

nb-exception-continuum-routes-knowing-not-meso :
  nbExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  nbExceptionContinuumFiberOk fiber-meso-acting ≡ false
nb-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  nbExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (nbExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not occupancy-engine sort Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

nb-exception-continuum-not-proved : nbExceptionContinuumProved ≡ false
nb-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

catalysis-second-law-conservation-framed : nbExceptionSecondLawConservationFramed ≡ true
catalysis-second-law-conservation-framed = refl

cu-exception-not-xor-pin : nbExceptionNotXor ≡ true
cu-exception-not-xor-pin = cu-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-cu-exception-axiom-minted-pin : notParallelNbExceptionAxiomMinted ≡ true
not-parallel-cu-exception-axiom-minted-pin = refl

continuum-not-forked-pin : continuumNotForked ≡ true
continuum-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel nb-exception-continuum axiom fork)
------------------------------------------------------------------------

nbExceptionContinuumAxiom :
  (nbExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (nbExceptionSecondLawConservationFramed ≡ true)
  × (nbExceptionNotXor ≡ true)
  × (evaluateNbExceptionContinuumClose nb-exception-continuum-unwired namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateNbExceptionContinuumClose nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessAbsent nbExceptionNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateNbExceptionContinuumClose nb-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateNbExceptionContinuumClose nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-cu-exception-admissible-ok)
  × (evaluateNbExceptionContinuumClose nb-exception-continuum-proved namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (nbExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (nbExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (nbExceptionContinuumVerdictOk (evaluateNbExceptionContinuumClose nb-exception-continuum-unwired namedNbExceptionNuanceProduct nbExceptionWitnessPresentZeroGap nbExceptionNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp nbExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a nbExceptionIdentity) ≡ true)
  × (isNbExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (occupancyEngineSortTagIndex ≡ 41)
  × (NbExceptionBundleWitness.present-count nbExceptionNuanceWitness ≡ 3)
  × (elementAtomicZ niobium ≡ 41)
  × (elementAtomicZ tantalum ≡ 73)
nbExceptionContinuumAxiom =
  nb-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , catalysis-second-law-conservation-framed
  , cu-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , cu-exception-admissible-ok
  , concurrent-product-ok
  , nb-exception-continuum-knowing-fiber-ok
  , nb-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , occupancy-engine-sort-tag-index
  , cu-exception-nuance-present-count
  , niobium-z-41
  , tantalum-z-73

nbExceptionContinuumNamed : String
nbExceptionContinuumNamed =
  "nbExceptionContinuum: Nb Z=41 occupancy-engine sort exception continuum conservation concurrent Pi_c identity conserved Interact restriction not extra force occupancy-engine sort concurrent product identity conserved present ge 2 product not XOR interact restriction typed no parallel nb-exception-continuum axiom not extra force"

nbExceptionContinuumCrossWitnessAuthority : String
nbExceptionContinuumCrossWitnessAuthority =
  "umst/umst-chem/src/occupancy_engine_sort.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

z041NbAuthority : String
z041NbAuthority =
  "umst/umst-chem/src/elements/z_041_nb.rs"

occupancyExceptionSetsAuthority : String
occupancyExceptionSetsAuthority =
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"

nbExceptionContinuumCellId : String
nbExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-NB-EXCEPTION-CONTINUUM"

nbExceptionContinuumNonClaim : String
nbExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-NB-EXCEPTION-CONTINUUM Nb Z=41 occupancy-engine sort exception continuum conservation concurrent Pi_c identity conserved Interact restriction not extra force occupancy-engine sort product not XOR interact restriction typed no parallel nb-exception-continuum axiom not extra force XOR mutually exclusive refuse nb-exception-continuum nuance witness concurrent nbExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite occupancy_engine_sort.rs l0_tables nb-exception-continuum not fork not physics GREEN not production_wired"

nb-exception-continuum-cell-id :
  nbExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-NB-EXCEPTION-CONTINUUM"
nb-exception-continuum-cell-id = refl

nb-exception-continuum-cites-catalysis-barrier-rs :
  nbExceptionContinuumCrossWitnessAuthority ≡
  "umst/umst-chem/src/occupancy_engine_sort.rs"
nb-exception-continuum-cites-catalysis-barrier-rs = refl

nb-exception-continuum-cites-l0-table-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
nb-exception-continuum-cites-l0-table-rs = refl

nb-exception-continuum-modality-unwired :
  nbExceptionContinuumModalityCurrent ≡ nb-exception-continuum-unwired
nb-exception-continuum-modality-unwired = refl

nbExceptionContinuumPhysicsGreenAuthorized : Set
nbExceptionContinuumPhysicsGreenAuthorized = ⊥

nb-exception-continuum-physics-green-false : ¬ nbExceptionContinuumPhysicsGreenAuthorized
nb-exception-continuum-physics-green-false ()

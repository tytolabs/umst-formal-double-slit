-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.CuExceptionContinuum.agda
--
-- Cu Z=29 **occupancy-engine sort** exception **continuum** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort + dblock exception + continuum witness;
--     **product** not XOR, no parallel cu-exception-continuum axiom)
--   * XOR mutually-exclusive refuse; cu-exception nuance witness concurrent
--     (occupancy-engine sort + dblock exception + continuum witness)
--   * **occupancy-engine sort** laws Unwired (cuExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_029_cu.rs
-- Sibling: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel cu-exception-continuum axiom; continuum not forked. Product not XOR.
-- Cu Z=29 d-block Madelung exception as occupancy-engine sort theorem, not extra force.
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

module ChemConstants.CuExceptionContinuum where

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
-- Modality + Cu Z=29 occupancy-engine sort exception continuum pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data CuExceptionContinuumModality : Set where
  cu-exception-continuum-unwired cu-exception-continuum-assumed
    cu-exception-continuum-proved cu-exception-continuum-surrogate
    : CuExceptionContinuumModality

cuExceptionContinuumModalityCurrent : CuExceptionContinuumModality
cuExceptionContinuumModalityCurrent = cu-exception-continuum-unwired

cuExceptionContinuumProved productionWired not118SquaredGreenTable
  cuExceptionSecondLawConservationFramed cuExceptionNotXor : Bool
cuExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
cuExceptionSecondLawConservationFramed = true
cuExceptionNotXor = true

occupancyEngineSortTyped notParallelCuExceptionAxiomMinted continuumNotForked : Bool
occupancyEngineSortTyped = true
notParallelCuExceptionAxiomMinted = true
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
occupancyEngineSortTagIndex = 29

occupancy-engine-sort-tag-index : occupancyEngineSortTagIndex ≡ 29
occupancy-engine-sort-tag-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Cu (Z=29), Ag (Z=47) d-block exception siblings
------------------------------------------------------------------------

data ElementTag : Set where
  copper silver : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ copper = 29
elementAtomicZ silver = 47

copper-z-29 : elementAtomicZ copper ≡ 29
copper-z-29 = refl

silver-z-47 : elementAtomicZ silver ≡ 47
silver-z-47 = refl

------------------------------------------------------------------------
-- CuExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data CuExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : CuExceptionBundleSlot

isSlotPresent : CuExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- CuExceptionBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record CuExceptionBundle : Set where
  field slot : ℕ → CuExceptionBundleSlot

cuExceptionBundleUnwired : CuExceptionBundle
cuExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : CuExceptionBundle → ℕ → CuExceptionBundleSlot → CuExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else CuExceptionBundle.slot b j }

withPresent : CuExceptionBundle → ℕ → CuExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record CuExceptionBundleWitness : Set where
  constructor mkCuExceptionBundleWitness
  field
    bundle : CuExceptionBundle
    present-count : ℕ

cuExceptionBundleIsConcurrentProduct : CuExceptionBundleWitness → Bool
cuExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? CuExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named cu-exception-continuum channel indices — interact restriction (1), not extra force (2), occupancy-engine sort (3)
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
-- CuException nuance witness — interact restriction + not extra force + occupancy-engine sort concurrent
------------------------------------------------------------------------

cuExceptionNuanceBundle : CuExceptionBundle
cuExceptionNuanceBundle =
  withPresent
    (withPresent
      (withPresent cuExceptionBundleUnwired occupancyEngineSortChannelIndex)
      dBlockExceptionChannelIndex)
    continuumWitnessChannelIndex

cuExceptionNuanceWitness : CuExceptionBundleWitness
cuExceptionNuanceWitness =
  mkCuExceptionBundleWitness cuExceptionNuanceBundle 3

cu-exception-nuance-occupancy-engine-sort-present :
  isSlotPresent (CuExceptionBundle.slot cuExceptionNuanceBundle occupancyEngineSortChannelIndex) ≡ true
cu-exception-nuance-occupancy-engine-sort-present = refl

cu-exception-nuance-dblock-exception-present :
  isSlotPresent (CuExceptionBundle.slot cuExceptionNuanceBundle dBlockExceptionChannelIndex) ≡ true
cu-exception-nuance-dblock-exception-present = refl

cu-exception-nuance-continuum-witness-present :
  isSlotPresent (CuExceptionBundle.slot cuExceptionNuanceBundle continuumWitnessChannelIndex) ≡ true
cu-exception-nuance-continuum-witness-present = refl

cu-exception-nuance-present-count : CuExceptionBundleWitness.present-count cuExceptionNuanceWitness ≡ 3
cu-exception-nuance-present-count = refl

cu-exception-nuance-concurrent-product :
  cuExceptionBundleIsConcurrentProduct cuExceptionNuanceWitness ≡ true
cu-exception-nuance-concurrent-product = refl

cu-exception-nuance-three-factors-concurrent :
  isSlotPresent (CuExceptionBundle.slot cuExceptionNuanceBundle occupancyEngineSortChannelIndex) ≡ true
  × isSlotPresent (CuExceptionBundle.slot cuExceptionNuanceBundle dBlockExceptionChannelIndex) ≡ true
  × isSlotPresent (CuExceptionBundle.slot cuExceptionNuanceBundle continuumWitnessChannelIndex) ≡ true
  × CuExceptionBundleWitness.present-count cuExceptionNuanceWitness ≡ 3
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

evaluateXorRefuse : CuExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if cuExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = CuExceptionBundleWitness.bundle w
       in if isSlotPresent (CuExceptionBundle.slot b i)
          then if isSlotPresent (CuExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : CuExceptionBundleWitness
unwiredWitness = mkCuExceptionBundleWitness cuExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

cu-exception-nuance-xor-product-ok :
  evaluateXorRefuse cuExceptionNuanceWitness occupancyEngineSortChannelIndex dBlockExceptionChannelIndex ≡ xor-product-ok
cu-exception-nuance-xor-product-ok = refl

cu-exception-not-xor : cuExceptionNotXor ≡ true
cu-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierCuExceptionStep scaffold — CuExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierCuExceptionStep : Set where
  cu-exception-identity : ClassifierCuExceptionStep
  slot-leaf : ℕ → ClassifierCuExceptionStep
  product-concurrent : ClassifierCuExceptionStep → ClassifierCuExceptionStep → ClassifierCuExceptionStep
  xor-mutually-exclusive : ClassifierCuExceptionStep → ClassifierCuExceptionStep → ClassifierCuExceptionStep

cuExceptionIdentity : ClassifierCuExceptionStep
cuExceptionIdentity = cu-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierCuExceptionStep → ClassifierCuExceptionStep → ClassifierCuExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortLeaf dBlockExceptionLeaf continuumWitnessLeaf : ClassifierCuExceptionStep
occupancyEngineSortLeaf = slot-leaf occupancyEngineSortChannelIndex
dBlockExceptionLeaf = slot-leaf dBlockExceptionChannelIndex
continuumWitnessLeaf = slot-leaf continuumWitnessChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierCuExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isCuExceptionIdentity : ClassifierCuExceptionStep → Bool
isCuExceptionIdentity cu-exception-identity = true
isCuExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at cu-exception-identity
------------------------------------------------------------------------

cu-exception-left-identity :
  ∀ (a : ClassifierCuExceptionStep) →
  isCuExceptionIdentity cuExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp cuExceptionIdentity a) ≡ true
cu-exception-left-identity a = refl , refl

cu-exception-right-identity :
  ∀ (a : ClassifierCuExceptionStep) →
  isProductConcurrent (productConcurrentOp a cuExceptionIdentity) ≡ true
  × isCuExceptionIdentity cuExceptionIdentity ≡ true
cu-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-cu-exception :
  (∀ a → isProductConcurrent (productConcurrentOp cuExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a cuExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-cu-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named cu-exception-continuum nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedCuExceptionNuanceProduct : ClassifierCuExceptionStep
namedCuExceptionNuanceProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    continuumWitnessLeaf

named-cu-exception-nuance-product-concurrent :
  isProductConcurrent namedCuExceptionNuanceProduct ≡ true
  × cuExceptionBundleIsConcurrentProduct cuExceptionNuanceWitness ≡ true
named-cu-exception-nuance-product-concurrent = refl , cu-exception-nuance-concurrent-product

------------------------------------------------------------------------
-- CuExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data CuExceptionAdmissibility : Set where
  cu-exception-admissible cu-exception-xor-refuse : CuExceptionAdmissibility

isCuExceptionPreserving : ClassifierCuExceptionStep → Bool
isCuExceptionPreserving cu-exception-identity = true
isCuExceptionPreserving (slot-leaf _) = true
isCuExceptionPreserving (product-concurrent a b) =
  isCuExceptionPreserving a ∧ isCuExceptionPreserving b
isCuExceptionPreserving (xor-mutually-exclusive _ _) = false

isCuExceptionAdmissible : ClassifierCuExceptionStep → Bool
isCuExceptionAdmissible step = isCuExceptionPreserving step

occupancy-engine-sort-leaf-admissible : isCuExceptionAdmissible occupancyEngineSortLeaf ≡ true
occupancy-engine-sort-leaf-admissible = refl

dblock-exception-leaf-admissible : isCuExceptionAdmissible dBlockExceptionLeaf ≡ true
dblock-exception-leaf-admissible = refl

continuum-witness-leaf-admissible : isCuExceptionAdmissible continuumWitnessLeaf ≡ true
continuum-witness-leaf-admissible = refl

named-cu-exception-nuance-admissible : isCuExceptionAdmissible namedCuExceptionNuanceProduct ≡ true
named-cu-exception-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isCuExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-witness-refuse :
  isCuExceptionAdmissible (xorMutuallyExclusiveOp dBlockExceptionLeaf continuumWitnessLeaf) ≡ false
xor-mutually-exclusive-continuum-witness-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data CuExceptionWitnessPresence : Set where
  cu-exception-witness-absent cu-exception-witness-present : CuExceptionWitnessPresence

record ClassifierCuExceptionWitness : Set where
  constructor mkClassifierCuExceptionWitness
  field
    witness-presence : CuExceptionWitnessPresence
    cu-exception-gap-total : ℕ

cuExceptionWitnessAbsent : ClassifierCuExceptionWitness
cuExceptionWitnessAbsent = mkClassifierCuExceptionWitness cu-exception-witness-absent zero

cuExceptionWitnessPresentZeroGap : ClassifierCuExceptionWitness
cuExceptionWitnessPresentZeroGap = mkClassifierCuExceptionWitness cu-exception-witness-present zero

cuExceptionWitnessPresentWithGaps : ℕ → ClassifierCuExceptionWitness
cuExceptionWitnessPresentWithGaps n = mkClassifierCuExceptionWitness cu-exception-witness-present n

cuExceptionWitnessGapFree : ClassifierCuExceptionWitness → Bool
cuExceptionWitnessGapFree (mkClassifierCuExceptionWitness cu-exception-witness-absent _) = false
cuExceptionWitnessGapFree (mkClassifierCuExceptionWitness cu-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

cu-exception-witness-present-zero-gap-free :
  cuExceptionWitnessGapFree cuExceptionWitnessPresentZeroGap ≡ true
cu-exception-witness-present-zero-gap-free = refl

cu-exception-witness-absent-not-gap-free :
  cuExceptionWitnessGapFree cuExceptionWitnessAbsent ≡ false
cu-exception-witness-absent-not-gap-free = refl

cu-exception-witness-with-gaps-not-gap-free :
  ∀ n → cuExceptionWitnessGapFree (cuExceptionWitnessPresentWithGaps (suc n)) ≡ false
cu-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-CuException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data CuExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-cu-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : CuExceptionContinuumVerdict

cuExceptionContinuumVerdictOk : CuExceptionContinuumVerdict → Bool
cuExceptionContinuumVerdictOk verdict-unwired-ok = true
cuExceptionContinuumVerdictOk verdict-cu-exception-admissible-ok = true
cuExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
cuExceptionContinuumVerdictOk _ = false

evaluateCuExceptionContinuumClose :
  CuExceptionContinuumModality → ClassifierCuExceptionStep → ClassifierCuExceptionWitness
  → CuExceptionBundleWitness → Bool → CuExceptionContinuumVerdict
evaluateCuExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateCuExceptionContinuumClose cu-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateCuExceptionContinuumClose cu-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateCuExceptionContinuumClose cu-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateCuExceptionContinuumClose cu-exception-continuum-proved _ (mkClassifierCuExceptionWitness cu-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateCuExceptionContinuumClose cu-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateCuExceptionContinuumClose cu-exception-continuum-proved _ (mkClassifierCuExceptionWitness cu-exception-witness-present _) w false
  with cuExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-cu-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without cu-exception-continuum witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-unwired namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-assumed namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-surrogate namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  cuExceptionContinuumVerdictOk
    (evaluateCuExceptionContinuumClose cu-exception-continuum-unwired namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false)
    ≡ true
  × cuExceptionContinuumVerdictOk
      (evaluateCuExceptionContinuumClose cu-exception-continuum-assumed namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false)
      ≡ true
  × cuExceptionContinuumVerdictOk
      (evaluateCuExceptionContinuumClose cu-exception-continuum-surrogate namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without cu-exception-continuum witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  cuExceptionContinuumVerdictOk
    (evaluateCuExceptionContinuumClose
       cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false ≡
  verdict-cu-exception-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  cuExceptionContinuumVerdictOk
    (evaluateCuExceptionContinuumClose
       cu-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
       cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-cu-exception-continuum — nuance **product** closed
------------------------------------------------------------------------

cu-exception-admissible-ok :
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-cu-exception-admissible-ok
cu-exception-admissible-ok = refl

cu-exception-admissible-verdict-ok :
  cuExceptionContinuumVerdictOk
    (evaluateCuExceptionContinuumClose
       cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
cu-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — cu-exception-continuum nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  cuExceptionContinuumVerdictOk
    (evaluateCuExceptionContinuumClose
       cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-cuExceptionContinuum-proved :
  cuExceptionContinuumVerdictOk
    (evaluateCuExceptionContinuumClose
       cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness false)
    ≡ true
  × cuExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-cuExceptionContinuum-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateCuExceptionContinuumClose
    cu-exception-continuum-unwired namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  cuExceptionContinuumVerdictOk
    (evaluateCuExceptionContinuumClose
       cu-exception-continuum-unwired namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

cuExceptionContinuumFiberOk : FormalFiber → Bool
cuExceptionContinuumFiberOk fiber-quantum-knowing = true
cuExceptionContinuumFiberOk fiber-meso-acting = false

cu-exception-continuum-knowing-fiber-ok :
  cuExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
cu-exception-continuum-knowing-fiber-ok = refl

cu-exception-continuum-meso-acting-not-ok :
  cuExceptionContinuumFiberOk fiber-meso-acting ≡ false
cu-exception-continuum-meso-acting-not-ok = refl

cu-exception-continuum-routes-knowing-not-meso :
  cuExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  cuExceptionContinuumFiberOk fiber-meso-acting ≡ false
cu-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  cuExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (cuExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not occupancy-engine sort Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

cu-exception-continuum-not-proved : cuExceptionContinuumProved ≡ false
cu-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

cu-exception-second-law-conservation-framed : cuExceptionSecondLawConservationFramed ≡ true
cu-exception-second-law-conservation-framed = refl

cu-exception-not-xor-pin : cuExceptionNotXor ≡ true
cu-exception-not-xor-pin = cu-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-cu-exception-axiom-minted-pin : notParallelCuExceptionAxiomMinted ≡ true
not-parallel-cu-exception-axiom-minted-pin = refl

continuum-not-forked-pin : continuumNotForked ≡ true
continuum-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel cu-exception-continuum axiom fork)
------------------------------------------------------------------------

cuExceptionContinuumAxiom :
  (cuExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (cuExceptionSecondLawConservationFramed ≡ true)
  × (cuExceptionNotXor ≡ true)
  × (evaluateCuExceptionContinuumClose cu-exception-continuum-unwired namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateCuExceptionContinuumClose cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessAbsent cuExceptionNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateCuExceptionContinuumClose cu-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateCuExceptionContinuumClose cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-cu-exception-admissible-ok)
  × (evaluateCuExceptionContinuumClose cu-exception-continuum-proved namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (cuExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (cuExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (cuExceptionContinuumVerdictOk (evaluateCuExceptionContinuumClose cu-exception-continuum-unwired namedCuExceptionNuanceProduct cuExceptionWitnessPresentZeroGap cuExceptionNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp cuExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a cuExceptionIdentity) ≡ true)
  × (isCuExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (occupancyEngineSortTagIndex ≡ 29)
  × (CuExceptionBundleWitness.present-count cuExceptionNuanceWitness ≡ 3)
  × (elementAtomicZ copper ≡ 29)
  × (elementAtomicZ silver ≡ 47)
cuExceptionContinuumAxiom =
  cu-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , cu-exception-second-law-conservation-framed
  , cu-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , cu-exception-admissible-ok
  , concurrent-product-ok
  , cu-exception-continuum-knowing-fiber-ok
  , cu-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , occupancy-engine-sort-tag-index
  , cu-exception-nuance-present-count
  , copper-z-29
  , silver-z-47

cuExceptionContinuumNamed : String
cuExceptionContinuumNamed =
  "cuExceptionContinuum: Cu Z=29 occupancy-engine sort exception continuum conservation concurrent Pi_c identity conserved Interact restriction not extra force occupancy-engine sort concurrent product identity conserved present ge 2 product not XOR interact restriction typed no parallel cu-exception-continuum axiom not extra force"

cuExceptionContinuumCrossWitnessAuthority : String
cuExceptionContinuumCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

z029CuAuthority : String
z029CuAuthority =
  "umst/umst-chem/src/elements/z_029_cu.rs"

occupancyExceptionSetsAuthority : String
occupancyExceptionSetsAuthority =
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"

cuExceptionContinuumCellId : String
cuExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-CU-EXCEPTION-CONTINUUM"

cuExceptionContinuumNonClaim : String
cuExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-CU-EXCEPTION-CONTINUUM Cu Z=29 occupancy-engine sort exception continuum conservation concurrent Pi_c identity conserved Interact restriction not extra force occupancy-engine sort product not XOR interact restriction typed no parallel cu-exception-continuum axiom not extra force XOR mutually exclusive refuse cu-exception-continuum nuance witness concurrent cuExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite occupancy_engine_sort.rs l0_tables cu-exception-continuum not fork not physics GREEN not production_wired"

cu-exception-continuum-cell-id :
  cuExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-CU-EXCEPTION-CONTINUUM"
cu-exception-continuum-cell-id = refl

cu-exception-continuum-cites-occupancy-engine-sort-rs :
  cuExceptionContinuumCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
cu-exception-continuum-cites-occupancy-engine-sort-rs = refl

cu-exception-continuum-cites-z029-cu-rs :
  z029CuAuthority ≡
  "umst/umst-chem/src/elements/z_029_cu.rs"
cu-exception-continuum-cites-z029-cu-rs = refl

cu-exception-continuum-modality-unwired :
  cuExceptionContinuumModalityCurrent ≡ cu-exception-continuum-unwired
cu-exception-continuum-modality-unwired = refl

cuExceptionContinuumPhysicsGreenAuthorized : Set
cuExceptionContinuumPhysicsGreenAuthorized = ⊥

cu-exception-continuum-physics-green-false : ¬ cuExceptionContinuumPhysicsGreenAuthorized
cu-exception-continuum-physics-green-false ()

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.SharedConservation.agda
--
-- Pattern class 1 **Shared** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (CEF + QTAIM + CAT-02 pullback; **product** not XOR)
--   * XOR mutually-exclusive refuse; shared nuance witness concurrent
--     (CEF sublattice + QTAIM bond paths + CAT-02 pullback)
--   * **shared** laws Unwired (shared01Proved = false)
--
-- INT: umst/umst-chem/src/x_rows/shared_conservation.rs (read-only cite)
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.SharedConservation where

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
-- Modality + pattern class 1 **Shared** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data SharedConservationModality : Set where
  shared-conservation-unwired shared-conservation-assumed
    shared-conservation-proved shared-conservation-surrogate
    : SharedConservationModality

sharedConservationModalityCurrent : SharedConservationModality
sharedConservationModalityCurrent = shared-conservation-unwired

shared01Proved productionWired not118SquaredGreenTable
  sharedSecondLawConservationFramed sharedNotXor : Bool
shared01Proved = false
productionWired = false
not118SquaredGreenTable = true
sharedSecondLawConservationFramed = true
sharedNotXor = true

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
-- Pattern class 1 Shared index pin
------------------------------------------------------------------------

sharedClassIndex : ℕ
sharedClassIndex = 1

shared-class-index-one : sharedClassIndex ≡ 1
shared-class-index-one = refl

------------------------------------------------------------------------
-- Named element Z pins — H (Z=1), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  hydrogen oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ hydrogen = 1
elementAtomicZ oganesson = 118

hydrogen-z-1 : elementAtomicZ hydrogen ≡ 1
hydrogen-z-1 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- SharedBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data SharedBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : SharedBundleSlot

isSlotPresent : SharedBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- SharedBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record SharedBundle : Set where
  field slot : ℕ → SharedBundleSlot

sharedBundleUnwired : SharedBundle
sharedBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : SharedBundle → ℕ → SharedBundleSlot → SharedBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else SharedBundle.slot b j }

withPresent : SharedBundle → ℕ → SharedBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record SharedBundleWitness : Set where
  constructor mkSharedBundleWitness
  field
    bundle : SharedBundle
    present-count : ℕ

sharedBundleIsConcurrentProduct : SharedBundleWitness → Bool
sharedBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? SharedBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named shared channel indices — CEF (1), QTAIM (2), CAT-02 pullback (3)
------------------------------------------------------------------------

cefSublatticeChannelIndex qtaimBondPathsChannelIndex cat02PullbackChannelIndex : ℕ
cefSublatticeChannelIndex = 1
qtaimBondPathsChannelIndex = 2
cat02PullbackChannelIndex = 3

cef-sublattice-index-one : cefSublatticeChannelIndex ≡ 1
cef-sublattice-index-one = refl

qtaim-bond-paths-index-two : qtaimBondPathsChannelIndex ≡ 2
qtaim-bond-paths-index-two = refl

cat02-pullback-index-three : cat02PullbackChannelIndex ≡ 3
cat02-pullback-index-three = refl

------------------------------------------------------------------------
-- Shared nuance witness — CEF + QTAIM + CAT-02 pullback concurrent
------------------------------------------------------------------------

sharedNuanceBundle : SharedBundle
sharedNuanceBundle =
  withPresent
    (withPresent
      (withPresent sharedBundleUnwired cefSublatticeChannelIndex)
      qtaimBondPathsChannelIndex)
    cat02PullbackChannelIndex

sharedNuanceWitness : SharedBundleWitness
sharedNuanceWitness =
  mkSharedBundleWitness sharedNuanceBundle 3

shared-nuance-cef-present :
  isSlotPresent (SharedBundle.slot sharedNuanceBundle cefSublatticeChannelIndex) ≡ true
shared-nuance-cef-present = refl

shared-nuance-qtaim-present :
  isSlotPresent (SharedBundle.slot sharedNuanceBundle qtaimBondPathsChannelIndex) ≡ true
shared-nuance-qtaim-present = refl

shared-nuance-cat02-present :
  isSlotPresent (SharedBundle.slot sharedNuanceBundle cat02PullbackChannelIndex) ≡ true
shared-nuance-cat02-present = refl

shared-nuance-present-count : SharedBundleWitness.present-count sharedNuanceWitness ≡ 3
shared-nuance-present-count = refl

shared-nuance-concurrent-product :
  sharedBundleIsConcurrentProduct sharedNuanceWitness ≡ true
shared-nuance-concurrent-product = refl

shared-nuance-three-factors-concurrent :
  isSlotPresent (SharedBundle.slot sharedNuanceBundle cefSublatticeChannelIndex) ≡ true
  × isSlotPresent (SharedBundle.slot sharedNuanceBundle qtaimBondPathsChannelIndex) ≡ true
  × isSlotPresent (SharedBundle.slot sharedNuanceBundle cat02PullbackChannelIndex) ≡ true
  × SharedBundleWitness.present-count sharedNuanceWitness ≡ 3
shared-nuance-three-factors-concurrent =
  shared-nuance-cef-present
  , shared-nuance-qtaim-present
  , shared-nuance-cat02-present
  , shared-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : SharedBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if sharedBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = SharedBundleWitness.bundle w
       in if isSlotPresent (SharedBundle.slot b i)
          then if isSlotPresent (SharedBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : SharedBundleWitness
unwiredWitness = mkSharedBundleWitness sharedBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

shared-nuance-xor-product-ok :
  evaluateXorRefuse sharedNuanceWitness cefSublatticeChannelIndex qtaimBondPathsChannelIndex ≡ xor-product-ok
shared-nuance-xor-product-ok = refl

shared-not-xor : sharedNotXor ≡ true
shared-not-xor = refl

------------------------------------------------------------------------
-- ClassifierSharedStep scaffold — SharedBundle **conservation**
------------------------------------------------------------------------

data ClassifierSharedStep : Set where
  shared-identity : ClassifierSharedStep
  slot-leaf : ℕ → ClassifierSharedStep
  product-concurrent : ClassifierSharedStep → ClassifierSharedStep → ClassifierSharedStep
  xor-mutually-exclusive : ClassifierSharedStep → ClassifierSharedStep → ClassifierSharedStep

sharedIdentity : ClassifierSharedStep
sharedIdentity = shared-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierSharedStep → ClassifierSharedStep → ClassifierSharedStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

cefLeaf qtaimLeaf cat02Leaf : ClassifierSharedStep
cefLeaf = slot-leaf cefSublatticeChannelIndex
qtaimLeaf = slot-leaf qtaimBondPathsChannelIndex
cat02Leaf = slot-leaf cat02PullbackChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierSharedStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isSharedIdentity : ClassifierSharedStep → Bool
isSharedIdentity shared-identity = true
isSharedIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at shared-identity
------------------------------------------------------------------------

shared-left-identity :
  ∀ (a : ClassifierSharedStep) →
  isSharedIdentity sharedIdentity ≡ true
  × isProductConcurrent (productConcurrentOp sharedIdentity a) ≡ true
shared-left-identity a = refl , refl

shared-right-identity :
  ∀ (a : ClassifierSharedStep) →
  isProductConcurrent (productConcurrentOp a sharedIdentity) ≡ true
  × isSharedIdentity sharedIdentity ≡ true
shared-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-shared :
  (∀ a → isProductConcurrent (productConcurrentOp sharedIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a sharedIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-shared =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named shared nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedSharedNuanceProduct : ClassifierSharedStep
namedSharedNuanceProduct =
  productConcurrentOp
    (productConcurrentOp cefLeaf qtaimLeaf)
    cat02Leaf

named-shared-nuance-product-concurrent :
  isProductConcurrent namedSharedNuanceProduct ≡ true
  × sharedBundleIsConcurrentProduct sharedNuanceWitness ≡ true
named-shared-nuance-product-concurrent = refl , shared-nuance-concurrent-product

------------------------------------------------------------------------
-- SharedBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data SharedAdmissibility : Set where
  shared-admissible shared-xor-refuse : SharedAdmissibility

isSharedPreserving : ClassifierSharedStep → Bool
isSharedPreserving shared-identity = true
isSharedPreserving (slot-leaf _) = true
isSharedPreserving (product-concurrent a b) =
  isSharedPreserving a ∧ isSharedPreserving b
isSharedPreserving (xor-mutually-exclusive _ _) = false

isSharedAdmissible : ClassifierSharedStep → Bool
isSharedAdmissible step = isSharedPreserving step

cef-leaf-admissible : isSharedAdmissible cefLeaf ≡ true
cef-leaf-admissible = refl

qtaim-leaf-admissible : isSharedAdmissible qtaimLeaf ≡ true
qtaim-leaf-admissible = refl

cat02-leaf-admissible : isSharedAdmissible cat02Leaf ≡ true
cat02-leaf-admissible = refl

named-shared-nuance-admissible : isSharedAdmissible namedSharedNuanceProduct ≡ true
named-shared-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isSharedAdmissible (xorMutuallyExclusiveOp cefLeaf qtaimLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-cat02-refuse :
  isSharedAdmissible (xorMutuallyExclusiveOp qtaimLeaf cat02Leaf) ≡ false
xor-mutually-exclusive-cat02-refuse = refl

------------------------------------------------------------------------
-- Shared witness — total-claim refuse without witness
------------------------------------------------------------------------

data SharedWitnessPresence : Set where
  shared-witness-absent shared-witness-present : SharedWitnessPresence

record ClassifierSharedWitness : Set where
  constructor mkClassifierSharedWitness
  field
    witness-presence : SharedWitnessPresence
    shared-gap-total : ℕ

sharedWitnessAbsent : ClassifierSharedWitness
sharedWitnessAbsent = mkClassifierSharedWitness shared-witness-absent zero

sharedWitnessPresentZeroGap : ClassifierSharedWitness
sharedWitnessPresentZeroGap = mkClassifierSharedWitness shared-witness-present zero

sharedWitnessPresentWithGaps : ℕ → ClassifierSharedWitness
sharedWitnessPresentWithGaps n = mkClassifierSharedWitness shared-witness-present n

sharedWitnessGapFree : ClassifierSharedWitness → Bool
sharedWitnessGapFree (mkClassifierSharedWitness shared-witness-absent _) = false
sharedWitnessGapFree (mkClassifierSharedWitness shared-witness-present n) =
  does (n ℕ-Props.≟ zero)

shared-witness-present-zero-gap-free :
  sharedWitnessGapFree sharedWitnessPresentZeroGap ≡ true
shared-witness-present-zero-gap-free = refl

shared-witness-absent-not-gap-free :
  sharedWitnessGapFree sharedWitnessAbsent ≡ false
shared-witness-absent-not-gap-free = refl

shared-witness-with-gaps-not-gap-free :
  ∀ n → sharedWitnessGapFree (sharedWitnessPresentWithGaps (suc n)) ≡ false
shared-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Shared **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data SharedConservationVerdict : Set where
  verdict-unwired-ok verdict-shared-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : SharedConservationVerdict

sharedConservationVerdictOk : SharedConservationVerdict → Bool
sharedConservationVerdictOk verdict-unwired-ok = true
sharedConservationVerdictOk verdict-shared-admissible-ok = true
sharedConservationVerdictOk verdict-concurrent-product-ok = true
sharedConservationVerdictOk _ = false

evaluateSharedConservationClose :
  SharedConservationModality → ClassifierSharedStep → ClassifierSharedWitness
  → SharedBundleWitness → Bool → SharedConservationVerdict
evaluateSharedConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateSharedConservationClose shared-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateSharedConservationClose shared-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateSharedConservationClose shared-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateSharedConservationClose shared-conservation-proved _ (mkClassifierSharedWitness shared-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateSharedConservationClose shared-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateSharedConservationClose shared-conservation-proved _ (mkClassifierSharedWitness shared-witness-present _) w false
  with sharedBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-shared-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without shared witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateSharedConservationClose
    shared-conservation-unwired namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateSharedConservationClose
    shared-conservation-assumed namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateSharedConservationClose
    shared-conservation-surrogate namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  sharedConservationVerdictOk
    (evaluateSharedConservationClose shared-conservation-unwired namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false)
    ≡ true
  × sharedConservationVerdictOk
      (evaluateSharedConservationClose shared-conservation-assumed namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false)
      ≡ true
  × sharedConservationVerdictOk
      (evaluateSharedConservationClose shared-conservation-surrogate namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without shared witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateSharedConservationClose
    shared-conservation-proved namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  sharedConservationVerdictOk
    (evaluateSharedConservationClose
       shared-conservation-proved namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateSharedConservationClose
    shared-conservation-proved namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false ≡
  verdict-shared-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateSharedConservationClose
    shared-conservation-proved
    (xorMutuallyExclusiveOp cefLeaf qtaimLeaf)
    sharedWitnessPresentZeroGap sharedNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  sharedConservationVerdictOk
    (evaluateSharedConservationClose
       shared-conservation-proved
       (xorMutuallyExclusiveOp cefLeaf qtaimLeaf)
       sharedWitnessPresentZeroGap sharedNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateSharedConservationClose
    shared-conservation-proved
    (xorMutuallyExclusiveOp cefLeaf qtaimLeaf)
    sharedWitnessPresentZeroGap sharedNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-shared — shared nuance **product** closed
------------------------------------------------------------------------

shared-admissible-ok :
  evaluateSharedConservationClose
    shared-conservation-proved namedSharedNuanceProduct sharedWitnessPresentZeroGap unwiredWitness false ≡
  verdict-shared-admissible-ok
shared-admissible-ok = refl

shared-admissible-verdict-ok :
  sharedConservationVerdictOk
    (evaluateSharedConservationClose
       shared-conservation-proved namedSharedNuanceProduct sharedWitnessPresentZeroGap unwiredWitness false)
    ≡ true
shared-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — shared nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateSharedConservationClose
    shared-conservation-proved namedSharedNuanceProduct sharedWitnessPresentZeroGap sharedNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  sharedConservationVerdictOk
    (evaluateSharedConservationClose
       shared-conservation-proved namedSharedNuanceProduct sharedWitnessPresentZeroGap sharedNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-shared01-proved :
  sharedConservationVerdictOk
    (evaluateSharedConservationClose
       shared-conservation-proved namedSharedNuanceProduct sharedWitnessPresentZeroGap sharedNuanceWitness false)
    ≡ true
  × shared01Proved ≡ false
concurrent-product-ok-still-not-shared01-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateSharedConservationClose
    shared-conservation-unwired namedSharedNuanceProduct sharedWitnessPresentZeroGap sharedNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  sharedConservationVerdictOk
    (evaluateSharedConservationClose
       shared-conservation-unwired namedSharedNuanceProduct sharedWitnessPresentZeroGap sharedNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

sharedConservationFiberOk : FormalFiber → Bool
sharedConservationFiberOk fiber-quantum-knowing = true
sharedConservationFiberOk fiber-meso-acting = false

shared-conservation-knowing-fiber-ok :
  sharedConservationFiberOk fiber-quantum-knowing ≡ true
shared-conservation-knowing-fiber-ok = refl

shared-conservation-meso-acting-not-ok :
  sharedConservationFiberOk fiber-meso-acting ≡ false
shared-conservation-meso-acting-not-ok = refl

shared-conservation-routes-knowing-not-meso :
  sharedConservationFiberOk fiber-quantum-knowing ≡ true ×
  sharedConservationFiberOk fiber-meso-acting ≡ false
shared-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  sharedConservationFiberOk fiber-quantum-knowing ∧
  not (sharedConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 1 Shared Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

shared01-not-proved : shared01Proved ≡ false
shared01-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

shared-second-law-conservation-framed : sharedSecondLawConservationFramed ≡ true
shared-second-law-conservation-framed = refl

shared-not-xor-pin : sharedNotXor ≡ true
shared-not-xor-pin = shared-not-xor

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second Shared axiom fork)
------------------------------------------------------------------------

sharedConservationAxiom :
  (shared01Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (sharedSecondLawConservationFramed ≡ true)
  × (sharedNotXor ≡ true)
  × (evaluateSharedConservationClose shared-conservation-unwired namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateSharedConservationClose shared-conservation-proved namedSharedNuanceProduct sharedWitnessAbsent sharedNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateSharedConservationClose shared-conservation-proved (xorMutuallyExclusiveOp cefLeaf qtaimLeaf) sharedWitnessPresentZeroGap sharedNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateSharedConservationClose shared-conservation-proved namedSharedNuanceProduct sharedWitnessPresentZeroGap unwiredWitness false ≡ verdict-shared-admissible-ok)
  × (evaluateSharedConservationClose shared-conservation-proved namedSharedNuanceProduct sharedWitnessPresentZeroGap sharedNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (sharedConservationFiberOk fiber-quantum-knowing ≡ true)
  × (sharedConservationFiberOk fiber-meso-acting ≡ false)
  × (sharedConservationVerdictOk (evaluateSharedConservationClose shared-conservation-unwired namedSharedNuanceProduct sharedWitnessPresentZeroGap sharedNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp sharedIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a sharedIdentity) ≡ true)
  × (isSharedAdmissible (xorMutuallyExclusiveOp cefLeaf qtaimLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (sharedClassIndex ≡ 1)
  × (SharedBundleWitness.present-count sharedNuanceWitness ≡ 3)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oganesson ≡ 118)
sharedConservationAxiom =
  shared01-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , shared-second-law-conservation-framed
  , shared-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , shared-admissible-ok
  , concurrent-product-ok
  , shared-conservation-knowing-fiber-ok
  , shared-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , shared-class-index-one
  , shared-nuance-present-count
  , hydrogen-z-1
  , oganesson-z-118

sharedConservationNamed : String
sharedConservationNamed =
  "sharedConservation: pattern class 1 Shared conservation concurrent Pi_c identity conserved CEF QTAIM CAT-02 pullback XOR refuse shared nuance witness concurrent"

sharedConservationCrossWitnessAuthority : String
sharedConservationCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/shared_conservation.rs"

sharedTableAuthority : String
sharedTableAuthority =
  "umst/umst-chem/src/l0_tables/shared.rs"

cefSublatticeAuthority : String
cefSublatticeAuthority =
  "umst/umst-chem/src/cef_sublattice_is_not_species.rs"

cat02PullbackAuthority : String
cat02PullbackAuthority =
  "umst/umst-chem/src/shared_substructure_limits.rs"

sharedConservationCellId : String
sharedConservationCellId = "CHEM-FORMAL-Q-AGDA-SHARED-CONSERVATION"

sharedConservationNonClaim : String
sharedConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-SHARED-CONSERVATION pattern class 1 Shared conservation concurrent Pi_c identity conserved CEF sublattice QTAIM bond paths CAT-02 pullback product not XOR XOR mutually exclusive refuse shared nuance witness concurrent shared01Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite shared_conservation.rs not fork not physics GREEN not production_wired"

shared-conservation-cell-id :
  sharedConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-SHARED-CONSERVATION"
shared-conservation-cell-id = refl

shared-conservation-cites-cross-witness-rs :
  sharedConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/shared_conservation.rs"
shared-conservation-cites-cross-witness-rs = refl

shared-conservation-modality-unwired :
  sharedConservationModalityCurrent ≡ shared-conservation-unwired
shared-conservation-modality-unwired = refl

sharedConservationPhysicsGreenAuthorized : Set
sharedConservationPhysicsGreenAuthorized = ⊥

shared-conservation-physics-green-false : ¬ sharedConservationPhysicsGreenAuthorized
shared-conservation-physics-green-false ()

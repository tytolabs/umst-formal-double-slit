-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.AgExceptionContinuum.agda
--
-- Ag Z=47 **occupancy-engine sort** exception **continuum** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort + dblock exception + continuum witness;
--     **product** not XOR, no parallel ag-exception-continuum axiom)
--   * XOR mutually-exclusive refuse; ag-exception nuance witness concurrent
--     (occupancy-engine sort + dblock exception + continuum witness)
--   * **occupancy-engine sort** laws Unwired (agExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_047_ag.rs
-- Sibling: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel ag-exception-continuum axiom; continuum not forked. Product not XOR.
-- Ag Z=47 d-block Madelung exception as occupancy-engine sort theorem, not extra force.
-- Homolog Cu Z=29 / Au Z=79 ≠ Ag occupancy copy.
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

module ChemConstants.AgExceptionContinuum where

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
-- Modality + Ag Z=47 occupancy-engine sort exception continuum pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data AgExceptionContinuumModality : Set where
  ag-exception-continuum-unwired ag-exception-continuum-assumed
    ag-exception-continuum-proved ag-exception-continuum-surrogate
    : AgExceptionContinuumModality

agExceptionContinuumModalityCurrent : AgExceptionContinuumModality
agExceptionContinuumModalityCurrent = ag-exception-continuum-unwired

agExceptionContinuumProved productionWired not118SquaredGreenTable
  agExceptionSecondLawConservationFramed agExceptionNotXor homologNotCopy : Bool
agExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
agExceptionSecondLawConservationFramed = true
agExceptionNotXor = true
homologNotCopy = true

occupancyEngineSortTyped notParallelAgExceptionAxiomMinted continuumNotForked : Bool
occupancyEngineSortTyped = true
notParallelAgExceptionAxiomMinted = true
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
-- Occupancy-engine sort Ag exception continuum index pin
------------------------------------------------------------------------

occupancyEngineSortTagIndex : ℕ
occupancyEngineSortTagIndex = 47

occupancy-engine-sort-tag-index : occupancyEngineSortTagIndex ≡ 47
occupancy-engine-sort-tag-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Ag (Z=47), Cu (Z=29) / Au (Z=79) homolog
------------------------------------------------------------------------

data ElementTag : Set where
  silver copper gold : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ silver = 47
elementAtomicZ copper = 29
elementAtomicZ gold = 79

silver-z-47 : elementAtomicZ silver ≡ 47
silver-z-47 = refl

copper-z-29 : elementAtomicZ copper ≡ 29
copper-z-29 = refl

gold-z-79 : elementAtomicZ gold ≡ 79
gold-z-79 = refl

periodHomologZOffset : ℕ
periodHomologZOffset = 18

ag-cu-homolog-z-offset :
  elementAtomicZ silver ≡ elementAtomicZ copper + periodHomologZOffset
ag-cu-homolog-z-offset = refl

periodHomologAuZOffset : ℕ
periodHomologAuZOffset = 32

ag-au-homolog-z-offset :
  elementAtomicZ gold ≡ elementAtomicZ silver + periodHomologAuZOffset
ag-au-homolog-z-offset = refl

------------------------------------------------------------------------
-- homolog ≠ copy — Cu / Au period homolog not Ag occupancy identity copy
------------------------------------------------------------------------

data HomologCopyVerdict : Set where
  homolog-not-copy homolog-is-copy : HomologCopyVerdict

evaluateHomologCopy : ℕ → ℕ → HomologCopyVerdict
evaluateHomologCopy zHomolog zSource =
  if does (zHomolog ℕ-Props.≟ (zSource + periodHomologZOffset))
  then homolog-not-copy
  else if does (zHomolog ℕ-Props.≟ (zSource + periodHomologAuZOffset))
  then homolog-not-copy
  else homolog-is-copy

ag-cu-homolog-not-copy :
  evaluateHomologCopy (elementAtomicZ silver) (elementAtomicZ copper) ≡ homolog-not-copy
ag-cu-homolog-not-copy = refl

ag-au-homolog-not-copy :
  evaluateHomologCopy (elementAtomicZ gold) (elementAtomicZ silver) ≡ homolog-not-copy
ag-au-homolog-not-copy = refl

silver-copper-distinct-z : elementAtomicZ silver ≢ elementAtomicZ copper
silver-copper-distinct-z eq with elementAtomicZ silver ℕ-Props.≟ elementAtomicZ copper
silver-copper-distinct-z eq | no ¬pq = ¬pq eq

silver-gold-distinct-z : elementAtomicZ silver ≢ elementAtomicZ gold
silver-gold-distinct-z eq with elementAtomicZ silver ℕ-Props.≟ elementAtomicZ gold
silver-gold-distinct-z eq | no ¬pq = ¬pq eq

homolog-not-copy-pin : homologNotCopy ≡ true
homolog-not-copy-pin = refl

------------------------------------------------------------------------
-- AgExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data AgExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : AgExceptionBundleSlot

isSlotPresent : AgExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- AgExceptionBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record AgExceptionBundle : Set where
  field slot : ℕ → AgExceptionBundleSlot

agExceptionBundleUnwired : AgExceptionBundle
agExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : AgExceptionBundle → ℕ → AgExceptionBundleSlot → AgExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else AgExceptionBundle.slot b j }

withPresent : AgExceptionBundle → ℕ → AgExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record AgExceptionBundleWitness : Set where
  constructor mkAgExceptionBundleWitness
  field
    bundle : AgExceptionBundle
    present-count : ℕ

agExceptionBundleIsConcurrentProduct : AgExceptionBundleWitness → Bool
agExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? AgExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named ag-exception-continuum channel indices — interact restriction (1), not extra force (2), occupancy-engine sort (3)
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
-- AgException nuance witness — interact restriction + not extra force + occupancy-engine sort concurrent
------------------------------------------------------------------------

agExceptionNuanceBundle : AgExceptionBundle
agExceptionNuanceBundle =
  withPresent
    (withPresent
      (withPresent agExceptionBundleUnwired occupancyEngineSortChannelIndex)
      dBlockExceptionChannelIndex)
    continuumWitnessChannelIndex

agExceptionNuanceWitness : AgExceptionBundleWitness
agExceptionNuanceWitness =
  mkAgExceptionBundleWitness agExceptionNuanceBundle 3

ag-exception-nuance-occupancy-engine-sort-present :
  isSlotPresent (AgExceptionBundle.slot agExceptionNuanceBundle occupancyEngineSortChannelIndex) ≡ true
ag-exception-nuance-occupancy-engine-sort-present = refl

ag-exception-nuance-dblock-exception-present :
  isSlotPresent (AgExceptionBundle.slot agExceptionNuanceBundle dBlockExceptionChannelIndex) ≡ true
ag-exception-nuance-dblock-exception-present = refl

ag-exception-nuance-continuum-witness-present :
  isSlotPresent (AgExceptionBundle.slot agExceptionNuanceBundle continuumWitnessChannelIndex) ≡ true
ag-exception-nuance-continuum-witness-present = refl

ag-exception-nuance-present-count : AgExceptionBundleWitness.present-count agExceptionNuanceWitness ≡ 3
ag-exception-nuance-present-count = refl

ag-exception-nuance-concurrent-product :
  agExceptionBundleIsConcurrentProduct agExceptionNuanceWitness ≡ true
ag-exception-nuance-concurrent-product = refl

ag-exception-nuance-three-factors-concurrent :
  isSlotPresent (AgExceptionBundle.slot agExceptionNuanceBundle occupancyEngineSortChannelIndex) ≡ true
  × isSlotPresent (AgExceptionBundle.slot agExceptionNuanceBundle dBlockExceptionChannelIndex) ≡ true
  × isSlotPresent (AgExceptionBundle.slot agExceptionNuanceBundle continuumWitnessChannelIndex) ≡ true
  × AgExceptionBundleWitness.present-count agExceptionNuanceWitness ≡ 3
ag-exception-nuance-three-factors-concurrent =
  ag-exception-nuance-occupancy-engine-sort-present
  , ag-exception-nuance-dblock-exception-present
  , ag-exception-nuance-continuum-witness-present
  , ag-exception-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : AgExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if agExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = AgExceptionBundleWitness.bundle w
       in if isSlotPresent (AgExceptionBundle.slot b i)
          then if isSlotPresent (AgExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : AgExceptionBundleWitness
unwiredWitness = mkAgExceptionBundleWitness agExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

ag-exception-nuance-xor-product-ok :
  evaluateXorRefuse agExceptionNuanceWitness occupancyEngineSortChannelIndex dBlockExceptionChannelIndex ≡ xor-product-ok
ag-exception-nuance-xor-product-ok = refl

ag-exception-not-xor : agExceptionNotXor ≡ true
ag-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierAgExceptionStep scaffold — AgExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierAgExceptionStep : Set where
  ag-exception-identity : ClassifierAgExceptionStep
  slot-leaf : ℕ → ClassifierAgExceptionStep
  product-concurrent : ClassifierAgExceptionStep → ClassifierAgExceptionStep → ClassifierAgExceptionStep
  xor-mutually-exclusive : ClassifierAgExceptionStep → ClassifierAgExceptionStep → ClassifierAgExceptionStep

agExceptionIdentity : ClassifierAgExceptionStep
agExceptionIdentity = ag-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierAgExceptionStep → ClassifierAgExceptionStep → ClassifierAgExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortLeaf dBlockExceptionLeaf continuumWitnessLeaf : ClassifierAgExceptionStep
occupancyEngineSortLeaf = slot-leaf occupancyEngineSortChannelIndex
dBlockExceptionLeaf = slot-leaf dBlockExceptionChannelIndex
continuumWitnessLeaf = slot-leaf continuumWitnessChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierAgExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isAgExceptionIdentity : ClassifierAgExceptionStep → Bool
isAgExceptionIdentity ag-exception-identity = true
isAgExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at ag-exception-identity
------------------------------------------------------------------------

ag-exception-left-identity :
  ∀ (a : ClassifierAgExceptionStep) →
  isAgExceptionIdentity agExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp agExceptionIdentity a) ≡ true
ag-exception-left-identity a = refl , refl

ag-exception-right-identity :
  ∀ (a : ClassifierAgExceptionStep) →
  isProductConcurrent (productConcurrentOp a agExceptionIdentity) ≡ true
  × isAgExceptionIdentity agExceptionIdentity ≡ true
ag-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-ag-exception :
  (∀ a → isProductConcurrent (productConcurrentOp agExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a agExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-ag-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named ag-exception-continuum nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedAgExceptionNuanceProduct : ClassifierAgExceptionStep
namedAgExceptionNuanceProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    continuumWitnessLeaf

named-ag-exception-nuance-product-concurrent :
  isProductConcurrent namedAgExceptionNuanceProduct ≡ true
  × agExceptionBundleIsConcurrentProduct agExceptionNuanceWitness ≡ true
named-ag-exception-nuance-product-concurrent = refl , ag-exception-nuance-concurrent-product

------------------------------------------------------------------------
-- AgExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data AgExceptionAdmissibility : Set where
  ag-exception-admissible ag-exception-xor-refuse : AgExceptionAdmissibility

isAgExceptionPreserving : ClassifierAgExceptionStep → Bool
isAgExceptionPreserving ag-exception-identity = true
isAgExceptionPreserving (slot-leaf _) = true
isAgExceptionPreserving (product-concurrent a b) =
  isAgExceptionPreserving a ∧ isAgExceptionPreserving b
isAgExceptionPreserving (xor-mutually-exclusive _ _) = false

isAgExceptionAdmissible : ClassifierAgExceptionStep → Bool
isAgExceptionAdmissible step = isAgExceptionPreserving step

occupancy-engine-sort-leaf-admissible : isAgExceptionAdmissible occupancyEngineSortLeaf ≡ true
occupancy-engine-sort-leaf-admissible = refl

dblock-exception-leaf-admissible : isAgExceptionAdmissible dBlockExceptionLeaf ≡ true
dblock-exception-leaf-admissible = refl

continuum-witness-leaf-admissible : isAgExceptionAdmissible continuumWitnessLeaf ≡ true
continuum-witness-leaf-admissible = refl

named-ag-exception-nuance-admissible : isAgExceptionAdmissible namedAgExceptionNuanceProduct ≡ true
named-ag-exception-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isAgExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-witness-refuse :
  isAgExceptionAdmissible (xorMutuallyExclusiveOp dBlockExceptionLeaf continuumWitnessLeaf) ≡ false
xor-mutually-exclusive-continuum-witness-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data AgExceptionWitnessPresence : Set where
  ag-exception-witness-absent ag-exception-witness-present : AgExceptionWitnessPresence

record ClassifierAgExceptionWitness : Set where
  constructor mkClassifierAgExceptionWitness
  field
    witness-presence : AgExceptionWitnessPresence
    ag-exception-gap-total : ℕ

agExceptionWitnessAbsent : ClassifierAgExceptionWitness
agExceptionWitnessAbsent = mkClassifierAgExceptionWitness ag-exception-witness-absent zero

agExceptionWitnessPresentZeroGap : ClassifierAgExceptionWitness
agExceptionWitnessPresentZeroGap = mkClassifierAgExceptionWitness ag-exception-witness-present zero

agExceptionWitnessPresentWithGaps : ℕ → ClassifierAgExceptionWitness
agExceptionWitnessPresentWithGaps n = mkClassifierAgExceptionWitness ag-exception-witness-present n

agExceptionWitnessGapFree : ClassifierAgExceptionWitness → Bool
agExceptionWitnessGapFree (mkClassifierAgExceptionWitness ag-exception-witness-absent _) = false
agExceptionWitnessGapFree (mkClassifierAgExceptionWitness ag-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

ag-exception-witness-present-zero-gap-free :
  agExceptionWitnessGapFree agExceptionWitnessPresentZeroGap ≡ true
ag-exception-witness-present-zero-gap-free = refl

ag-exception-witness-absent-not-gap-free :
  agExceptionWitnessGapFree agExceptionWitnessAbsent ≡ false
ag-exception-witness-absent-not-gap-free = refl

ag-exception-witness-with-gaps-not-gap-free :
  ∀ n → agExceptionWitnessGapFree (agExceptionWitnessPresentWithGaps (suc n)) ≡ false
ag-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-AgException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data AgExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-ag-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : AgExceptionContinuumVerdict

agExceptionContinuumVerdictOk : AgExceptionContinuumVerdict → Bool
agExceptionContinuumVerdictOk verdict-unwired-ok = true
agExceptionContinuumVerdictOk verdict-ag-exception-admissible-ok = true
agExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
agExceptionContinuumVerdictOk _ = false

evaluateAgExceptionContinuumClose :
  AgExceptionContinuumModality → ClassifierAgExceptionStep → ClassifierAgExceptionWitness
  → AgExceptionBundleWitness → Bool → AgExceptionContinuumVerdict
evaluateAgExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateAgExceptionContinuumClose ag-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateAgExceptionContinuumClose ag-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateAgExceptionContinuumClose ag-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateAgExceptionContinuumClose ag-exception-continuum-proved _ (mkClassifierAgExceptionWitness ag-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateAgExceptionContinuumClose ag-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateAgExceptionContinuumClose ag-exception-continuum-proved _ (mkClassifierAgExceptionWitness ag-exception-witness-present _) w false
  with agExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-ag-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without ag-exception-continuum witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-unwired namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-assumed namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-surrogate namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  agExceptionContinuumVerdictOk
    (evaluateAgExceptionContinuumClose ag-exception-continuum-unwired namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false)
    ≡ true
  × agExceptionContinuumVerdictOk
      (evaluateAgExceptionContinuumClose ag-exception-continuum-assumed namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false)
      ≡ true
  × agExceptionContinuumVerdictOk
      (evaluateAgExceptionContinuumClose ag-exception-continuum-surrogate namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without ag-exception-continuum witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  agExceptionContinuumVerdictOk
    (evaluateAgExceptionContinuumClose
       ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false ≡
  verdict-ag-exception-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    agExceptionWitnessPresentZeroGap agExceptionNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  agExceptionContinuumVerdictOk
    (evaluateAgExceptionContinuumClose
       ag-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
       agExceptionWitnessPresentZeroGap agExceptionNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf)
    agExceptionWitnessPresentZeroGap agExceptionNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-ag-exception-continuum — nuance **product** closed
------------------------------------------------------------------------

ag-exception-admissible-ok :
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-ag-exception-admissible-ok
ag-exception-admissible-ok = refl

ag-exception-admissible-verdict-ok :
  agExceptionContinuumVerdictOk
    (evaluateAgExceptionContinuumClose
       ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
ag-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — ag-exception-continuum nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap agExceptionNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  agExceptionContinuumVerdictOk
    (evaluateAgExceptionContinuumClose
       ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap agExceptionNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-agExceptionContinuum-proved :
  agExceptionContinuumVerdictOk
    (evaluateAgExceptionContinuumClose
       ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap agExceptionNuanceWitness false)
    ≡ true
  × agExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-agExceptionContinuum-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateAgExceptionContinuumClose
    ag-exception-continuum-unwired namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap agExceptionNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  agExceptionContinuumVerdictOk
    (evaluateAgExceptionContinuumClose
       ag-exception-continuum-unwired namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap agExceptionNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

agExceptionContinuumFiberOk : FormalFiber → Bool
agExceptionContinuumFiberOk fiber-quantum-knowing = true
agExceptionContinuumFiberOk fiber-meso-acting = false

ag-exception-continuum-knowing-fiber-ok :
  agExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
ag-exception-continuum-knowing-fiber-ok = refl

ag-exception-continuum-meso-acting-not-ok :
  agExceptionContinuumFiberOk fiber-meso-acting ≡ false
ag-exception-continuum-meso-acting-not-ok = refl

ag-exception-continuum-routes-knowing-not-meso :
  agExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  agExceptionContinuumFiberOk fiber-meso-acting ≡ false
ag-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  agExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (agExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not occupancy-engine sort Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

ag-exception-continuum-not-proved : agExceptionContinuumProved ≡ false
ag-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

ag-exception-second-law-conservation-framed : agExceptionSecondLawConservationFramed ≡ true
ag-exception-second-law-conservation-framed = refl

ag-exception-not-xor-pin : agExceptionNotXor ≡ true
ag-exception-not-xor-pin = ag-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-ag-exception-axiom-minted-pin : notParallelAgExceptionAxiomMinted ≡ true
not-parallel-ag-exception-axiom-minted-pin = refl

continuum-not-forked-pin : continuumNotForked ≡ true
continuum-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel ag-exception-continuum axiom fork)
------------------------------------------------------------------------

agExceptionContinuumAxiom :
  (agExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (agExceptionSecondLawConservationFramed ≡ true)
  × (agExceptionNotXor ≡ true)
  × (evaluateAgExceptionContinuumClose ag-exception-continuum-unwired namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateAgExceptionContinuumClose ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessAbsent agExceptionNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateAgExceptionContinuumClose ag-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) agExceptionWitnessPresentZeroGap agExceptionNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateAgExceptionContinuumClose ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-ag-exception-admissible-ok)
  × (evaluateAgExceptionContinuumClose ag-exception-continuum-proved namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap agExceptionNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (agExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (agExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (agExceptionContinuumVerdictOk (evaluateAgExceptionContinuumClose ag-exception-continuum-unwired namedAgExceptionNuanceProduct agExceptionWitnessPresentZeroGap agExceptionNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp agExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a agExceptionIdentity) ≡ true)
  × (isAgExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortLeaf dBlockExceptionLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (occupancyEngineSortTagIndex ≡ 47)
  × (AgExceptionBundleWitness.present-count agExceptionNuanceWitness ≡ 3)
  × (elementAtomicZ silver ≡ 47)
  × (elementAtomicZ copper ≡ 29)
  × (elementAtomicZ gold ≡ 79)
  × (homologNotCopy ≡ true)
  × (evaluateHomologCopy (elementAtomicZ silver) (elementAtomicZ copper) ≡ homolog-not-copy)
  × (evaluateHomologCopy (elementAtomicZ gold) (elementAtomicZ silver) ≡ homolog-not-copy)
agExceptionContinuumAxiom =
  ag-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , ag-exception-second-law-conservation-framed
  , ag-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , ag-exception-admissible-ok
  , concurrent-product-ok
  , ag-exception-continuum-knowing-fiber-ok
  , ag-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , occupancy-engine-sort-tag-index
  , ag-exception-nuance-present-count
  , silver-z-47
  , copper-z-29
  , gold-z-79
  , homolog-not-copy-pin
  , ag-cu-homolog-not-copy
  , ag-au-homolog-not-copy

agExceptionContinuumNamed : String
agExceptionContinuumNamed =
  "agExceptionContinuum: Ag Z=47 occupancy-engine sort exception continuum conservation concurrent Pi_c identity conserved Interact restriction not extra force occupancy-engine sort concurrent product identity conserved present ge 2 product not XOR interact restriction typed no parallel ag-exception-continuum axiom homolog Cu Au not copy not extra force"

agExceptionContinuumCrossWitnessAuthority : String
agExceptionContinuumCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

z047AgAuthority : String
z047AgAuthority =
  "umst/umst-chem/src/elements/z_047_ag.rs"

z029CuAuthority : String
z029CuAuthority =
  "umst/umst-chem/src/elements/z_029_cu.rs"

z079AuAuthority : String
z079AuAuthority =
  "umst/umst-chem/src/elements/z_079_au.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

occupancyExceptionSetsAuthority : String
occupancyExceptionSetsAuthority =
  "umst/umst-chem/src/x_rows/occupancy_exception_sets.rs"

agExceptionContinuumCellId : String
agExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-AG-EXCEPTION-CONTINUUM"

agExceptionContinuumNonClaim : String
agExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-AG-EXCEPTION-CONTINUUM Ag Z=47 occupancy-engine sort exception continuum conservation concurrent Pi_c identity conserved Interact restriction not extra force occupancy-engine sort product not XOR interact restriction typed no parallel ag-exception-continuum axiom homolog Cu Z=29 Au Z=79 not copy XOR mutually exclusive refuse ag-exception-continuum nuance witness concurrent agExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite occupancy_engine_sort.rs homolog_exception_not_copy l0_tables ag-exception-continuum not fork not physics GREEN not production_wired"

ag-exception-continuum-cell-id :
  agExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-AG-EXCEPTION-CONTINUUM"
ag-exception-continuum-cell-id = refl

ag-exception-continuum-cites-occupancy-engine-sort-rs :
  agExceptionContinuumCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
ag-exception-continuum-cites-occupancy-engine-sort-rs = refl

ag-exception-continuum-cites-z047-ag-rs :
  z047AgAuthority ≡
  "umst/umst-chem/src/elements/z_047_ag.rs"
ag-exception-continuum-cites-z047-ag-rs = refl

ag-exception-continuum-cites-z029-cu-rs :
  z029CuAuthority ≡
  "umst/umst-chem/src/elements/z_029_cu.rs"
ag-exception-continuum-cites-z029-cu-rs = refl

ag-exception-continuum-cites-z079-au-rs :
  z079AuAuthority ≡
  "umst/umst-chem/src/elements/z_079_au.rs"
ag-exception-continuum-cites-z079-au-rs = refl

ag-exception-continuum-cites-homolog-not-copy-rs :
  homologExceptionNotCopyAuthority ≡
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"
ag-exception-continuum-cites-homolog-not-copy-rs = refl

ag-exception-continuum-modality-unwired :
  agExceptionContinuumModalityCurrent ≡ ag-exception-continuum-unwired
ag-exception-continuum-modality-unwired = refl

agExceptionContinuumPhysicsGreenAuthorized : Set
agExceptionContinuumPhysicsGreenAuthorized = ⊥

ag-exception-continuum-physics-green-false : ¬ agExceptionContinuumPhysicsGreenAuthorized
ag-exception-continuum-physics-green-false ()

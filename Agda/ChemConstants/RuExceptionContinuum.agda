-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.RuExceptionContinuum.agda
--
-- Ru Z=44 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (ore ⊗ isotope mix ⊗ purify Refine-cost ⊗ G-stability ⊗ Env;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Ru exception continuum witness concurrent
--     (ore + isotope mix + purify Refine-cost + G-stability + Env)
--   * **Ru exception continuum** laws Unwired (ruExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_044_ru.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Homolog cite: umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs
-- Mirrors sibling `ChemConstants/MoExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy (Fe/Os). Product not XOR.
-- Ru Z=44 DBlock occupancy-engine sort exception, not 26th axiom.
-- WAVE100: no lib.rs / eos.rs / nano wiring.
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

module ChemConstants.RuExceptionContinuum where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

open import ChemConstants.DBlockOccupancyExceptions using
  ( DBlockException; dblock-Ru
  ; DBlockException-z
  ; dblock-exception-ru-z
  ; dblockOccupancyQlatticeAuthority
  ; dblockOccupancyMadelungWitnessAuthority
  )
open import ChemConstants.OccupancyEngineSort using
  ( occupancyEngineSortBucket
  ; isDBlockExceptionBucket
  ; dblock-ru-sorts-dblock-bucket
  ; occupancyEngineSortProved
  ; occupancy-engine-sort-not-proved
  )

------------------------------------------------------------------------
-- Modality + Ru exception continuum **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data RuExceptionContinuumModality : Set where
  ru-exception-continuum-unwired ru-exception-continuum-assumed
    ru-exception-continuum-proved ru-exception-continuum-surrogate
    : RuExceptionContinuumModality

ruExceptionContinuumModalityCurrent : RuExceptionContinuumModality
ruExceptionContinuumModalityCurrent = ru-exception-continuum-unwired

ruExceptionContinuumProved productionWired not118SquaredGreenTable
  ruExceptionContinuumSecondLawConservationFramed ruExceptionContinuumNotXor
  homologNotCopy occupancyEngineSortCited : Bool
ruExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
ruExceptionContinuumSecondLawConservationFramed = true
ruExceptionContinuumNotXor = true
homologNotCopy = true
occupancyEngineSortCited = true

occupancyEngineSortTyped notParallelOccupancyAxiomMinted homologNotCopyNotForked : Bool
occupancyEngineSortTyped = true
notParallelOccupancyAxiomMinted = true
homologNotCopyNotForked = true

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
-- Ru Z=44 occupancy-engine sort index pin
------------------------------------------------------------------------

ruZ44OccupancyEngineSortIndex : ℕ
ruZ44OccupancyEngineSortIndex = 44

ru-z44-occupancy-engine-sort-index : ruZ44OccupancyEngineSortIndex ≡ 44
ru-z44-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Ru (Z=44), Fe (Z=26 homolog), Os (Z=76 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  iron ruthenium osmium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ iron = 26
elementAtomicZ ruthenium = 44
elementAtomicZ osmium = 76

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

ruthenium-z-44 : elementAtomicZ ruthenium ≡ 44
ruthenium-z-44 = refl

osmium-z-76 : elementAtomicZ osmium ≡ 76
osmium-z-76 = refl

periodHomologZOffset : ℕ
periodHomologZOffset = 18

period6HomologZOffset : ℕ
period6HomologZOffset = 32

fe-ru-homolog-z-offset :
  elementAtomicZ ruthenium ≡ elementAtomicZ iron + periodHomologZOffset
fe-ru-homolog-z-offset = refl

ru-os-homolog-z-offset :
  elementAtomicZ osmium ≡ elementAtomicZ ruthenium + period6HomologZOffset
ru-os-homolog-z-offset = refl

ru-z-matches-dblock-exception :
  elementAtomicZ ruthenium ≡ DBlockException-z dblock-Ru
ru-z-matches-dblock-exception = refl

------------------------------------------------------------------------
-- Occupancy-engine sort bucket — Ru DBlockException
------------------------------------------------------------------------

ru-sorts-dblock-bucket :
  isDBlockExceptionBucket (occupancyEngineSortBucket (DBlockException-z dblock-Ru)) ≡ true
ru-sorts-dblock-bucket = dblock-ru-sorts-dblock-bucket

------------------------------------------------------------------------
-- homolog ≠ copy — Fe/Os period homologs not Ru occupancy identity copy
------------------------------------------------------------------------

data HomologCopyVerdict : Set where
  homolog-not-copy homolog-is-copy : HomologCopyVerdict

evaluateHomologCopyWithOffset : ℕ → ℕ → ℕ → HomologCopyVerdict
evaluateHomologCopyWithOffset zHomolog zSource offset =
  if does (zHomolog ℕ-Props.≟ (zSource + offset))
  then homolog-not-copy
  else homolog-is-copy

fe-ru-homolog-not-copy :
  evaluateHomologCopyWithOffset (elementAtomicZ ruthenium) (elementAtomicZ iron) periodHomologZOffset ≡ homolog-not-copy
fe-ru-homolog-not-copy = refl

ru-os-homolog-not-copy :
  evaluateHomologCopyWithOffset (elementAtomicZ osmium) (elementAtomicZ ruthenium) period6HomologZOffset ≡ homolog-not-copy
ru-os-homolog-not-copy = refl

iron-osmium-distinct-z : elementAtomicZ iron ≢ elementAtomicZ osmium
iron-osmium-distinct-z eq with elementAtomicZ iron ℕ-Props.≟ elementAtomicZ osmium
iron-osmium-distinct-z eq | no ¬pq = ¬pq eq

homolog-not-copy-pin : homologNotCopy ≡ true
homolog-not-copy-pin = refl

------------------------------------------------------------------------
-- RuExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data RuExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : RuExceptionBundleSlot

isSlotPresent : RuExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- RuExceptionBundle — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record RuExceptionBundle : Set where
  field slot : ℕ → RuExceptionBundleSlot

ruExceptionBundleUnwired : RuExceptionBundle
ruExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : RuExceptionBundle → ℕ → RuExceptionBundleSlot → RuExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else RuExceptionBundle.slot b j }

withPresent : RuExceptionBundle → ℕ → RuExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record RuExceptionBundleWitness : Set where
  constructor mkRuExceptionBundleWitness
  field
    bundle : RuExceptionBundle
    present-count : ℕ

ruExceptionBundleIsConcurrentProduct : RuExceptionBundleWitness → Bool
ruExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? RuExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named continuum channel indices — ore (1), isotope (2), purify (3), G-stability (4), Env (5)
------------------------------------------------------------------------

oreChannelIndex isotopeMixChannelIndex purifyRefineCostChannelIndex
  gStabilityChannelIndex envChannelIndex : ℕ
oreChannelIndex = 1
isotopeMixChannelIndex = 2
purifyRefineCostChannelIndex = 3
gStabilityChannelIndex = 4
envChannelIndex = 5

ore-index-one : oreChannelIndex ≡ 1
ore-index-one = refl

isotope-mix-index-two : isotopeMixChannelIndex ≡ 2
isotope-mix-index-two = refl

purify-refine-cost-index-three : purifyRefineCostChannelIndex ≡ 3
purify-refine-cost-index-three = refl

g-stability-index-four : gStabilityChannelIndex ≡ 4
g-stability-index-four = refl

env-index-five : envChannelIndex ≡ 5
env-index-five = refl

------------------------------------------------------------------------
-- Cr exception continuum nuance witness — five concurrent product factors
------------------------------------------------------------------------

ruExceptionContinuumWitnessBundle : RuExceptionBundle
ruExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent
        (withPresent
          (withPresent ruExceptionBundleUnwired oreChannelIndex)
          isotopeMixChannelIndex)
        purifyRefineCostChannelIndex)
      gStabilityChannelIndex)
    envChannelIndex

ruExceptionContinuumWitness : RuExceptionBundleWitness
ruExceptionContinuumWitness =
  mkRuExceptionBundleWitness ruExceptionContinuumWitnessBundle 5

ru-nuance-ore-present :
  isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle oreChannelIndex) ≡ true
ru-nuance-ore-present = refl

ru-nuance-isotope-present :
  isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle isotopeMixChannelIndex) ≡ true
ru-nuance-isotope-present = refl

ru-nuance-purify-present :
  isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle purifyRefineCostChannelIndex) ≡ true
ru-nuance-purify-present = refl

ru-nuance-g-stability-present :
  isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle gStabilityChannelIndex) ≡ true
ru-nuance-g-stability-present = refl

ru-nuance-env-present :
  isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle envChannelIndex) ≡ true
ru-nuance-env-present = refl

ru-nuance-present-count : RuExceptionBundleWitness.present-count ruExceptionContinuumWitness ≡ 5
ru-nuance-present-count = refl

ru-nuance-concurrent-product :
  ruExceptionBundleIsConcurrentProduct ruExceptionContinuumWitness ≡ true
ru-nuance-concurrent-product = refl

ru-nuance-five-factors-concurrent :
  isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle oreChannelIndex) ≡ true
  × isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle isotopeMixChannelIndex) ≡ true
  × isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle purifyRefineCostChannelIndex) ≡ true
  × isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle gStabilityChannelIndex) ≡ true
  × isSlotPresent (RuExceptionBundle.slot ruExceptionContinuumWitnessBundle envChannelIndex) ≡ true
  × RuExceptionBundleWitness.present-count ruExceptionContinuumWitness ≡ 5
ru-nuance-five-factors-concurrent =
  ru-nuance-ore-present
  , ru-nuance-isotope-present
  , ru-nuance-purify-present
  , ru-nuance-g-stability-present
  , ru-nuance-env-present
  , ru-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : RuExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if ruExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = RuExceptionBundleWitness.bundle w
       in if isSlotPresent (RuExceptionBundle.slot b i)
          then if isSlotPresent (RuExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : RuExceptionBundleWitness
unwiredWitness = mkRuExceptionBundleWitness ruExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

ru-nuance-xor-product-ok :
  evaluateXorRefuse ruExceptionContinuumWitness oreChannelIndex isotopeMixChannelIndex ≡ xor-product-ok
ru-nuance-xor-product-ok = refl

ru-exception-continuum-not-xor : ruExceptionContinuumNotXor ≡ true
ru-exception-continuum-not-xor = refl

------------------------------------------------------------------------
-- ClassifierRuExceptionContinuumStep scaffold — continuum **conservation**
------------------------------------------------------------------------

data ClassifierRuExceptionContinuumStep : Set where
  ru-exception-identity : ClassifierRuExceptionContinuumStep
  slot-leaf : ℕ → ClassifierRuExceptionContinuumStep
  product-concurrent : ClassifierRuExceptionContinuumStep → ClassifierRuExceptionContinuumStep → ClassifierRuExceptionContinuumStep
  xor-mutually-exclusive : ClassifierRuExceptionContinuumStep → ClassifierRuExceptionContinuumStep → ClassifierRuExceptionContinuumStep

ruExceptionIdentity : ClassifierRuExceptionContinuumStep
ruExceptionIdentity = ru-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierRuExceptionContinuumStep → ClassifierRuExceptionContinuumStep → ClassifierRuExceptionContinuumStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

oreLeaf isotopeMixLeaf purifyRefineCostLeaf gStabilityLeaf envLeaf : ClassifierRuExceptionContinuumStep
oreLeaf = slot-leaf oreChannelIndex
isotopeMixLeaf = slot-leaf isotopeMixChannelIndex
purifyRefineCostLeaf = slot-leaf purifyRefineCostChannelIndex
gStabilityLeaf = slot-leaf gStabilityChannelIndex
envLeaf = slot-leaf envChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierRuExceptionContinuumStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isRuExceptionIdentity : ClassifierRuExceptionContinuumStep → Bool
isRuExceptionIdentity ru-exception-identity = true
isRuExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at continuum-identity
------------------------------------------------------------------------

ru-exception-left-identity :
  ∀ (a : ClassifierRuExceptionContinuumStep) →
  isRuExceptionIdentity ruExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp ruExceptionIdentity a) ≡ true
ru-exception-left-identity a = refl , refl

ru-exception-right-identity :
  ∀ (a : ClassifierRuExceptionContinuumStep) →
  isProductConcurrent (productConcurrentOp a ruExceptionIdentity) ≡ true
  × isRuExceptionIdentity ruExceptionIdentity ≡ true
ru-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-ru-exception :
  (∀ a → isProductConcurrent (productConcurrentOp ruExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a ruExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-ru-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Cr exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedRuExceptionContinuumProduct : ClassifierRuExceptionContinuumStep
namedRuExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp
      (productConcurrentOp
        (productConcurrentOp oreLeaf isotopeMixLeaf)
        purifyRefineCostLeaf)
      gStabilityLeaf)
    envLeaf

named-ru-exception-continuum-product-concurrent :
  isProductConcurrent namedRuExceptionContinuumProduct ≡ true
  × ruExceptionBundleIsConcurrentProduct ruExceptionContinuumWitness ≡ true
named-ru-exception-continuum-product-concurrent = refl , ru-nuance-concurrent-product

------------------------------------------------------------------------
-- RuExceptionContinuum admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data RuExceptionAdmissibility : Set where
  ru-exception-admissible ru-exception-xor-refuse : RuExceptionAdmissibility

isRuExceptionPreserving : ClassifierRuExceptionContinuumStep → Bool
isRuExceptionPreserving ru-exception-identity = true
isRuExceptionPreserving (slot-leaf _) = true
isRuExceptionPreserving (product-concurrent a b) =
  isRuExceptionPreserving a ∧ isRuExceptionPreserving b
isRuExceptionPreserving (xor-mutually-exclusive _ _) = false

isRuExceptionAdmissible : ClassifierRuExceptionContinuumStep → Bool
isRuExceptionAdmissible step = isRuExceptionPreserving step

ore-leaf-admissible : isRuExceptionAdmissible oreLeaf ≡ true
ore-leaf-admissible = refl

isotope-mix-leaf-admissible : isRuExceptionAdmissible isotopeMixLeaf ≡ true
isotope-mix-leaf-admissible = refl

purify-refine-cost-leaf-admissible : isRuExceptionAdmissible purifyRefineCostLeaf ≡ true
purify-refine-cost-leaf-admissible = refl

g-stability-leaf-admissible : isRuExceptionAdmissible gStabilityLeaf ≡ true
g-stability-leaf-admissible = refl

env-leaf-admissible : isRuExceptionAdmissible envLeaf ≡ true
env-leaf-admissible = refl

named-ru-exception-continuum-admissible : isRuExceptionAdmissible namedRuExceptionContinuumProduct ≡ true
named-ru-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isRuExceptionAdmissible (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-g-stability-env-refuse :
  isRuExceptionAdmissible (xorMutuallyExclusiveOp gStabilityLeaf envLeaf) ≡ false
xor-mutually-exclusive-g-stability-env-refuse = refl

------------------------------------------------------------------------
-- Witness presence — total-claim refuse without witness
------------------------------------------------------------------------

data RuExceptionWitnessPresence : Set where
  ru-exception-witness-absent ru-exception-witness-present : RuExceptionWitnessPresence

record ClassifierRuExceptionContinuumWitness : Set where
  constructor mkClassifierRuExceptionContinuumWitness
  field
    witness-presence : RuExceptionWitnessPresence
    ru-exception-gap-total : ℕ

ruExceptionWitnessAbsent : ClassifierRuExceptionContinuumWitness
ruExceptionWitnessAbsent = mkClassifierRuExceptionContinuumWitness ru-exception-witness-absent zero

ruExceptionWitnessPresentZeroGap : ClassifierRuExceptionContinuumWitness
ruExceptionWitnessPresentZeroGap = mkClassifierRuExceptionContinuumWitness ru-exception-witness-present zero

ruExceptionWitnessPresentWithGaps : ℕ → ClassifierRuExceptionContinuumWitness
ruExceptionWitnessPresentWithGaps n = mkClassifierRuExceptionContinuumWitness ru-exception-witness-present n

ruExceptionWitnessGapFree : ClassifierRuExceptionContinuumWitness → Bool
ruExceptionWitnessGapFree (mkClassifierRuExceptionContinuumWitness ru-exception-witness-absent _) = false
ruExceptionWitnessGapFree (mkClassifierRuExceptionContinuumWitness ru-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

ru-exception-witness-present-zero-gap-free :
  ruExceptionWitnessGapFree ruExceptionWitnessPresentZeroGap ≡ true
ru-exception-witness-present-zero-gap-free = refl

ru-exception-witness-absent-not-gap-free :
  ruExceptionWitnessGapFree ruExceptionWitnessAbsent ≡ false
ru-exception-witness-absent-not-gap-free = refl

ru-exception-witness-with-gaps-not-gap-free :
  ∀ n → ruExceptionWitnessGapFree (ruExceptionWitnessPresentWithGaps (suc n)) ≡ false
ru-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Cr-exception-continuum **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data RuExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-ru-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : RuExceptionContinuumVerdict

ruExceptionContinuumVerdictOk : RuExceptionContinuumVerdict → Bool
ruExceptionContinuumVerdictOk verdict-unwired-ok = true
ruExceptionContinuumVerdictOk verdict-ru-exception-admissible-ok = true
ruExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
ruExceptionContinuumVerdictOk _ = false

evaluateRuExceptionContinuumClose :
  RuExceptionContinuumModality → ClassifierRuExceptionContinuumStep → ClassifierRuExceptionContinuumWitness
  → RuExceptionBundleWitness → Bool → RuExceptionContinuumVerdict
evaluateRuExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateRuExceptionContinuumClose ru-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateRuExceptionContinuumClose ru-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateRuExceptionContinuumClose ru-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateRuExceptionContinuumClose ru-exception-continuum-proved _ (mkClassifierRuExceptionContinuumWitness ru-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateRuExceptionContinuumClose ru-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateRuExceptionContinuumClose ru-exception-continuum-proved _ (mkClassifierRuExceptionContinuumWitness ru-exception-witness-present _) w false
  with ruExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-ru-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without continuum witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-unwired namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-assumed namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-surrogate namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  ruExceptionContinuumVerdictOk
    (evaluateRuExceptionContinuumClose ru-exception-continuum-unwired namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false)
    ≡ true
  × ruExceptionContinuumVerdictOk
      (evaluateRuExceptionContinuumClose ru-exception-continuum-assumed namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false)
      ≡ true
  × ruExceptionContinuumVerdictOk
      (evaluateRuExceptionContinuumClose ru-exception-continuum-surrogate namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without continuum witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  ruExceptionContinuumVerdictOk
    (evaluateRuExceptionContinuumClose
       ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false ≡
  verdict-ru-exception-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-proved
    (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf)
    ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  ruExceptionContinuumVerdictOk
    (evaluateRuExceptionContinuumClose
       ru-exception-continuum-proved
       (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf)
       ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-proved
    (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf)
    ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-continuum — nuance **product** closed
------------------------------------------------------------------------

ru-exception-admissible-ok :
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-ru-exception-admissible-ok
ru-exception-admissible-ok = refl

ru-exception-admissible-verdict-ok :
  ruExceptionContinuumVerdictOk
    (evaluateRuExceptionContinuumClose
       ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
ru-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — Cr exception continuum nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  ruExceptionContinuumVerdictOk
    (evaluateRuExceptionContinuumClose
       ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-ru-exception-continuum-proved :
  ruExceptionContinuumVerdictOk
    (evaluateRuExceptionContinuumClose
       ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness false)
    ≡ true
  × ruExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-ru-exception-continuum-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateRuExceptionContinuumClose
    ru-exception-continuum-unwired namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  ruExceptionContinuumVerdictOk
    (evaluateRuExceptionContinuumClose
       ru-exception-continuum-unwired namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

ruExceptionContinuumFiberOk : FormalFiber → Bool
ruExceptionContinuumFiberOk fiber-quantum-knowing = true
ruExceptionContinuumFiberOk fiber-meso-acting = false

ru-exception-continuum-knowing-fiber-ok :
  ruExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
ru-exception-continuum-knowing-fiber-ok = refl

ru-exception-continuum-meso-acting-not-ok :
  ruExceptionContinuumFiberOk fiber-meso-acting ≡ false
ru-exception-continuum-meso-acting-not-ok = refl

ru-exception-continuum-routes-knowing-not-meso :
  ruExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  ruExceptionContinuumFiberOk fiber-meso-acting ≡ false
ru-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  ruExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (ruExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Cr exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

ru-exception-continuum-not-proved : ruExceptionContinuumProved ≡ false
ru-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

ru-exception-continuum-second-law-conservation-framed :
  ruExceptionContinuumSecondLawConservationFramed ≡ true
ru-exception-continuum-second-law-conservation-framed = refl

ru-exception-continuum-not-xor-pin : ruExceptionContinuumNotXor ≡ true
ru-exception-continuum-not-xor-pin = ru-exception-continuum-not-xor

occupancy-engine-sort-cited-pin : occupancyEngineSortCited ≡ true
occupancy-engine-sort-cited-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

occupancy-engine-sort-not-proved-pin : occupancyEngineSortProved ≡ false
occupancy-engine-sort-not-proved-pin = occupancy-engine-sort-not-proved

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel ru-exception-continuum axiom fork)
------------------------------------------------------------------------

ruExceptionContinuumAxiom :
  (ruExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (ruExceptionContinuumSecondLawConservationFramed ≡ true)
  × (ruExceptionContinuumNotXor ≡ true)
  × (homologNotCopy ≡ true)
  × (occupancyEngineSortCited ≡ true)
  × (evaluateRuExceptionContinuumClose ru-exception-continuum-unwired namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateRuExceptionContinuumClose ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessAbsent ruExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateRuExceptionContinuumClose ru-exception-continuum-proved (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf) ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateRuExceptionContinuumClose ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-ru-exception-admissible-ok)
  × (evaluateRuExceptionContinuumClose ru-exception-continuum-proved namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (ruExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (ruExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (ruExceptionContinuumVerdictOk (evaluateRuExceptionContinuumClose ru-exception-continuum-unwired namedRuExceptionContinuumProduct ruExceptionWitnessPresentZeroGap ruExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp ruExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a ruExceptionIdentity) ≡ true)
  × (isRuExceptionAdmissible (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (elementAtomicZ ruthenium ≡ 44)
  × (elementAtomicZ osmium ≡ 76)
  × (RuExceptionBundleWitness.present-count ruExceptionContinuumWitness ≡ 5)
  × (isDBlockExceptionBucket (occupancyEngineSortBucket (DBlockException-z dblock-Ru)) ≡ true)
  × (evaluateHomologCopyWithOffset (elementAtomicZ ruthenium) (elementAtomicZ iron) periodHomologZOffset ≡ homolog-not-copy)
ruExceptionContinuumAxiom =
  ru-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , ru-exception-continuum-second-law-conservation-framed
  , ru-exception-continuum-not-xor-pin
  , homolog-not-copy-pin
  , occupancy-engine-sort-cited-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , ru-exception-admissible-ok
  , concurrent-product-ok
  , ru-exception-continuum-knowing-fiber-ok
  , ru-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , ruthenium-z-44
  , osmium-z-76
  , ru-nuance-present-count
  , ru-sorts-dblock-bucket
  , fe-ru-homolog-not-copy

ruExceptionContinuumNamed : String
ruExceptionContinuumNamed =
  "ruExceptionContinuum: Ru Z=44 occupancy-engine sort exception continuum concurrent Pi_c identity conserved ore isotope mix purify Refine-cost G-stability Env concurrent product identity conserved present ge 2 product not XOR homolog Fe Os not copy occupancy engine sort typed no parallel occupancy axiom homolog not copy not forked"

ruExceptionContinuumAuthority : String
ruExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_044_ru.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

ruExceptionContinuumCellId : String
ruExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-RU-EXCEPTION-CONTINUUM"

ruExceptionContinuumNonClaim : String
ruExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-RU-EXCEPTION-CONTINUUM Ru Z=44 occupancy-engine sort exception continuum concurrent Pi_c identity conserved ore isotope mix purify Refine-cost G-stability Env product not XOR homolog Fe Z=26 Os Z=76 not copy occupancy engine sort typed no parallel occupancy axiom homolog not copy not forked XOR mutually exclusive refuse Ru exception continuum witness concurrent ruExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_044_ru.rs occupancy_engine_sort.rs homolog_exception_not_copy not fork not physics GREEN not production_wired WAVE100 no lib.rs"

ru-exception-continuum-cell-id :
  ruExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-RU-EXCEPTION-CONTINUUM"
ru-exception-continuum-cell-id = refl

ru-exception-continuum-cites-z044-ru-rs :
  ruExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_044_ru.rs"
ru-exception-continuum-cites-z044-ru-rs = refl

ru-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
ru-exception-continuum-cites-occupancy-engine-sort-rs = refl

ru-exception-continuum-cites-homolog-exception-not-copy-rs :
  homologExceptionNotCopyAuthority ≡
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs"
ru-exception-continuum-cites-homolog-exception-not-copy-rs = refl

ru-exception-continuum-modality-unwired :
  ruExceptionContinuumModalityCurrent ≡ ru-exception-continuum-unwired
ru-exception-continuum-modality-unwired = refl

RuExceptionContinuumPhysicsGreenAuthorized : Set
RuExceptionContinuumPhysicsGreenAuthorized = ⊥

ru-exception-continuum-physics-green-false : ¬ RuExceptionContinuumPhysicsGreenAuthorized
ru-exception-continuum-physics-green-false ()

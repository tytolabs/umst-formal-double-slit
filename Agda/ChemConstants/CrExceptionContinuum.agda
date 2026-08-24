-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.CrExceptionContinuum.agda
--
-- Cr Z=24 **occupancy-engine sort** exception **continuum** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (ore ⊗ isotope mix ⊗ purify Refine-cost ⊗ G-stability ⊗ Env;
--     **product** not XOR, no parallel cr-exception-continuum axiom)
--   * XOR mutually-exclusive refuse; Cr exception continuum nuance witness concurrent
--     (ore + isotope mix + purify Refine-cost + G-stability + Env)
--   * **cr-exception-continuum** laws Unwired (crExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/x_rows/cr_exception_continuum.rs
-- Occupancy sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Goldschmidt cite: umst/umst-chem/src/l0_tables/goldschmidt.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- Homolog Mo Z=42 ≠ Cr occupancy copy. DBlockException Cr Z=24 occupancy-engine sort.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.CrExceptionContinuum where

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
  ( DBlockException; dblock-Cr; dblock-Mo
  ; DBlockException-z
  ; dblock-exception-cr-z
  ; dblock-exception-mo-z
  ; dblockOccupancyQlatticeAuthority
  ; dblockOccupancyMadelungWitnessAuthority
  )
open import ChemConstants.OccupancyEngineSort using
  ( occupancyEngineSortBucket
  ; isDBlockExceptionBucket
  ; dblock-cr-sorts-dblock-bucket
  ; dblock-mo-sorts-dblock-bucket
  ; occupancyEngineSortProved
  ; occupancy-engine-sort-not-proved
  )

------------------------------------------------------------------------
-- Modality + Cr exception continuum **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data CrExceptionContinuumModality : Set where
  cr-exception-continuum-unwired cr-exception-continuum-assumed
    cr-exception-continuum-proved cr-exception-continuum-surrogate
    : CrExceptionContinuumModality

crExceptionContinuumModalityCurrent : CrExceptionContinuumModality
crExceptionContinuumModalityCurrent = cr-exception-continuum-unwired

crExceptionContinuumProved productionWired not118SquaredGreenTable
  crExceptionContinuumSecondLawConservationFramed crExceptionContinuumNotXor
  homologNotCopy occupancyEngineSortCited : Bool
crExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
crExceptionContinuumSecondLawConservationFramed = true
crExceptionContinuumNotXor = true
homologNotCopy = true
occupancyEngineSortCited = true

notParallelCrExceptionContinuumAxiomMinted goldschmidtCitedReadOnly : Bool
notParallelCrExceptionContinuumAxiomMinted = true
goldschmidtCitedReadOnly = true

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
-- Named element Z pins — Cr (Z=24), Mo (Z=42) homolog
------------------------------------------------------------------------

data ElementTag : Set where
  chromium molybdenum : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ chromium = 24
elementAtomicZ molybdenum = 42

chromium-z-24 : elementAtomicZ chromium ≡ 24
chromium-z-24 = refl

molybdenum-z-42 : elementAtomicZ molybdenum ≡ 42
molybdenum-z-42 = refl

periodHomologZOffset : ℕ
periodHomologZOffset = 18

cr-mo-homolog-z-offset :
  elementAtomicZ molybdenum ≡ elementAtomicZ chromium + periodHomologZOffset
cr-mo-homolog-z-offset = refl

cr-z-matches-dblock-exception :
  elementAtomicZ chromium ≡ DBlockException-z dblock-Cr
cr-z-matches-dblock-exception = refl

mo-z-matches-dblock-exception :
  elementAtomicZ molybdenum ≡ DBlockException-z dblock-Mo
mo-z-matches-dblock-exception = refl

------------------------------------------------------------------------
-- Occupancy-engine sort bucket — Cr and Mo DBlockException
------------------------------------------------------------------------

cr-sorts-dblock-bucket :
  isDBlockExceptionBucket (occupancyEngineSortBucket (DBlockException-z dblock-Cr)) ≡ true
cr-sorts-dblock-bucket = dblock-cr-sorts-dblock-bucket

mo-sorts-dblock-bucket :
  isDBlockExceptionBucket (occupancyEngineSortBucket (DBlockException-z dblock-Mo)) ≡ true
mo-sorts-dblock-bucket = dblock-mo-sorts-dblock-bucket

------------------------------------------------------------------------
-- homolog ≠ copy — Mo period homolog not Cr occupancy identity copy
------------------------------------------------------------------------

data HomologCopyVerdict : Set where
  homolog-not-copy homolog-is-copy : HomologCopyVerdict

evaluateHomologCopy : ℕ → ℕ → HomologCopyVerdict
evaluateHomologCopy zHomolog zSource =
  if does (zHomolog ℕ-Props.≟ (zSource + periodHomologZOffset))
  then homolog-not-copy
  else homolog-is-copy

mo-cr-homolog-not-copy :
  evaluateHomologCopy (elementAtomicZ molybdenum) (elementAtomicZ chromium) ≡ homolog-not-copy
mo-cr-homolog-not-copy = refl

chromium-mo-distinct-z : elementAtomicZ chromium ≢ elementAtomicZ molybdenum
chromium-mo-distinct-z eq with elementAtomicZ chromium ℕ-Props.≟ elementAtomicZ molybdenum
chromium-mo-distinct-z eq | no ¬pq = ¬pq eq

homolog-not-copy-pin : homologNotCopy ≡ true
homolog-not-copy-pin = refl

------------------------------------------------------------------------
-- CrExceptionContinuumBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data CrExceptionContinuumBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : CrExceptionContinuumBundleSlot

isSlotPresent : CrExceptionContinuumBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- CrExceptionContinuumBundle — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record CrExceptionContinuumBundle : Set where
  field slot : ℕ → CrExceptionContinuumBundleSlot

crExceptionContinuumBundleUnwired : CrExceptionContinuumBundle
crExceptionContinuumBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : CrExceptionContinuumBundle → ℕ → CrExceptionContinuumBundleSlot → CrExceptionContinuumBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else CrExceptionContinuumBundle.slot b j }

withPresent : CrExceptionContinuumBundle → ℕ → CrExceptionContinuumBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record CrExceptionContinuumBundleWitness : Set where
  constructor mkCrExceptionContinuumBundleWitness
  field
    bundle : CrExceptionContinuumBundle
    present-count : ℕ

crExceptionContinuumBundleIsConcurrentProduct : CrExceptionContinuumBundleWitness → Bool
crExceptionContinuumBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? CrExceptionContinuumBundleWitness.present-count w)

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

crExceptionContinuumNuanceBundle : CrExceptionContinuumBundle
crExceptionContinuumNuanceBundle =
  withPresent
    (withPresent
      (withPresent
        (withPresent
          (withPresent crExceptionContinuumBundleUnwired oreChannelIndex)
          isotopeMixChannelIndex)
        purifyRefineCostChannelIndex)
      gStabilityChannelIndex)
    envChannelIndex

crExceptionContinuumNuanceWitness : CrExceptionContinuumBundleWitness
crExceptionContinuumNuanceWitness =
  mkCrExceptionContinuumBundleWitness crExceptionContinuumNuanceBundle 5

cr-nuance-ore-present :
  isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle oreChannelIndex) ≡ true
cr-nuance-ore-present = refl

cr-nuance-isotope-present :
  isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle isotopeMixChannelIndex) ≡ true
cr-nuance-isotope-present = refl

cr-nuance-purify-present :
  isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle purifyRefineCostChannelIndex) ≡ true
cr-nuance-purify-present = refl

cr-nuance-g-stability-present :
  isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle gStabilityChannelIndex) ≡ true
cr-nuance-g-stability-present = refl

cr-nuance-env-present :
  isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle envChannelIndex) ≡ true
cr-nuance-env-present = refl

cr-nuance-present-count : CrExceptionContinuumBundleWitness.present-count crExceptionContinuumNuanceWitness ≡ 5
cr-nuance-present-count = refl

cr-nuance-concurrent-product :
  crExceptionContinuumBundleIsConcurrentProduct crExceptionContinuumNuanceWitness ≡ true
cr-nuance-concurrent-product = refl

cr-nuance-five-factors-concurrent :
  isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle oreChannelIndex) ≡ true
  × isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle isotopeMixChannelIndex) ≡ true
  × isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle purifyRefineCostChannelIndex) ≡ true
  × isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle gStabilityChannelIndex) ≡ true
  × isSlotPresent (CrExceptionContinuumBundle.slot crExceptionContinuumNuanceBundle envChannelIndex) ≡ true
  × CrExceptionContinuumBundleWitness.present-count crExceptionContinuumNuanceWitness ≡ 5
cr-nuance-five-factors-concurrent =
  cr-nuance-ore-present
  , cr-nuance-isotope-present
  , cr-nuance-purify-present
  , cr-nuance-g-stability-present
  , cr-nuance-env-present
  , cr-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : CrExceptionContinuumBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if crExceptionContinuumBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = CrExceptionContinuumBundleWitness.bundle w
       in if isSlotPresent (CrExceptionContinuumBundle.slot b i)
          then if isSlotPresent (CrExceptionContinuumBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : CrExceptionContinuumBundleWitness
unwiredWitness = mkCrExceptionContinuumBundleWitness crExceptionContinuumBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

cr-nuance-xor-product-ok :
  evaluateXorRefuse crExceptionContinuumNuanceWitness oreChannelIndex isotopeMixChannelIndex ≡ xor-product-ok
cr-nuance-xor-product-ok = refl

cr-exception-continuum-not-xor : crExceptionContinuumNotXor ≡ true
cr-exception-continuum-not-xor = refl

------------------------------------------------------------------------
-- ClassifierCrExceptionContinuumStep scaffold — continuum **conservation**
------------------------------------------------------------------------

data ClassifierCrExceptionContinuumStep : Set where
  continuum-identity : ClassifierCrExceptionContinuumStep
  slot-leaf : ℕ → ClassifierCrExceptionContinuumStep
  product-concurrent : ClassifierCrExceptionContinuumStep → ClassifierCrExceptionContinuumStep → ClassifierCrExceptionContinuumStep
  xor-mutually-exclusive : ClassifierCrExceptionContinuumStep → ClassifierCrExceptionContinuumStep → ClassifierCrExceptionContinuumStep

continuumIdentity : ClassifierCrExceptionContinuumStep
continuumIdentity = continuum-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierCrExceptionContinuumStep → ClassifierCrExceptionContinuumStep → ClassifierCrExceptionContinuumStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

oreLeaf isotopeMixLeaf purifyRefineCostLeaf gStabilityLeaf envLeaf : ClassifierCrExceptionContinuumStep
oreLeaf = slot-leaf oreChannelIndex
isotopeMixLeaf = slot-leaf isotopeMixChannelIndex
purifyRefineCostLeaf = slot-leaf purifyRefineCostChannelIndex
gStabilityLeaf = slot-leaf gStabilityChannelIndex
envLeaf = slot-leaf envChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierCrExceptionContinuumStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isContinuumIdentity : ClassifierCrExceptionContinuumStep → Bool
isContinuumIdentity continuum-identity = true
isContinuumIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at continuum-identity
------------------------------------------------------------------------

continuum-left-identity :
  ∀ (a : ClassifierCrExceptionContinuumStep) →
  isContinuumIdentity continuumIdentity ≡ true
  × isProductConcurrent (productConcurrentOp continuumIdentity a) ≡ true
continuum-left-identity a = refl , refl

continuum-right-identity :
  ∀ (a : ClassifierCrExceptionContinuumStep) →
  isProductConcurrent (productConcurrentOp a continuumIdentity) ≡ true
  × isContinuumIdentity continuumIdentity ≡ true
continuum-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-continuum :
  (∀ a → isProductConcurrent (productConcurrentOp continuumIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a continuumIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-continuum =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Cr exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedCrExceptionContinuumProduct : ClassifierCrExceptionContinuumStep
namedCrExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp
      (productConcurrentOp
        (productConcurrentOp oreLeaf isotopeMixLeaf)
        purifyRefineCostLeaf)
      gStabilityLeaf)
    envLeaf

named-cr-exception-continuum-product-concurrent :
  isProductConcurrent namedCrExceptionContinuumProduct ≡ true
  × crExceptionContinuumBundleIsConcurrentProduct crExceptionContinuumNuanceWitness ≡ true
named-cr-exception-continuum-product-concurrent = refl , cr-nuance-concurrent-product

------------------------------------------------------------------------
-- CrExceptionContinuum admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data CrExceptionContinuumAdmissibility : Set where
  continuum-admissible continuum-xor-refuse : CrExceptionContinuumAdmissibility

isContinuumPreserving : ClassifierCrExceptionContinuumStep → Bool
isContinuumPreserving continuum-identity = true
isContinuumPreserving (slot-leaf _) = true
isContinuumPreserving (product-concurrent a b) =
  isContinuumPreserving a ∧ isContinuumPreserving b
isContinuumPreserving (xor-mutually-exclusive _ _) = false

isContinuumAdmissible : ClassifierCrExceptionContinuumStep → Bool
isContinuumAdmissible step = isContinuumPreserving step

ore-leaf-admissible : isContinuumAdmissible oreLeaf ≡ true
ore-leaf-admissible = refl

isotope-mix-leaf-admissible : isContinuumAdmissible isotopeMixLeaf ≡ true
isotope-mix-leaf-admissible = refl

purify-refine-cost-leaf-admissible : isContinuumAdmissible purifyRefineCostLeaf ≡ true
purify-refine-cost-leaf-admissible = refl

g-stability-leaf-admissible : isContinuumAdmissible gStabilityLeaf ≡ true
g-stability-leaf-admissible = refl

env-leaf-admissible : isContinuumAdmissible envLeaf ≡ true
env-leaf-admissible = refl

named-cr-exception-continuum-admissible : isContinuumAdmissible namedCrExceptionContinuumProduct ≡ true
named-cr-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isContinuumAdmissible (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-g-stability-env-refuse :
  isContinuumAdmissible (xorMutuallyExclusiveOp gStabilityLeaf envLeaf) ≡ false
xor-mutually-exclusive-g-stability-env-refuse = refl

------------------------------------------------------------------------
-- Witness presence — total-claim refuse without witness
------------------------------------------------------------------------

data CrExceptionContinuumWitnessPresence : Set where
  continuum-witness-absent continuum-witness-present : CrExceptionContinuumWitnessPresence

record ClassifierCrExceptionContinuumWitness : Set where
  constructor mkClassifierCrExceptionContinuumWitness
  field
    witness-presence : CrExceptionContinuumWitnessPresence
    continuum-gap-total : ℕ

continuumWitnessAbsent : ClassifierCrExceptionContinuumWitness
continuumWitnessAbsent = mkClassifierCrExceptionContinuumWitness continuum-witness-absent zero

continuumWitnessPresentZeroGap : ClassifierCrExceptionContinuumWitness
continuumWitnessPresentZeroGap = mkClassifierCrExceptionContinuumWitness continuum-witness-present zero

continuumWitnessPresentWithGaps : ℕ → ClassifierCrExceptionContinuumWitness
continuumWitnessPresentWithGaps n = mkClassifierCrExceptionContinuumWitness continuum-witness-present n

continuumWitnessGapFree : ClassifierCrExceptionContinuumWitness → Bool
continuumWitnessGapFree (mkClassifierCrExceptionContinuumWitness continuum-witness-absent _) = false
continuumWitnessGapFree (mkClassifierCrExceptionContinuumWitness continuum-witness-present n) =
  does (n ℕ-Props.≟ zero)

continuum-witness-present-zero-gap-free :
  continuumWitnessGapFree continuumWitnessPresentZeroGap ≡ true
continuum-witness-present-zero-gap-free = refl

continuum-witness-absent-not-gap-free :
  continuumWitnessGapFree continuumWitnessAbsent ≡ false
continuum-witness-absent-not-gap-free = refl

continuum-witness-with-gaps-not-gap-free :
  ∀ n → continuumWitnessGapFree (continuumWitnessPresentWithGaps (suc n)) ≡ false
continuum-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Cr-exception-continuum **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data CrExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-continuum-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : CrExceptionContinuumVerdict

crExceptionContinuumVerdictOk : CrExceptionContinuumVerdict → Bool
crExceptionContinuumVerdictOk verdict-unwired-ok = true
crExceptionContinuumVerdictOk verdict-continuum-admissible-ok = true
crExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
crExceptionContinuumVerdictOk _ = false

evaluateCrExceptionContinuumClose :
  CrExceptionContinuumModality → ClassifierCrExceptionContinuumStep → ClassifierCrExceptionContinuumWitness
  → CrExceptionContinuumBundleWitness → Bool → CrExceptionContinuumVerdict
evaluateCrExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateCrExceptionContinuumClose cr-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateCrExceptionContinuumClose cr-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateCrExceptionContinuumClose cr-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateCrExceptionContinuumClose cr-exception-continuum-proved _ (mkClassifierCrExceptionContinuumWitness continuum-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateCrExceptionContinuumClose cr-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateCrExceptionContinuumClose cr-exception-continuum-proved _ (mkClassifierCrExceptionContinuumWitness continuum-witness-present _) w false
  with crExceptionContinuumBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-continuum-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without continuum witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-unwired namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-assumed namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-surrogate namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  crExceptionContinuumVerdictOk
    (evaluateCrExceptionContinuumClose cr-exception-continuum-unwired namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false)
    ≡ true
  × crExceptionContinuumVerdictOk
      (evaluateCrExceptionContinuumClose cr-exception-continuum-assumed namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false)
      ≡ true
  × crExceptionContinuumVerdictOk
      (evaluateCrExceptionContinuumClose cr-exception-continuum-surrogate namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without continuum witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  crExceptionContinuumVerdictOk
    (evaluateCrExceptionContinuumClose
       cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false ≡
  verdict-continuum-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-proved
    (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf)
    continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  crExceptionContinuumVerdictOk
    (evaluateCrExceptionContinuumClose
       cr-exception-continuum-proved
       (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf)
       continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-proved
    (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf)
    continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-continuum — nuance **product** closed
------------------------------------------------------------------------

continuum-admissible-ok :
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap unwiredWitness false ≡
  verdict-continuum-admissible-ok
continuum-admissible-ok = refl

continuum-admissible-verdict-ok :
  crExceptionContinuumVerdictOk
    (evaluateCrExceptionContinuumClose
       cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap unwiredWitness false)
    ≡ true
continuum-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — Cr exception continuum nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  crExceptionContinuumVerdictOk
    (evaluateCrExceptionContinuumClose
       cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-cr-exception-continuum-proved :
  crExceptionContinuumVerdictOk
    (evaluateCrExceptionContinuumClose
       cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness false)
    ≡ true
  × crExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-cr-exception-continuum-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateCrExceptionContinuumClose
    cr-exception-continuum-unwired namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  crExceptionContinuumVerdictOk
    (evaluateCrExceptionContinuumClose
       cr-exception-continuum-unwired namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

crExceptionContinuumFiberOk : FormalFiber → Bool
crExceptionContinuumFiberOk fiber-quantum-knowing = true
crExceptionContinuumFiberOk fiber-meso-acting = false

cr-exception-continuum-knowing-fiber-ok :
  crExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
cr-exception-continuum-knowing-fiber-ok = refl

cr-exception-continuum-meso-acting-not-ok :
  crExceptionContinuumFiberOk fiber-meso-acting ≡ false
cr-exception-continuum-meso-acting-not-ok = refl

cr-exception-continuum-routes-knowing-not-meso :
  crExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  crExceptionContinuumFiberOk fiber-meso-acting ≡ false
cr-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  crExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (crExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Cr exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

cr-exception-continuum-not-proved : crExceptionContinuumProved ≡ false
cr-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

cr-exception-continuum-second-law-conservation-framed :
  crExceptionContinuumSecondLawConservationFramed ≡ true
cr-exception-continuum-second-law-conservation-framed = refl

cr-exception-continuum-not-xor-pin : crExceptionContinuumNotXor ≡ true
cr-exception-continuum-not-xor-pin = cr-exception-continuum-not-xor

occupancy-engine-sort-cited-pin : occupancyEngineSortCited ≡ true
occupancy-engine-sort-cited-pin = refl

goldschmidt-cited-read-only-pin : goldschmidtCitedReadOnly ≡ true
goldschmidt-cited-read-only-pin = refl

not-parallel-cr-exception-continuum-axiom-minted-pin :
  notParallelCrExceptionContinuumAxiomMinted ≡ true
not-parallel-cr-exception-continuum-axiom-minted-pin = refl

occupancy-engine-sort-not-proved-pin : occupancyEngineSortProved ≡ false
occupancy-engine-sort-not-proved-pin = occupancy-engine-sort-not-proved

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel cr-exception-continuum axiom fork)
------------------------------------------------------------------------

crExceptionContinuumAxiom :
  (crExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (crExceptionContinuumSecondLawConservationFramed ≡ true)
  × (crExceptionContinuumNotXor ≡ true)
  × (homologNotCopy ≡ true)
  × (occupancyEngineSortCited ≡ true)
  × (evaluateCrExceptionContinuumClose cr-exception-continuum-unwired namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateCrExceptionContinuumClose cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessAbsent crExceptionContinuumNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateCrExceptionContinuumClose cr-exception-continuum-proved (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf) continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateCrExceptionContinuumClose cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap unwiredWitness false ≡ verdict-continuum-admissible-ok)
  × (evaluateCrExceptionContinuumClose cr-exception-continuum-proved namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (crExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (crExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (crExceptionContinuumVerdictOk (evaluateCrExceptionContinuumClose cr-exception-continuum-unwired namedCrExceptionContinuumProduct continuumWitnessPresentZeroGap crExceptionContinuumNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp continuumIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a continuumIdentity) ≡ true)
  × (isContinuumAdmissible (xorMutuallyExclusiveOp oreLeaf isotopeMixLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (elementAtomicZ chromium ≡ 24)
  × (elementAtomicZ molybdenum ≡ 42)
  × (CrExceptionContinuumBundleWitness.present-count crExceptionContinuumNuanceWitness ≡ 5)
  × (isDBlockExceptionBucket (occupancyEngineSortBucket (DBlockException-z dblock-Cr)) ≡ true)
  × (evaluateHomologCopy (elementAtomicZ molybdenum) (elementAtomicZ chromium) ≡ homolog-not-copy)
crExceptionContinuumAxiom =
  cr-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , cr-exception-continuum-second-law-conservation-framed
  , cr-exception-continuum-not-xor-pin
  , homolog-not-copy-pin
  , occupancy-engine-sort-cited-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , continuum-admissible-ok
  , concurrent-product-ok
  , cr-exception-continuum-knowing-fiber-ok
  , cr-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , chromium-z-24
  , molybdenum-z-42
  , cr-nuance-present-count
  , cr-sorts-dblock-bucket
  , mo-cr-homolog-not-copy

crExceptionContinuumNamed : String
crExceptionContinuumNamed =
  "crExceptionContinuum: Cr Z=24 DBlock occupancy-engine sort exception continuum concurrent Pi_c identity conserved ore isotope mix purify Refine-cost G-stability Env concurrent product identity conserved present ge 2 product not XOR homolog not copy occupancy engine sort cited Goldschmidt read-only no parallel cr exception continuum axiom"

crExceptionContinuumCrossWitnessAuthority : String
crExceptionContinuumCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/cr_exception_continuum.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

goldschmidtTableAuthority : String
goldschmidtTableAuthority =
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"

qlatticeAuthority : String
qlatticeAuthority = dblockOccupancyQlatticeAuthority

madelungWitnessAuthority : String
madelungWitnessAuthority = dblockOccupancyMadelungWitnessAuthority

crExceptionContinuumCellId : String
crExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-CR-EXCEPTION-CONTINUUM"

crExceptionContinuumNonClaim : String
crExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-CR-EXCEPTION-CONTINUUM Cr Z=24 DBlock occupancy-engine sort exception continuum concurrent Pi_c identity conserved ore isotope mix purify Refine-cost G-stability Env product not XOR homolog Mo Z=42 not copy occupancy engine sort cited Goldschmidt read-only XOR mutually exclusive refuse cr exception continuum nuance witness concurrent crExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite cr_exception_continuum.rs occupancy_engine_sort.rs not fork not physics GREEN not production_wired"

cr-exception-continuum-cell-id :
  crExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-CR-EXCEPTION-CONTINUUM"
cr-exception-continuum-cell-id = refl

cr-exception-continuum-cites-cross-witness-rs :
  crExceptionContinuumCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/cr_exception_continuum.rs"
cr-exception-continuum-cites-cross-witness-rs = refl

cr-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
cr-exception-continuum-cites-occupancy-engine-sort-rs = refl

cr-exception-continuum-cites-goldschmidt-rs :
  goldschmidtTableAuthority ≡
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"
cr-exception-continuum-cites-goldschmidt-rs = refl

cr-exception-continuum-modality-unwired :
  crExceptionContinuumModalityCurrent ≡ cr-exception-continuum-unwired
cr-exception-continuum-modality-unwired = refl

CrExceptionContinuumPhysicsGreenAuthorized : Set
CrExceptionContinuumPhysicsGreenAuthorized = ⊥

cr-exception-continuum-physics-green-false : ¬ CrExceptionContinuumPhysicsGreenAuthorized
cr-exception-continuum-physics-green-false ()

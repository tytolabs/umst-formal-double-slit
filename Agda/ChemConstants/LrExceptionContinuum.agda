-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.LrExceptionContinuum.agda
--
-- Lr Z=103 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Lr exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Lr exception continuum** laws Unwired (lrExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_103_lr.rs
-- Homolog sibling: umst/umst-chem/src/elements/z_071_lu.rs (Lu Z=71 ≠ Lr occupancy copy)
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/MoExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Lr Z=103 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.LrExceptionContinuum where


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
-- Modality + Lr Z=103 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data LrExceptionContinuumModality : Set where
  lr-exception-continuum-unwired lr-exception-continuum-assumed
    lr-exception-continuum-proved lr-exception-continuum-surrogate
    : LrExceptionContinuumModality

lrExceptionContinuumModalityCurrent : LrExceptionContinuumModality
lrExceptionContinuumModalityCurrent = lr-exception-continuum-unwired

lrExceptionContinuumProved productionWired not118SquaredGreenTable
  lrExceptionContinuumSecondLawConservationFramed lrExceptionContinuumNotXor : Bool
lrExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
lrExceptionContinuumSecondLawConservationFramed = true
lrExceptionContinuumNotXor = true

occupancyEngineSortTyped notParallelOccupancyAxiomMinted homologNotCopyNotForked : Bool
occupancyEngineSortTyped = true
notParallelOccupancyAxiomMinted = true
homologNotCopyNotForked = true

------------------------------------------------------------------------
-- IUPAC table cardinality 118 — Π_c structure, not 118²
------------------------------------------------------------------------

iupacTableCardinality : ℕ
iupacTableCardinality = 118

iupac-table-cardinality-one-eighteen : iupacTableCardinality ≡ 118
iupac-table-cardinality-one-eighteen = refl

iupac-table-not-118-squared :
  does (iupacTableCardinality ℕ-Props.≟ (118 * 118)) ≡ false
iupac-table-not-118-squared = refl

------------------------------------------------------------------------
-- Lr Z=103 occupancy-engine sort index pin
------------------------------------------------------------------------

lrZ103OccupancyEngineSortIndex : ℕ
lrZ103OccupancyEngineSortIndex = 103

lr-z103-occupancy-engine-sort-index : lrZ103OccupancyEngineSortIndex ≡ 103
lr-z103-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Lr (Z=103), Lu (Z=71 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  lawrencium lutetium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ lawrencium = 103
elementAtomicZ lutetium = 71

lawrencium-z-103 : elementAtomicZ lawrencium ≡ 103
lawrencium-z-103 = refl

lutetium-z-71 : elementAtomicZ lutetium ≡ 71
lutetium-z-71 = refl

------------------------------------------------------------------------
-- LrExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data LrExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : LrExceptionBundleSlot

isSlotPresent : LrExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- LrExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record LrExceptionBundle : Set where
  field slot : ℕ → LrExceptionBundleSlot

lrExceptionBundleUnwired : LrExceptionBundle
lrExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : LrExceptionBundle → ℕ → LrExceptionBundleSlot → LrExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else LrExceptionBundle.slot b j }

withPresent : LrExceptionBundle → ℕ → LrExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record LrExceptionBundleWitness : Set where
  constructor mkLrExceptionBundleWitness
  field
    bundle : LrExceptionBundle
    present-count : ℕ

lrExceptionBundleIsConcurrentProduct : LrExceptionBundleWitness → Bool
lrExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? LrExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Lr exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
------------------------------------------------------------------------

occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex continuumEnvRestrictionChannelIndex : ℕ
occupancyEngineSortDBlockChannelIndex = 1
madelungExceptionTheoremChannelIndex = 2
continuumEnvRestrictionChannelIndex = 3

occupancy-engine-sort-dblock-index-one : occupancyEngineSortDBlockChannelIndex ≡ 1
occupancy-engine-sort-dblock-index-one = refl

madelung-exception-theorem-index-two : madelungExceptionTheoremChannelIndex ≡ 2
madelung-exception-theorem-index-two = refl

continuum-env-restriction-index-three : continuumEnvRestrictionChannelIndex ≡ 3
continuum-env-restriction-index-three = refl

------------------------------------------------------------------------
-- Lr exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

lrExceptionContinuumWitnessBundle : LrExceptionBundle
lrExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent lrExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

lrExceptionContinuumWitness : LrExceptionBundleWitness
lrExceptionContinuumWitness =
  mkLrExceptionBundleWitness lrExceptionContinuumWitnessBundle 3

lr-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (LrExceptionBundle.slot lrExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
lr-exception-occupancy-engine-sort-dblock-present = refl

lr-exception-madelung-exception-theorem-present :
  isSlotPresent (LrExceptionBundle.slot lrExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
lr-exception-madelung-exception-theorem-present = refl

lr-exception-continuum-env-restriction-present :
  isSlotPresent (LrExceptionBundle.slot lrExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
lr-exception-continuum-env-restriction-present = refl

lr-exception-present-count : LrExceptionBundleWitness.present-count lrExceptionContinuumWitness ≡ 3
lr-exception-present-count = refl

lr-exception-concurrent-product :
  lrExceptionBundleIsConcurrentProduct lrExceptionContinuumWitness ≡ true
lr-exception-concurrent-product = refl

lr-exception-three-factors-concurrent :
  isSlotPresent (LrExceptionBundle.slot lrExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (LrExceptionBundle.slot lrExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (LrExceptionBundle.slot lrExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × LrExceptionBundleWitness.present-count lrExceptionContinuumWitness ≡ 3
lr-exception-three-factors-concurrent =
  lr-exception-occupancy-engine-sort-dblock-present
  , lr-exception-madelung-exception-theorem-present
  , lr-exception-continuum-env-restriction-present
  , lr-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : LrExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if lrExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = LrExceptionBundleWitness.bundle w
       in if isSlotPresent (LrExceptionBundle.slot b i)
          then if isSlotPresent (LrExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : LrExceptionBundleWitness
unwiredWitness = mkLrExceptionBundleWitness lrExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

lr-exception-xor-product-ok :
  evaluateXorRefuse lrExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
lr-exception-xor-product-ok = refl

lr-exception-not-xor : lrExceptionContinuumNotXor ≡ true
lr-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierLrExceptionStep scaffold — LrExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierLrExceptionStep : Set where
  lr-exception-identity : ClassifierLrExceptionStep
  slot-leaf : ℕ → ClassifierLrExceptionStep
  product-concurrent : ClassifierLrExceptionStep → ClassifierLrExceptionStep → ClassifierLrExceptionStep
  xor-mutually-exclusive : ClassifierLrExceptionStep → ClassifierLrExceptionStep → ClassifierLrExceptionStep

lrExceptionIdentity : ClassifierLrExceptionStep
lrExceptionIdentity = lr-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierLrExceptionStep → ClassifierLrExceptionStep → ClassifierLrExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierLrExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierLrExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isLrExceptionIdentity : ClassifierLrExceptionStep → Bool
isLrExceptionIdentity lr-exception-identity = true
isLrExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at lr-exception-identity
------------------------------------------------------------------------

lr-exception-left-identity :
  ∀ (a : ClassifierLrExceptionStep) →
  isLrExceptionIdentity lrExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp lrExceptionIdentity a) ≡ true
lr-exception-left-identity a = refl , refl

lr-exception-right-identity :
  ∀ (a : ClassifierLrExceptionStep) →
  isProductConcurrent (productConcurrentOp a lrExceptionIdentity) ≡ true
  × isLrExceptionIdentity lrExceptionIdentity ≡ true
lr-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-lr-exception :
  (∀ a → isProductConcurrent (productConcurrentOp lrExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a lrExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-lr-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Lr exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedLrExceptionContinuumProduct : ClassifierLrExceptionStep
namedLrExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-lr-exception-continuum-product-concurrent :
  isProductConcurrent namedLrExceptionContinuumProduct ≡ true
  × lrExceptionBundleIsConcurrentProduct lrExceptionContinuumWitness ≡ true
named-lr-exception-continuum-product-concurrent = refl , lr-exception-concurrent-product

------------------------------------------------------------------------
-- LrExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data LrExceptionAdmissibility : Set where
  lr-exception-admissible lr-exception-xor-refuse : LrExceptionAdmissibility

isLrExceptionPreserving : ClassifierLrExceptionStep → Bool
isLrExceptionPreserving lr-exception-identity = true
isLrExceptionPreserving (slot-leaf _) = true
isLrExceptionPreserving (product-concurrent a b) =
  isLrExceptionPreserving a ∧ isLrExceptionPreserving b
isLrExceptionPreserving (xor-mutually-exclusive _ _) = false

isLrExceptionAdmissible : ClassifierLrExceptionStep → Bool
isLrExceptionAdmissible step = isLrExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isLrExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isLrExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isLrExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-lr-exception-continuum-admissible : isLrExceptionAdmissible namedLrExceptionContinuumProduct ≡ true
named-lr-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isLrExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isLrExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data LrExceptionWitnessPresence : Set where
  lr-exception-witness-absent lr-exception-witness-present : LrExceptionWitnessPresence

record ClassifierLrExceptionWitness : Set where
  constructor mkClassifierLrExceptionWitness
  field
    witness-presence : LrExceptionWitnessPresence
    lr-exception-gap-total : ℕ

lrExceptionWitnessAbsent : ClassifierLrExceptionWitness
lrExceptionWitnessAbsent = mkClassifierLrExceptionWitness lr-exception-witness-absent zero

lrExceptionWitnessPresentZeroGap : ClassifierLrExceptionWitness
lrExceptionWitnessPresentZeroGap = mkClassifierLrExceptionWitness lr-exception-witness-present zero

lrExceptionWitnessPresentWithGaps : ℕ → ClassifierLrExceptionWitness
lrExceptionWitnessPresentWithGaps n = mkClassifierLrExceptionWitness lr-exception-witness-present n

lrExceptionWitnessGapFree : ClassifierLrExceptionWitness → Bool
lrExceptionWitnessGapFree (mkClassifierLrExceptionWitness lr-exception-witness-absent _) = false
lrExceptionWitnessGapFree (mkClassifierLrExceptionWitness lr-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

lr-exception-witness-present-zero-gap-free :
  lrExceptionWitnessGapFree lrExceptionWitnessPresentZeroGap ≡ true
lr-exception-witness-present-zero-gap-free = refl

lr-exception-witness-absent-not-gap-free :
  lrExceptionWitnessGapFree lrExceptionWitnessAbsent ≡ false
lr-exception-witness-absent-not-gap-free = refl

lr-exception-witness-with-gaps-not-gap-free :
  ∀ n → lrExceptionWitnessGapFree (lrExceptionWitnessPresentWithGaps (suc n)) ≡ false
lr-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-LrException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data LrExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-lr-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : LrExceptionContinuumVerdict

lrExceptionContinuumVerdictOk : LrExceptionContinuumVerdict → Bool
lrExceptionContinuumVerdictOk verdict-unwired-ok = true
lrExceptionContinuumVerdictOk verdict-lr-exception-admissible-ok = true
lrExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
lrExceptionContinuumVerdictOk _ = false

evaluateLrExceptionContinuumClose :
  LrExceptionContinuumModality → ClassifierLrExceptionStep → ClassifierLrExceptionWitness
  → LrExceptionBundleWitness → Bool → LrExceptionContinuumVerdict
evaluateLrExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateLrExceptionContinuumClose lr-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateLrExceptionContinuumClose lr-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateLrExceptionContinuumClose lr-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateLrExceptionContinuumClose lr-exception-continuum-proved _ (mkClassifierLrExceptionWitness lr-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateLrExceptionContinuumClose lr-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateLrExceptionContinuumClose lr-exception-continuum-proved _ (mkClassifierLrExceptionWitness lr-exception-witness-present _) w false
  with lrExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-lr-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-unwired namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-assumed namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-surrogate namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  lrExceptionContinuumVerdictOk
    (evaluateLrExceptionContinuumClose lr-exception-continuum-unwired namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false)
    ≡ true
  × lrExceptionContinuumVerdictOk
      (evaluateLrExceptionContinuumClose lr-exception-continuum-assumed namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false)
      ≡ true
  × lrExceptionContinuumVerdictOk
      (evaluateLrExceptionContinuumClose lr-exception-continuum-surrogate namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  lrExceptionContinuumVerdictOk
    (evaluateLrExceptionContinuumClose
       lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

MoTotalClaimWhenWitnessAbsent : Set
MoTotalClaimWhenWitnessAbsent =
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false ≡
  verdict-lr-exception-admissible-ok

total-claim-⊥-when-witness-absent : MoTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  lrExceptionContinuumVerdictOk
    (evaluateLrExceptionContinuumClose
       lr-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

MoXorMutuallyExclusiveWhenConcurrent : Set
MoXorMutuallyExclusiveWhenConcurrent =
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : MoXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

lr-exception-admissible-ok :
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-lr-exception-admissible-ok
lr-exception-admissible-ok = refl

lr-exception-admissible-verdict-ok :
  lrExceptionContinuumVerdictOk
    (evaluateLrExceptionContinuumClose
       lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
lr-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  lrExceptionContinuumVerdictOk
    (evaluateLrExceptionContinuumClose
       lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-lr-exception-proved :
  lrExceptionContinuumVerdictOk
    (evaluateLrExceptionContinuumClose
       lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness false)
    ≡ true
  × lrExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-lr-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateLrExceptionContinuumClose
    lr-exception-continuum-unwired namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  lrExceptionContinuumVerdictOk
    (evaluateLrExceptionContinuumClose
       lr-exception-continuum-unwired namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

lrExceptionContinuumFiberOk : FormalFiber → Bool
lrExceptionContinuumFiberOk fiber-quantum-knowing = true
lrExceptionContinuumFiberOk fiber-meso-acting = false

lr-exception-continuum-knowing-fiber-ok :
  lrExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
lr-exception-continuum-knowing-fiber-ok = refl

lr-exception-continuum-meso-acting-not-ok :
  lrExceptionContinuumFiberOk fiber-meso-acting ≡ false
lr-exception-continuum-meso-acting-not-ok = refl

lr-exception-continuum-routes-knowing-not-meso :
  lrExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  lrExceptionContinuumFiberOk fiber-meso-acting ≡ false
lr-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  lrExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (lrExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Lr exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

lr-exception-continuum-not-proved : lrExceptionContinuumProved ≡ false
lr-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

lr-exception-continuum-second-law-conservation-framed : lrExceptionContinuumSecondLawConservationFramed ≡ true
lr-exception-continuum-second-law-conservation-framed = refl

lr-exception-not-xor-pin : lrExceptionContinuumNotXor ≡ true
lr-exception-not-xor-pin = lr-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

lrExceptionContinuumAxiom :
  (lrExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (lrExceptionContinuumSecondLawConservationFramed ≡ true)
  × (lrExceptionContinuumNotXor ≡ true)
  × (evaluateLrExceptionContinuumClose lr-exception-continuum-unwired namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateLrExceptionContinuumClose lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessAbsent lrExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateLrExceptionContinuumClose lr-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateLrExceptionContinuumClose lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-lr-exception-admissible-ok)
  × (evaluateLrExceptionContinuumClose lr-exception-continuum-proved namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (lrExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (lrExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (lrExceptionContinuumVerdictOk (evaluateLrExceptionContinuumClose lr-exception-continuum-unwired namedLrExceptionContinuumProduct lrExceptionWitnessPresentZeroGap lrExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp lrExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a lrExceptionIdentity) ≡ true)
  × (isLrExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (lrZ103OccupancyEngineSortIndex ≡ 103)
  × (LrExceptionBundleWitness.present-count lrExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ lawrencium ≡ 103)
  × (elementAtomicZ lutetium ≡ 71)
lrExceptionContinuumAxiom =
  lr-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , lr-exception-continuum-second-law-conservation-framed
  , lr-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , lr-exception-admissible-ok
  , concurrent-product-ok
  , lr-exception-continuum-knowing-fiber-ok
  , lr-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , lr-z103-occupancy-engine-sort-index
  , lr-exception-present-count
  , lawrencium-z-103
  , lutetium-z-71

lrExceptionContinuumNamed : String
lrExceptionContinuumNamed =
  "lrExceptionContinuum: Lr Z=103 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

lrExceptionContinuumAuthority : String
lrExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_103_lr.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

lrExceptionContinuumCellId : String
lrExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-LR-EXCEPTION-CONTINUUM"

lrExceptionContinuumNonClaim : String
lrExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-LR-EXCEPTION-CONTINUUM Lr Z=103 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Lr exception continuum witness concurrent lrExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_103_lr.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

lr-exception-continuum-cell-id :
  lrExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-LR-EXCEPTION-CONTINUUM"
lr-exception-continuum-cell-id = refl

lr-exception-continuum-cites-z103-lr-rs :
  lrExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_103_lr.rs"
lr-exception-continuum-cites-z103-lr-rs = refl

lr-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
lr-exception-continuum-cites-occupancy-engine-sort-rs = refl

lr-exception-continuum-modality-unwired :
  lrExceptionContinuumModalityCurrent ≡ lr-exception-continuum-unwired
lr-exception-continuum-modality-unwired = refl

lrExceptionContinuumPhysicsGreenAuthorized : Set
lrExceptionContinuumPhysicsGreenAuthorized = ⊥

lr-exception-continuum-physics-green-false : ¬ lrExceptionContinuumPhysicsGreenAuthorized
lr-exception-continuum-physics-green-false ()

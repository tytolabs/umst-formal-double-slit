-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.RhExceptionContinuum.agda
--
-- Rh Z=45 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Rh exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Rh exception continuum** laws Unwired (rhExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_045_rh.rs
-- Homolog Co Z=27 / Ir Z=77 — not Co 3d⁷4s² copy, not Ir Xe-core chart copy.
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog Co Ir not copy. Product not XOR.
-- Rh Z=45 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.RhExceptionContinuum where


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
-- Modality + Rh Z=45 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data RhExceptionContinuumModality : Set where
  rh-exception-continuum-unwired rh-exception-continuum-assumed
    rh-exception-continuum-proved rh-exception-continuum-surrogate
    : RhExceptionContinuumModality

rhExceptionContinuumModalityCurrent : RhExceptionContinuumModality
rhExceptionContinuumModalityCurrent = rh-exception-continuum-unwired

rhExceptionContinuumProved productionWired not118SquaredGreenTable
  rhExceptionContinuumSecondLawConservationFramed rhExceptionContinuumNotXor : Bool
rhExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
rhExceptionContinuumSecondLawConservationFramed = true
rhExceptionContinuumNotXor = true

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
-- Rh Z=45 occupancy-engine sort index pin
------------------------------------------------------------------------

rhZ45OccupancyEngineSortIndex : ℕ
rhZ45OccupancyEngineSortIndex = 45

rh-z45-occupancy-engine-sort-index : rhZ45OccupancyEngineSortIndex ≡ 45
rh-z45-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Rh (Z=45), Co (Z=27 homolog), Ir (Z=77 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  rhodium cobalt iridium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ rhodium = 45
elementAtomicZ cobalt = 27
elementAtomicZ iridium = 77

rhodium-z-45 : elementAtomicZ rhodium ≡ 45
rhodium-z-45 = refl

cobalt-z-27 : elementAtomicZ cobalt ≡ 27
cobalt-z-27 = refl

iridium-z-77 : elementAtomicZ iridium ≡ 77
iridium-z-77 = refl

------------------------------------------------------------------------
-- RhExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data RhExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : RhExceptionBundleSlot

isSlotPresent : RhExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- RhExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record RhExceptionBundle : Set where
  field slot : ℕ → RhExceptionBundleSlot

rhExceptionBundleUnwired : RhExceptionBundle
rhExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : RhExceptionBundle → ℕ → RhExceptionBundleSlot → RhExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else RhExceptionBundle.slot b j }

withPresent : RhExceptionBundle → ℕ → RhExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record RhExceptionBundleWitness : Set where
  constructor mkRhExceptionBundleWitness
  field
    bundle : RhExceptionBundle
    present-count : ℕ

rhExceptionBundleIsConcurrentProduct : RhExceptionBundleWitness → Bool
rhExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? RhExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Rh exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Rh exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

rhExceptionContinuumWitnessBundle : RhExceptionBundle
rhExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent rhExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

rhExceptionContinuumWitness : RhExceptionBundleWitness
rhExceptionContinuumWitness =
  mkRhExceptionBundleWitness rhExceptionContinuumWitnessBundle 3

rh-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (RhExceptionBundle.slot rhExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
rh-exception-occupancy-engine-sort-dblock-present = refl

rh-exception-madelung-exception-theorem-present :
  isSlotPresent (RhExceptionBundle.slot rhExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
rh-exception-madelung-exception-theorem-present = refl

rh-exception-continuum-env-restriction-present :
  isSlotPresent (RhExceptionBundle.slot rhExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
rh-exception-continuum-env-restriction-present = refl

rh-exception-present-count : RhExceptionBundleWitness.present-count rhExceptionContinuumWitness ≡ 3
rh-exception-present-count = refl

rh-exception-concurrent-product :
  rhExceptionBundleIsConcurrentProduct rhExceptionContinuumWitness ≡ true
rh-exception-concurrent-product = refl

rh-exception-three-factors-concurrent :
  isSlotPresent (RhExceptionBundle.slot rhExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (RhExceptionBundle.slot rhExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (RhExceptionBundle.slot rhExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × RhExceptionBundleWitness.present-count rhExceptionContinuumWitness ≡ 3
rh-exception-three-factors-concurrent =
  rh-exception-occupancy-engine-sort-dblock-present
  , rh-exception-madelung-exception-theorem-present
  , rh-exception-continuum-env-restriction-present
  , rh-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : RhExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if rhExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = RhExceptionBundleWitness.bundle w
       in if isSlotPresent (RhExceptionBundle.slot b i)
          then if isSlotPresent (RhExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : RhExceptionBundleWitness
unwiredWitness = mkRhExceptionBundleWitness rhExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

rh-exception-xor-product-ok :
  evaluateXorRefuse rhExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
rh-exception-xor-product-ok = refl

rh-exception-not-xor : rhExceptionContinuumNotXor ≡ true
rh-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierRhExceptionStep scaffold — RhExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierRhExceptionStep : Set where
  rh-exception-identity : ClassifierRhExceptionStep
  slot-leaf : ℕ → ClassifierRhExceptionStep
  product-concurrent : ClassifierRhExceptionStep → ClassifierRhExceptionStep → ClassifierRhExceptionStep
  xor-mutually-exclusive : ClassifierRhExceptionStep → ClassifierRhExceptionStep → ClassifierRhExceptionStep

rhExceptionIdentity : ClassifierRhExceptionStep
rhExceptionIdentity = rh-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierRhExceptionStep → ClassifierRhExceptionStep → ClassifierRhExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierRhExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierRhExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isRhExceptionIdentity : ClassifierRhExceptionStep → Bool
isRhExceptionIdentity rh-exception-identity = true
isRhExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at rh-exception-identity
------------------------------------------------------------------------

rh-exception-left-identity :
  ∀ (a : ClassifierRhExceptionStep) →
  isRhExceptionIdentity rhExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp rhExceptionIdentity a) ≡ true
rh-exception-left-identity a = refl , refl

rh-exception-right-identity :
  ∀ (a : ClassifierRhExceptionStep) →
  isProductConcurrent (productConcurrentOp a rhExceptionIdentity) ≡ true
  × isRhExceptionIdentity rhExceptionIdentity ≡ true
rh-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-rh-exception :
  (∀ a → isProductConcurrent (productConcurrentOp rhExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a rhExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-rh-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Rh exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedRhExceptionContinuumProduct : ClassifierRhExceptionStep
namedRhExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-rh-exception-continuum-product-concurrent :
  isProductConcurrent namedRhExceptionContinuumProduct ≡ true
  × rhExceptionBundleIsConcurrentProduct rhExceptionContinuumWitness ≡ true
named-rh-exception-continuum-product-concurrent = refl , rh-exception-concurrent-product

------------------------------------------------------------------------
-- RhExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data RhExceptionAdmissibility : Set where
  rh-exception-admissible rh-exception-xor-refuse : RhExceptionAdmissibility

isRhExceptionPreserving : ClassifierRhExceptionStep → Bool
isRhExceptionPreserving rh-exception-identity = true
isRhExceptionPreserving (slot-leaf _) = true
isRhExceptionPreserving (product-concurrent a b) =
  isRhExceptionPreserving a ∧ isRhExceptionPreserving b
isRhExceptionPreserving (xor-mutually-exclusive _ _) = false

isRhExceptionAdmissible : ClassifierRhExceptionStep → Bool
isRhExceptionAdmissible step = isRhExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isRhExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isRhExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isRhExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-rh-exception-continuum-admissible : isRhExceptionAdmissible namedRhExceptionContinuumProduct ≡ true
named-rh-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isRhExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isRhExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data RhExceptionWitnessPresence : Set where
  rh-exception-witness-absent rh-exception-witness-present : RhExceptionWitnessPresence

record ClassifierRhExceptionWitness : Set where
  constructor mkClassifierRhExceptionWitness
  field
    witness-presence : RhExceptionWitnessPresence
    rh-exception-gap-total : ℕ

rhExceptionWitnessAbsent : ClassifierRhExceptionWitness
rhExceptionWitnessAbsent = mkClassifierRhExceptionWitness rh-exception-witness-absent zero

rhExceptionWitnessPresentZeroGap : ClassifierRhExceptionWitness
rhExceptionWitnessPresentZeroGap = mkClassifierRhExceptionWitness rh-exception-witness-present zero

rhExceptionWitnessPresentWithGaps : ℕ → ClassifierRhExceptionWitness
rhExceptionWitnessPresentWithGaps n = mkClassifierRhExceptionWitness rh-exception-witness-present n

rhExceptionWitnessGapFree : ClassifierRhExceptionWitness → Bool
rhExceptionWitnessGapFree (mkClassifierRhExceptionWitness rh-exception-witness-absent _) = false
rhExceptionWitnessGapFree (mkClassifierRhExceptionWitness rh-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

rh-exception-witness-present-zero-gap-free :
  rhExceptionWitnessGapFree rhExceptionWitnessPresentZeroGap ≡ true
rh-exception-witness-present-zero-gap-free = refl

rh-exception-witness-absent-not-gap-free :
  rhExceptionWitnessGapFree rhExceptionWitnessAbsent ≡ false
rh-exception-witness-absent-not-gap-free = refl

rh-exception-witness-with-gaps-not-gap-free :
  ∀ n → rhExceptionWitnessGapFree (rhExceptionWitnessPresentWithGaps (suc n)) ≡ false
rh-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-RhException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data RhExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-rh-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : RhExceptionContinuumVerdict

rhExceptionContinuumVerdictOk : RhExceptionContinuumVerdict → Bool
rhExceptionContinuumVerdictOk verdict-unwired-ok = true
rhExceptionContinuumVerdictOk verdict-rh-exception-admissible-ok = true
rhExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
rhExceptionContinuumVerdictOk _ = false

evaluateRhExceptionContinuumClose :
  RhExceptionContinuumModality → ClassifierRhExceptionStep → ClassifierRhExceptionWitness
  → RhExceptionBundleWitness → Bool → RhExceptionContinuumVerdict
evaluateRhExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateRhExceptionContinuumClose rh-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateRhExceptionContinuumClose rh-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateRhExceptionContinuumClose rh-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateRhExceptionContinuumClose rh-exception-continuum-proved _ (mkClassifierRhExceptionWitness rh-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateRhExceptionContinuumClose rh-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateRhExceptionContinuumClose rh-exception-continuum-proved _ (mkClassifierRhExceptionWitness rh-exception-witness-present _) w false
  with rhExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-rh-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-unwired namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-assumed namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-surrogate namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  rhExceptionContinuumVerdictOk
    (evaluateRhExceptionContinuumClose rh-exception-continuum-unwired namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false)
    ≡ true
  × rhExceptionContinuumVerdictOk
      (evaluateRhExceptionContinuumClose rh-exception-continuum-assumed namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false)
      ≡ true
  × rhExceptionContinuumVerdictOk
      (evaluateRhExceptionContinuumClose rh-exception-continuum-surrogate namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  rhExceptionContinuumVerdictOk
    (evaluateRhExceptionContinuumClose
       rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

RhTotalClaimWhenWitnessAbsent : Set
RhTotalClaimWhenWitnessAbsent =
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false ≡
  verdict-rh-exception-admissible-ok

total-claim-⊥-when-witness-absent : RhTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  rhExceptionContinuumVerdictOk
    (evaluateRhExceptionContinuumClose
       rh-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

RhXorMutuallyExclusiveWhenConcurrent : Set
RhXorMutuallyExclusiveWhenConcurrent =
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : RhXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

rh-exception-admissible-ok :
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-rh-exception-admissible-ok
rh-exception-admissible-ok = refl

rh-exception-admissible-verdict-ok :
  rhExceptionContinuumVerdictOk
    (evaluateRhExceptionContinuumClose
       rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
rh-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  rhExceptionContinuumVerdictOk
    (evaluateRhExceptionContinuumClose
       rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-rh-exception-proved :
  rhExceptionContinuumVerdictOk
    (evaluateRhExceptionContinuumClose
       rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness false)
    ≡ true
  × rhExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-rh-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateRhExceptionContinuumClose
    rh-exception-continuum-unwired namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  rhExceptionContinuumVerdictOk
    (evaluateRhExceptionContinuumClose
       rh-exception-continuum-unwired namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

rhExceptionContinuumFiberOk : FormalFiber → Bool
rhExceptionContinuumFiberOk fiber-quantum-knowing = true
rhExceptionContinuumFiberOk fiber-meso-acting = false

rh-exception-continuum-knowing-fiber-ok :
  rhExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
rh-exception-continuum-knowing-fiber-ok = refl

rh-exception-continuum-meso-acting-not-ok :
  rhExceptionContinuumFiberOk fiber-meso-acting ≡ false
rh-exception-continuum-meso-acting-not-ok = refl

rh-exception-continuum-routes-knowing-not-meso :
  rhExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  rhExceptionContinuumFiberOk fiber-meso-acting ≡ false
rh-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  rhExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (rhExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Rh exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

rh-exception-continuum-not-proved : rhExceptionContinuumProved ≡ false
rh-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

rh-exception-continuum-second-law-conservation-framed : rhExceptionContinuumSecondLawConservationFramed ≡ true
rh-exception-continuum-second-law-conservation-framed = refl

rh-exception-not-xor-pin : rhExceptionContinuumNotXor ≡ true
rh-exception-not-xor-pin = rh-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

rhExceptionContinuumAxiom :
  (rhExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (rhExceptionContinuumSecondLawConservationFramed ≡ true)
  × (rhExceptionContinuumNotXor ≡ true)
  × (evaluateRhExceptionContinuumClose rh-exception-continuum-unwired namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateRhExceptionContinuumClose rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessAbsent rhExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateRhExceptionContinuumClose rh-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateRhExceptionContinuumClose rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-rh-exception-admissible-ok)
  × (evaluateRhExceptionContinuumClose rh-exception-continuum-proved namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (rhExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (rhExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (rhExceptionContinuumVerdictOk (evaluateRhExceptionContinuumClose rh-exception-continuum-unwired namedRhExceptionContinuumProduct rhExceptionWitnessPresentZeroGap rhExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp rhExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a rhExceptionIdentity) ≡ true)
  × (isRhExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (rhZ45OccupancyEngineSortIndex ≡ 45)
  × (RhExceptionBundleWitness.present-count rhExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ rhodium ≡ 45)
  × (elementAtomicZ cobalt ≡ 27)
  × (elementAtomicZ iridium ≡ 77)
rhExceptionContinuumAxiom =
  rh-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , rh-exception-continuum-second-law-conservation-framed
  , rh-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , rh-exception-admissible-ok
  , concurrent-product-ok
  , rh-exception-continuum-knowing-fiber-ok
  , rh-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , rh-z45-occupancy-engine-sort-index
  , rh-exception-present-count
  , rhodium-z-45
  , cobalt-z-27
  , iridium-z-77

rhExceptionContinuumNamed : String
rhExceptionContinuumNamed =
  "rhExceptionContinuum: Rh Z=45 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog Co Ir not copy"

rhExceptionContinuumAuthority : String
rhExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_045_rh.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

rhExceptionContinuumCellId : String
rhExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-RH-EXCEPTION-CONTINUUM"

rhExceptionContinuumNonClaim : String
rhExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-RH-EXCEPTION-CONTINUUM Rh Z=45 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog Co Ir not copy XOR mutually exclusive refuse Rh exception continuum witness concurrent rhExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_045_rh.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

rh-exception-continuum-cell-id :
  rhExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-RH-EXCEPTION-CONTINUUM"
rh-exception-continuum-cell-id = refl

rh-exception-continuum-cites-z045-rh-rs :
  rhExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_045_rh.rs"
rh-exception-continuum-cites-z045-rh-rs = refl

rh-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
rh-exception-continuum-cites-occupancy-engine-sort-rs = refl

rh-exception-continuum-modality-unwired :
  rhExceptionContinuumModalityCurrent ≡ rh-exception-continuum-unwired
rh-exception-continuum-modality-unwired = refl

rhExceptionContinuumPhysicsGreenAuthorized : Set
rhExceptionContinuumPhysicsGreenAuthorized = ⊥

rh-exception-continuum-physics-green-false : ¬ rhExceptionContinuumPhysicsGreenAuthorized
rh-exception-continuum-physics-green-false ()

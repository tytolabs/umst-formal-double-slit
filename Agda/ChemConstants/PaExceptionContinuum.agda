-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PaExceptionContinuum.agda
--
-- Pa Z=91 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Pa exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Pa exception continuum** laws Unwired (paExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_091_pa.rs
-- Homolog Th Z=90 period-7 sibling — not Th 6d²7s² copy.
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Pa Z=91 Actinide occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.PaExceptionContinuum where


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
-- Modality + Pa Z=91 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PaExceptionContinuumModality : Set where
  pa-exception-continuum-unwired pa-exception-continuum-assumed
    pa-exception-continuum-proved pa-exception-continuum-surrogate
    : PaExceptionContinuumModality

paExceptionContinuumModalityCurrent : PaExceptionContinuumModality
paExceptionContinuumModalityCurrent = pa-exception-continuum-unwired

paExceptionContinuumProved productionWired not118SquaredGreenTable
  paExceptionContinuumSecondLawConservationFramed paExceptionContinuumNotXor : Bool
paExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
paExceptionContinuumSecondLawConservationFramed = true
paExceptionContinuumNotXor = true

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
-- Pa Z=91 occupancy-engine sort index pin
------------------------------------------------------------------------

paZ91OccupancyEngineSortIndex : ℕ
paZ91OccupancyEngineSortIndex = 91

pa-z91-occupancy-engine-sort-index : paZ91OccupancyEngineSortIndex ≡ 91
pa-z91-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Pa (Z=91), Th (Z=90 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  protactinium thorium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ protactinium = 91
elementAtomicZ thorium = 90

protactinium-z-91 : elementAtomicZ protactinium ≡ 91
protactinium-z-91 = refl

thorium-z-90 : elementAtomicZ thorium ≡ 90
thorium-z-90 = refl

------------------------------------------------------------------------
-- PaExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PaExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PaExceptionBundleSlot

isSlotPresent : PaExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- PaExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record PaExceptionBundle : Set where
  field slot : ℕ → PaExceptionBundleSlot

paExceptionBundleUnwired : PaExceptionBundle
paExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : PaExceptionBundle → ℕ → PaExceptionBundleSlot → PaExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else PaExceptionBundle.slot b j }

withPresent : PaExceptionBundle → ℕ → PaExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PaExceptionBundleWitness : Set where
  constructor mkPaExceptionBundleWitness
  field
    bundle : PaExceptionBundle
    present-count : ℕ

paExceptionBundleIsConcurrentProduct : PaExceptionBundleWitness → Bool
paExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PaExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Pa exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Pa exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

paExceptionContinuumWitnessBundle : PaExceptionBundle
paExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent paExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

paExceptionContinuumWitness : PaExceptionBundleWitness
paExceptionContinuumWitness =
  mkPaExceptionBundleWitness paExceptionContinuumWitnessBundle 3

pa-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (PaExceptionBundle.slot paExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
pa-exception-occupancy-engine-sort-dblock-present = refl

pa-exception-madelung-exception-theorem-present :
  isSlotPresent (PaExceptionBundle.slot paExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
pa-exception-madelung-exception-theorem-present = refl

pa-exception-continuum-env-restriction-present :
  isSlotPresent (PaExceptionBundle.slot paExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
pa-exception-continuum-env-restriction-present = refl

pa-exception-present-count : PaExceptionBundleWitness.present-count paExceptionContinuumWitness ≡ 3
pa-exception-present-count = refl

pa-exception-concurrent-product :
  paExceptionBundleIsConcurrentProduct paExceptionContinuumWitness ≡ true
pa-exception-concurrent-product = refl

pa-exception-three-factors-concurrent :
  isSlotPresent (PaExceptionBundle.slot paExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (PaExceptionBundle.slot paExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (PaExceptionBundle.slot paExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × PaExceptionBundleWitness.present-count paExceptionContinuumWitness ≡ 3
pa-exception-three-factors-concurrent =
  pa-exception-occupancy-engine-sort-dblock-present
  , pa-exception-madelung-exception-theorem-present
  , pa-exception-continuum-env-restriction-present
  , pa-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PaExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if paExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = PaExceptionBundleWitness.bundle w
       in if isSlotPresent (PaExceptionBundle.slot b i)
          then if isSlotPresent (PaExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PaExceptionBundleWitness
unwiredWitness = mkPaExceptionBundleWitness paExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

pa-exception-xor-product-ok :
  evaluateXorRefuse paExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
pa-exception-xor-product-ok = refl

pa-exception-not-xor : paExceptionContinuumNotXor ≡ true
pa-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPaExceptionStep scaffold — PaExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierPaExceptionStep : Set where
  pa-exception-identity : ClassifierPaExceptionStep
  slot-leaf : ℕ → ClassifierPaExceptionStep
  product-concurrent : ClassifierPaExceptionStep → ClassifierPaExceptionStep → ClassifierPaExceptionStep
  xor-mutually-exclusive : ClassifierPaExceptionStep → ClassifierPaExceptionStep → ClassifierPaExceptionStep

paExceptionIdentity : ClassifierPaExceptionStep
paExceptionIdentity = pa-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPaExceptionStep → ClassifierPaExceptionStep → ClassifierPaExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierPaExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierPaExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isPaExceptionIdentity : ClassifierPaExceptionStep → Bool
isPaExceptionIdentity pa-exception-identity = true
isPaExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at pa-exception-identity
------------------------------------------------------------------------

pa-exception-left-identity :
  ∀ (a : ClassifierPaExceptionStep) →
  isPaExceptionIdentity paExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp paExceptionIdentity a) ≡ true
pa-exception-left-identity a = refl , refl

pa-exception-right-identity :
  ∀ (a : ClassifierPaExceptionStep) →
  isProductConcurrent (productConcurrentOp a paExceptionIdentity) ≡ true
  × isPaExceptionIdentity paExceptionIdentity ≡ true
pa-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-pa-exception :
  (∀ a → isProductConcurrent (productConcurrentOp paExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a paExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-pa-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Pa exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedPaExceptionContinuumProduct : ClassifierPaExceptionStep
namedPaExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-pa-exception-continuum-product-concurrent :
  isProductConcurrent namedPaExceptionContinuumProduct ≡ true
  × paExceptionBundleIsConcurrentProduct paExceptionContinuumWitness ≡ true
named-pa-exception-continuum-product-concurrent = refl , pa-exception-concurrent-product

------------------------------------------------------------------------
-- PaExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data PaExceptionAdmissibility : Set where
  pa-exception-admissible pa-exception-xor-refuse : PaExceptionAdmissibility

isPaExceptionPreserving : ClassifierPaExceptionStep → Bool
isPaExceptionPreserving pa-exception-identity = true
isPaExceptionPreserving (slot-leaf _) = true
isPaExceptionPreserving (product-concurrent a b) =
  isPaExceptionPreserving a ∧ isPaExceptionPreserving b
isPaExceptionPreserving (xor-mutually-exclusive _ _) = false

isPaExceptionAdmissible : ClassifierPaExceptionStep → Bool
isPaExceptionAdmissible step = isPaExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isPaExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isPaExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isPaExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-pa-exception-continuum-admissible : isPaExceptionAdmissible namedPaExceptionContinuumProduct ≡ true
named-pa-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isPaExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isPaExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data PaExceptionWitnessPresence : Set where
  pa-exception-witness-absent pa-exception-witness-present : PaExceptionWitnessPresence

record ClassifierPaExceptionWitness : Set where
  constructor mkClassifierPaExceptionWitness
  field
    witness-presence : PaExceptionWitnessPresence
    pa-exception-gap-total : ℕ

paExceptionWitnessAbsent : ClassifierPaExceptionWitness
paExceptionWitnessAbsent = mkClassifierPaExceptionWitness pa-exception-witness-absent zero

paExceptionWitnessPresentZeroGap : ClassifierPaExceptionWitness
paExceptionWitnessPresentZeroGap = mkClassifierPaExceptionWitness pa-exception-witness-present zero

paExceptionWitnessPresentWithGaps : ℕ → ClassifierPaExceptionWitness
paExceptionWitnessPresentWithGaps n = mkClassifierPaExceptionWitness pa-exception-witness-present n

paExceptionWitnessGapFree : ClassifierPaExceptionWitness → Bool
paExceptionWitnessGapFree (mkClassifierPaExceptionWitness pa-exception-witness-absent _) = false
paExceptionWitnessGapFree (mkClassifierPaExceptionWitness pa-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

pa-exception-witness-present-zero-gap-free :
  paExceptionWitnessGapFree paExceptionWitnessPresentZeroGap ≡ true
pa-exception-witness-present-zero-gap-free = refl

pa-exception-witness-absent-not-gap-free :
  paExceptionWitnessGapFree paExceptionWitnessAbsent ≡ false
pa-exception-witness-absent-not-gap-free = refl

pa-exception-witness-with-gaps-not-gap-free :
  ∀ n → paExceptionWitnessGapFree (paExceptionWitnessPresentWithGaps (suc n)) ≡ false
pa-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-PaException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PaExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-pa-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : PaExceptionContinuumVerdict

paExceptionContinuumVerdictOk : PaExceptionContinuumVerdict → Bool
paExceptionContinuumVerdictOk verdict-unwired-ok = true
paExceptionContinuumVerdictOk verdict-pa-exception-admissible-ok = true
paExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
paExceptionContinuumVerdictOk _ = false

evaluatePaExceptionContinuumClose :
  PaExceptionContinuumModality → ClassifierPaExceptionStep → ClassifierPaExceptionWitness
  → PaExceptionBundleWitness → Bool → PaExceptionContinuumVerdict
evaluatePaExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluatePaExceptionContinuumClose pa-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluatePaExceptionContinuumClose pa-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluatePaExceptionContinuumClose pa-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluatePaExceptionContinuumClose pa-exception-continuum-proved _ (mkClassifierPaExceptionWitness pa-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluatePaExceptionContinuumClose pa-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluatePaExceptionContinuumClose pa-exception-continuum-proved _ (mkClassifierPaExceptionWitness pa-exception-witness-present _) w false
  with paExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-pa-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-unwired namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-assumed namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-surrogate namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  paExceptionContinuumVerdictOk
    (evaluatePaExceptionContinuumClose pa-exception-continuum-unwired namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false)
    ≡ true
  × paExceptionContinuumVerdictOk
      (evaluatePaExceptionContinuumClose pa-exception-continuum-assumed namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false)
      ≡ true
  × paExceptionContinuumVerdictOk
      (evaluatePaExceptionContinuumClose pa-exception-continuum-surrogate namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  paExceptionContinuumVerdictOk
    (evaluatePaExceptionContinuumClose
       pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

PaTotalClaimWhenWitnessAbsent : Set
PaTotalClaimWhenWitnessAbsent =
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false ≡
  verdict-pa-exception-admissible-ok

total-claim-⊥-when-witness-absent : PaTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    paExceptionWitnessPresentZeroGap paExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  paExceptionContinuumVerdictOk
    (evaluatePaExceptionContinuumClose
       pa-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       paExceptionWitnessPresentZeroGap paExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

PaXorMutuallyExclusiveWhenConcurrent : Set
PaXorMutuallyExclusiveWhenConcurrent =
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    paExceptionWitnessPresentZeroGap paExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : PaXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

pa-exception-admissible-ok :
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-pa-exception-admissible-ok
pa-exception-admissible-ok = refl

pa-exception-admissible-verdict-ok :
  paExceptionContinuumVerdictOk
    (evaluatePaExceptionContinuumClose
       pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
pa-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap paExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  paExceptionContinuumVerdictOk
    (evaluatePaExceptionContinuumClose
       pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap paExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-pa-exception-proved :
  paExceptionContinuumVerdictOk
    (evaluatePaExceptionContinuumClose
       pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap paExceptionContinuumWitness false)
    ≡ true
  × paExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-pa-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePaExceptionContinuumClose
    pa-exception-continuum-unwired namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap paExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  paExceptionContinuumVerdictOk
    (evaluatePaExceptionContinuumClose
       pa-exception-continuum-unwired namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap paExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

paExceptionContinuumFiberOk : FormalFiber → Bool
paExceptionContinuumFiberOk fiber-quantum-knowing = true
paExceptionContinuumFiberOk fiber-meso-acting = false

pa-exception-continuum-knowing-fiber-ok :
  paExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
pa-exception-continuum-knowing-fiber-ok = refl

pa-exception-continuum-meso-acting-not-ok :
  paExceptionContinuumFiberOk fiber-meso-acting ≡ false
pa-exception-continuum-meso-acting-not-ok = refl

pa-exception-continuum-routes-knowing-not-meso :
  paExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  paExceptionContinuumFiberOk fiber-meso-acting ≡ false
pa-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  paExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (paExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Pa exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

pa-exception-continuum-not-proved : paExceptionContinuumProved ≡ false
pa-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

pa-exception-continuum-second-law-conservation-framed : paExceptionContinuumSecondLawConservationFramed ≡ true
pa-exception-continuum-second-law-conservation-framed = refl

pa-exception-not-xor-pin : paExceptionContinuumNotXor ≡ true
pa-exception-not-xor-pin = pa-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

paExceptionContinuumAxiom :
  (paExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (paExceptionContinuumSecondLawConservationFramed ≡ true)
  × (paExceptionContinuumNotXor ≡ true)
  × (evaluatePaExceptionContinuumClose pa-exception-continuum-unwired namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluatePaExceptionContinuumClose pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessAbsent paExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluatePaExceptionContinuumClose pa-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) paExceptionWitnessPresentZeroGap paExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluatePaExceptionContinuumClose pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-pa-exception-admissible-ok)
  × (evaluatePaExceptionContinuumClose pa-exception-continuum-proved namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap paExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (paExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (paExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (paExceptionContinuumVerdictOk (evaluatePaExceptionContinuumClose pa-exception-continuum-unwired namedPaExceptionContinuumProduct paExceptionWitnessPresentZeroGap paExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp paExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a paExceptionIdentity) ≡ true)
  × (isPaExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (paZ91OccupancyEngineSortIndex ≡ 91)
  × (PaExceptionBundleWitness.present-count paExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ protactinium ≡ 91)
  × (elementAtomicZ thorium ≡ 90)
paExceptionContinuumAxiom =
  pa-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , pa-exception-continuum-second-law-conservation-framed
  , pa-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , pa-exception-admissible-ok
  , concurrent-product-ok
  , pa-exception-continuum-knowing-fiber-ok
  , pa-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , pa-z91-occupancy-engine-sort-index
  , pa-exception-present-count
  , protactinium-z-91
  , thorium-z-90

paExceptionContinuumNamed : String
paExceptionContinuumNamed =
  "paExceptionContinuum: Pa Z=91 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

paExceptionContinuumAuthority : String
paExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_091_pa.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

paExceptionContinuumCellId : String
paExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-PA-EXCEPTION-CONTINUUM"

paExceptionContinuumNonClaim : String
paExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-PA-EXCEPTION-CONTINUUM Pa Z=91 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Pa exception continuum witness concurrent paExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_091_pa.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

pa-exception-continuum-cell-id :
  paExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-PA-EXCEPTION-CONTINUUM"
pa-exception-continuum-cell-id = refl

pa-exception-continuum-cites-z091-pa-rs :
  paExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_091_pa.rs"
pa-exception-continuum-cites-z091-pa-rs = refl

pa-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
pa-exception-continuum-cites-occupancy-engine-sort-rs = refl

pa-exception-continuum-modality-unwired :
  paExceptionContinuumModalityCurrent ≡ pa-exception-continuum-unwired
pa-exception-continuum-modality-unwired = refl

paExceptionContinuumPhysicsGreenAuthorized : Set
paExceptionContinuumPhysicsGreenAuthorized = ⊥

pa-exception-continuum-physics-green-false : ¬ paExceptionContinuumPhysicsGreenAuthorized
pa-exception-continuum-physics-green-false ()

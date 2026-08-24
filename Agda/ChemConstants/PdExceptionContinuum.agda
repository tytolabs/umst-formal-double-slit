-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PdExceptionContinuum.agda
--
-- Pd Z=46 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Pd exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Pd exception continuum** laws Unwired (pdExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_046_pd.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Pd Z=46 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.PdExceptionContinuum where


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
-- Modality + Pd Z=46 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PdExceptionContinuumModality : Set where
  pd-exception-continuum-unwired pd-exception-continuum-assumed
    pd-exception-continuum-proved pd-exception-continuum-surrogate
    : PdExceptionContinuumModality

pdExceptionContinuumModalityCurrent : PdExceptionContinuumModality
pdExceptionContinuumModalityCurrent = pd-exception-continuum-unwired

pdExceptionContinuumProved productionWired not118SquaredGreenTable
  pdExceptionContinuumSecondLawConservationFramed pdExceptionContinuumNotXor : Bool
pdExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
pdExceptionContinuumSecondLawConservationFramed = true
pdExceptionContinuumNotXor = true

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
-- Pd Z=46 occupancy-engine sort index pin
------------------------------------------------------------------------

pdZ46OccupancyEngineSortIndex : ℕ
pdZ46OccupancyEngineSortIndex = 46

pd-z46-occupancy-engine-sort-index : pdZ46OccupancyEngineSortIndex ≡ 46
pd-z46-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Pd (Z=46), Rh (Z=45 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  palladium rhodium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ palladium = 46
elementAtomicZ rhodium = 45

palladium-z-46 : elementAtomicZ palladium ≡ 46
palladium-z-46 = refl

rhodium-z-45 : elementAtomicZ rhodium ≡ 45
rhodium-z-45 = refl

------------------------------------------------------------------------
-- PdExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PdExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PdExceptionBundleSlot

isSlotPresent : PdExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- PdExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record PdExceptionBundle : Set where
  field slot : ℕ → PdExceptionBundleSlot

pdExceptionBundleUnwired : PdExceptionBundle
pdExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : PdExceptionBundle → ℕ → PdExceptionBundleSlot → PdExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else PdExceptionBundle.slot b j }

withPresent : PdExceptionBundle → ℕ → PdExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PdExceptionBundleWitness : Set where
  constructor mkPdExceptionBundleWitness
  field
    bundle : PdExceptionBundle
    present-count : ℕ

pdExceptionBundleIsConcurrentProduct : PdExceptionBundleWitness → Bool
pdExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PdExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Pd exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Pd exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

pdExceptionContinuumWitnessBundle : PdExceptionBundle
pdExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent pdExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

pdExceptionContinuumWitness : PdExceptionBundleWitness
pdExceptionContinuumWitness =
  mkPdExceptionBundleWitness pdExceptionContinuumWitnessBundle 3

pd-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (PdExceptionBundle.slot pdExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
pd-exception-occupancy-engine-sort-dblock-present = refl

pd-exception-madelung-exception-theorem-present :
  isSlotPresent (PdExceptionBundle.slot pdExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
pd-exception-madelung-exception-theorem-present = refl

pd-exception-continuum-env-restriction-present :
  isSlotPresent (PdExceptionBundle.slot pdExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
pd-exception-continuum-env-restriction-present = refl

pd-exception-present-count : PdExceptionBundleWitness.present-count pdExceptionContinuumWitness ≡ 3
pd-exception-present-count = refl

pd-exception-concurrent-product :
  pdExceptionBundleIsConcurrentProduct pdExceptionContinuumWitness ≡ true
pd-exception-concurrent-product = refl

pd-exception-three-factors-concurrent :
  isSlotPresent (PdExceptionBundle.slot pdExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (PdExceptionBundle.slot pdExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (PdExceptionBundle.slot pdExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × PdExceptionBundleWitness.present-count pdExceptionContinuumWitness ≡ 3
pd-exception-three-factors-concurrent =
  pd-exception-occupancy-engine-sort-dblock-present
  , pd-exception-madelung-exception-theorem-present
  , pd-exception-continuum-env-restriction-present
  , pd-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PdExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if pdExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = PdExceptionBundleWitness.bundle w
       in if isSlotPresent (PdExceptionBundle.slot b i)
          then if isSlotPresent (PdExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PdExceptionBundleWitness
unwiredWitness = mkPdExceptionBundleWitness pdExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

pd-exception-xor-product-ok :
  evaluateXorRefuse pdExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
pd-exception-xor-product-ok = refl

pd-exception-not-xor : pdExceptionContinuumNotXor ≡ true
pd-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPdExceptionStep scaffold — PdExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierPdExceptionStep : Set where
  pd-exception-identity : ClassifierPdExceptionStep
  slot-leaf : ℕ → ClassifierPdExceptionStep
  product-concurrent : ClassifierPdExceptionStep → ClassifierPdExceptionStep → ClassifierPdExceptionStep
  xor-mutually-exclusive : ClassifierPdExceptionStep → ClassifierPdExceptionStep → ClassifierPdExceptionStep

pdExceptionIdentity : ClassifierPdExceptionStep
pdExceptionIdentity = pd-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPdExceptionStep → ClassifierPdExceptionStep → ClassifierPdExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierPdExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierPdExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isPdExceptionIdentity : ClassifierPdExceptionStep → Bool
isPdExceptionIdentity pd-exception-identity = true
isPdExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at pd-exception-identity
------------------------------------------------------------------------

pd-exception-left-identity :
  ∀ (a : ClassifierPdExceptionStep) →
  isPdExceptionIdentity pdExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp pdExceptionIdentity a) ≡ true
pd-exception-left-identity a = refl , refl

pd-exception-right-identity :
  ∀ (a : ClassifierPdExceptionStep) →
  isProductConcurrent (productConcurrentOp a pdExceptionIdentity) ≡ true
  × isPdExceptionIdentity pdExceptionIdentity ≡ true
pd-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-pd-exception :
  (∀ a → isProductConcurrent (productConcurrentOp pdExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a pdExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-pd-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Pd exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedPdExceptionContinuumProduct : ClassifierPdExceptionStep
namedPdExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-pd-exception-continuum-product-concurrent :
  isProductConcurrent namedPdExceptionContinuumProduct ≡ true
  × pdExceptionBundleIsConcurrentProduct pdExceptionContinuumWitness ≡ true
named-pd-exception-continuum-product-concurrent = refl , pd-exception-concurrent-product

------------------------------------------------------------------------
-- PdExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data PdExceptionAdmissibility : Set where
  pd-exception-admissible pd-exception-xor-refuse : PdExceptionAdmissibility

isPdExceptionPreserving : ClassifierPdExceptionStep → Bool
isPdExceptionPreserving pd-exception-identity = true
isPdExceptionPreserving (slot-leaf _) = true
isPdExceptionPreserving (product-concurrent a b) =
  isPdExceptionPreserving a ∧ isPdExceptionPreserving b
isPdExceptionPreserving (xor-mutually-exclusive _ _) = false

isPdExceptionAdmissible : ClassifierPdExceptionStep → Bool
isPdExceptionAdmissible step = isPdExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isPdExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isPdExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isPdExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-pd-exception-continuum-admissible : isPdExceptionAdmissible namedPdExceptionContinuumProduct ≡ true
named-pd-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isPdExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isPdExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data PdExceptionWitnessPresence : Set where
  pd-exception-witness-absent pd-exception-witness-present : PdExceptionWitnessPresence

record ClassifierPdExceptionWitness : Set where
  constructor mkClassifierPdExceptionWitness
  field
    witness-presence : PdExceptionWitnessPresence
    pd-exception-gap-total : ℕ

pdExceptionWitnessAbsent : ClassifierPdExceptionWitness
pdExceptionWitnessAbsent = mkClassifierPdExceptionWitness pd-exception-witness-absent zero

pdExceptionWitnessPresentZeroGap : ClassifierPdExceptionWitness
pdExceptionWitnessPresentZeroGap = mkClassifierPdExceptionWitness pd-exception-witness-present zero

pdExceptionWitnessPresentWithGaps : ℕ → ClassifierPdExceptionWitness
pdExceptionWitnessPresentWithGaps n = mkClassifierPdExceptionWitness pd-exception-witness-present n

pdExceptionWitnessGapFree : ClassifierPdExceptionWitness → Bool
pdExceptionWitnessGapFree (mkClassifierPdExceptionWitness pd-exception-witness-absent _) = false
pdExceptionWitnessGapFree (mkClassifierPdExceptionWitness pd-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

pd-exception-witness-present-zero-gap-free :
  pdExceptionWitnessGapFree pdExceptionWitnessPresentZeroGap ≡ true
pd-exception-witness-present-zero-gap-free = refl

pd-exception-witness-absent-not-gap-free :
  pdExceptionWitnessGapFree pdExceptionWitnessAbsent ≡ false
pd-exception-witness-absent-not-gap-free = refl

pd-exception-witness-with-gaps-not-gap-free :
  ∀ n → pdExceptionWitnessGapFree (pdExceptionWitnessPresentWithGaps (suc n)) ≡ false
pd-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-PdException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PdExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-pd-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : PdExceptionContinuumVerdict

pdExceptionContinuumVerdictOk : PdExceptionContinuumVerdict → Bool
pdExceptionContinuumVerdictOk verdict-unwired-ok = true
pdExceptionContinuumVerdictOk verdict-pd-exception-admissible-ok = true
pdExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
pdExceptionContinuumVerdictOk _ = false

evaluatePdExceptionContinuumClose :
  PdExceptionContinuumModality → ClassifierPdExceptionStep → ClassifierPdExceptionWitness
  → PdExceptionBundleWitness → Bool → PdExceptionContinuumVerdict
evaluatePdExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluatePdExceptionContinuumClose pd-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluatePdExceptionContinuumClose pd-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluatePdExceptionContinuumClose pd-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluatePdExceptionContinuumClose pd-exception-continuum-proved _ (mkClassifierPdExceptionWitness pd-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluatePdExceptionContinuumClose pd-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluatePdExceptionContinuumClose pd-exception-continuum-proved _ (mkClassifierPdExceptionWitness pd-exception-witness-present _) w false
  with pdExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-pd-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-unwired namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-assumed namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-surrogate namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  pdExceptionContinuumVerdictOk
    (evaluatePdExceptionContinuumClose pd-exception-continuum-unwired namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false)
    ≡ true
  × pdExceptionContinuumVerdictOk
      (evaluatePdExceptionContinuumClose pd-exception-continuum-assumed namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false)
      ≡ true
  × pdExceptionContinuumVerdictOk
      (evaluatePdExceptionContinuumClose pd-exception-continuum-surrogate namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  pdExceptionContinuumVerdictOk
    (evaluatePdExceptionContinuumClose
       pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

PdTotalClaimWhenWitnessAbsent : Set
PdTotalClaimWhenWitnessAbsent =
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false ≡
  verdict-pd-exception-admissible-ok

total-claim-⊥-when-witness-absent : PdTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  pdExceptionContinuumVerdictOk
    (evaluatePdExceptionContinuumClose
       pd-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

PdXorMutuallyExclusiveWhenConcurrent : Set
PdXorMutuallyExclusiveWhenConcurrent =
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : PdXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

pd-exception-admissible-ok :
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-pd-exception-admissible-ok
pd-exception-admissible-ok = refl

pd-exception-admissible-verdict-ok :
  pdExceptionContinuumVerdictOk
    (evaluatePdExceptionContinuumClose
       pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
pd-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  pdExceptionContinuumVerdictOk
    (evaluatePdExceptionContinuumClose
       pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-pd-exception-proved :
  pdExceptionContinuumVerdictOk
    (evaluatePdExceptionContinuumClose
       pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness false)
    ≡ true
  × pdExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-pd-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePdExceptionContinuumClose
    pd-exception-continuum-unwired namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  pdExceptionContinuumVerdictOk
    (evaluatePdExceptionContinuumClose
       pd-exception-continuum-unwired namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

pdExceptionContinuumFiberOk : FormalFiber → Bool
pdExceptionContinuumFiberOk fiber-quantum-knowing = true
pdExceptionContinuumFiberOk fiber-meso-acting = false

pd-exception-continuum-knowing-fiber-ok :
  pdExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
pd-exception-continuum-knowing-fiber-ok = refl

pd-exception-continuum-meso-acting-not-ok :
  pdExceptionContinuumFiberOk fiber-meso-acting ≡ false
pd-exception-continuum-meso-acting-not-ok = refl

pd-exception-continuum-routes-knowing-not-meso :
  pdExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  pdExceptionContinuumFiberOk fiber-meso-acting ≡ false
pd-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  pdExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (pdExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Pd exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

pd-exception-continuum-not-proved : pdExceptionContinuumProved ≡ false
pd-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

pd-exception-continuum-second-law-conservation-framed : pdExceptionContinuumSecondLawConservationFramed ≡ true
pd-exception-continuum-second-law-conservation-framed = refl

pd-exception-not-xor-pin : pdExceptionContinuumNotXor ≡ true
pd-exception-not-xor-pin = pd-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

pdExceptionContinuumAxiom :
  (pdExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (pdExceptionContinuumSecondLawConservationFramed ≡ true)
  × (pdExceptionContinuumNotXor ≡ true)
  × (evaluatePdExceptionContinuumClose pd-exception-continuum-unwired namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluatePdExceptionContinuumClose pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessAbsent pdExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluatePdExceptionContinuumClose pd-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluatePdExceptionContinuumClose pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-pd-exception-admissible-ok)
  × (evaluatePdExceptionContinuumClose pd-exception-continuum-proved namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (pdExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (pdExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (pdExceptionContinuumVerdictOk (evaluatePdExceptionContinuumClose pd-exception-continuum-unwired namedPdExceptionContinuumProduct pdExceptionWitnessPresentZeroGap pdExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp pdExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a pdExceptionIdentity) ≡ true)
  × (isPdExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (pdZ46OccupancyEngineSortIndex ≡ 46)
  × (PdExceptionBundleWitness.present-count pdExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ palladium ≡ 46)
  × (elementAtomicZ rhodium ≡ 45)
pdExceptionContinuumAxiom =
  pd-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , pd-exception-continuum-second-law-conservation-framed
  , pd-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , pd-exception-admissible-ok
  , concurrent-product-ok
  , pd-exception-continuum-knowing-fiber-ok
  , pd-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , pd-z46-occupancy-engine-sort-index
  , pd-exception-present-count
  , palladium-z-46
  , rhodium-z-45

pdExceptionContinuumNamed : String
pdExceptionContinuumNamed =
  "pdExceptionContinuum: Pd Z=46 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

pdExceptionContinuumAuthority : String
pdExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_046_pd.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

pdExceptionContinuumCellId : String
pdExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-PD-EXCEPTION-CONTINUUM"

pdExceptionContinuumNonClaim : String
pdExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-PD-EXCEPTION-CONTINUUM Pd Z=46 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Pd exception continuum witness concurrent pdExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_046_pd.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

pd-exception-continuum-cell-id :
  pdExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-PD-EXCEPTION-CONTINUUM"
pd-exception-continuum-cell-id = refl

pd-exception-continuum-cites-z046-pd-rs :
  pdExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_046_pd.rs"
pd-exception-continuum-cites-z046-pd-rs = refl

pd-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
pd-exception-continuum-cites-occupancy-engine-sort-rs = refl

pd-exception-continuum-modality-unwired :
  pdExceptionContinuumModalityCurrent ≡ pd-exception-continuum-unwired
pd-exception-continuum-modality-unwired = refl

pdExceptionContinuumPhysicsGreenAuthorized : Set
pdExceptionContinuumPhysicsGreenAuthorized = ⊥

pd-exception-continuum-physics-green-false : ¬ pdExceptionContinuumPhysicsGreenAuthorized
pd-exception-continuum-physics-green-false ()

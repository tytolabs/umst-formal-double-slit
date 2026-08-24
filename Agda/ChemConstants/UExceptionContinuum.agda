-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.UExceptionContinuum.agda
--
-- U Z=92 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; U exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **U exception continuum** laws Unwired (uExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_092_u.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/MoExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- U Z=92 f-block occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.UExceptionContinuum where


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
-- Modality + U Z=92 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data UExceptionContinuumModality : Set where
  u-exception-continuum-unwired u-exception-continuum-assumed
    u-exception-continuum-proved u-exception-continuum-surrogate
    : UExceptionContinuumModality

uExceptionContinuumModalityCurrent : UExceptionContinuumModality
uExceptionContinuumModalityCurrent = u-exception-continuum-unwired

uExceptionContinuumProved productionWired not118SquaredGreenTable
  uExceptionContinuumSecondLawConservationFramed uExceptionContinuumNotXor : Bool
uExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
uExceptionContinuumSecondLawConservationFramed = true
uExceptionContinuumNotXor = true

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
-- U Z=92 occupancy-engine sort index pin
------------------------------------------------------------------------

uZ92OccupancyEngineSortIndex : ℕ
uZ92OccupancyEngineSortIndex = 92

u-z92-occupancy-engine-sort-index : uZ92OccupancyEngineSortIndex ≡ 92
u-z92-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — U (Z=92), W (Z=74 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  uranium tungsten : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ uranium = 92
elementAtomicZ tungsten = 74

uranium-z-92 : elementAtomicZ uranium ≡ 92
uranium-z-92 = refl

tungsten-z-74 : elementAtomicZ tungsten ≡ 74
tungsten-z-74 = refl

------------------------------------------------------------------------
-- UExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data UExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : UExceptionBundleSlot

isSlotPresent : UExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- UExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record UExceptionBundle : Set where
  field slot : ℕ → UExceptionBundleSlot

uExceptionBundleUnwired : UExceptionBundle
uExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : UExceptionBundle → ℕ → UExceptionBundleSlot → UExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else UExceptionBundle.slot b j }

withPresent : UExceptionBundle → ℕ → UExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record UExceptionBundleWitness : Set where
  constructor mkUExceptionBundleWitness
  field
    bundle : UExceptionBundle
    present-count : ℕ

uExceptionBundleIsConcurrentProduct : UExceptionBundleWitness → Bool
uExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? UExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named U exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- U exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

uExceptionContinuumWitnessBundle : UExceptionBundle
uExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent uExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

uExceptionContinuumWitness : UExceptionBundleWitness
uExceptionContinuumWitness =
  mkUExceptionBundleWitness uExceptionContinuumWitnessBundle 3

u-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (UExceptionBundle.slot uExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
u-exception-occupancy-engine-sort-dblock-present = refl

u-exception-madelung-exception-theorem-present :
  isSlotPresent (UExceptionBundle.slot uExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
u-exception-madelung-exception-theorem-present = refl

u-exception-continuum-env-restriction-present :
  isSlotPresent (UExceptionBundle.slot uExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
u-exception-continuum-env-restriction-present = refl

u-exception-present-count : UExceptionBundleWitness.present-count uExceptionContinuumWitness ≡ 3
u-exception-present-count = refl

u-exception-concurrent-product :
  uExceptionBundleIsConcurrentProduct uExceptionContinuumWitness ≡ true
u-exception-concurrent-product = refl

u-exception-three-factors-concurrent :
  isSlotPresent (UExceptionBundle.slot uExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (UExceptionBundle.slot uExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (UExceptionBundle.slot uExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × UExceptionBundleWitness.present-count uExceptionContinuumWitness ≡ 3
u-exception-three-factors-concurrent =
  u-exception-occupancy-engine-sort-dblock-present
  , u-exception-madelung-exception-theorem-present
  , u-exception-continuum-env-restriction-present
  , u-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : UExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if uExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = UExceptionBundleWitness.bundle w
       in if isSlotPresent (UExceptionBundle.slot b i)
          then if isSlotPresent (UExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : UExceptionBundleWitness
unwiredWitness = mkUExceptionBundleWitness uExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

u-exception-xor-product-ok :
  evaluateXorRefuse uExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
u-exception-xor-product-ok = refl

u-exception-not-xor : uExceptionContinuumNotXor ≡ true
u-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierUExceptionStep scaffold — UExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierUExceptionStep : Set where
  u-exception-identity : ClassifierUExceptionStep
  slot-leaf : ℕ → ClassifierUExceptionStep
  product-concurrent : ClassifierUExceptionStep → ClassifierUExceptionStep → ClassifierUExceptionStep
  xor-mutually-exclusive : ClassifierUExceptionStep → ClassifierUExceptionStep → ClassifierUExceptionStep

uExceptionIdentity : ClassifierUExceptionStep
uExceptionIdentity = u-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierUExceptionStep → ClassifierUExceptionStep → ClassifierUExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierUExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierUExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isUExceptionIdentity : ClassifierUExceptionStep → Bool
isUExceptionIdentity u-exception-identity = true
isUExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at u-exception-identity
------------------------------------------------------------------------

u-exception-left-identity :
  ∀ (a : ClassifierUExceptionStep) →
  isUExceptionIdentity uExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp uExceptionIdentity a) ≡ true
u-exception-left-identity a = refl , refl

u-exception-right-identity :
  ∀ (a : ClassifierUExceptionStep) →
  isProductConcurrent (productConcurrentOp a uExceptionIdentity) ≡ true
  × isUExceptionIdentity uExceptionIdentity ≡ true
u-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-u-exception :
  (∀ a → isProductConcurrent (productConcurrentOp uExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a uExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-u-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named U exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedUExceptionContinuumProduct : ClassifierUExceptionStep
namedUExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-u-exception-continuum-product-concurrent :
  isProductConcurrent namedUExceptionContinuumProduct ≡ true
  × uExceptionBundleIsConcurrentProduct uExceptionContinuumWitness ≡ true
named-u-exception-continuum-product-concurrent = refl , u-exception-concurrent-product

------------------------------------------------------------------------
-- UExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data UExceptionAdmissibility : Set where
  u-exception-admissible u-exception-xor-refuse : UExceptionAdmissibility

isUExceptionPreserving : ClassifierUExceptionStep → Bool
isUExceptionPreserving u-exception-identity = true
isUExceptionPreserving (slot-leaf _) = true
isUExceptionPreserving (product-concurrent a b) =
  isUExceptionPreserving a ∧ isUExceptionPreserving b
isUExceptionPreserving (xor-mutually-exclusive _ _) = false

isUExceptionAdmissible : ClassifierUExceptionStep → Bool
isUExceptionAdmissible step = isUExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isUExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isUExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isUExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-u-exception-continuum-admissible : isUExceptionAdmissible namedUExceptionContinuumProduct ≡ true
named-u-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isUExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isUExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data UExceptionWitnessPresence : Set where
  u-exception-witness-absent u-exception-witness-present : UExceptionWitnessPresence

record ClassifierUExceptionWitness : Set where
  constructor mkClassifierUExceptionWitness
  field
    witness-presence : UExceptionWitnessPresence
    u-exception-gap-total : ℕ

uExceptionWitnessAbsent : ClassifierUExceptionWitness
uExceptionWitnessAbsent = mkClassifierUExceptionWitness u-exception-witness-absent zero

uExceptionWitnessPresentZeroGap : ClassifierUExceptionWitness
uExceptionWitnessPresentZeroGap = mkClassifierUExceptionWitness u-exception-witness-present zero

uExceptionWitnessPresentWithGaps : ℕ → ClassifierUExceptionWitness
uExceptionWitnessPresentWithGaps n = mkClassifierUExceptionWitness u-exception-witness-present n

uExceptionWitnessGapFree : ClassifierUExceptionWitness → Bool
uExceptionWitnessGapFree (mkClassifierUExceptionWitness u-exception-witness-absent _) = false
uExceptionWitnessGapFree (mkClassifierUExceptionWitness u-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

u-exception-witness-present-zero-gap-free :
  uExceptionWitnessGapFree uExceptionWitnessPresentZeroGap ≡ true
u-exception-witness-present-zero-gap-free = refl

u-exception-witness-absent-not-gap-free :
  uExceptionWitnessGapFree uExceptionWitnessAbsent ≡ false
u-exception-witness-absent-not-gap-free = refl

u-exception-witness-with-gaps-not-gap-free :
  ∀ n → uExceptionWitnessGapFree (uExceptionWitnessPresentWithGaps (suc n)) ≡ false
u-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-UException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data UExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-u-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : UExceptionContinuumVerdict

uExceptionContinuumVerdictOk : UExceptionContinuumVerdict → Bool
uExceptionContinuumVerdictOk verdict-unwired-ok = true
uExceptionContinuumVerdictOk verdict-u-exception-admissible-ok = true
uExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
uExceptionContinuumVerdictOk _ = false

evaluateUExceptionContinuumClose :
  UExceptionContinuumModality → ClassifierUExceptionStep → ClassifierUExceptionWitness
  → UExceptionBundleWitness → Bool → UExceptionContinuumVerdict
evaluateUExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateUExceptionContinuumClose u-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateUExceptionContinuumClose u-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateUExceptionContinuumClose u-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateUExceptionContinuumClose u-exception-continuum-proved _ (mkClassifierUExceptionWitness u-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateUExceptionContinuumClose u-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateUExceptionContinuumClose u-exception-continuum-proved _ (mkClassifierUExceptionWitness u-exception-witness-present _) w false
  with uExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-u-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateUExceptionContinuumClose
    u-exception-continuum-unwired namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateUExceptionContinuumClose
    u-exception-continuum-assumed namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateUExceptionContinuumClose
    u-exception-continuum-surrogate namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  uExceptionContinuumVerdictOk
    (evaluateUExceptionContinuumClose u-exception-continuum-unwired namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false)
    ≡ true
  × uExceptionContinuumVerdictOk
      (evaluateUExceptionContinuumClose u-exception-continuum-assumed namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false)
      ≡ true
  × uExceptionContinuumVerdictOk
      (evaluateUExceptionContinuumClose u-exception-continuum-surrogate namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateUExceptionContinuumClose
    u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  uExceptionContinuumVerdictOk
    (evaluateUExceptionContinuumClose
       u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

UTotalClaimWhenWitnessAbsent : Set
UTotalClaimWhenWitnessAbsent =
  evaluateUExceptionContinuumClose
    u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false ≡
  verdict-u-exception-admissible-ok

total-claim-⊥-when-witness-absent : UTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateUExceptionContinuumClose
    u-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    uExceptionWitnessPresentZeroGap uExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  uExceptionContinuumVerdictOk
    (evaluateUExceptionContinuumClose
       u-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       uExceptionWitnessPresentZeroGap uExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

UXorMutuallyExclusiveWhenConcurrent : Set
UXorMutuallyExclusiveWhenConcurrent =
  evaluateUExceptionContinuumClose
    u-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    uExceptionWitnessPresentZeroGap uExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : UXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

u-exception-admissible-ok :
  evaluateUExceptionContinuumClose
    u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-u-exception-admissible-ok
u-exception-admissible-ok = refl

u-exception-admissible-verdict-ok :
  uExceptionContinuumVerdictOk
    (evaluateUExceptionContinuumClose
       u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
u-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateUExceptionContinuumClose
    u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap uExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  uExceptionContinuumVerdictOk
    (evaluateUExceptionContinuumClose
       u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap uExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-u-exception-proved :
  uExceptionContinuumVerdictOk
    (evaluateUExceptionContinuumClose
       u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap uExceptionContinuumWitness false)
    ≡ true
  × uExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-u-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateUExceptionContinuumClose
    u-exception-continuum-unwired namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap uExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  uExceptionContinuumVerdictOk
    (evaluateUExceptionContinuumClose
       u-exception-continuum-unwired namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap uExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

uExceptionContinuumFiberOk : FormalFiber → Bool
uExceptionContinuumFiberOk fiber-quantum-knowing = true
uExceptionContinuumFiberOk fiber-meso-acting = false

u-exception-continuum-knowing-fiber-ok :
  uExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
u-exception-continuum-knowing-fiber-ok = refl

u-exception-continuum-meso-acting-not-ok :
  uExceptionContinuumFiberOk fiber-meso-acting ≡ false
u-exception-continuum-meso-acting-not-ok = refl

u-exception-continuum-routes-knowing-not-meso :
  uExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  uExceptionContinuumFiberOk fiber-meso-acting ≡ false
u-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  uExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (uExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not U exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

u-exception-continuum-not-proved : uExceptionContinuumProved ≡ false
u-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

u-exception-continuum-second-law-conservation-framed : uExceptionContinuumSecondLawConservationFramed ≡ true
u-exception-continuum-second-law-conservation-framed = refl

u-exception-not-xor-pin : uExceptionContinuumNotXor ≡ true
u-exception-not-xor-pin = u-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

uExceptionContinuumAxiom :
  (uExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (uExceptionContinuumSecondLawConservationFramed ≡ true)
  × (uExceptionContinuumNotXor ≡ true)
  × (evaluateUExceptionContinuumClose u-exception-continuum-unwired namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateUExceptionContinuumClose u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessAbsent uExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateUExceptionContinuumClose u-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) uExceptionWitnessPresentZeroGap uExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateUExceptionContinuumClose u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-u-exception-admissible-ok)
  × (evaluateUExceptionContinuumClose u-exception-continuum-proved namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap uExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (uExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (uExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (uExceptionContinuumVerdictOk (evaluateUExceptionContinuumClose u-exception-continuum-unwired namedUExceptionContinuumProduct uExceptionWitnessPresentZeroGap uExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp uExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a uExceptionIdentity) ≡ true)
  × (isUExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (uZ92OccupancyEngineSortIndex ≡ 92)
  × (UExceptionBundleWitness.present-count uExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ uranium ≡ 92)
  × (elementAtomicZ tungsten ≡ 74)
uExceptionContinuumAxiom =
  u-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , u-exception-continuum-second-law-conservation-framed
  , u-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , u-exception-admissible-ok
  , concurrent-product-ok
  , u-exception-continuum-knowing-fiber-ok
  , u-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , u-z92-occupancy-engine-sort-index
  , u-exception-present-count
  , uranium-z-92
  , tungsten-z-74

uExceptionContinuumNamed : String
uExceptionContinuumNamed =
  "uExceptionContinuum: U Z=92 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog W Z=74 not copy"

uExceptionContinuumAuthority : String
uExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_092_u.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

uExceptionContinuumCellId : String
uExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-U-EXCEPTION-CONTINUUM"

uExceptionContinuumNonClaim : String
uExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-U-EXCEPTION-CONTINUUM U Z=92 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog W Z=74 not copy XOR mutually exclusive refuse U exception continuum witness concurrent uExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_092_u.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

u-exception-continuum-cell-id :
  uExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-U-EXCEPTION-CONTINUUM"
u-exception-continuum-cell-id = refl

u-exception-continuum-cites-z092-u-rs :
  uExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_092_u.rs"
u-exception-continuum-cites-z092-u-rs = refl

u-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
u-exception-continuum-cites-occupancy-engine-sort-rs = refl

u-exception-continuum-modality-unwired :
  uExceptionContinuumModalityCurrent ≡ u-exception-continuum-unwired
u-exception-continuum-modality-unwired = refl

uExceptionContinuumPhysicsGreenAuthorized : Set
uExceptionContinuumPhysicsGreenAuthorized = ⊥

u-exception-continuum-physics-green-false : ¬ uExceptionContinuumPhysicsGreenAuthorized
u-exception-continuum-physics-green-false ()

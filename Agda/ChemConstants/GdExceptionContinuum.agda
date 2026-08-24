-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.GdExceptionContinuum.agda
--
-- Gd Z=64 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Gd exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Gd exception continuum** laws Unwired (gdExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_064_gd.rs
-- Homolog Eu Z=63 not copy Y Z=39 Cm Z=96
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/MoExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Gd Z=64 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.GdExceptionContinuum where


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
-- Modality + Gd Z=64 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data GdExceptionContinuumModality : Set where
  gd-exception-continuum-unwired gd-exception-continuum-assumed
    gd-exception-continuum-proved gd-exception-continuum-surrogate
    : GdExceptionContinuumModality

gdExceptionContinuumModalityCurrent : GdExceptionContinuumModality
gdExceptionContinuumModalityCurrent = gd-exception-continuum-unwired

gdExceptionContinuumProved productionWired not118SquaredGreenTable
  gdExceptionContinuumSecondLawConservationFramed gdExceptionContinuumNotXor : Bool
gdExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
gdExceptionContinuumSecondLawConservationFramed = true
gdExceptionContinuumNotXor = true

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
-- Gd Z=64 occupancy-engine sort index pin
------------------------------------------------------------------------

gdZ64OccupancyEngineSortIndex : ℕ
gdZ64OccupancyEngineSortIndex = 64

gd-z64-occupancy-engine-sort-index : gdZ64OccupancyEngineSortIndex ≡ 64
gd-z64-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Gd (Z=64), Eu (Z=63 homolog not Y/Cm copy)
------------------------------------------------------------------------

data ElementTag : Set where
  gadolinium europium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ gadolinium = 64
elementAtomicZ europium = 63

gadolinium-z-64 : elementAtomicZ gadolinium ≡ 64
gadolinium-z-64 = refl

europium-z-63 : elementAtomicZ europium ≡ 63
europium-z-63 = refl

------------------------------------------------------------------------
-- GdExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data GdExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : GdExceptionBundleSlot

isSlotPresent : GdExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- GdExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record GdExceptionBundle : Set where
  field slot : ℕ → GdExceptionBundleSlot

gdExceptionBundleUnwired : GdExceptionBundle
gdExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : GdExceptionBundle → ℕ → GdExceptionBundleSlot → GdExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else GdExceptionBundle.slot b j }

withPresent : GdExceptionBundle → ℕ → GdExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record GdExceptionBundleWitness : Set where
  constructor mkGdExceptionBundleWitness
  field
    bundle : GdExceptionBundle
    present-count : ℕ

gdExceptionBundleIsConcurrentProduct : GdExceptionBundleWitness → Bool
gdExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? GdExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Gd exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Gd exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

gdExceptionContinuumWitnessBundle : GdExceptionBundle
gdExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent gdExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

gdExceptionContinuumWitness : GdExceptionBundleWitness
gdExceptionContinuumWitness =
  mkGdExceptionBundleWitness gdExceptionContinuumWitnessBundle 3

gd-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (GdExceptionBundle.slot gdExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
gd-exception-occupancy-engine-sort-dblock-present = refl

gd-exception-madelung-exception-theorem-present :
  isSlotPresent (GdExceptionBundle.slot gdExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
gd-exception-madelung-exception-theorem-present = refl

gd-exception-continuum-env-restriction-present :
  isSlotPresent (GdExceptionBundle.slot gdExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
gd-exception-continuum-env-restriction-present = refl

gd-exception-present-count : GdExceptionBundleWitness.present-count gdExceptionContinuumWitness ≡ 3
gd-exception-present-count = refl

gd-exception-concurrent-product :
  gdExceptionBundleIsConcurrentProduct gdExceptionContinuumWitness ≡ true
gd-exception-concurrent-product = refl

gd-exception-three-factors-concurrent :
  isSlotPresent (GdExceptionBundle.slot gdExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (GdExceptionBundle.slot gdExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (GdExceptionBundle.slot gdExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × GdExceptionBundleWitness.present-count gdExceptionContinuumWitness ≡ 3
gd-exception-three-factors-concurrent =
  gd-exception-occupancy-engine-sort-dblock-present
  , gd-exception-madelung-exception-theorem-present
  , gd-exception-continuum-env-restriction-present
  , gd-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : GdExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if gdExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = GdExceptionBundleWitness.bundle w
       in if isSlotPresent (GdExceptionBundle.slot b i)
          then if isSlotPresent (GdExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : GdExceptionBundleWitness
unwiredWitness = mkGdExceptionBundleWitness gdExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

gd-exception-xor-product-ok :
  evaluateXorRefuse gdExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
gd-exception-xor-product-ok = refl

gd-exception-not-xor : gdExceptionContinuumNotXor ≡ true
gd-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierGdExceptionStep scaffold — GdExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierGdExceptionStep : Set where
  gd-exception-identity : ClassifierGdExceptionStep
  slot-leaf : ℕ → ClassifierGdExceptionStep
  product-concurrent : ClassifierGdExceptionStep → ClassifierGdExceptionStep → ClassifierGdExceptionStep
  xor-mutually-exclusive : ClassifierGdExceptionStep → ClassifierGdExceptionStep → ClassifierGdExceptionStep

gdExceptionIdentity : ClassifierGdExceptionStep
gdExceptionIdentity = gd-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierGdExceptionStep → ClassifierGdExceptionStep → ClassifierGdExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierGdExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierGdExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isGdExceptionIdentity : ClassifierGdExceptionStep → Bool
isGdExceptionIdentity gd-exception-identity = true
isGdExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at gd-exception-identity
------------------------------------------------------------------------

gd-exception-left-identity :
  ∀ (a : ClassifierGdExceptionStep) →
  isGdExceptionIdentity gdExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp gdExceptionIdentity a) ≡ true
gd-exception-left-identity a = refl , refl

gd-exception-right-identity :
  ∀ (a : ClassifierGdExceptionStep) →
  isProductConcurrent (productConcurrentOp a gdExceptionIdentity) ≡ true
  × isGdExceptionIdentity gdExceptionIdentity ≡ true
gd-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-mo-exception :
  (∀ a → isProductConcurrent (productConcurrentOp gdExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a gdExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-mo-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Gd exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedGdExceptionContinuumProduct : ClassifierGdExceptionStep
namedGdExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-gd-exception-continuum-product-concurrent :
  isProductConcurrent namedGdExceptionContinuumProduct ≡ true
  × gdExceptionBundleIsConcurrentProduct gdExceptionContinuumWitness ≡ true
named-gd-exception-continuum-product-concurrent = refl , gd-exception-concurrent-product

------------------------------------------------------------------------
-- GdExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data GdExceptionAdmissibility : Set where
  gd-exception-admissible gd-exception-xor-refuse : GdExceptionAdmissibility

isGdExceptionPreserving : ClassifierGdExceptionStep → Bool
isGdExceptionPreserving gd-exception-identity = true
isGdExceptionPreserving (slot-leaf _) = true
isGdExceptionPreserving (product-concurrent a b) =
  isGdExceptionPreserving a ∧ isGdExceptionPreserving b
isGdExceptionPreserving (xor-mutually-exclusive _ _) = false

isGdExceptionAdmissible : ClassifierGdExceptionStep → Bool
isGdExceptionAdmissible step = isGdExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isGdExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isGdExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isGdExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-gd-exception-continuum-admissible : isGdExceptionAdmissible namedGdExceptionContinuumProduct ≡ true
named-gd-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isGdExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isGdExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data GdExceptionWitnessPresence : Set where
  gd-exception-witness-absent gd-exception-witness-present : GdExceptionWitnessPresence

record ClassifierGdExceptionWitness : Set where
  constructor mkClassifierGdExceptionWitness
  field
    witness-presence : GdExceptionWitnessPresence
    mo-exception-gap-total : ℕ

gdExceptionWitnessAbsent : ClassifierGdExceptionWitness
gdExceptionWitnessAbsent = mkClassifierGdExceptionWitness gd-exception-witness-absent zero

gdExceptionWitnessPresentZeroGap : ClassifierGdExceptionWitness
gdExceptionWitnessPresentZeroGap = mkClassifierGdExceptionWitness gd-exception-witness-present zero

gdExceptionWitnessPresentWithGaps : ℕ → ClassifierGdExceptionWitness
gdExceptionWitnessPresentWithGaps n = mkClassifierGdExceptionWitness gd-exception-witness-present n

gdExceptionWitnessGapFree : ClassifierGdExceptionWitness → Bool
gdExceptionWitnessGapFree (mkClassifierGdExceptionWitness gd-exception-witness-absent _) = false
gdExceptionWitnessGapFree (mkClassifierGdExceptionWitness gd-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

gd-exception-witness-present-zero-gap-free :
  gdExceptionWitnessGapFree gdExceptionWitnessPresentZeroGap ≡ true
gd-exception-witness-present-zero-gap-free = refl

gd-exception-witness-absent-not-gap-free :
  gdExceptionWitnessGapFree gdExceptionWitnessAbsent ≡ false
gd-exception-witness-absent-not-gap-free = refl

gd-exception-witness-with-gaps-not-gap-free :
  ∀ n → gdExceptionWitnessGapFree (gdExceptionWitnessPresentWithGaps (suc n)) ≡ false
gd-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-GdException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data GdExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-gd-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : GdExceptionContinuumVerdict

gdExceptionContinuumVerdictOk : GdExceptionContinuumVerdict → Bool
gdExceptionContinuumVerdictOk verdict-unwired-ok = true
gdExceptionContinuumVerdictOk verdict-gd-exception-admissible-ok = true
gdExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
gdExceptionContinuumVerdictOk _ = false

evaluateGdExceptionContinuumClose :
  GdExceptionContinuumModality → ClassifierGdExceptionStep → ClassifierGdExceptionWitness
  → GdExceptionBundleWitness → Bool → GdExceptionContinuumVerdict
evaluateGdExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateGdExceptionContinuumClose gd-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateGdExceptionContinuumClose gd-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateGdExceptionContinuumClose gd-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateGdExceptionContinuumClose gd-exception-continuum-proved _ (mkClassifierGdExceptionWitness gd-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateGdExceptionContinuumClose gd-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateGdExceptionContinuumClose gd-exception-continuum-proved _ (mkClassifierGdExceptionWitness gd-exception-witness-present _) w false
  with gdExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-gd-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-unwired namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-assumed namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-surrogate namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  gdExceptionContinuumVerdictOk
    (evaluateGdExceptionContinuumClose gd-exception-continuum-unwired namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false)
    ≡ true
  × gdExceptionContinuumVerdictOk
      (evaluateGdExceptionContinuumClose gd-exception-continuum-assumed namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false)
      ≡ true
  × gdExceptionContinuumVerdictOk
      (evaluateGdExceptionContinuumClose gd-exception-continuum-surrogate namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  gdExceptionContinuumVerdictOk
    (evaluateGdExceptionContinuumClose
       gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

GdTotalClaimWhenWitnessAbsent : Set
GdTotalClaimWhenWitnessAbsent =
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false ≡
  verdict-gd-exception-admissible-ok

total-claim-⊥-when-witness-absent : GdTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  gdExceptionContinuumVerdictOk
    (evaluateGdExceptionContinuumClose
       gd-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

GdXorMutuallyExclusiveWhenConcurrent : Set
GdXorMutuallyExclusiveWhenConcurrent =
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : GdXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

gd-exception-admissible-ok :
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-gd-exception-admissible-ok
gd-exception-admissible-ok = refl

gd-exception-admissible-verdict-ok :
  gdExceptionContinuumVerdictOk
    (evaluateGdExceptionContinuumClose
       gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
gd-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  gdExceptionContinuumVerdictOk
    (evaluateGdExceptionContinuumClose
       gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-mo-exception-proved :
  gdExceptionContinuumVerdictOk
    (evaluateGdExceptionContinuumClose
       gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness false)
    ≡ true
  × gdExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-mo-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateGdExceptionContinuumClose
    gd-exception-continuum-unwired namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  gdExceptionContinuumVerdictOk
    (evaluateGdExceptionContinuumClose
       gd-exception-continuum-unwired namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

gdExceptionContinuumFiberOk : FormalFiber → Bool
gdExceptionContinuumFiberOk fiber-quantum-knowing = true
gdExceptionContinuumFiberOk fiber-meso-acting = false

gd-exception-continuum-knowing-fiber-ok :
  gdExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
gd-exception-continuum-knowing-fiber-ok = refl

gd-exception-continuum-meso-acting-not-ok :
  gdExceptionContinuumFiberOk fiber-meso-acting ≡ false
gd-exception-continuum-meso-acting-not-ok = refl

gd-exception-continuum-routes-knowing-not-meso :
  gdExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  gdExceptionContinuumFiberOk fiber-meso-acting ≡ false
gd-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  gdExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (gdExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Gd exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

gd-exception-continuum-not-proved : gdExceptionContinuumProved ≡ false
gd-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

gd-exception-continuum-second-law-conservation-framed : gdExceptionContinuumSecondLawConservationFramed ≡ true
gd-exception-continuum-second-law-conservation-framed = refl

gd-exception-not-xor-pin : gdExceptionContinuumNotXor ≡ true
gd-exception-not-xor-pin = gd-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

gdExceptionContinuumAxiom :
  (gdExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (gdExceptionContinuumSecondLawConservationFramed ≡ true)
  × (gdExceptionContinuumNotXor ≡ true)
  × (evaluateGdExceptionContinuumClose gd-exception-continuum-unwired namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateGdExceptionContinuumClose gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessAbsent gdExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateGdExceptionContinuumClose gd-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateGdExceptionContinuumClose gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-gd-exception-admissible-ok)
  × (evaluateGdExceptionContinuumClose gd-exception-continuum-proved namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (gdExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (gdExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (gdExceptionContinuumVerdictOk (evaluateGdExceptionContinuumClose gd-exception-continuum-unwired namedGdExceptionContinuumProduct gdExceptionWitnessPresentZeroGap gdExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp gdExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a gdExceptionIdentity) ≡ true)
  × (isGdExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (gdZ64OccupancyEngineSortIndex ≡ 64)
  × (GdExceptionBundleWitness.present-count gdExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ gadolinium ≡ 64)
  × (elementAtomicZ europium ≡ 63)
gdExceptionContinuumAxiom =
  gd-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , gd-exception-continuum-second-law-conservation-framed
  , gd-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , gd-exception-admissible-ok
  , concurrent-product-ok
  , gd-exception-continuum-knowing-fiber-ok
  , gd-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , gd-z64-occupancy-engine-sort-index
  , gd-exception-present-count
  , gadolinium-z-64
  , europium-z-63

gdExceptionContinuumNamed : String
gdExceptionContinuumNamed =
  "gdExceptionContinuum: Gd Z=64 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog Eu Z=63 not copy Y Cm"

gdExceptionContinuumAuthority : String
gdExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_064_gd.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

gdExceptionContinuumCellId : String
gdExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-GD-EXCEPTION-CONTINUUM"

gdExceptionContinuumNonClaim : String
gdExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-GD-EXCEPTION-CONTINUUM Gd Z=64 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog Eu Z=63 not copy Y Z=39 Cm Z=96 XOR mutually exclusive refuse Gd exception continuum witness concurrent gdExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_064_gd.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

gd-exception-continuum-cell-id :
  gdExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-GD-EXCEPTION-CONTINUUM"
gd-exception-continuum-cell-id = refl

gd-exception-continuum-cites-z064-gd-rs :
  gdExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_064_gd.rs"
gd-exception-continuum-cites-z064-gd-rs = refl

gd-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
gd-exception-continuum-cites-occupancy-engine-sort-rs = refl

gd-exception-continuum-modality-unwired :
  gdExceptionContinuumModalityCurrent ≡ gd-exception-continuum-unwired
gd-exception-continuum-modality-unwired = refl

gdExceptionContinuumPhysicsGreenAuthorized : Set
gdExceptionContinuumPhysicsGreenAuthorized = ⊥

gd-exception-continuum-physics-green-false : ¬ gdExceptionContinuumPhysicsGreenAuthorized
gd-exception-continuum-physics-green-false ()

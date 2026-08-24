-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.LaExceptionContinuum.agda
--
-- La Z=57 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; La exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **La exception continuum** laws Unwired (laExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_057_la.rs
-- Homolog siblings: umst/umst-chem/src/elements/z_039_y.rs, z_089_ac.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/MoExceptionContinuum.agda` style.
-- Homolog Y Z=39 / Ac Z=89 ≠ La occupancy copy.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- La Z=57 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.LaExceptionContinuum where


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
-- Modality + La Z=57 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data LaExceptionContinuumModality : Set where
  la-exception-continuum-unwired la-exception-continuum-assumed
    la-exception-continuum-proved la-exception-continuum-surrogate
    : LaExceptionContinuumModality

laExceptionContinuumModalityCurrent : LaExceptionContinuumModality
laExceptionContinuumModalityCurrent = la-exception-continuum-unwired

laExceptionContinuumProved productionWired not118SquaredGreenTable
  laExceptionContinuumSecondLawConservationFramed laExceptionContinuumNotXor : Bool
laExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
laExceptionContinuumSecondLawConservationFramed = true
laExceptionContinuumNotXor = true

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
-- La Z=57 occupancy-engine sort index pin
------------------------------------------------------------------------

laZ57OccupancyEngineSortIndex : ℕ
laZ57OccupancyEngineSortIndex = 57

la-z57-occupancy-engine-sort-index : laZ57OccupancyEngineSortIndex ≡ 57
la-z57-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — La (Z=57), Y (Z=39) / Ac (Z=89) homolog
------------------------------------------------------------------------

data ElementTag : Set where
  lanthanum yttrium actinium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ lanthanum = 57
elementAtomicZ yttrium = 39
elementAtomicZ actinium = 89

actinium-z-89 : elementAtomicZ actinium ≡ 89
actinium-z-89 = refl

periodHomologZOffset : ℕ
periodHomologZOffset = 18

la-y-homolog-z-offset :
  elementAtomicZ lanthanum ≡ elementAtomicZ yttrium + periodHomologZOffset
la-y-homolog-z-offset = refl

periodHomologAcZOffset : ℕ
periodHomologAcZOffset = 32

ac-la-homolog-z-offset :
  elementAtomicZ actinium ≡ elementAtomicZ lanthanum + periodHomologAcZOffset
ac-la-homolog-z-offset = refl

lanthanum-z-57 : elementAtomicZ lanthanum ≡ 57
lanthanum-z-57 = refl

yttrium-z-39 : elementAtomicZ yttrium ≡ 39
yttrium-z-39 = refl

------------------------------------------------------------------------
-- LaExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data LaExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : LaExceptionBundleSlot

isSlotPresent : LaExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- LaExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record LaExceptionBundle : Set where
  field slot : ℕ → LaExceptionBundleSlot

laExceptionBundleUnwired : LaExceptionBundle
laExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : LaExceptionBundle → ℕ → LaExceptionBundleSlot → LaExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else LaExceptionBundle.slot b j }

withPresent : LaExceptionBundle → ℕ → LaExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record LaExceptionBundleWitness : Set where
  constructor mkLaExceptionBundleWitness
  field
    bundle : LaExceptionBundle
    present-count : ℕ

laExceptionBundleIsConcurrentProduct : LaExceptionBundleWitness → Bool
laExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? LaExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named La exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- La exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

laExceptionContinuumWitnessBundle : LaExceptionBundle
laExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent laExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

laExceptionContinuumWitness : LaExceptionBundleWitness
laExceptionContinuumWitness =
  mkLaExceptionBundleWitness laExceptionContinuumWitnessBundle 3

la-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (LaExceptionBundle.slot laExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
la-exception-occupancy-engine-sort-dblock-present = refl

la-exception-madelung-exception-theorem-present :
  isSlotPresent (LaExceptionBundle.slot laExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
la-exception-madelung-exception-theorem-present = refl

la-exception-continuum-env-restriction-present :
  isSlotPresent (LaExceptionBundle.slot laExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
la-exception-continuum-env-restriction-present = refl

la-exception-present-count : LaExceptionBundleWitness.present-count laExceptionContinuumWitness ≡ 3
la-exception-present-count = refl

la-exception-concurrent-product :
  laExceptionBundleIsConcurrentProduct laExceptionContinuumWitness ≡ true
la-exception-concurrent-product = refl

la-exception-three-factors-concurrent :
  isSlotPresent (LaExceptionBundle.slot laExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (LaExceptionBundle.slot laExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (LaExceptionBundle.slot laExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × LaExceptionBundleWitness.present-count laExceptionContinuumWitness ≡ 3
la-exception-three-factors-concurrent =
  la-exception-occupancy-engine-sort-dblock-present
  , la-exception-madelung-exception-theorem-present
  , la-exception-continuum-env-restriction-present
  , la-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : LaExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if laExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = LaExceptionBundleWitness.bundle w
       in if isSlotPresent (LaExceptionBundle.slot b i)
          then if isSlotPresent (LaExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : LaExceptionBundleWitness
unwiredWitness = mkLaExceptionBundleWitness laExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

la-exception-xor-product-ok :
  evaluateXorRefuse laExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
la-exception-xor-product-ok = refl

la-exception-not-xor : laExceptionContinuumNotXor ≡ true
la-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierLaExceptionStep scaffold — LaExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierLaExceptionStep : Set where
  la-exception-identity : ClassifierLaExceptionStep
  slot-leaf : ℕ → ClassifierLaExceptionStep
  product-concurrent : ClassifierLaExceptionStep → ClassifierLaExceptionStep → ClassifierLaExceptionStep
  xor-mutually-exclusive : ClassifierLaExceptionStep → ClassifierLaExceptionStep → ClassifierLaExceptionStep

laExceptionIdentity : ClassifierLaExceptionStep
laExceptionIdentity = la-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierLaExceptionStep → ClassifierLaExceptionStep → ClassifierLaExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierLaExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierLaExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isLaExceptionIdentity : ClassifierLaExceptionStep → Bool
isLaExceptionIdentity la-exception-identity = true
isLaExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at la-exception-identity
------------------------------------------------------------------------

la-exception-left-identity :
  ∀ (a : ClassifierLaExceptionStep) →
  isLaExceptionIdentity laExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp laExceptionIdentity a) ≡ true
la-exception-left-identity a = refl , refl

la-exception-right-identity :
  ∀ (a : ClassifierLaExceptionStep) →
  isProductConcurrent (productConcurrentOp a laExceptionIdentity) ≡ true
  × isLaExceptionIdentity laExceptionIdentity ≡ true
la-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-la-exception :
  (∀ a → isProductConcurrent (productConcurrentOp laExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a laExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-la-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named La exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedLaExceptionContinuumProduct : ClassifierLaExceptionStep
namedLaExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-la-exception-continuum-product-concurrent :
  isProductConcurrent namedLaExceptionContinuumProduct ≡ true
  × laExceptionBundleIsConcurrentProduct laExceptionContinuumWitness ≡ true
named-la-exception-continuum-product-concurrent = refl , la-exception-concurrent-product

------------------------------------------------------------------------
-- LaExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data LaExceptionAdmissibility : Set where
  la-exception-admissible la-exception-xor-refuse : LaExceptionAdmissibility

isLaExceptionPreserving : ClassifierLaExceptionStep → Bool
isLaExceptionPreserving la-exception-identity = true
isLaExceptionPreserving (slot-leaf _) = true
isLaExceptionPreserving (product-concurrent a b) =
  isLaExceptionPreserving a ∧ isLaExceptionPreserving b
isLaExceptionPreserving (xor-mutually-exclusive _ _) = false

isLaExceptionAdmissible : ClassifierLaExceptionStep → Bool
isLaExceptionAdmissible step = isLaExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isLaExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isLaExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isLaExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-la-exception-continuum-admissible : isLaExceptionAdmissible namedLaExceptionContinuumProduct ≡ true
named-la-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isLaExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isLaExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data LaExceptionWitnessPresence : Set where
  la-exception-witness-absent la-exception-witness-present : LaExceptionWitnessPresence

record ClassifierLaExceptionWitness : Set where
  constructor mkClassifierLaExceptionWitness
  field
    witness-presence : LaExceptionWitnessPresence
    la-exception-gap-total : ℕ

laExceptionWitnessAbsent : ClassifierLaExceptionWitness
laExceptionWitnessAbsent = mkClassifierLaExceptionWitness la-exception-witness-absent zero

laExceptionWitnessPresentZeroGap : ClassifierLaExceptionWitness
laExceptionWitnessPresentZeroGap = mkClassifierLaExceptionWitness la-exception-witness-present zero

laExceptionWitnessPresentWithGaps : ℕ → ClassifierLaExceptionWitness
laExceptionWitnessPresentWithGaps n = mkClassifierLaExceptionWitness la-exception-witness-present n

laExceptionWitnessGapFree : ClassifierLaExceptionWitness → Bool
laExceptionWitnessGapFree (mkClassifierLaExceptionWitness la-exception-witness-absent _) = false
laExceptionWitnessGapFree (mkClassifierLaExceptionWitness la-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

la-exception-witness-present-zero-gap-free :
  laExceptionWitnessGapFree laExceptionWitnessPresentZeroGap ≡ true
la-exception-witness-present-zero-gap-free = refl

la-exception-witness-absent-not-gap-free :
  laExceptionWitnessGapFree laExceptionWitnessAbsent ≡ false
la-exception-witness-absent-not-gap-free = refl

la-exception-witness-with-gaps-not-gap-free :
  ∀ n → laExceptionWitnessGapFree (laExceptionWitnessPresentWithGaps (suc n)) ≡ false
la-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-LaException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data LaExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-la-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : LaExceptionContinuumVerdict

laExceptionContinuumVerdictOk : LaExceptionContinuumVerdict → Bool
laExceptionContinuumVerdictOk verdict-unwired-ok = true
laExceptionContinuumVerdictOk verdict-la-exception-admissible-ok = true
laExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
laExceptionContinuumVerdictOk _ = false

evaluateLaExceptionContinuumClose :
  LaExceptionContinuumModality → ClassifierLaExceptionStep → ClassifierLaExceptionWitness
  → LaExceptionBundleWitness → Bool → LaExceptionContinuumVerdict
evaluateLaExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateLaExceptionContinuumClose la-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateLaExceptionContinuumClose la-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateLaExceptionContinuumClose la-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateLaExceptionContinuumClose la-exception-continuum-proved _ (mkClassifierLaExceptionWitness la-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateLaExceptionContinuumClose la-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateLaExceptionContinuumClose la-exception-continuum-proved _ (mkClassifierLaExceptionWitness la-exception-witness-present _) w false
  with laExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-la-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateLaExceptionContinuumClose
    la-exception-continuum-unwired namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateLaExceptionContinuumClose
    la-exception-continuum-assumed namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateLaExceptionContinuumClose
    la-exception-continuum-surrogate namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  laExceptionContinuumVerdictOk
    (evaluateLaExceptionContinuumClose la-exception-continuum-unwired namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false)
    ≡ true
  × laExceptionContinuumVerdictOk
      (evaluateLaExceptionContinuumClose la-exception-continuum-assumed namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false)
      ≡ true
  × laExceptionContinuumVerdictOk
      (evaluateLaExceptionContinuumClose la-exception-continuum-surrogate namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateLaExceptionContinuumClose
    la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  laExceptionContinuumVerdictOk
    (evaluateLaExceptionContinuumClose
       la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

LaTotalClaimWhenWitnessAbsent : Set
LaTotalClaimWhenWitnessAbsent =
  evaluateLaExceptionContinuumClose
    la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false ≡
  verdict-la-exception-admissible-ok

total-claim-⊥-when-witness-absent : LaTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateLaExceptionContinuumClose
    la-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    laExceptionWitnessPresentZeroGap laExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  laExceptionContinuumVerdictOk
    (evaluateLaExceptionContinuumClose
       la-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       laExceptionWitnessPresentZeroGap laExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

LaXorMutuallyExclusiveWhenConcurrent : Set
LaXorMutuallyExclusiveWhenConcurrent =
  evaluateLaExceptionContinuumClose
    la-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    laExceptionWitnessPresentZeroGap laExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : LaXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

la-exception-admissible-ok :
  evaluateLaExceptionContinuumClose
    la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-la-exception-admissible-ok
la-exception-admissible-ok = refl

la-exception-admissible-verdict-ok :
  laExceptionContinuumVerdictOk
    (evaluateLaExceptionContinuumClose
       la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
la-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateLaExceptionContinuumClose
    la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap laExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  laExceptionContinuumVerdictOk
    (evaluateLaExceptionContinuumClose
       la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap laExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-la-exception-proved :
  laExceptionContinuumVerdictOk
    (evaluateLaExceptionContinuumClose
       la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap laExceptionContinuumWitness false)
    ≡ true
  × laExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-la-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateLaExceptionContinuumClose
    la-exception-continuum-unwired namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap laExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  laExceptionContinuumVerdictOk
    (evaluateLaExceptionContinuumClose
       la-exception-continuum-unwired namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap laExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

laExceptionContinuumFiberOk : FormalFiber → Bool
laExceptionContinuumFiberOk fiber-quantum-knowing = true
laExceptionContinuumFiberOk fiber-meso-acting = false

la-exception-continuum-knowing-fiber-ok :
  laExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
la-exception-continuum-knowing-fiber-ok = refl

la-exception-continuum-meso-acting-not-ok :
  laExceptionContinuumFiberOk fiber-meso-acting ≡ false
la-exception-continuum-meso-acting-not-ok = refl

la-exception-continuum-routes-knowing-not-meso :
  laExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  laExceptionContinuumFiberOk fiber-meso-acting ≡ false
la-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  laExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (laExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not La exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

la-exception-continuum-not-proved : laExceptionContinuumProved ≡ false
la-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

la-exception-continuum-second-law-conservation-framed : laExceptionContinuumSecondLawConservationFramed ≡ true
la-exception-continuum-second-law-conservation-framed = refl

la-exception-not-xor-pin : laExceptionContinuumNotXor ≡ true
la-exception-not-xor-pin = la-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

laExceptionContinuumAxiom :
  (laExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (laExceptionContinuumSecondLawConservationFramed ≡ true)
  × (laExceptionContinuumNotXor ≡ true)
  × (evaluateLaExceptionContinuumClose la-exception-continuum-unwired namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateLaExceptionContinuumClose la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessAbsent laExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateLaExceptionContinuumClose la-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) laExceptionWitnessPresentZeroGap laExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateLaExceptionContinuumClose la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-la-exception-admissible-ok)
  × (evaluateLaExceptionContinuumClose la-exception-continuum-proved namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap laExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (laExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (laExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (laExceptionContinuumVerdictOk (evaluateLaExceptionContinuumClose la-exception-continuum-unwired namedLaExceptionContinuumProduct laExceptionWitnessPresentZeroGap laExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp laExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a laExceptionIdentity) ≡ true)
  × (isLaExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (laZ57OccupancyEngineSortIndex ≡ 57)
  × (LaExceptionBundleWitness.present-count laExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ lanthanum ≡ 57)
  × (elementAtomicZ yttrium ≡ 39)
  × (elementAtomicZ actinium ≡ 89)
  × (homologNotCopyNotForked ≡ true)
laExceptionContinuumAxiom =
  la-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , la-exception-continuum-second-law-conservation-framed
  , la-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , la-exception-admissible-ok
  , concurrent-product-ok
  , la-exception-continuum-knowing-fiber-ok
  , la-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , la-z57-occupancy-engine-sort-index
  , la-exception-present-count
  , lanthanum-z-57
  , yttrium-z-39
  , actinium-z-89
  , homolog-not-copy-not-forked-pin

laExceptionContinuumNamed : String
laExceptionContinuumNamed =
  "laExceptionContinuum: La Z=57 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy Y Ac"

laExceptionContinuumAuthority : String
laExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_057_la.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

yttriumHomologAuthority : String
yttriumHomologAuthority =
  "umst/umst-chem/src/elements/z_039_y.rs"

actiniumHomologAuthority : String
actiniumHomologAuthority =
  "umst/umst-chem/src/elements/z_089_ac.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

laExceptionContinuumCellId : String
laExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-LA-EXCEPTION-CONTINUUM"

laExceptionContinuumNonClaim : String
laExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-LA-EXCEPTION-CONTINUUM La Z=57 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy Y Ac XOR mutually exclusive refuse La exception continuum witness concurrent laExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_057_la.rs occupancy_engine_sort homolog Y Z=39 Ac Z=89 not copy not fork not physics GREEN not production_wired"

la-exception-continuum-cell-id :
  laExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-LA-EXCEPTION-CONTINUUM"
la-exception-continuum-cell-id = refl

la-exception-continuum-cites-z057-la-rs :
  laExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_057_la.rs"
la-exception-continuum-cites-z057-la-rs = refl

la-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
la-exception-continuum-cites-occupancy-engine-sort-rs = refl

la-exception-continuum-modality-unwired :
  laExceptionContinuumModalityCurrent ≡ la-exception-continuum-unwired
la-exception-continuum-modality-unwired = refl

laExceptionContinuumPhysicsGreenAuthorized : Set
laExceptionContinuumPhysicsGreenAuthorized = ⊥

la-exception-continuum-physics-green-false : ¬ laExceptionContinuumPhysicsGreenAuthorized
la-exception-continuum-physics-green-false ()

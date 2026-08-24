-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.MoExceptionContinuum.agda
--
-- Mo Z=42 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Mo exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Mo exception continuum** laws Unwired (moExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_042_mo.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Mo Z=42 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.MoExceptionContinuum where


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
-- Modality + Mo Z=42 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data MoExceptionContinuumModality : Set where
  mo-exception-continuum-unwired mo-exception-continuum-assumed
    mo-exception-continuum-proved mo-exception-continuum-surrogate
    : MoExceptionContinuumModality

moExceptionContinuumModalityCurrent : MoExceptionContinuumModality
moExceptionContinuumModalityCurrent = mo-exception-continuum-unwired

moExceptionContinuumProved productionWired not118SquaredGreenTable
  moExceptionContinuumSecondLawConservationFramed moExceptionContinuumNotXor : Bool
moExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
moExceptionContinuumSecondLawConservationFramed = true
moExceptionContinuumNotXor = true

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
-- Mo Z=42 occupancy-engine sort index pin
------------------------------------------------------------------------

moZ42OccupancyEngineSortIndex : ℕ
moZ42OccupancyEngineSortIndex = 42

mo-z42-occupancy-engine-sort-index : moZ42OccupancyEngineSortIndex ≡ 42
mo-z42-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Mo (Z=42), Cr (Z=24 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  molybdenum chromium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ molybdenum = 42
elementAtomicZ chromium = 24

molybdenum-z-42 : elementAtomicZ molybdenum ≡ 42
molybdenum-z-42 = refl

chromium-z-24 : elementAtomicZ chromium ≡ 24
chromium-z-24 = refl

------------------------------------------------------------------------
-- MoExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data MoExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : MoExceptionBundleSlot

isSlotPresent : MoExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- MoExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record MoExceptionBundle : Set where
  field slot : ℕ → MoExceptionBundleSlot

moExceptionBundleUnwired : MoExceptionBundle
moExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : MoExceptionBundle → ℕ → MoExceptionBundleSlot → MoExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else MoExceptionBundle.slot b j }

withPresent : MoExceptionBundle → ℕ → MoExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record MoExceptionBundleWitness : Set where
  constructor mkMoExceptionBundleWitness
  field
    bundle : MoExceptionBundle
    present-count : ℕ

moExceptionBundleIsConcurrentProduct : MoExceptionBundleWitness → Bool
moExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? MoExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Mo exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Mo exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

moExceptionContinuumWitnessBundle : MoExceptionBundle
moExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent moExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

moExceptionContinuumWitness : MoExceptionBundleWitness
moExceptionContinuumWitness =
  mkMoExceptionBundleWitness moExceptionContinuumWitnessBundle 3

mo-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (MoExceptionBundle.slot moExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
mo-exception-occupancy-engine-sort-dblock-present = refl

mo-exception-madelung-exception-theorem-present :
  isSlotPresent (MoExceptionBundle.slot moExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
mo-exception-madelung-exception-theorem-present = refl

mo-exception-continuum-env-restriction-present :
  isSlotPresent (MoExceptionBundle.slot moExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
mo-exception-continuum-env-restriction-present = refl

mo-exception-present-count : MoExceptionBundleWitness.present-count moExceptionContinuumWitness ≡ 3
mo-exception-present-count = refl

mo-exception-concurrent-product :
  moExceptionBundleIsConcurrentProduct moExceptionContinuumWitness ≡ true
mo-exception-concurrent-product = refl

mo-exception-three-factors-concurrent :
  isSlotPresent (MoExceptionBundle.slot moExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (MoExceptionBundle.slot moExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (MoExceptionBundle.slot moExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × MoExceptionBundleWitness.present-count moExceptionContinuumWitness ≡ 3
mo-exception-three-factors-concurrent =
  mo-exception-occupancy-engine-sort-dblock-present
  , mo-exception-madelung-exception-theorem-present
  , mo-exception-continuum-env-restriction-present
  , mo-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : MoExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if moExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = MoExceptionBundleWitness.bundle w
       in if isSlotPresent (MoExceptionBundle.slot b i)
          then if isSlotPresent (MoExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : MoExceptionBundleWitness
unwiredWitness = mkMoExceptionBundleWitness moExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

mo-exception-xor-product-ok :
  evaluateXorRefuse moExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
mo-exception-xor-product-ok = refl

mo-exception-not-xor : moExceptionContinuumNotXor ≡ true
mo-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierMoExceptionStep scaffold — MoExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierMoExceptionStep : Set where
  mo-exception-identity : ClassifierMoExceptionStep
  slot-leaf : ℕ → ClassifierMoExceptionStep
  product-concurrent : ClassifierMoExceptionStep → ClassifierMoExceptionStep → ClassifierMoExceptionStep
  xor-mutually-exclusive : ClassifierMoExceptionStep → ClassifierMoExceptionStep → ClassifierMoExceptionStep

moExceptionIdentity : ClassifierMoExceptionStep
moExceptionIdentity = mo-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierMoExceptionStep → ClassifierMoExceptionStep → ClassifierMoExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierMoExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierMoExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isMoExceptionIdentity : ClassifierMoExceptionStep → Bool
isMoExceptionIdentity mo-exception-identity = true
isMoExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at mo-exception-identity
------------------------------------------------------------------------

mo-exception-left-identity :
  ∀ (a : ClassifierMoExceptionStep) →
  isMoExceptionIdentity moExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp moExceptionIdentity a) ≡ true
mo-exception-left-identity a = refl , refl

mo-exception-right-identity :
  ∀ (a : ClassifierMoExceptionStep) →
  isProductConcurrent (productConcurrentOp a moExceptionIdentity) ≡ true
  × isMoExceptionIdentity moExceptionIdentity ≡ true
mo-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-mo-exception :
  (∀ a → isProductConcurrent (productConcurrentOp moExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a moExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-mo-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Mo exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedMoExceptionContinuumProduct : ClassifierMoExceptionStep
namedMoExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-mo-exception-continuum-product-concurrent :
  isProductConcurrent namedMoExceptionContinuumProduct ≡ true
  × moExceptionBundleIsConcurrentProduct moExceptionContinuumWitness ≡ true
named-mo-exception-continuum-product-concurrent = refl , mo-exception-concurrent-product

------------------------------------------------------------------------
-- MoExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data MoExceptionAdmissibility : Set where
  mo-exception-admissible mo-exception-xor-refuse : MoExceptionAdmissibility

isMoExceptionPreserving : ClassifierMoExceptionStep → Bool
isMoExceptionPreserving mo-exception-identity = true
isMoExceptionPreserving (slot-leaf _) = true
isMoExceptionPreserving (product-concurrent a b) =
  isMoExceptionPreserving a ∧ isMoExceptionPreserving b
isMoExceptionPreserving (xor-mutually-exclusive _ _) = false

isMoExceptionAdmissible : ClassifierMoExceptionStep → Bool
isMoExceptionAdmissible step = isMoExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isMoExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isMoExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isMoExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-mo-exception-continuum-admissible : isMoExceptionAdmissible namedMoExceptionContinuumProduct ≡ true
named-mo-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isMoExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isMoExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data MoExceptionWitnessPresence : Set where
  mo-exception-witness-absent mo-exception-witness-present : MoExceptionWitnessPresence

record ClassifierMoExceptionWitness : Set where
  constructor mkClassifierMoExceptionWitness
  field
    witness-presence : MoExceptionWitnessPresence
    mo-exception-gap-total : ℕ

moExceptionWitnessAbsent : ClassifierMoExceptionWitness
moExceptionWitnessAbsent = mkClassifierMoExceptionWitness mo-exception-witness-absent zero

moExceptionWitnessPresentZeroGap : ClassifierMoExceptionWitness
moExceptionWitnessPresentZeroGap = mkClassifierMoExceptionWitness mo-exception-witness-present zero

moExceptionWitnessPresentWithGaps : ℕ → ClassifierMoExceptionWitness
moExceptionWitnessPresentWithGaps n = mkClassifierMoExceptionWitness mo-exception-witness-present n

moExceptionWitnessGapFree : ClassifierMoExceptionWitness → Bool
moExceptionWitnessGapFree (mkClassifierMoExceptionWitness mo-exception-witness-absent _) = false
moExceptionWitnessGapFree (mkClassifierMoExceptionWitness mo-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

mo-exception-witness-present-zero-gap-free :
  moExceptionWitnessGapFree moExceptionWitnessPresentZeroGap ≡ true
mo-exception-witness-present-zero-gap-free = refl

mo-exception-witness-absent-not-gap-free :
  moExceptionWitnessGapFree moExceptionWitnessAbsent ≡ false
mo-exception-witness-absent-not-gap-free = refl

mo-exception-witness-with-gaps-not-gap-free :
  ∀ n → moExceptionWitnessGapFree (moExceptionWitnessPresentWithGaps (suc n)) ≡ false
mo-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-MoException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data MoExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-mo-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : MoExceptionContinuumVerdict

moExceptionContinuumVerdictOk : MoExceptionContinuumVerdict → Bool
moExceptionContinuumVerdictOk verdict-unwired-ok = true
moExceptionContinuumVerdictOk verdict-mo-exception-admissible-ok = true
moExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
moExceptionContinuumVerdictOk _ = false

evaluateMoExceptionContinuumClose :
  MoExceptionContinuumModality → ClassifierMoExceptionStep → ClassifierMoExceptionWitness
  → MoExceptionBundleWitness → Bool → MoExceptionContinuumVerdict
evaluateMoExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateMoExceptionContinuumClose mo-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateMoExceptionContinuumClose mo-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateMoExceptionContinuumClose mo-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateMoExceptionContinuumClose mo-exception-continuum-proved _ (mkClassifierMoExceptionWitness mo-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateMoExceptionContinuumClose mo-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateMoExceptionContinuumClose mo-exception-continuum-proved _ (mkClassifierMoExceptionWitness mo-exception-witness-present _) w false
  with moExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-mo-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-unwired namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-assumed namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-surrogate namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  moExceptionContinuumVerdictOk
    (evaluateMoExceptionContinuumClose mo-exception-continuum-unwired namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false)
    ≡ true
  × moExceptionContinuumVerdictOk
      (evaluateMoExceptionContinuumClose mo-exception-continuum-assumed namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false)
      ≡ true
  × moExceptionContinuumVerdictOk
      (evaluateMoExceptionContinuumClose mo-exception-continuum-surrogate namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  moExceptionContinuumVerdictOk
    (evaluateMoExceptionContinuumClose
       mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

MoTotalClaimWhenWitnessAbsent : Set
MoTotalClaimWhenWitnessAbsent =
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false ≡
  verdict-mo-exception-admissible-ok

total-claim-⊥-when-witness-absent : MoTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    moExceptionWitnessPresentZeroGap moExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  moExceptionContinuumVerdictOk
    (evaluateMoExceptionContinuumClose
       mo-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       moExceptionWitnessPresentZeroGap moExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

MoXorMutuallyExclusiveWhenConcurrent : Set
MoXorMutuallyExclusiveWhenConcurrent =
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    moExceptionWitnessPresentZeroGap moExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : MoXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

mo-exception-admissible-ok :
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-mo-exception-admissible-ok
mo-exception-admissible-ok = refl

mo-exception-admissible-verdict-ok :
  moExceptionContinuumVerdictOk
    (evaluateMoExceptionContinuumClose
       mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
mo-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap moExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  moExceptionContinuumVerdictOk
    (evaluateMoExceptionContinuumClose
       mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap moExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-mo-exception-proved :
  moExceptionContinuumVerdictOk
    (evaluateMoExceptionContinuumClose
       mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap moExceptionContinuumWitness false)
    ≡ true
  × moExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-mo-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateMoExceptionContinuumClose
    mo-exception-continuum-unwired namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap moExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  moExceptionContinuumVerdictOk
    (evaluateMoExceptionContinuumClose
       mo-exception-continuum-unwired namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap moExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

moExceptionContinuumFiberOk : FormalFiber → Bool
moExceptionContinuumFiberOk fiber-quantum-knowing = true
moExceptionContinuumFiberOk fiber-meso-acting = false

mo-exception-continuum-knowing-fiber-ok :
  moExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
mo-exception-continuum-knowing-fiber-ok = refl

mo-exception-continuum-meso-acting-not-ok :
  moExceptionContinuumFiberOk fiber-meso-acting ≡ false
mo-exception-continuum-meso-acting-not-ok = refl

mo-exception-continuum-routes-knowing-not-meso :
  moExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  moExceptionContinuumFiberOk fiber-meso-acting ≡ false
mo-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  moExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (moExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Mo exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

mo-exception-continuum-not-proved : moExceptionContinuumProved ≡ false
mo-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

mo-exception-continuum-second-law-conservation-framed : moExceptionContinuumSecondLawConservationFramed ≡ true
mo-exception-continuum-second-law-conservation-framed = refl

mo-exception-not-xor-pin : moExceptionContinuumNotXor ≡ true
mo-exception-not-xor-pin = mo-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

moExceptionContinuumAxiom :
  (moExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (moExceptionContinuumSecondLawConservationFramed ≡ true)
  × (moExceptionContinuumNotXor ≡ true)
  × (evaluateMoExceptionContinuumClose mo-exception-continuum-unwired namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateMoExceptionContinuumClose mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessAbsent moExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateMoExceptionContinuumClose mo-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) moExceptionWitnessPresentZeroGap moExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateMoExceptionContinuumClose mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-mo-exception-admissible-ok)
  × (evaluateMoExceptionContinuumClose mo-exception-continuum-proved namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap moExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (moExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (moExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (moExceptionContinuumVerdictOk (evaluateMoExceptionContinuumClose mo-exception-continuum-unwired namedMoExceptionContinuumProduct moExceptionWitnessPresentZeroGap moExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp moExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a moExceptionIdentity) ≡ true)
  × (isMoExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (moZ42OccupancyEngineSortIndex ≡ 42)
  × (MoExceptionBundleWitness.present-count moExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ molybdenum ≡ 42)
  × (elementAtomicZ chromium ≡ 24)
moExceptionContinuumAxiom =
  mo-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , mo-exception-continuum-second-law-conservation-framed
  , mo-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , mo-exception-admissible-ok
  , concurrent-product-ok
  , mo-exception-continuum-knowing-fiber-ok
  , mo-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , mo-z42-occupancy-engine-sort-index
  , mo-exception-present-count
  , molybdenum-z-42
  , chromium-z-24

moExceptionContinuumNamed : String
moExceptionContinuumNamed =
  "moExceptionContinuum: Mo Z=42 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

moExceptionContinuumAuthority : String
moExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_042_mo.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

moExceptionContinuumCellId : String
moExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-MO-EXCEPTION-CONTINUUM"

moExceptionContinuumNonClaim : String
moExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-MO-EXCEPTION-CONTINUUM Mo Z=42 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Mo exception continuum witness concurrent moExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_042_mo.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

mo-exception-continuum-cell-id :
  moExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-MO-EXCEPTION-CONTINUUM"
mo-exception-continuum-cell-id = refl

mo-exception-continuum-cites-z042-mo-rs :
  moExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_042_mo.rs"
mo-exception-continuum-cites-z042-mo-rs = refl

mo-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
mo-exception-continuum-cites-occupancy-engine-sort-rs = refl

mo-exception-continuum-modality-unwired :
  moExceptionContinuumModalityCurrent ≡ mo-exception-continuum-unwired
mo-exception-continuum-modality-unwired = refl

moExceptionContinuumPhysicsGreenAuthorized : Set
moExceptionContinuumPhysicsGreenAuthorized = ⊥

mo-exception-continuum-physics-green-false : ¬ moExceptionContinuumPhysicsGreenAuthorized
mo-exception-continuum-physics-green-false ()

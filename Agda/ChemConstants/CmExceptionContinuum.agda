-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.CmExceptionContinuum.agda
--
-- Cm Z=96 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Cm exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Cm exception continuum** laws Unwired (cmExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_096_cm.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Cm Z=96 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.CmExceptionContinuum where


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
-- Modality + Cm Z=96 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data CmExceptionContinuumModality : Set where
  cm-exception-continuum-unwired cm-exception-continuum-assumed
    cm-exception-continuum-proved cm-exception-continuum-surrogate
    : CmExceptionContinuumModality

cmExceptionContinuumModalityCurrent : CmExceptionContinuumModality
cmExceptionContinuumModalityCurrent = cm-exception-continuum-unwired

cmExceptionContinuumProved productionWired not118SquaredGreenTable
  cmExceptionContinuumSecondLawConservationFramed cmExceptionContinuumNotXor : Bool
cmExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
cmExceptionContinuumSecondLawConservationFramed = true
cmExceptionContinuumNotXor = true

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
-- Cm Z=96 occupancy-engine sort index pin
------------------------------------------------------------------------

cmZ96OccupancyEngineSortIndex : ℕ
cmZ96OccupancyEngineSortIndex = 96

cm-z96-occupancy-engine-sort-index : cmZ96OccupancyEngineSortIndex ≡ 96
cm-z96-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Cm (Z=96), Gd (Z=64 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  curium gadolinium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ curium = 96
elementAtomicZ gadolinium = 64

curium-z-96 : elementAtomicZ curium ≡ 96
curium-z-96 = refl

gadolinium-z-64 : elementAtomicZ gadolinium ≡ 64
gadolinium-z-64 = refl

------------------------------------------------------------------------
-- CmExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data CmExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : CmExceptionBundleSlot

isSlotPresent : CmExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- CmExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record CmExceptionBundle : Set where
  field slot : ℕ → CmExceptionBundleSlot

cmExceptionBundleUnwired : CmExceptionBundle
cmExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : CmExceptionBundle → ℕ → CmExceptionBundleSlot → CmExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else CmExceptionBundle.slot b j }

withPresent : CmExceptionBundle → ℕ → CmExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record CmExceptionBundleWitness : Set where
  constructor mkCmExceptionBundleWitness
  field
    bundle : CmExceptionBundle
    present-count : ℕ

cmExceptionBundleIsConcurrentProduct : CmExceptionBundleWitness → Bool
cmExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? CmExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Cm exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Cm exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

cmExceptionContinuumWitnessBundle : CmExceptionBundle
cmExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent cmExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

cmExceptionContinuumWitness : CmExceptionBundleWitness
cmExceptionContinuumWitness =
  mkCmExceptionBundleWitness cmExceptionContinuumWitnessBundle 3

cm-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (CmExceptionBundle.slot cmExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
cm-exception-occupancy-engine-sort-dblock-present = refl

cm-exception-madelung-exception-theorem-present :
  isSlotPresent (CmExceptionBundle.slot cmExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
cm-exception-madelung-exception-theorem-present = refl

cm-exception-continuum-env-restriction-present :
  isSlotPresent (CmExceptionBundle.slot cmExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
cm-exception-continuum-env-restriction-present = refl

cm-exception-present-count : CmExceptionBundleWitness.present-count cmExceptionContinuumWitness ≡ 3
cm-exception-present-count = refl

cm-exception-concurrent-product :
  cmExceptionBundleIsConcurrentProduct cmExceptionContinuumWitness ≡ true
cm-exception-concurrent-product = refl

cm-exception-three-factors-concurrent :
  isSlotPresent (CmExceptionBundle.slot cmExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (CmExceptionBundle.slot cmExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (CmExceptionBundle.slot cmExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × CmExceptionBundleWitness.present-count cmExceptionContinuumWitness ≡ 3
cm-exception-three-factors-concurrent =
  cm-exception-occupancy-engine-sort-dblock-present
  , cm-exception-madelung-exception-theorem-present
  , cm-exception-continuum-env-restriction-present
  , cm-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : CmExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if cmExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = CmExceptionBundleWitness.bundle w
       in if isSlotPresent (CmExceptionBundle.slot b i)
          then if isSlotPresent (CmExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : CmExceptionBundleWitness
unwiredWitness = mkCmExceptionBundleWitness cmExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

cm-exception-xor-product-ok :
  evaluateXorRefuse cmExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
cm-exception-xor-product-ok = refl

cm-exception-not-xor : cmExceptionContinuumNotXor ≡ true
cm-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierCmExceptionStep scaffold — CmExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierCmExceptionStep : Set where
  cm-exception-identity : ClassifierCmExceptionStep
  slot-leaf : ℕ → ClassifierCmExceptionStep
  product-concurrent : ClassifierCmExceptionStep → ClassifierCmExceptionStep → ClassifierCmExceptionStep
  xor-mutually-exclusive : ClassifierCmExceptionStep → ClassifierCmExceptionStep → ClassifierCmExceptionStep

cmExceptionIdentity : ClassifierCmExceptionStep
cmExceptionIdentity = cm-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierCmExceptionStep → ClassifierCmExceptionStep → ClassifierCmExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierCmExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierCmExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isCmExceptionIdentity : ClassifierCmExceptionStep → Bool
isCmExceptionIdentity cm-exception-identity = true
isCmExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at cm-exception-identity
------------------------------------------------------------------------

cm-exception-left-identity :
  ∀ (a : ClassifierCmExceptionStep) →
  isCmExceptionIdentity cmExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp cmExceptionIdentity a) ≡ true
cm-exception-left-identity a = refl , refl

cm-exception-right-identity :
  ∀ (a : ClassifierCmExceptionStep) →
  isProductConcurrent (productConcurrentOp a cmExceptionIdentity) ≡ true
  × isCmExceptionIdentity cmExceptionIdentity ≡ true
cm-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-cm-exception :
  (∀ a → isProductConcurrent (productConcurrentOp cmExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a cmExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-cm-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Cm exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedCmExceptionContinuumProduct : ClassifierCmExceptionStep
namedCmExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-cm-exception-continuum-product-concurrent :
  isProductConcurrent namedCmExceptionContinuumProduct ≡ true
  × cmExceptionBundleIsConcurrentProduct cmExceptionContinuumWitness ≡ true
named-cm-exception-continuum-product-concurrent = refl , cm-exception-concurrent-product

------------------------------------------------------------------------
-- CmExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data CmExceptionAdmissibility : Set where
  cm-exception-admissible cm-exception-xor-refuse : CmExceptionAdmissibility

isCmExceptionPreserving : ClassifierCmExceptionStep → Bool
isCmExceptionPreserving cm-exception-identity = true
isCmExceptionPreserving (slot-leaf _) = true
isCmExceptionPreserving (product-concurrent a b) =
  isCmExceptionPreserving a ∧ isCmExceptionPreserving b
isCmExceptionPreserving (xor-mutually-exclusive _ _) = false

isCmExceptionAdmissible : ClassifierCmExceptionStep → Bool
isCmExceptionAdmissible step = isCmExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isCmExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isCmExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isCmExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-cm-exception-continuum-admissible : isCmExceptionAdmissible namedCmExceptionContinuumProduct ≡ true
named-cm-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isCmExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isCmExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data CmExceptionWitnessPresence : Set where
  cm-exception-witness-absent cm-exception-witness-present : CmExceptionWitnessPresence

record ClassifierCmExceptionWitness : Set where
  constructor mkClassifierCmExceptionWitness
  field
    witness-presence : CmExceptionWitnessPresence
    cm-exception-gap-total : ℕ

cmExceptionWitnessAbsent : ClassifierCmExceptionWitness
cmExceptionWitnessAbsent = mkClassifierCmExceptionWitness cm-exception-witness-absent zero

cmExceptionWitnessPresentZeroGap : ClassifierCmExceptionWitness
cmExceptionWitnessPresentZeroGap = mkClassifierCmExceptionWitness cm-exception-witness-present zero

cmExceptionWitnessPresentWithGaps : ℕ → ClassifierCmExceptionWitness
cmExceptionWitnessPresentWithGaps n = mkClassifierCmExceptionWitness cm-exception-witness-present n

cmExceptionWitnessGapFree : ClassifierCmExceptionWitness → Bool
cmExceptionWitnessGapFree (mkClassifierCmExceptionWitness cm-exception-witness-absent _) = false
cmExceptionWitnessGapFree (mkClassifierCmExceptionWitness cm-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

cm-exception-witness-present-zero-gap-free :
  cmExceptionWitnessGapFree cmExceptionWitnessPresentZeroGap ≡ true
cm-exception-witness-present-zero-gap-free = refl

cm-exception-witness-absent-not-gap-free :
  cmExceptionWitnessGapFree cmExceptionWitnessAbsent ≡ false
cm-exception-witness-absent-not-gap-free = refl

cm-exception-witness-with-gaps-not-gap-free :
  ∀ n → cmExceptionWitnessGapFree (cmExceptionWitnessPresentWithGaps (suc n)) ≡ false
cm-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-CmException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data CmExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-cm-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : CmExceptionContinuumVerdict

cmExceptionContinuumVerdictOk : CmExceptionContinuumVerdict → Bool
cmExceptionContinuumVerdictOk verdict-unwired-ok = true
cmExceptionContinuumVerdictOk verdict-cm-exception-admissible-ok = true
cmExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
cmExceptionContinuumVerdictOk _ = false

evaluateCmExceptionContinuumClose :
  CmExceptionContinuumModality → ClassifierCmExceptionStep → ClassifierCmExceptionWitness
  → CmExceptionBundleWitness → Bool → CmExceptionContinuumVerdict
evaluateCmExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateCmExceptionContinuumClose cm-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateCmExceptionContinuumClose cm-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateCmExceptionContinuumClose cm-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateCmExceptionContinuumClose cm-exception-continuum-proved _ (mkClassifierCmExceptionWitness cm-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateCmExceptionContinuumClose cm-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateCmExceptionContinuumClose cm-exception-continuum-proved _ (mkClassifierCmExceptionWitness cm-exception-witness-present _) w false
  with cmExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-cm-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-unwired namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-assumed namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-surrogate namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  cmExceptionContinuumVerdictOk
    (evaluateCmExceptionContinuumClose cm-exception-continuum-unwired namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false)
    ≡ true
  × cmExceptionContinuumVerdictOk
      (evaluateCmExceptionContinuumClose cm-exception-continuum-assumed namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false)
      ≡ true
  × cmExceptionContinuumVerdictOk
      (evaluateCmExceptionContinuumClose cm-exception-continuum-surrogate namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  cmExceptionContinuumVerdictOk
    (evaluateCmExceptionContinuumClose
       cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

CmTotalClaimWhenWitnessAbsent : Set
CmTotalClaimWhenWitnessAbsent =
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false ≡
  verdict-cm-exception-admissible-ok

total-claim-⊥-when-witness-absent : CmTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  cmExceptionContinuumVerdictOk
    (evaluateCmExceptionContinuumClose
       cm-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

CmXorMutuallyExclusiveWhenConcurrent : Set
CmXorMutuallyExclusiveWhenConcurrent =
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : CmXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

cm-exception-admissible-ok :
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-cm-exception-admissible-ok
cm-exception-admissible-ok = refl

cm-exception-admissible-verdict-ok :
  cmExceptionContinuumVerdictOk
    (evaluateCmExceptionContinuumClose
       cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
cm-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  cmExceptionContinuumVerdictOk
    (evaluateCmExceptionContinuumClose
       cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-cm-exception-proved :
  cmExceptionContinuumVerdictOk
    (evaluateCmExceptionContinuumClose
       cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness false)
    ≡ true
  × cmExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-cm-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateCmExceptionContinuumClose
    cm-exception-continuum-unwired namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  cmExceptionContinuumVerdictOk
    (evaluateCmExceptionContinuumClose
       cm-exception-continuum-unwired namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

cmExceptionContinuumFiberOk : FormalFiber → Bool
cmExceptionContinuumFiberOk fiber-quantum-knowing = true
cmExceptionContinuumFiberOk fiber-meso-acting = false

cm-exception-continuum-knowing-fiber-ok :
  cmExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
cm-exception-continuum-knowing-fiber-ok = refl

cm-exception-continuum-meso-acting-not-ok :
  cmExceptionContinuumFiberOk fiber-meso-acting ≡ false
cm-exception-continuum-meso-acting-not-ok = refl

cm-exception-continuum-routes-knowing-not-meso :
  cmExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  cmExceptionContinuumFiberOk fiber-meso-acting ≡ false
cm-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  cmExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (cmExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Cm exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

cm-exception-continuum-not-proved : cmExceptionContinuumProved ≡ false
cm-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

cm-exception-continuum-second-law-conservation-framed : cmExceptionContinuumSecondLawConservationFramed ≡ true
cm-exception-continuum-second-law-conservation-framed = refl

cm-exception-not-xor-pin : cmExceptionContinuumNotXor ≡ true
cm-exception-not-xor-pin = cm-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

cmExceptionContinuumAxiom :
  (cmExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (cmExceptionContinuumSecondLawConservationFramed ≡ true)
  × (cmExceptionContinuumNotXor ≡ true)
  × (evaluateCmExceptionContinuumClose cm-exception-continuum-unwired namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateCmExceptionContinuumClose cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessAbsent cmExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateCmExceptionContinuumClose cm-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateCmExceptionContinuumClose cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-cm-exception-admissible-ok)
  × (evaluateCmExceptionContinuumClose cm-exception-continuum-proved namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (cmExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (cmExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (cmExceptionContinuumVerdictOk (evaluateCmExceptionContinuumClose cm-exception-continuum-unwired namedCmExceptionContinuumProduct cmExceptionWitnessPresentZeroGap cmExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp cmExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a cmExceptionIdentity) ≡ true)
  × (isCmExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (cmZ96OccupancyEngineSortIndex ≡ 96)
  × (CmExceptionBundleWitness.present-count cmExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ curium ≡ 96)
  × (elementAtomicZ gadolinium ≡ 64)
cmExceptionContinuumAxiom =
  cm-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , cm-exception-continuum-second-law-conservation-framed
  , cm-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , cm-exception-admissible-ok
  , concurrent-product-ok
  , cm-exception-continuum-knowing-fiber-ok
  , cm-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , cm-z96-occupancy-engine-sort-index
  , cm-exception-present-count
  , curium-z-96
  , gadolinium-z-64

cmExceptionContinuumNamed : String
cmExceptionContinuumNamed =
  "cmExceptionContinuum: Cm Z=96 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

cmExceptionContinuumAuthority : String
cmExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_096_cm.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

cmExceptionContinuumCellId : String
cmExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-CM-EXCEPTION-CONTINUUM"

cmExceptionContinuumNonClaim : String
cmExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-CM-EXCEPTION-CONTINUUM Cm Z=96 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Cm exception continuum witness concurrent cmExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_096_cm.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

cm-exception-continuum-cell-id :
  cmExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-CM-EXCEPTION-CONTINUUM"
cm-exception-continuum-cell-id = refl

cm-exception-continuum-cites-z096-cm-rs :
  cmExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_096_cm.rs"
cm-exception-continuum-cites-z096-cm-rs = refl

cm-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
cm-exception-continuum-cites-occupancy-engine-sort-rs = refl

cm-exception-continuum-modality-unwired :
  cmExceptionContinuumModalityCurrent ≡ cm-exception-continuum-unwired
cm-exception-continuum-modality-unwired = refl

cmExceptionContinuumPhysicsGreenAuthorized : Set
cmExceptionContinuumPhysicsGreenAuthorized = ⊥

cm-exception-continuum-physics-green-false : ¬ cmExceptionContinuumPhysicsGreenAuthorized
cm-exception-continuum-physics-green-false ()

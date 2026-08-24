-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.AcExceptionContinuum.agda
--
-- Ac Z=89 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Ac exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Ac exception continuum** laws Unwired (acExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_089_ac.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Ac Z=89 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.AcExceptionContinuum where


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
-- Modality + Ac Z=89 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data AcExceptionContinuumModality : Set where
  ac-exception-continuum-unwired ac-exception-continuum-assumed
    ac-exception-continuum-proved ac-exception-continuum-surrogate
    : AcExceptionContinuumModality

acExceptionContinuumModalityCurrent : AcExceptionContinuumModality
acExceptionContinuumModalityCurrent = ac-exception-continuum-unwired

acExceptionContinuumProved productionWired not118SquaredGreenTable
  acExceptionContinuumSecondLawConservationFramed acExceptionContinuumNotXor : Bool
acExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
acExceptionContinuumSecondLawConservationFramed = true
acExceptionContinuumNotXor = true

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
-- Ac Z=89 occupancy-engine sort index pin
------------------------------------------------------------------------

acZ89OccupancyEngineSortIndex : ℕ
acZ89OccupancyEngineSortIndex = 89

ac-z89-occupancy-engine-sort-index : acZ89OccupancyEngineSortIndex ≡ 89
ac-z89-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Ac (Z=89), La (Z=57 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  actinium lanthanum : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ actinium = 89
elementAtomicZ lanthanum = 57

actinium-z-89 : elementAtomicZ actinium ≡ 89
actinium-z-89 = refl

lanthanum-z-57 : elementAtomicZ lanthanum ≡ 57
lanthanum-z-57 = refl

------------------------------------------------------------------------
-- AcExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data AcExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : AcExceptionBundleSlot

isSlotPresent : AcExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- AcExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record AcExceptionBundle : Set where
  field slot : ℕ → AcExceptionBundleSlot

acExceptionBundleUnwired : AcExceptionBundle
acExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : AcExceptionBundle → ℕ → AcExceptionBundleSlot → AcExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else AcExceptionBundle.slot b j }

withPresent : AcExceptionBundle → ℕ → AcExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record AcExceptionBundleWitness : Set where
  constructor mkAcExceptionBundleWitness
  field
    bundle : AcExceptionBundle
    present-count : ℕ

acExceptionBundleIsConcurrentProduct : AcExceptionBundleWitness → Bool
acExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? AcExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Ac exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Ac exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

acExceptionContinuumWitnessBundle : AcExceptionBundle
acExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent acExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

acExceptionContinuumWitness : AcExceptionBundleWitness
acExceptionContinuumWitness =
  mkAcExceptionBundleWitness acExceptionContinuumWitnessBundle 3

ac-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (AcExceptionBundle.slot acExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
ac-exception-occupancy-engine-sort-dblock-present = refl

ac-exception-madelung-exception-theorem-present :
  isSlotPresent (AcExceptionBundle.slot acExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
ac-exception-madelung-exception-theorem-present = refl

ac-exception-continuum-env-restriction-present :
  isSlotPresent (AcExceptionBundle.slot acExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
ac-exception-continuum-env-restriction-present = refl

ac-exception-present-count : AcExceptionBundleWitness.present-count acExceptionContinuumWitness ≡ 3
ac-exception-present-count = refl

ac-exception-concurrent-product :
  acExceptionBundleIsConcurrentProduct acExceptionContinuumWitness ≡ true
ac-exception-concurrent-product = refl

ac-exception-three-factors-concurrent :
  isSlotPresent (AcExceptionBundle.slot acExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (AcExceptionBundle.slot acExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (AcExceptionBundle.slot acExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × AcExceptionBundleWitness.present-count acExceptionContinuumWitness ≡ 3
ac-exception-three-factors-concurrent =
  ac-exception-occupancy-engine-sort-dblock-present
  , ac-exception-madelung-exception-theorem-present
  , ac-exception-continuum-env-restriction-present
  , ac-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : AcExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if acExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = AcExceptionBundleWitness.bundle w
       in if isSlotPresent (AcExceptionBundle.slot b i)
          then if isSlotPresent (AcExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : AcExceptionBundleWitness
unwiredWitness = mkAcExceptionBundleWitness acExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

ac-exception-xor-product-ok :
  evaluateXorRefuse acExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
ac-exception-xor-product-ok = refl

ac-exception-not-xor : acExceptionContinuumNotXor ≡ true
ac-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierAcExceptionStep scaffold — AcExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierAcExceptionStep : Set where
  ac-exception-identity : ClassifierAcExceptionStep
  slot-leaf : ℕ → ClassifierAcExceptionStep
  product-concurrent : ClassifierAcExceptionStep → ClassifierAcExceptionStep → ClassifierAcExceptionStep
  xor-mutually-exclusive : ClassifierAcExceptionStep → ClassifierAcExceptionStep → ClassifierAcExceptionStep

acExceptionIdentity : ClassifierAcExceptionStep
acExceptionIdentity = ac-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierAcExceptionStep → ClassifierAcExceptionStep → ClassifierAcExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierAcExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierAcExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isAcExceptionIdentity : ClassifierAcExceptionStep → Bool
isAcExceptionIdentity ac-exception-identity = true
isAcExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at ac-exception-identity
------------------------------------------------------------------------

ac-exception-left-identity :
  ∀ (a : ClassifierAcExceptionStep) →
  isAcExceptionIdentity acExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp acExceptionIdentity a) ≡ true
ac-exception-left-identity a = refl , refl

ac-exception-right-identity :
  ∀ (a : ClassifierAcExceptionStep) →
  isProductConcurrent (productConcurrentOp a acExceptionIdentity) ≡ true
  × isAcExceptionIdentity acExceptionIdentity ≡ true
ac-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-ac-exception :
  (∀ a → isProductConcurrent (productConcurrentOp acExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a acExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-ac-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Ac exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedAcExceptionContinuumProduct : ClassifierAcExceptionStep
namedAcExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-ac-exception-continuum-product-concurrent :
  isProductConcurrent namedAcExceptionContinuumProduct ≡ true
  × acExceptionBundleIsConcurrentProduct acExceptionContinuumWitness ≡ true
named-ac-exception-continuum-product-concurrent = refl , ac-exception-concurrent-product

------------------------------------------------------------------------
-- AcExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data AcExceptionAdmissibility : Set where
  ac-exception-admissible ac-exception-xor-refuse : AcExceptionAdmissibility

isAcExceptionPreserving : ClassifierAcExceptionStep → Bool
isAcExceptionPreserving ac-exception-identity = true
isAcExceptionPreserving (slot-leaf _) = true
isAcExceptionPreserving (product-concurrent a b) =
  isAcExceptionPreserving a ∧ isAcExceptionPreserving b
isAcExceptionPreserving (xor-mutually-exclusive _ _) = false

isAcExceptionAdmissible : ClassifierAcExceptionStep → Bool
isAcExceptionAdmissible step = isAcExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isAcExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isAcExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isAcExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-ac-exception-continuum-admissible : isAcExceptionAdmissible namedAcExceptionContinuumProduct ≡ true
named-ac-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isAcExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isAcExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data AcExceptionWitnessPresence : Set where
  ac-exception-witness-absent ac-exception-witness-present : AcExceptionWitnessPresence

record ClassifierAcExceptionWitness : Set where
  constructor mkClassifierAcExceptionWitness
  field
    witness-presence : AcExceptionWitnessPresence
    ac-exception-gap-total : ℕ

acExceptionWitnessAbsent : ClassifierAcExceptionWitness
acExceptionWitnessAbsent = mkClassifierAcExceptionWitness ac-exception-witness-absent zero

acExceptionWitnessPresentZeroGap : ClassifierAcExceptionWitness
acExceptionWitnessPresentZeroGap = mkClassifierAcExceptionWitness ac-exception-witness-present zero

acExceptionWitnessPresentWithGaps : ℕ → ClassifierAcExceptionWitness
acExceptionWitnessPresentWithGaps n = mkClassifierAcExceptionWitness ac-exception-witness-present n

acExceptionWitnessGapFree : ClassifierAcExceptionWitness → Bool
acExceptionWitnessGapFree (mkClassifierAcExceptionWitness ac-exception-witness-absent _) = false
acExceptionWitnessGapFree (mkClassifierAcExceptionWitness ac-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

ac-exception-witness-present-zero-gap-free :
  acExceptionWitnessGapFree acExceptionWitnessPresentZeroGap ≡ true
ac-exception-witness-present-zero-gap-free = refl

ac-exception-witness-absent-not-gap-free :
  acExceptionWitnessGapFree acExceptionWitnessAbsent ≡ false
ac-exception-witness-absent-not-gap-free = refl

ac-exception-witness-with-gaps-not-gap-free :
  ∀ n → acExceptionWitnessGapFree (acExceptionWitnessPresentWithGaps (suc n)) ≡ false
ac-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-AcException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data AcExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-ac-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : AcExceptionContinuumVerdict

acExceptionContinuumVerdictOk : AcExceptionContinuumVerdict → Bool
acExceptionContinuumVerdictOk verdict-unwired-ok = true
acExceptionContinuumVerdictOk verdict-ac-exception-admissible-ok = true
acExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
acExceptionContinuumVerdictOk _ = false

evaluateAcExceptionContinuumClose :
  AcExceptionContinuumModality → ClassifierAcExceptionStep → ClassifierAcExceptionWitness
  → AcExceptionBundleWitness → Bool → AcExceptionContinuumVerdict
evaluateAcExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateAcExceptionContinuumClose ac-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateAcExceptionContinuumClose ac-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateAcExceptionContinuumClose ac-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateAcExceptionContinuumClose ac-exception-continuum-proved _ (mkClassifierAcExceptionWitness ac-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateAcExceptionContinuumClose ac-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateAcExceptionContinuumClose ac-exception-continuum-proved _ (mkClassifierAcExceptionWitness ac-exception-witness-present _) w false
  with acExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-ac-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-unwired namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-assumed namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-surrogate namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  acExceptionContinuumVerdictOk
    (evaluateAcExceptionContinuumClose ac-exception-continuum-unwired namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false)
    ≡ true
  × acExceptionContinuumVerdictOk
      (evaluateAcExceptionContinuumClose ac-exception-continuum-assumed namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false)
      ≡ true
  × acExceptionContinuumVerdictOk
      (evaluateAcExceptionContinuumClose ac-exception-continuum-surrogate namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  acExceptionContinuumVerdictOk
    (evaluateAcExceptionContinuumClose
       ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

AcTotalClaimWhenWitnessAbsent : Set
AcTotalClaimWhenWitnessAbsent =
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false ≡
  verdict-ac-exception-admissible-ok

total-claim-⊥-when-witness-absent : AcTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    acExceptionWitnessPresentZeroGap acExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  acExceptionContinuumVerdictOk
    (evaluateAcExceptionContinuumClose
       ac-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       acExceptionWitnessPresentZeroGap acExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

AcXorMutuallyExclusiveWhenConcurrent : Set
AcXorMutuallyExclusiveWhenConcurrent =
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    acExceptionWitnessPresentZeroGap acExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : AcXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

ac-exception-admissible-ok :
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-ac-exception-admissible-ok
ac-exception-admissible-ok = refl

ac-exception-admissible-verdict-ok :
  acExceptionContinuumVerdictOk
    (evaluateAcExceptionContinuumClose
       ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
ac-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap acExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  acExceptionContinuumVerdictOk
    (evaluateAcExceptionContinuumClose
       ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap acExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-ac-exception-proved :
  acExceptionContinuumVerdictOk
    (evaluateAcExceptionContinuumClose
       ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap acExceptionContinuumWitness false)
    ≡ true
  × acExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-ac-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateAcExceptionContinuumClose
    ac-exception-continuum-unwired namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap acExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  acExceptionContinuumVerdictOk
    (evaluateAcExceptionContinuumClose
       ac-exception-continuum-unwired namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap acExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

acExceptionContinuumFiberOk : FormalFiber → Bool
acExceptionContinuumFiberOk fiber-quantum-knowing = true
acExceptionContinuumFiberOk fiber-meso-acting = false

ac-exception-continuum-knowing-fiber-ok :
  acExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
ac-exception-continuum-knowing-fiber-ok = refl

ac-exception-continuum-meso-acting-not-ok :
  acExceptionContinuumFiberOk fiber-meso-acting ≡ false
ac-exception-continuum-meso-acting-not-ok = refl

ac-exception-continuum-routes-knowing-not-meso :
  acExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  acExceptionContinuumFiberOk fiber-meso-acting ≡ false
ac-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  acExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (acExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Ac exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

ac-exception-continuum-not-proved : acExceptionContinuumProved ≡ false
ac-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

ac-exception-continuum-second-law-conservation-framed : acExceptionContinuumSecondLawConservationFramed ≡ true
ac-exception-continuum-second-law-conservation-framed = refl

ac-exception-not-xor-pin : acExceptionContinuumNotXor ≡ true
ac-exception-not-xor-pin = ac-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

acExceptionContinuumAxiom :
  (acExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (acExceptionContinuumSecondLawConservationFramed ≡ true)
  × (acExceptionContinuumNotXor ≡ true)
  × (evaluateAcExceptionContinuumClose ac-exception-continuum-unwired namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateAcExceptionContinuumClose ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessAbsent acExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateAcExceptionContinuumClose ac-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) acExceptionWitnessPresentZeroGap acExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateAcExceptionContinuumClose ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-ac-exception-admissible-ok)
  × (evaluateAcExceptionContinuumClose ac-exception-continuum-proved namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap acExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (acExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (acExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (acExceptionContinuumVerdictOk (evaluateAcExceptionContinuumClose ac-exception-continuum-unwired namedAcExceptionContinuumProduct acExceptionWitnessPresentZeroGap acExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp acExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a acExceptionIdentity) ≡ true)
  × (isAcExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (acZ89OccupancyEngineSortIndex ≡ 89)
  × (AcExceptionBundleWitness.present-count acExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ actinium ≡ 89)
  × (elementAtomicZ lanthanum ≡ 57)
acExceptionContinuumAxiom =
  ac-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , ac-exception-continuum-second-law-conservation-framed
  , ac-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , ac-exception-admissible-ok
  , concurrent-product-ok
  , ac-exception-continuum-knowing-fiber-ok
  , ac-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , ac-z89-occupancy-engine-sort-index
  , ac-exception-present-count
  , actinium-z-89
  , lanthanum-z-57

acExceptionContinuumNamed : String
acExceptionContinuumNamed =
  "acExceptionContinuum: Ac Z=89 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

acExceptionContinuumAuthority : String
acExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_089_ac.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

acExceptionContinuumCellId : String
acExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-AC-EXCEPTION-CONTINUUM"

acExceptionContinuumNonClaim : String
acExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-AC-EXCEPTION-CONTINUUM Ac Z=89 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Ac exception continuum witness concurrent acExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_089_ac.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

ac-exception-continuum-cell-id :
  acExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-AC-EXCEPTION-CONTINUUM"
ac-exception-continuum-cell-id = refl

ac-exception-continuum-cites-z089-ac-rs :
  acExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_089_ac.rs"
ac-exception-continuum-cites-z089-ac-rs = refl

ac-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
ac-exception-continuum-cites-occupancy-engine-sort-rs = refl

ac-exception-continuum-modality-unwired :
  acExceptionContinuumModalityCurrent ≡ ac-exception-continuum-unwired
ac-exception-continuum-modality-unwired = refl

acExceptionContinuumPhysicsGreenAuthorized : Set
acExceptionContinuumPhysicsGreenAuthorized = ⊥

ac-exception-continuum-physics-green-false : ¬ acExceptionContinuumPhysicsGreenAuthorized
ac-exception-continuum-physics-green-false ()

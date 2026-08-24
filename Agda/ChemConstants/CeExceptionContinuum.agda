-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.CeExceptionContinuum.agda
--
-- Ce Z=58 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Ce exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Ce exception continuum** laws Unwired (ceExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_058_ce.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog Th not copy. Product not XOR.
-- Ce Z=58 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.CeExceptionContinuum where


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
-- Modality + Ce Z=58 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data CeExceptionContinuumModality : Set where
  ce-exception-continuum-unwired ce-exception-continuum-assumed
    ce-exception-continuum-proved ce-exception-continuum-surrogate
    : CeExceptionContinuumModality

ceExceptionContinuumModalityCurrent : CeExceptionContinuumModality
ceExceptionContinuumModalityCurrent = ce-exception-continuum-unwired

ceExceptionContinuumProved productionWired not118SquaredGreenTable
  ceExceptionContinuumSecondLawConservationFramed ceExceptionContinuumNotXor : Bool
ceExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
ceExceptionContinuumSecondLawConservationFramed = true
ceExceptionContinuumNotXor = true

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
-- Ce Z=58 occupancy-engine sort index pin
------------------------------------------------------------------------

ceZ58OccupancyEngineSortIndex : ℕ
ceZ58OccupancyEngineSortIndex = 58

ce-z58-occupancy-engine-sort-index : ceZ58OccupancyEngineSortIndex ≡ 58
ce-z58-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Ce (Z=58), Th (Z=90 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  cerium thorium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ cerium = 58
elementAtomicZ thorium = 90

cerium-z-58 : elementAtomicZ cerium ≡ 58
cerium-z-58 = refl

thorium-z-90 : elementAtomicZ thorium ≡ 90
thorium-z-90 = refl

------------------------------------------------------------------------
-- CeExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data CeExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : CeExceptionBundleSlot

isSlotPresent : CeExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- CeExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record CeExceptionBundle : Set where
  field slot : ℕ → CeExceptionBundleSlot

ceExceptionBundleUnwired : CeExceptionBundle
ceExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : CeExceptionBundle → ℕ → CeExceptionBundleSlot → CeExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else CeExceptionBundle.slot b j }

withPresent : CeExceptionBundle → ℕ → CeExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record CeExceptionBundleWitness : Set where
  constructor mkCeExceptionBundleWitness
  field
    bundle : CeExceptionBundle
    present-count : ℕ

ceExceptionBundleIsConcurrentProduct : CeExceptionBundleWitness → Bool
ceExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? CeExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Ce exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Ce exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

ceExceptionContinuumWitnessBundle : CeExceptionBundle
ceExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent ceExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

ceExceptionContinuumWitness : CeExceptionBundleWitness
ceExceptionContinuumWitness =
  mkCeExceptionBundleWitness ceExceptionContinuumWitnessBundle 3

ce-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (CeExceptionBundle.slot ceExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
ce-exception-occupancy-engine-sort-dblock-present = refl

ce-exception-madelung-exception-theorem-present :
  isSlotPresent (CeExceptionBundle.slot ceExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
ce-exception-madelung-exception-theorem-present = refl

ce-exception-continuum-env-restriction-present :
  isSlotPresent (CeExceptionBundle.slot ceExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
ce-exception-continuum-env-restriction-present = refl

ce-exception-present-count : CeExceptionBundleWitness.present-count ceExceptionContinuumWitness ≡ 3
ce-exception-present-count = refl

ce-exception-concurrent-product :
  ceExceptionBundleIsConcurrentProduct ceExceptionContinuumWitness ≡ true
ce-exception-concurrent-product = refl

ce-exception-three-factors-concurrent :
  isSlotPresent (CeExceptionBundle.slot ceExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (CeExceptionBundle.slot ceExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (CeExceptionBundle.slot ceExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × CeExceptionBundleWitness.present-count ceExceptionContinuumWitness ≡ 3
ce-exception-three-factors-concurrent =
  ce-exception-occupancy-engine-sort-dblock-present
  , ce-exception-madelung-exception-theorem-present
  , ce-exception-continuum-env-restriction-present
  , ce-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : CeExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if ceExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = CeExceptionBundleWitness.bundle w
       in if isSlotPresent (CeExceptionBundle.slot b i)
          then if isSlotPresent (CeExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : CeExceptionBundleWitness
unwiredWitness = mkCeExceptionBundleWitness ceExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

ce-exception-xor-product-ok :
  evaluateXorRefuse ceExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
ce-exception-xor-product-ok = refl

ce-exception-not-xor : ceExceptionContinuumNotXor ≡ true
ce-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierCeExceptionStep scaffold — CeExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierCeExceptionStep : Set where
  ce-exception-identity : ClassifierCeExceptionStep
  slot-leaf : ℕ → ClassifierCeExceptionStep
  product-concurrent : ClassifierCeExceptionStep → ClassifierCeExceptionStep → ClassifierCeExceptionStep
  xor-mutually-exclusive : ClassifierCeExceptionStep → ClassifierCeExceptionStep → ClassifierCeExceptionStep

ceExceptionIdentity : ClassifierCeExceptionStep
ceExceptionIdentity = ce-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierCeExceptionStep → ClassifierCeExceptionStep → ClassifierCeExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierCeExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierCeExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isCeExceptionIdentity : ClassifierCeExceptionStep → Bool
isCeExceptionIdentity ce-exception-identity = true
isCeExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at ce-exception-identity
------------------------------------------------------------------------

ce-exception-left-identity :
  ∀ (a : ClassifierCeExceptionStep) →
  isCeExceptionIdentity ceExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp ceExceptionIdentity a) ≡ true
ce-exception-left-identity a = refl , refl

ce-exception-right-identity :
  ∀ (a : ClassifierCeExceptionStep) →
  isProductConcurrent (productConcurrentOp a ceExceptionIdentity) ≡ true
  × isCeExceptionIdentity ceExceptionIdentity ≡ true
ce-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-ce-exception :
  (∀ a → isProductConcurrent (productConcurrentOp ceExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a ceExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-ce-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Ce exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedCeExceptionContinuumProduct : ClassifierCeExceptionStep
namedCeExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-ce-exception-continuum-product-concurrent :
  isProductConcurrent namedCeExceptionContinuumProduct ≡ true
  × ceExceptionBundleIsConcurrentProduct ceExceptionContinuumWitness ≡ true
named-ce-exception-continuum-product-concurrent = refl , ce-exception-concurrent-product

------------------------------------------------------------------------
-- CeExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data CeExceptionAdmissibility : Set where
  ce-exception-admissible ce-exception-xor-refuse : CeExceptionAdmissibility

isCeExceptionPreserving : ClassifierCeExceptionStep → Bool
isCeExceptionPreserving ce-exception-identity = true
isCeExceptionPreserving (slot-leaf _) = true
isCeExceptionPreserving (product-concurrent a b) =
  isCeExceptionPreserving a ∧ isCeExceptionPreserving b
isCeExceptionPreserving (xor-mutually-exclusive _ _) = false

isCeExceptionAdmissible : ClassifierCeExceptionStep → Bool
isCeExceptionAdmissible step = isCeExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isCeExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isCeExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isCeExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-ce-exception-continuum-admissible : isCeExceptionAdmissible namedCeExceptionContinuumProduct ≡ true
named-ce-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isCeExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isCeExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data CeExceptionWitnessPresence : Set where
  ce-exception-witness-absent ce-exception-witness-present : CeExceptionWitnessPresence

record ClassifierCeExceptionWitness : Set where
  constructor mkClassifierCeExceptionWitness
  field
    witness-presence : CeExceptionWitnessPresence
    ce-exception-gap-total : ℕ

ceExceptionWitnessAbsent : ClassifierCeExceptionWitness
ceExceptionWitnessAbsent = mkClassifierCeExceptionWitness ce-exception-witness-absent zero

ceExceptionWitnessPresentZeroGap : ClassifierCeExceptionWitness
ceExceptionWitnessPresentZeroGap = mkClassifierCeExceptionWitness ce-exception-witness-present zero

ceExceptionWitnessPresentWithGaps : ℕ → ClassifierCeExceptionWitness
ceExceptionWitnessPresentWithGaps n = mkClassifierCeExceptionWitness ce-exception-witness-present n

ceExceptionWitnessGapFree : ClassifierCeExceptionWitness → Bool
ceExceptionWitnessGapFree (mkClassifierCeExceptionWitness ce-exception-witness-absent _) = false
ceExceptionWitnessGapFree (mkClassifierCeExceptionWitness ce-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

ce-exception-witness-present-zero-gap-free :
  ceExceptionWitnessGapFree ceExceptionWitnessPresentZeroGap ≡ true
ce-exception-witness-present-zero-gap-free = refl

ce-exception-witness-absent-not-gap-free :
  ceExceptionWitnessGapFree ceExceptionWitnessAbsent ≡ false
ce-exception-witness-absent-not-gap-free = refl

ce-exception-witness-with-gaps-not-gap-free :
  ∀ n → ceExceptionWitnessGapFree (ceExceptionWitnessPresentWithGaps (suc n)) ≡ false
ce-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-CeException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data CeExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-ce-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : CeExceptionContinuumVerdict

ceExceptionContinuumVerdictOk : CeExceptionContinuumVerdict → Bool
ceExceptionContinuumVerdictOk verdict-unwired-ok = true
ceExceptionContinuumVerdictOk verdict-ce-exception-admissible-ok = true
ceExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
ceExceptionContinuumVerdictOk _ = false

evaluateCeExceptionContinuumClose :
  CeExceptionContinuumModality → ClassifierCeExceptionStep → ClassifierCeExceptionWitness
  → CeExceptionBundleWitness → Bool → CeExceptionContinuumVerdict
evaluateCeExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateCeExceptionContinuumClose ce-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateCeExceptionContinuumClose ce-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateCeExceptionContinuumClose ce-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateCeExceptionContinuumClose ce-exception-continuum-proved _ (mkClassifierCeExceptionWitness ce-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateCeExceptionContinuumClose ce-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateCeExceptionContinuumClose ce-exception-continuum-proved _ (mkClassifierCeExceptionWitness ce-exception-witness-present _) w false
  with ceExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-ce-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-unwired namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-assumed namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-surrogate namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  ceExceptionContinuumVerdictOk
    (evaluateCeExceptionContinuumClose ce-exception-continuum-unwired namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false)
    ≡ true
  × ceExceptionContinuumVerdictOk
      (evaluateCeExceptionContinuumClose ce-exception-continuum-assumed namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false)
      ≡ true
  × ceExceptionContinuumVerdictOk
      (evaluateCeExceptionContinuumClose ce-exception-continuum-surrogate namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  ceExceptionContinuumVerdictOk
    (evaluateCeExceptionContinuumClose
       ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

CeTotalClaimWhenWitnessAbsent : Set
CeTotalClaimWhenWitnessAbsent =
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false ≡
  verdict-ce-exception-admissible-ok

total-claim-⊥-when-witness-absent : CeTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  ceExceptionContinuumVerdictOk
    (evaluateCeExceptionContinuumClose
       ce-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

CeXorMutuallyExclusiveWhenConcurrent : Set
CeXorMutuallyExclusiveWhenConcurrent =
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : CeXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

ce-exception-admissible-ok :
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-ce-exception-admissible-ok
ce-exception-admissible-ok = refl

ce-exception-admissible-verdict-ok :
  ceExceptionContinuumVerdictOk
    (evaluateCeExceptionContinuumClose
       ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
ce-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  ceExceptionContinuumVerdictOk
    (evaluateCeExceptionContinuumClose
       ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-ce-exception-proved :
  ceExceptionContinuumVerdictOk
    (evaluateCeExceptionContinuumClose
       ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness false)
    ≡ true
  × ceExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-ce-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateCeExceptionContinuumClose
    ce-exception-continuum-unwired namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  ceExceptionContinuumVerdictOk
    (evaluateCeExceptionContinuumClose
       ce-exception-continuum-unwired namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

ceExceptionContinuumFiberOk : FormalFiber → Bool
ceExceptionContinuumFiberOk fiber-quantum-knowing = true
ceExceptionContinuumFiberOk fiber-meso-acting = false

ce-exception-continuum-knowing-fiber-ok :
  ceExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
ce-exception-continuum-knowing-fiber-ok = refl

ce-exception-continuum-meso-acting-not-ok :
  ceExceptionContinuumFiberOk fiber-meso-acting ≡ false
ce-exception-continuum-meso-acting-not-ok = refl

ce-exception-continuum-routes-knowing-not-meso :
  ceExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  ceExceptionContinuumFiberOk fiber-meso-acting ≡ false
ce-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  ceExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (ceExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Ce exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

ce-exception-continuum-not-proved : ceExceptionContinuumProved ≡ false
ce-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

ce-exception-continuum-second-law-conservation-framed : ceExceptionContinuumSecondLawConservationFramed ≡ true
ce-exception-continuum-second-law-conservation-framed = refl

ce-exception-not-xor-pin : ceExceptionContinuumNotXor ≡ true
ce-exception-not-xor-pin = ce-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

ceExceptionContinuumAxiom :
  (ceExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (ceExceptionContinuumSecondLawConservationFramed ≡ true)
  × (ceExceptionContinuumNotXor ≡ true)
  × (evaluateCeExceptionContinuumClose ce-exception-continuum-unwired namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateCeExceptionContinuumClose ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessAbsent ceExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateCeExceptionContinuumClose ce-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateCeExceptionContinuumClose ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-ce-exception-admissible-ok)
  × (evaluateCeExceptionContinuumClose ce-exception-continuum-proved namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (ceExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (ceExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (ceExceptionContinuumVerdictOk (evaluateCeExceptionContinuumClose ce-exception-continuum-unwired namedCeExceptionContinuumProduct ceExceptionWitnessPresentZeroGap ceExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp ceExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a ceExceptionIdentity) ≡ true)
  × (isCeExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (ceZ58OccupancyEngineSortIndex ≡ 58)
  × (CeExceptionBundleWitness.present-count ceExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ cerium ≡ 58)
  × (elementAtomicZ thorium ≡ 90)
ceExceptionContinuumAxiom =
  ce-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , ce-exception-continuum-second-law-conservation-framed
  , ce-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , ce-exception-admissible-ok
  , concurrent-product-ok
  , ce-exception-continuum-knowing-fiber-ok
  , ce-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , ce-z58-occupancy-engine-sort-index
  , ce-exception-present-count
  , cerium-z-58
  , thorium-z-90

ceExceptionContinuumNamed : String
ceExceptionContinuumNamed =
  "ceExceptionContinuum: Ce Z=58 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

ceExceptionContinuumAuthority : String
ceExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_058_ce.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

ceExceptionContinuumCellId : String
ceExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-CE-EXCEPTION-CONTINUUM"

ceExceptionContinuumNonClaim : String
ceExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-CE-EXCEPTION-CONTINUUM Ce Z=58 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Ce exception continuum witness concurrent ceExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_058_ce.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

ce-exception-continuum-cell-id :
  ceExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-CE-EXCEPTION-CONTINUUM"
ce-exception-continuum-cell-id = refl

ce-exception-continuum-cites-z058-ce-rs :
  ceExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_058_ce.rs"
ce-exception-continuum-cites-z058-ce-rs = refl

ce-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
ce-exception-continuum-cites-occupancy-engine-sort-rs = refl

ce-exception-continuum-modality-unwired :
  ceExceptionContinuumModalityCurrent ≡ ce-exception-continuum-unwired
ce-exception-continuum-modality-unwired = refl

ceExceptionContinuumPhysicsGreenAuthorized : Set
ceExceptionContinuumPhysicsGreenAuthorized = ⊥

ce-exception-continuum-physics-green-false : ¬ ceExceptionContinuumPhysicsGreenAuthorized
ce-exception-continuum-physics-green-false ()

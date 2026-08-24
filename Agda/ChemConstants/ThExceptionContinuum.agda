-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ThExceptionContinuum.agda
--
-- Th Z=90 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Th exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Th exception continuum** laws Unwired (thExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_090_th.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Th Z=90 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.ThExceptionContinuum where


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
-- Modality + Th Z=90 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ThExceptionContinuumModality : Set where
  th-exception-continuum-unwired th-exception-continuum-assumed
    th-exception-continuum-proved th-exception-continuum-surrogate
    : ThExceptionContinuumModality

thExceptionContinuumModalityCurrent : ThExceptionContinuumModality
thExceptionContinuumModalityCurrent = th-exception-continuum-unwired

thExceptionContinuumProved productionWired not118SquaredGreenTable
  thExceptionContinuumSecondLawConservationFramed thExceptionContinuumNotXor : Bool
thExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
thExceptionContinuumSecondLawConservationFramed = true
thExceptionContinuumNotXor = true

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
-- Th Z=90 occupancy-engine sort index pin
------------------------------------------------------------------------

thZ90OccupancyEngineSortIndex : ℕ
thZ90OccupancyEngineSortIndex = 90

th-z90-occupancy-engine-sort-index : thZ90OccupancyEngineSortIndex ≡ 90
th-z90-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Th (Z=90), Ce (Z=58 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  thorium cerium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ thorium = 90
elementAtomicZ cerium = 58

thorium-z-90 : elementAtomicZ thorium ≡ 90
thorium-z-90 = refl

cerium-z-58 : elementAtomicZ cerium ≡ 58
cerium-z-58 = refl

------------------------------------------------------------------------
-- ThExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data ThExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : ThExceptionBundleSlot

isSlotPresent : ThExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- ThExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record ThExceptionBundle : Set where
  field slot : ℕ → ThExceptionBundleSlot

thExceptionBundleUnwired : ThExceptionBundle
thExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : ThExceptionBundle → ℕ → ThExceptionBundleSlot → ThExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else ThExceptionBundle.slot b j }

withPresent : ThExceptionBundle → ℕ → ThExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record ThExceptionBundleWitness : Set where
  constructor mkThExceptionBundleWitness
  field
    bundle : ThExceptionBundle
    present-count : ℕ

thExceptionBundleIsConcurrentProduct : ThExceptionBundleWitness → Bool
thExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? ThExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Th exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Th exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

thExceptionContinuumWitnessBundle : ThExceptionBundle
thExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent thExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

thExceptionContinuumWitness : ThExceptionBundleWitness
thExceptionContinuumWitness =
  mkThExceptionBundleWitness thExceptionContinuumWitnessBundle 3

th-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (ThExceptionBundle.slot thExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
th-exception-occupancy-engine-sort-dblock-present = refl

th-exception-madelung-exception-theorem-present :
  isSlotPresent (ThExceptionBundle.slot thExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
th-exception-madelung-exception-theorem-present = refl

th-exception-continuum-env-restriction-present :
  isSlotPresent (ThExceptionBundle.slot thExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
th-exception-continuum-env-restriction-present = refl

th-exception-present-count : ThExceptionBundleWitness.present-count thExceptionContinuumWitness ≡ 3
th-exception-present-count = refl

th-exception-concurrent-product :
  thExceptionBundleIsConcurrentProduct thExceptionContinuumWitness ≡ true
th-exception-concurrent-product = refl

th-exception-three-factors-concurrent :
  isSlotPresent (ThExceptionBundle.slot thExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (ThExceptionBundle.slot thExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (ThExceptionBundle.slot thExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × ThExceptionBundleWitness.present-count thExceptionContinuumWitness ≡ 3
th-exception-three-factors-concurrent =
  th-exception-occupancy-engine-sort-dblock-present
  , th-exception-madelung-exception-theorem-present
  , th-exception-continuum-env-restriction-present
  , th-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : ThExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if thExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = ThExceptionBundleWitness.bundle w
       in if isSlotPresent (ThExceptionBundle.slot b i)
          then if isSlotPresent (ThExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : ThExceptionBundleWitness
unwiredWitness = mkThExceptionBundleWitness thExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

th-exception-xor-product-ok :
  evaluateXorRefuse thExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
th-exception-xor-product-ok = refl

th-exception-not-xor : thExceptionContinuumNotXor ≡ true
th-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierThExceptionStep scaffold — ThExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierThExceptionStep : Set where
  th-exception-identity : ClassifierThExceptionStep
  slot-leaf : ℕ → ClassifierThExceptionStep
  product-concurrent : ClassifierThExceptionStep → ClassifierThExceptionStep → ClassifierThExceptionStep
  xor-mutually-exclusive : ClassifierThExceptionStep → ClassifierThExceptionStep → ClassifierThExceptionStep

thExceptionIdentity : ClassifierThExceptionStep
thExceptionIdentity = th-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierThExceptionStep → ClassifierThExceptionStep → ClassifierThExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierThExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierThExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isThExceptionIdentity : ClassifierThExceptionStep → Bool
isThExceptionIdentity th-exception-identity = true
isThExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at th-exception-identity
------------------------------------------------------------------------

th-exception-left-identity :
  ∀ (a : ClassifierThExceptionStep) →
  isThExceptionIdentity thExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp thExceptionIdentity a) ≡ true
th-exception-left-identity a = refl , refl

th-exception-right-identity :
  ∀ (a : ClassifierThExceptionStep) →
  isProductConcurrent (productConcurrentOp a thExceptionIdentity) ≡ true
  × isThExceptionIdentity thExceptionIdentity ≡ true
th-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-th-exception :
  (∀ a → isProductConcurrent (productConcurrentOp thExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a thExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-th-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Th exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedThExceptionContinuumProduct : ClassifierThExceptionStep
namedThExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-th-exception-continuum-product-concurrent :
  isProductConcurrent namedThExceptionContinuumProduct ≡ true
  × thExceptionBundleIsConcurrentProduct thExceptionContinuumWitness ≡ true
named-th-exception-continuum-product-concurrent = refl , th-exception-concurrent-product

------------------------------------------------------------------------
-- ThExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data ThExceptionAdmissibility : Set where
  th-exception-admissible th-exception-xor-refuse : ThExceptionAdmissibility

isThExceptionPreserving : ClassifierThExceptionStep → Bool
isThExceptionPreserving th-exception-identity = true
isThExceptionPreserving (slot-leaf _) = true
isThExceptionPreserving (product-concurrent a b) =
  isThExceptionPreserving a ∧ isThExceptionPreserving b
isThExceptionPreserving (xor-mutually-exclusive _ _) = false

isThExceptionAdmissible : ClassifierThExceptionStep → Bool
isThExceptionAdmissible step = isThExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isThExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isThExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isThExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-th-exception-continuum-admissible : isThExceptionAdmissible namedThExceptionContinuumProduct ≡ true
named-th-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isThExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isThExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data ThExceptionWitnessPresence : Set where
  th-exception-witness-absent th-exception-witness-present : ThExceptionWitnessPresence

record ClassifierThExceptionWitness : Set where
  constructor mkClassifierThExceptionWitness
  field
    witness-presence : ThExceptionWitnessPresence
    th-exception-gap-total : ℕ

thExceptionWitnessAbsent : ClassifierThExceptionWitness
thExceptionWitnessAbsent = mkClassifierThExceptionWitness th-exception-witness-absent zero

thExceptionWitnessPresentZeroGap : ClassifierThExceptionWitness
thExceptionWitnessPresentZeroGap = mkClassifierThExceptionWitness th-exception-witness-present zero

thExceptionWitnessPresentWithGaps : ℕ → ClassifierThExceptionWitness
thExceptionWitnessPresentWithGaps n = mkClassifierThExceptionWitness th-exception-witness-present n

thExceptionWitnessGapFree : ClassifierThExceptionWitness → Bool
thExceptionWitnessGapFree (mkClassifierThExceptionWitness th-exception-witness-absent _) = false
thExceptionWitnessGapFree (mkClassifierThExceptionWitness th-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

th-exception-witness-present-zero-gap-free :
  thExceptionWitnessGapFree thExceptionWitnessPresentZeroGap ≡ true
th-exception-witness-present-zero-gap-free = refl

th-exception-witness-absent-not-gap-free :
  thExceptionWitnessGapFree thExceptionWitnessAbsent ≡ false
th-exception-witness-absent-not-gap-free = refl

th-exception-witness-with-gaps-not-gap-free :
  ∀ n → thExceptionWitnessGapFree (thExceptionWitnessPresentWithGaps (suc n)) ≡ false
th-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-ThException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data ThExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-th-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : ThExceptionContinuumVerdict

thExceptionContinuumVerdictOk : ThExceptionContinuumVerdict → Bool
thExceptionContinuumVerdictOk verdict-unwired-ok = true
thExceptionContinuumVerdictOk verdict-th-exception-admissible-ok = true
thExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
thExceptionContinuumVerdictOk _ = false

evaluateThExceptionContinuumClose :
  ThExceptionContinuumModality → ClassifierThExceptionStep → ClassifierThExceptionWitness
  → ThExceptionBundleWitness → Bool → ThExceptionContinuumVerdict
evaluateThExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateThExceptionContinuumClose th-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateThExceptionContinuumClose th-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateThExceptionContinuumClose th-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateThExceptionContinuumClose th-exception-continuum-proved _ (mkClassifierThExceptionWitness th-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateThExceptionContinuumClose th-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateThExceptionContinuumClose th-exception-continuum-proved _ (mkClassifierThExceptionWitness th-exception-witness-present _) w false
  with thExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-th-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateThExceptionContinuumClose
    th-exception-continuum-unwired namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateThExceptionContinuumClose
    th-exception-continuum-assumed namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateThExceptionContinuumClose
    th-exception-continuum-surrogate namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  thExceptionContinuumVerdictOk
    (evaluateThExceptionContinuumClose th-exception-continuum-unwired namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false)
    ≡ true
  × thExceptionContinuumVerdictOk
      (evaluateThExceptionContinuumClose th-exception-continuum-assumed namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false)
      ≡ true
  × thExceptionContinuumVerdictOk
      (evaluateThExceptionContinuumClose th-exception-continuum-surrogate namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateThExceptionContinuumClose
    th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  thExceptionContinuumVerdictOk
    (evaluateThExceptionContinuumClose
       th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

ThTotalClaimWhenWitnessAbsent : Set
ThTotalClaimWhenWitnessAbsent =
  evaluateThExceptionContinuumClose
    th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false ≡
  verdict-th-exception-admissible-ok

total-claim-⊥-when-witness-absent : ThTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateThExceptionContinuumClose
    th-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    thExceptionWitnessPresentZeroGap thExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  thExceptionContinuumVerdictOk
    (evaluateThExceptionContinuumClose
       th-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       thExceptionWitnessPresentZeroGap thExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

ThXorMutuallyExclusiveWhenConcurrent : Set
ThXorMutuallyExclusiveWhenConcurrent =
  evaluateThExceptionContinuumClose
    th-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    thExceptionWitnessPresentZeroGap thExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : ThXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

th-exception-admissible-ok :
  evaluateThExceptionContinuumClose
    th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-th-exception-admissible-ok
th-exception-admissible-ok = refl

th-exception-admissible-verdict-ok :
  thExceptionContinuumVerdictOk
    (evaluateThExceptionContinuumClose
       th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
th-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateThExceptionContinuumClose
    th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap thExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  thExceptionContinuumVerdictOk
    (evaluateThExceptionContinuumClose
       th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap thExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-th-exception-proved :
  thExceptionContinuumVerdictOk
    (evaluateThExceptionContinuumClose
       th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap thExceptionContinuumWitness false)
    ≡ true
  × thExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-th-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateThExceptionContinuumClose
    th-exception-continuum-unwired namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap thExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  thExceptionContinuumVerdictOk
    (evaluateThExceptionContinuumClose
       th-exception-continuum-unwired namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap thExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

thExceptionContinuumFiberOk : FormalFiber → Bool
thExceptionContinuumFiberOk fiber-quantum-knowing = true
thExceptionContinuumFiberOk fiber-meso-acting = false

th-exception-continuum-knowing-fiber-ok :
  thExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
th-exception-continuum-knowing-fiber-ok = refl

th-exception-continuum-meso-acting-not-ok :
  thExceptionContinuumFiberOk fiber-meso-acting ≡ false
th-exception-continuum-meso-acting-not-ok = refl

th-exception-continuum-routes-knowing-not-meso :
  thExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  thExceptionContinuumFiberOk fiber-meso-acting ≡ false
th-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  thExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (thExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Th exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

th-exception-continuum-not-proved : thExceptionContinuumProved ≡ false
th-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

th-exception-continuum-second-law-conservation-framed : thExceptionContinuumSecondLawConservationFramed ≡ true
th-exception-continuum-second-law-conservation-framed = refl

th-exception-not-xor-pin : thExceptionContinuumNotXor ≡ true
th-exception-not-xor-pin = th-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

thExceptionContinuumAxiom :
  (thExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (thExceptionContinuumSecondLawConservationFramed ≡ true)
  × (thExceptionContinuumNotXor ≡ true)
  × (evaluateThExceptionContinuumClose th-exception-continuum-unwired namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateThExceptionContinuumClose th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessAbsent thExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateThExceptionContinuumClose th-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) thExceptionWitnessPresentZeroGap thExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateThExceptionContinuumClose th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-th-exception-admissible-ok)
  × (evaluateThExceptionContinuumClose th-exception-continuum-proved namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap thExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (thExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (thExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (thExceptionContinuumVerdictOk (evaluateThExceptionContinuumClose th-exception-continuum-unwired namedThExceptionContinuumProduct thExceptionWitnessPresentZeroGap thExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp thExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a thExceptionIdentity) ≡ true)
  × (isThExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (thZ90OccupancyEngineSortIndex ≡ 90)
  × (ThExceptionBundleWitness.present-count thExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ thorium ≡ 90)
  × (elementAtomicZ cerium ≡ 58)
thExceptionContinuumAxiom =
  th-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , th-exception-continuum-second-law-conservation-framed
  , th-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , th-exception-admissible-ok
  , concurrent-product-ok
  , th-exception-continuum-knowing-fiber-ok
  , th-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , th-z90-occupancy-engine-sort-index
  , th-exception-present-count
  , thorium-z-90
  , cerium-z-58

thExceptionContinuumNamed : String
thExceptionContinuumNamed =
  "thExceptionContinuum: Th Z=90 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

thExceptionContinuumAuthority : String
thExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_090_th.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

thExceptionContinuumCellId : String
thExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-TH-EXCEPTION-CONTINUUM"

thExceptionContinuumNonClaim : String
thExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-TH-EXCEPTION-CONTINUUM Th Z=90 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Th exception continuum witness concurrent thExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_090_th.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

th-exception-continuum-cell-id :
  thExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-TH-EXCEPTION-CONTINUUM"
th-exception-continuum-cell-id = refl

th-exception-continuum-cites-z090-th-rs :
  thExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_090_th.rs"
th-exception-continuum-cites-z090-th-rs = refl

th-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
th-exception-continuum-cites-occupancy-engine-sort-rs = refl

th-exception-continuum-modality-unwired :
  thExceptionContinuumModalityCurrent ≡ th-exception-continuum-unwired
th-exception-continuum-modality-unwired = refl

thExceptionContinuumPhysicsGreenAuthorized : Set
thExceptionContinuumPhysicsGreenAuthorized = ⊥

th-exception-continuum-physics-green-false : ¬ thExceptionContinuumPhysicsGreenAuthorized
th-exception-continuum-physics-green-false ()

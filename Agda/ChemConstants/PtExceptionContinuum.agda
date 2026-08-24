-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PtExceptionContinuum.agda
--
-- Pt Z=78 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Pt exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Pt exception continuum** laws Unwired (ptExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_078_pt.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy Ni/Pd. Product not XOR.
-- Pt Z=78 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.PtExceptionContinuum where


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
-- Modality + Pt Z=78 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PtExceptionContinuumModality : Set where
  pt-exception-continuum-unwired pt-exception-continuum-assumed
    pt-exception-continuum-proved pt-exception-continuum-surrogate
    : PtExceptionContinuumModality

ptExceptionContinuumModalityCurrent : PtExceptionContinuumModality
ptExceptionContinuumModalityCurrent = pt-exception-continuum-unwired

ptExceptionContinuumProved productionWired not118SquaredGreenTable
  ptExceptionContinuumSecondLawConservationFramed ptExceptionContinuumNotXor : Bool
ptExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
ptExceptionContinuumSecondLawConservationFramed = true
ptExceptionContinuumNotXor = true

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
-- Pt Z=78 occupancy-engine sort index pin
------------------------------------------------------------------------

ptZ78OccupancyEngineSortIndex : ℕ
ptZ78OccupancyEngineSortIndex = 78

pt-z78-occupancy-engine-sort-index : ptZ78OccupancyEngineSortIndex ≡ 78
pt-z78-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Pt (Z=78), Pd (Z=46 homolog not Ni/Pd copy)
------------------------------------------------------------------------

data ElementTag : Set where
  platinum palladium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ platinum = 78
elementAtomicZ palladium = 46

platinum-z-78 : elementAtomicZ platinum ≡ 78
platinum-z-78 = refl

palladium-z-46 : elementAtomicZ palladium ≡ 46
palladium-z-46 = refl

------------------------------------------------------------------------
-- PtExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PtExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PtExceptionBundleSlot

isSlotPresent : PtExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- PtExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record PtExceptionBundle : Set where
  field slot : ℕ → PtExceptionBundleSlot

ptExceptionBundleUnwired : PtExceptionBundle
ptExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : PtExceptionBundle → ℕ → PtExceptionBundleSlot → PtExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else PtExceptionBundle.slot b j }

withPresent : PtExceptionBundle → ℕ → PtExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PtExceptionBundleWitness : Set where
  constructor mkPtExceptionBundleWitness
  field
    bundle : PtExceptionBundle
    present-count : ℕ

ptExceptionBundleIsConcurrentProduct : PtExceptionBundleWitness → Bool
ptExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PtExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Pt exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Pt exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

ptExceptionContinuumWitnessBundle : PtExceptionBundle
ptExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent ptExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

ptExceptionContinuumWitness : PtExceptionBundleWitness
ptExceptionContinuumWitness =
  mkPtExceptionBundleWitness ptExceptionContinuumWitnessBundle 3

pt-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (PtExceptionBundle.slot ptExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
pt-exception-occupancy-engine-sort-dblock-present = refl

pt-exception-madelung-exception-theorem-present :
  isSlotPresent (PtExceptionBundle.slot ptExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
pt-exception-madelung-exception-theorem-present = refl

pt-exception-continuum-env-restriction-present :
  isSlotPresent (PtExceptionBundle.slot ptExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
pt-exception-continuum-env-restriction-present = refl

pt-exception-present-count : PtExceptionBundleWitness.present-count ptExceptionContinuumWitness ≡ 3
pt-exception-present-count = refl

pt-exception-concurrent-product :
  ptExceptionBundleIsConcurrentProduct ptExceptionContinuumWitness ≡ true
pt-exception-concurrent-product = refl

pt-exception-three-factors-concurrent :
  isSlotPresent (PtExceptionBundle.slot ptExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (PtExceptionBundle.slot ptExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (PtExceptionBundle.slot ptExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × PtExceptionBundleWitness.present-count ptExceptionContinuumWitness ≡ 3
pt-exception-three-factors-concurrent =
  pt-exception-occupancy-engine-sort-dblock-present
  , pt-exception-madelung-exception-theorem-present
  , pt-exception-continuum-env-restriction-present
  , pt-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PtExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if ptExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = PtExceptionBundleWitness.bundle w
       in if isSlotPresent (PtExceptionBundle.slot b i)
          then if isSlotPresent (PtExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PtExceptionBundleWitness
unwiredWitness = mkPtExceptionBundleWitness ptExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

pt-exception-xor-product-ok :
  evaluateXorRefuse ptExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
pt-exception-xor-product-ok = refl

pt-exception-not-xor : ptExceptionContinuumNotXor ≡ true
pt-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPtExceptionStep scaffold — PtExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierPtExceptionStep : Set where
  pt-exception-identity : ClassifierPtExceptionStep
  slot-leaf : ℕ → ClassifierPtExceptionStep
  product-concurrent : ClassifierPtExceptionStep → ClassifierPtExceptionStep → ClassifierPtExceptionStep
  xor-mutually-exclusive : ClassifierPtExceptionStep → ClassifierPtExceptionStep → ClassifierPtExceptionStep

ptExceptionIdentity : ClassifierPtExceptionStep
ptExceptionIdentity = pt-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPtExceptionStep → ClassifierPtExceptionStep → ClassifierPtExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierPtExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierPtExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isPtExceptionIdentity : ClassifierPtExceptionStep → Bool
isPtExceptionIdentity pt-exception-identity = true
isPtExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at pt-exception-identity
------------------------------------------------------------------------

pt-exception-left-identity :
  ∀ (a : ClassifierPtExceptionStep) →
  isPtExceptionIdentity ptExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp ptExceptionIdentity a) ≡ true
pt-exception-left-identity a = refl , refl

pt-exception-right-identity :
  ∀ (a : ClassifierPtExceptionStep) →
  isProductConcurrent (productConcurrentOp a ptExceptionIdentity) ≡ true
  × isPtExceptionIdentity ptExceptionIdentity ≡ true
pt-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-pt-exception :
  (∀ a → isProductConcurrent (productConcurrentOp ptExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a ptExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-pt-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Pt exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedPtExceptionContinuumProduct : ClassifierPtExceptionStep
namedPtExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-pt-exception-continuum-product-concurrent :
  isProductConcurrent namedPtExceptionContinuumProduct ≡ true
  × ptExceptionBundleIsConcurrentProduct ptExceptionContinuumWitness ≡ true
named-pt-exception-continuum-product-concurrent = refl , pt-exception-concurrent-product

------------------------------------------------------------------------
-- PtExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data PtExceptionAdmissibility : Set where
  pt-exception-admissible pt-exception-xor-refuse : PtExceptionAdmissibility

isPtExceptionPreserving : ClassifierPtExceptionStep → Bool
isPtExceptionPreserving pt-exception-identity = true
isPtExceptionPreserving (slot-leaf _) = true
isPtExceptionPreserving (product-concurrent a b) =
  isPtExceptionPreserving a ∧ isPtExceptionPreserving b
isPtExceptionPreserving (xor-mutually-exclusive _ _) = false

isPtExceptionAdmissible : ClassifierPtExceptionStep → Bool
isPtExceptionAdmissible step = isPtExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isPtExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isPtExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isPtExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-pt-exception-continuum-admissible : isPtExceptionAdmissible namedPtExceptionContinuumProduct ≡ true
named-pt-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isPtExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isPtExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data PtExceptionWitnessPresence : Set where
  pt-exception-witness-absent pt-exception-witness-present : PtExceptionWitnessPresence

record ClassifierPtExceptionWitness : Set where
  constructor mkClassifierPtExceptionWitness
  field
    witness-presence : PtExceptionWitnessPresence
    pt-exception-gap-total : ℕ

ptExceptionWitnessAbsent : ClassifierPtExceptionWitness
ptExceptionWitnessAbsent = mkClassifierPtExceptionWitness pt-exception-witness-absent zero

ptExceptionWitnessPresentZeroGap : ClassifierPtExceptionWitness
ptExceptionWitnessPresentZeroGap = mkClassifierPtExceptionWitness pt-exception-witness-present zero

ptExceptionWitnessPresentWithGaps : ℕ → ClassifierPtExceptionWitness
ptExceptionWitnessPresentWithGaps n = mkClassifierPtExceptionWitness pt-exception-witness-present n

ptExceptionWitnessGapFree : ClassifierPtExceptionWitness → Bool
ptExceptionWitnessGapFree (mkClassifierPtExceptionWitness pt-exception-witness-absent _) = false
ptExceptionWitnessGapFree (mkClassifierPtExceptionWitness pt-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

pt-exception-witness-present-zero-gap-free :
  ptExceptionWitnessGapFree ptExceptionWitnessPresentZeroGap ≡ true
pt-exception-witness-present-zero-gap-free = refl

pt-exception-witness-absent-not-gap-free :
  ptExceptionWitnessGapFree ptExceptionWitnessAbsent ≡ false
pt-exception-witness-absent-not-gap-free = refl

pt-exception-witness-with-gaps-not-gap-free :
  ∀ n → ptExceptionWitnessGapFree (ptExceptionWitnessPresentWithGaps (suc n)) ≡ false
pt-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-PtException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PtExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-pt-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : PtExceptionContinuumVerdict

ptExceptionContinuumVerdictOk : PtExceptionContinuumVerdict → Bool
ptExceptionContinuumVerdictOk verdict-unwired-ok = true
ptExceptionContinuumVerdictOk verdict-pt-exception-admissible-ok = true
ptExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
ptExceptionContinuumVerdictOk _ = false

evaluatePtExceptionContinuumClose :
  PtExceptionContinuumModality → ClassifierPtExceptionStep → ClassifierPtExceptionWitness
  → PtExceptionBundleWitness → Bool → PtExceptionContinuumVerdict
evaluatePtExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluatePtExceptionContinuumClose pt-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluatePtExceptionContinuumClose pt-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluatePtExceptionContinuumClose pt-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluatePtExceptionContinuumClose pt-exception-continuum-proved _ (mkClassifierPtExceptionWitness pt-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluatePtExceptionContinuumClose pt-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluatePtExceptionContinuumClose pt-exception-continuum-proved _ (mkClassifierPtExceptionWitness pt-exception-witness-present _) w false
  with ptExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-pt-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-unwired namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-assumed namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-surrogate namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  ptExceptionContinuumVerdictOk
    (evaluatePtExceptionContinuumClose pt-exception-continuum-unwired namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false)
    ≡ true
  × ptExceptionContinuumVerdictOk
      (evaluatePtExceptionContinuumClose pt-exception-continuum-assumed namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false)
      ≡ true
  × ptExceptionContinuumVerdictOk
      (evaluatePtExceptionContinuumClose pt-exception-continuum-surrogate namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  ptExceptionContinuumVerdictOk
    (evaluatePtExceptionContinuumClose
       pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

PtTotalClaimWhenWitnessAbsent : Set
PtTotalClaimWhenWitnessAbsent =
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false ≡
  verdict-pt-exception-admissible-ok

total-claim-⊥-when-witness-absent : PtTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  ptExceptionContinuumVerdictOk
    (evaluatePtExceptionContinuumClose
       pt-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

PtXorMutuallyExclusiveWhenConcurrent : Set
PtXorMutuallyExclusiveWhenConcurrent =
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : PtXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

pt-exception-admissible-ok :
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-pt-exception-admissible-ok
pt-exception-admissible-ok = refl

pt-exception-admissible-verdict-ok :
  ptExceptionContinuumVerdictOk
    (evaluatePtExceptionContinuumClose
       pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
pt-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  ptExceptionContinuumVerdictOk
    (evaluatePtExceptionContinuumClose
       pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-pt-exception-proved :
  ptExceptionContinuumVerdictOk
    (evaluatePtExceptionContinuumClose
       pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness false)
    ≡ true
  × ptExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-pt-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePtExceptionContinuumClose
    pt-exception-continuum-unwired namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  ptExceptionContinuumVerdictOk
    (evaluatePtExceptionContinuumClose
       pt-exception-continuum-unwired namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

ptExceptionContinuumFiberOk : FormalFiber → Bool
ptExceptionContinuumFiberOk fiber-quantum-knowing = true
ptExceptionContinuumFiberOk fiber-meso-acting = false

pt-exception-continuum-knowing-fiber-ok :
  ptExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
pt-exception-continuum-knowing-fiber-ok = refl

pt-exception-continuum-meso-acting-not-ok :
  ptExceptionContinuumFiberOk fiber-meso-acting ≡ false
pt-exception-continuum-meso-acting-not-ok = refl

pt-exception-continuum-routes-knowing-not-meso :
  ptExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  ptExceptionContinuumFiberOk fiber-meso-acting ≡ false
pt-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  ptExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (ptExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Pt exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

pt-exception-continuum-not-proved : ptExceptionContinuumProved ≡ false
pt-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

pt-exception-continuum-second-law-conservation-framed : ptExceptionContinuumSecondLawConservationFramed ≡ true
pt-exception-continuum-second-law-conservation-framed = refl

pt-exception-not-xor-pin : ptExceptionContinuumNotXor ≡ true
pt-exception-not-xor-pin = pt-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

ptExceptionContinuumAxiom :
  (ptExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (ptExceptionContinuumSecondLawConservationFramed ≡ true)
  × (ptExceptionContinuumNotXor ≡ true)
  × (evaluatePtExceptionContinuumClose pt-exception-continuum-unwired namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluatePtExceptionContinuumClose pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessAbsent ptExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluatePtExceptionContinuumClose pt-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluatePtExceptionContinuumClose pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-pt-exception-admissible-ok)
  × (evaluatePtExceptionContinuumClose pt-exception-continuum-proved namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (ptExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (ptExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (ptExceptionContinuumVerdictOk (evaluatePtExceptionContinuumClose pt-exception-continuum-unwired namedPtExceptionContinuumProduct ptExceptionWitnessPresentZeroGap ptExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp ptExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a ptExceptionIdentity) ≡ true)
  × (isPtExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (ptZ78OccupancyEngineSortIndex ≡ 78)
  × (PtExceptionBundleWitness.present-count ptExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ platinum ≡ 78)
  × (elementAtomicZ palladium ≡ 46)
ptExceptionContinuumAxiom =
  pt-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , pt-exception-continuum-second-law-conservation-framed
  , pt-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , pt-exception-admissible-ok
  , concurrent-product-ok
  , pt-exception-continuum-knowing-fiber-ok
  , pt-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , pt-z78-occupancy-engine-sort-index
  , pt-exception-present-count
  , platinum-z-78
  , palladium-z-46

ptExceptionContinuumNamed : String
ptExceptionContinuumNamed =
  "ptExceptionContinuum: Pt Z=78 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy Ni Pd"

ptExceptionContinuumAuthority : String
ptExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_078_pt.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

ptExceptionContinuumCellId : String
ptExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-PT-EXCEPTION-CONTINUUM"

ptExceptionContinuumNonClaim : String
ptExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-PT-EXCEPTION-CONTINUUM Pt Z=78 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy Ni Pd XOR mutually exclusive refuse Pt exception continuum witness concurrent ptExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_078_pt.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

pt-exception-continuum-cell-id :
  ptExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-PT-EXCEPTION-CONTINUUM"
pt-exception-continuum-cell-id = refl

pt-exception-continuum-cites-z078-pt-rs :
  ptExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_078_pt.rs"
pt-exception-continuum-cites-z078-pt-rs = refl

pt-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
pt-exception-continuum-cites-occupancy-engine-sort-rs = refl

pt-exception-continuum-modality-unwired :
  ptExceptionContinuumModalityCurrent ≡ pt-exception-continuum-unwired
pt-exception-continuum-modality-unwired = refl

ptExceptionContinuumPhysicsGreenAuthorized : Set
ptExceptionContinuumPhysicsGreenAuthorized = ⊥

pt-exception-continuum-physics-green-false : ¬ ptExceptionContinuumPhysicsGreenAuthorized
pt-exception-continuum-physics-green-false ()

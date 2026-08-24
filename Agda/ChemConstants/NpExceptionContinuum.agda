-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.NpExceptionContinuum.agda
--
-- Np Z=93 **occupancy-engine sort exception continuum** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction;
--     **product** not XOR, no parallel occupancy axiom)
--   * XOR mutually-exclusive refuse; Np exception continuum witness concurrent
--     (occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction)
--   * **Np exception continuum** laws Unwired (npExceptionContinuumProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/elements/z_093_np.rs
-- L0 sort: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs
-- Mirrors sibling `ChemConstants/CuExceptionContinuum.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel occupancy axiom; homolog not copy. Product not XOR.
-- Np Z=93 DBlock occupancy-engine sort exception, not 26th axiom.
------------------------------------------------------------------------
module ChemConstants.NpExceptionContinuum where


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
-- Modality + Np Z=93 **occupancy-engine sort exception continuum** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data NpExceptionContinuumModality : Set where
  np-exception-continuum-unwired np-exception-continuum-assumed
    np-exception-continuum-proved np-exception-continuum-surrogate
    : NpExceptionContinuumModality

npExceptionContinuumModalityCurrent : NpExceptionContinuumModality
npExceptionContinuumModalityCurrent = np-exception-continuum-unwired

npExceptionContinuumProved productionWired not118SquaredGreenTable
  npExceptionContinuumSecondLawConservationFramed npExceptionContinuumNotXor : Bool
npExceptionContinuumProved = false
productionWired = false
not118SquaredGreenTable = true
npExceptionContinuumSecondLawConservationFramed = true
npExceptionContinuumNotXor = true

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
-- Np Z=93 occupancy-engine sort index pin
------------------------------------------------------------------------

npZ93OccupancyEngineSortIndex : ℕ
npZ93OccupancyEngineSortIndex = 93

np-z93-occupancy-engine-sort-index : npZ93OccupancyEngineSortIndex ≡ 93
np-z93-occupancy-engine-sort-index = refl

------------------------------------------------------------------------
-- Named element Z pins — Np (Z=93), U (Z=92 homolog)
------------------------------------------------------------------------

data ElementTag : Set where
  neptunium uranium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ neptunium = 93
elementAtomicZ uranium = 92

neptunium-z-93 : elementAtomicZ neptunium ≡ 93
neptunium-z-93 = refl

uranium-z-92 : elementAtomicZ uranium ≡ 92
uranium-z-92 = refl

------------------------------------------------------------------------
-- NpExceptionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data NpExceptionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : NpExceptionBundleSlot

isSlotPresent : NpExceptionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- NpExceptionBundle_118 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record NpExceptionBundle : Set where
  field slot : ℕ → NpExceptionBundleSlot

npExceptionBundleUnwired : NpExceptionBundle
npExceptionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : NpExceptionBundle → ℕ → NpExceptionBundleSlot → NpExceptionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else NpExceptionBundle.slot b j }

withPresent : NpExceptionBundle → ℕ → NpExceptionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record NpExceptionBundleWitness : Set where
  constructor mkNpExceptionBundleWitness
  field
    bundle : NpExceptionBundle
    present-count : ℕ

npExceptionBundleIsConcurrentProduct : NpExceptionBundleWitness → Bool
npExceptionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? NpExceptionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named Np exception continuum channel indices — occupancy-engine sort DBlock (1), Madelung exception theorem (2), continuum Env restriction (3)
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
-- Np exception continuum witness — occupancy-engine sort DBlock + Madelung exception theorem + continuum Env restriction concurrent
------------------------------------------------------------------------

npExceptionContinuumWitnessBundle : NpExceptionBundle
npExceptionContinuumWitnessBundle =
  withPresent
    (withPresent
      (withPresent npExceptionBundleUnwired occupancyEngineSortDBlockChannelIndex)
      madelungExceptionTheoremChannelIndex)
    continuumEnvRestrictionChannelIndex

npExceptionContinuumWitness : NpExceptionBundleWitness
npExceptionContinuumWitness =
  mkNpExceptionBundleWitness npExceptionContinuumWitnessBundle 3

np-exception-occupancy-engine-sort-dblock-present :
  isSlotPresent (NpExceptionBundle.slot npExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
np-exception-occupancy-engine-sort-dblock-present = refl

np-exception-madelung-exception-theorem-present :
  isSlotPresent (NpExceptionBundle.slot npExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
np-exception-madelung-exception-theorem-present = refl

np-exception-continuum-env-restriction-present :
  isSlotPresent (NpExceptionBundle.slot npExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
np-exception-continuum-env-restriction-present = refl

np-exception-present-count : NpExceptionBundleWitness.present-count npExceptionContinuumWitness ≡ 3
np-exception-present-count = refl

np-exception-concurrent-product :
  npExceptionBundleIsConcurrentProduct npExceptionContinuumWitness ≡ true
np-exception-concurrent-product = refl

np-exception-three-factors-concurrent :
  isSlotPresent (NpExceptionBundle.slot npExceptionContinuumWitnessBundle occupancyEngineSortDBlockChannelIndex) ≡ true
  × isSlotPresent (NpExceptionBundle.slot npExceptionContinuumWitnessBundle madelungExceptionTheoremChannelIndex) ≡ true
  × isSlotPresent (NpExceptionBundle.slot npExceptionContinuumWitnessBundle continuumEnvRestrictionChannelIndex) ≡ true
  × NpExceptionBundleWitness.present-count npExceptionContinuumWitness ≡ 3
np-exception-three-factors-concurrent =
  np-exception-occupancy-engine-sort-dblock-present
  , np-exception-madelung-exception-theorem-present
  , np-exception-continuum-env-restriction-present
  , np-exception-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : NpExceptionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if npExceptionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = NpExceptionBundleWitness.bundle w
       in if isSlotPresent (NpExceptionBundle.slot b i)
          then if isSlotPresent (NpExceptionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : NpExceptionBundleWitness
unwiredWitness = mkNpExceptionBundleWitness npExceptionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

np-exception-xor-product-ok :
  evaluateXorRefuse npExceptionContinuumWitness occupancyEngineSortDBlockChannelIndex madelungExceptionTheoremChannelIndex ≡ xor-product-ok
np-exception-xor-product-ok = refl

np-exception-not-xor : npExceptionContinuumNotXor ≡ true
np-exception-not-xor = refl

------------------------------------------------------------------------
-- ClassifierNpExceptionStep scaffold — NpExceptionBundle **conservation**
------------------------------------------------------------------------

data ClassifierNpExceptionStep : Set where
  np-exception-identity : ClassifierNpExceptionStep
  slot-leaf : ℕ → ClassifierNpExceptionStep
  product-concurrent : ClassifierNpExceptionStep → ClassifierNpExceptionStep → ClassifierNpExceptionStep
  xor-mutually-exclusive : ClassifierNpExceptionStep → ClassifierNpExceptionStep → ClassifierNpExceptionStep

npExceptionIdentity : ClassifierNpExceptionStep
npExceptionIdentity = np-exception-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierNpExceptionStep → ClassifierNpExceptionStep → ClassifierNpExceptionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf : ClassifierNpExceptionStep
occupancyEngineSortDBlockLeaf = slot-leaf occupancyEngineSortDBlockChannelIndex
madelungExceptionTheoremLeaf = slot-leaf madelungExceptionTheoremChannelIndex
continuumEnvRestrictionLeaf = slot-leaf continuumEnvRestrictionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierNpExceptionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isNpExceptionIdentity : ClassifierNpExceptionStep → Bool
isNpExceptionIdentity np-exception-identity = true
isNpExceptionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at np-exception-identity
------------------------------------------------------------------------

np-exception-left-identity :
  ∀ (a : ClassifierNpExceptionStep) →
  isNpExceptionIdentity npExceptionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp npExceptionIdentity a) ≡ true
np-exception-left-identity a = refl , refl

np-exception-right-identity :
  ∀ (a : ClassifierNpExceptionStep) →
  isProductConcurrent (productConcurrentOp a npExceptionIdentity) ≡ true
  × isNpExceptionIdentity npExceptionIdentity ≡ true
np-exception-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-np-exception :
  (∀ a → isProductConcurrent (productConcurrentOp npExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a npExceptionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-np-exception =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named Np exception continuum **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedNpExceptionContinuumProduct : ClassifierNpExceptionStep
namedNpExceptionContinuumProduct =
  productConcurrentOp
    (productConcurrentOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    continuumEnvRestrictionLeaf

named-np-exception-continuum-product-concurrent :
  isProductConcurrent namedNpExceptionContinuumProduct ≡ true
  × npExceptionBundleIsConcurrentProduct npExceptionContinuumWitness ≡ true
named-np-exception-continuum-product-concurrent = refl , np-exception-concurrent-product

------------------------------------------------------------------------
-- NpExceptionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data NpExceptionAdmissibility : Set where
  np-exception-admissible np-exception-xor-refuse : NpExceptionAdmissibility

isNpExceptionPreserving : ClassifierNpExceptionStep → Bool
isNpExceptionPreserving np-exception-identity = true
isNpExceptionPreserving (slot-leaf _) = true
isNpExceptionPreserving (product-concurrent a b) =
  isNpExceptionPreserving a ∧ isNpExceptionPreserving b
isNpExceptionPreserving (xor-mutually-exclusive _ _) = false

isNpExceptionAdmissible : ClassifierNpExceptionStep → Bool
isNpExceptionAdmissible step = isNpExceptionPreserving step

occupancy-engine-sort-dblock-leaf-admissible : isNpExceptionAdmissible occupancyEngineSortDBlockLeaf ≡ true
occupancy-engine-sort-dblock-leaf-admissible = refl

madelung-exception-theorem-leaf-admissible : isNpExceptionAdmissible madelungExceptionTheoremLeaf ≡ true
madelung-exception-theorem-leaf-admissible = refl

continuum-env-restriction-leaf-admissible : isNpExceptionAdmissible continuumEnvRestrictionLeaf ≡ true
continuum-env-restriction-leaf-admissible = refl

named-np-exception-continuum-admissible : isNpExceptionAdmissible namedNpExceptionContinuumProduct ≡ true
named-np-exception-continuum-admissible = refl

xor-mutually-exclusive-refuse :
  isNpExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-env-refuse :
  isNpExceptionAdmissible (xorMutuallyExclusiveOp madelungExceptionTheoremLeaf continuumEnvRestrictionLeaf) ≡ false
xor-mutually-exclusive-continuum-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data NpExceptionWitnessPresence : Set where
  np-exception-witness-absent np-exception-witness-present : NpExceptionWitnessPresence

record ClassifierNpExceptionWitness : Set where
  constructor mkClassifierNpExceptionWitness
  field
    witness-presence : NpExceptionWitnessPresence
    np-exception-gap-total : ℕ

npExceptionWitnessAbsent : ClassifierNpExceptionWitness
npExceptionWitnessAbsent = mkClassifierNpExceptionWitness np-exception-witness-absent zero

npExceptionWitnessPresentZeroGap : ClassifierNpExceptionWitness
npExceptionWitnessPresentZeroGap = mkClassifierNpExceptionWitness np-exception-witness-present zero

npExceptionWitnessPresentWithGaps : ℕ → ClassifierNpExceptionWitness
npExceptionWitnessPresentWithGaps n = mkClassifierNpExceptionWitness np-exception-witness-present n

npExceptionWitnessGapFree : ClassifierNpExceptionWitness → Bool
npExceptionWitnessGapFree (mkClassifierNpExceptionWitness np-exception-witness-absent _) = false
npExceptionWitnessGapFree (mkClassifierNpExceptionWitness np-exception-witness-present n) =
  does (n ℕ-Props.≟ zero)

np-exception-witness-present-zero-gap-free :
  npExceptionWitnessGapFree npExceptionWitnessPresentZeroGap ≡ true
np-exception-witness-present-zero-gap-free = refl

np-exception-witness-absent-not-gap-free :
  npExceptionWitnessGapFree npExceptionWitnessAbsent ≡ false
np-exception-witness-absent-not-gap-free = refl

np-exception-witness-with-gaps-not-gap-free :
  ∀ n → npExceptionWitnessGapFree (npExceptionWitnessPresentWithGaps (suc n)) ≡ false
np-exception-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-NpException **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data NpExceptionContinuumVerdict : Set where
  verdict-unwired-ok verdict-np-exception-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : NpExceptionContinuumVerdict

npExceptionContinuumVerdictOk : NpExceptionContinuumVerdict → Bool
npExceptionContinuumVerdictOk verdict-unwired-ok = true
npExceptionContinuumVerdictOk verdict-np-exception-admissible-ok = true
npExceptionContinuumVerdictOk verdict-concurrent-product-ok = true
npExceptionContinuumVerdictOk _ = false

evaluateNpExceptionContinuumClose :
  NpExceptionContinuumModality → ClassifierNpExceptionStep → ClassifierNpExceptionWitness
  → NpExceptionBundleWitness → Bool → NpExceptionContinuumVerdict
evaluateNpExceptionContinuumClose _ _ _ _ true = verdict-green-invent-refuse
evaluateNpExceptionContinuumClose np-exception-continuum-unwired _ _ _ false = verdict-unwired-ok
evaluateNpExceptionContinuumClose np-exception-continuum-assumed _ _ _ false = verdict-unwired-ok
evaluateNpExceptionContinuumClose np-exception-continuum-surrogate _ _ _ false = verdict-unwired-ok
evaluateNpExceptionContinuumClose np-exception-continuum-proved _ (mkClassifierNpExceptionWitness np-exception-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateNpExceptionContinuumClose np-exception-continuum-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateNpExceptionContinuumClose np-exception-continuum-proved _ (mkClassifierNpExceptionWitness np-exception-witness-present _) w false
  with npExceptionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-np-exception-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateNpExceptionContinuumClose
    np-exception-continuum-unwired namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateNpExceptionContinuumClose
    np-exception-continuum-assumed namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateNpExceptionContinuumClose
    np-exception-continuum-surrogate namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  npExceptionContinuumVerdictOk
    (evaluateNpExceptionContinuumClose np-exception-continuum-unwired namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false)
    ≡ true
  × npExceptionContinuumVerdictOk
      (evaluateNpExceptionContinuumClose np-exception-continuum-assumed namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false)
      ≡ true
  × npExceptionContinuumVerdictOk
      (evaluateNpExceptionContinuumClose np-exception-continuum-surrogate namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateNpExceptionContinuumClose
    np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  npExceptionContinuumVerdictOk
    (evaluateNpExceptionContinuumClose
       np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

NpTotalClaimWhenWitnessAbsent : Set
NpTotalClaimWhenWitnessAbsent =
  evaluateNpExceptionContinuumClose
    np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false ≡
  verdict-np-exception-admissible-ok

total-claim-⊥-when-witness-absent : NpTotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateNpExceptionContinuumClose
    np-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    npExceptionWitnessPresentZeroGap npExceptionContinuumWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  npExceptionContinuumVerdictOk
    (evaluateNpExceptionContinuumClose
       np-exception-continuum-proved
       (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
       npExceptionWitnessPresentZeroGap npExceptionContinuumWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

NpXorMutuallyExclusiveWhenConcurrent : Set
NpXorMutuallyExclusiveWhenConcurrent =
  evaluateNpExceptionContinuumClose
    np-exception-continuum-proved
    (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf)
    npExceptionWitnessPresentZeroGap npExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : NpXorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

np-exception-admissible-ok :
  evaluateNpExceptionContinuumClose
    np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-np-exception-admissible-ok
np-exception-admissible-ok = refl

np-exception-admissible-verdict-ok :
  npExceptionContinuumVerdictOk
    (evaluateNpExceptionContinuumClose
       np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
np-exception-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateNpExceptionContinuumClose
    np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap npExceptionContinuumWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  npExceptionContinuumVerdictOk
    (evaluateNpExceptionContinuumClose
       np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap npExceptionContinuumWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-np-exception-proved :
  npExceptionContinuumVerdictOk
    (evaluateNpExceptionContinuumClose
       np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap npExceptionContinuumWitness false)
    ≡ true
  × npExceptionContinuumProved ≡ false
concurrent-product-ok-still-not-np-exception-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateNpExceptionContinuumClose
    np-exception-continuum-unwired namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap npExceptionContinuumWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  npExceptionContinuumVerdictOk
    (evaluateNpExceptionContinuumClose
       np-exception-continuum-unwired namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap npExceptionContinuumWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

npExceptionContinuumFiberOk : FormalFiber → Bool
npExceptionContinuumFiberOk fiber-quantum-knowing = true
npExceptionContinuumFiberOk fiber-meso-acting = false

np-exception-continuum-knowing-fiber-ok :
  npExceptionContinuumFiberOk fiber-quantum-knowing ≡ true
np-exception-continuum-knowing-fiber-ok = refl

np-exception-continuum-meso-acting-not-ok :
  npExceptionContinuumFiberOk fiber-meso-acting ≡ false
np-exception-continuum-meso-acting-not-ok = refl

np-exception-continuum-routes-knowing-not-meso :
  npExceptionContinuumFiberOk fiber-quantum-knowing ≡ true ×
  npExceptionContinuumFiberOk fiber-meso-acting ≡ false
np-exception-continuum-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  npExceptionContinuumFiberOk fiber-quantum-knowing ∧
  not (npExceptionContinuumFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Np exception continuum Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

np-exception-continuum-not-proved : npExceptionContinuumProved ≡ false
np-exception-continuum-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

np-exception-continuum-second-law-conservation-framed : npExceptionContinuumSecondLawConservationFramed ≡ true
np-exception-continuum-second-law-conservation-framed = refl

np-exception-not-xor-pin : npExceptionContinuumNotXor ≡ true
np-exception-not-xor-pin = np-exception-not-xor

occupancy-engine-sort-typed-pin : occupancyEngineSortTyped ≡ true
occupancy-engine-sort-typed-pin = refl

not-parallel-occupancy-axiom-minted-pin : notParallelOccupancyAxiomMinted ≡ true
not-parallel-occupancy-axiom-minted-pin = refl

homolog-not-copy-not-forked-pin : homologNotCopyNotForked ≡ true
homolog-not-copy-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel occupancy axiom fork)
------------------------------------------------------------------------

npExceptionContinuumAxiom :
  (npExceptionContinuumProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (npExceptionContinuumSecondLawConservationFramed ≡ true)
  × (npExceptionContinuumNotXor ≡ true)
  × (evaluateNpExceptionContinuumClose np-exception-continuum-unwired namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false ≡ verdict-unwired-ok)
  × (evaluateNpExceptionContinuumClose np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessAbsent npExceptionContinuumWitness false ≡ verdict-total-claim-refuse)
  × (evaluateNpExceptionContinuumClose np-exception-continuum-proved (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) npExceptionWitnessPresentZeroGap npExceptionContinuumWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateNpExceptionContinuumClose np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap unwiredWitness false ≡ verdict-np-exception-admissible-ok)
  × (evaluateNpExceptionContinuumClose np-exception-continuum-proved namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap npExceptionContinuumWitness false ≡ verdict-concurrent-product-ok)
  × (npExceptionContinuumFiberOk fiber-quantum-knowing ≡ true)
  × (npExceptionContinuumFiberOk fiber-meso-acting ≡ false)
  × (npExceptionContinuumVerdictOk (evaluateNpExceptionContinuumClose np-exception-continuum-unwired namedNpExceptionContinuumProduct npExceptionWitnessPresentZeroGap npExceptionContinuumWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp npExceptionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a npExceptionIdentity) ≡ true)
  × (isNpExceptionAdmissible (xorMutuallyExclusiveOp occupancyEngineSortDBlockLeaf madelungExceptionTheoremLeaf) ≡ false)
  × (iupacTableCardinality ≡ 118)
  × (npZ93OccupancyEngineSortIndex ≡ 93)
  × (NpExceptionBundleWitness.present-count npExceptionContinuumWitness ≡ 3)
  × (elementAtomicZ neptunium ≡ 93)
  × (elementAtomicZ uranium ≡ 92)
npExceptionContinuumAxiom =
  np-exception-continuum-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , np-exception-continuum-second-law-conservation-framed
  , np-exception-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , np-exception-admissible-ok
  , concurrent-product-ok
  , np-exception-continuum-knowing-fiber-ok
  , np-exception-continuum-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , iupac-table-cardinality-one-eighteen
  , np-z93-occupancy-engine-sort-index
  , np-exception-present-count
  , neptunium-z-93
  , uranium-z-92

npExceptionContinuumNamed : String
npExceptionContinuumNamed =
  "npExceptionContinuum: Np Z=93 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction concurrent product identity conserved present ge 2 product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy"

npExceptionContinuumAuthority : String
npExceptionContinuumAuthority =
  "umst/umst-chem/src/elements/z_093_np.rs"

occupancyEngineSortAuthority : String
occupancyEngineSortAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"

homologExceptionNotCopyAuthority : String
homologExceptionNotCopyAuthority =
  "umst/umst-chem/src/homolog_exception_not_copy.rs"

nuanceAlongEnvContinuumAuthority : String
nuanceAlongEnvContinuumAuthority =
  "umst/umst-chem/src/nuance_along_environment_continuum.rs"

npExceptionContinuumCellId : String
npExceptionContinuumCellId = "CHEM-FORMAL-Q-AGDA-NP-EXCEPTION-CONTINUUM"

npExceptionContinuumNonClaim : String
npExceptionContinuumNonClaim =
  "CHEM-FORMAL-Q-AGDA-NP-EXCEPTION-CONTINUUM Np Z=93 occupancy-engine sort exception continuum concurrent Pi_c identity conserved occupancy-engine sort DBlock Madelung exception theorem continuum Env restriction product not XOR occupancy engine sort typed no parallel occupancy axiom homolog not copy XOR mutually exclusive refuse Np exception continuum witness concurrent npExceptionContinuumProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite z_093_np.rs occupancy_engine_sort not fork not physics GREEN not production_wired"

np-exception-continuum-cell-id :
  npExceptionContinuumCellId ≡ "CHEM-FORMAL-Q-AGDA-NP-EXCEPTION-CONTINUUM"
np-exception-continuum-cell-id = refl

np-exception-continuum-cites-z093-np-rs :
  npExceptionContinuumAuthority ≡
  "umst/umst-chem/src/elements/z_093_np.rs"
np-exception-continuum-cites-z093-np-rs = refl

np-exception-continuum-cites-occupancy-engine-sort-rs :
  occupancyEngineSortAuthority ≡
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs"
np-exception-continuum-cites-occupancy-engine-sort-rs = refl

np-exception-continuum-modality-unwired :
  npExceptionContinuumModalityCurrent ≡ np-exception-continuum-unwired
np-exception-continuum-modality-unwired = refl

npExceptionContinuumPhysicsGreenAuthorized : Set
npExceptionContinuumPhysicsGreenAuthorized = ⊥

np-exception-continuum-physics-green-false : ¬ npExceptionContinuumPhysicsGreenAuthorized
np-exception-continuum-physics-green-false ()

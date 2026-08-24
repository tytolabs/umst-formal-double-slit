-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PurifyRefineLiveConservation.agda
--
-- CHEM-FORMAL-Q-AGDA-PURIFY-REFINE-LIVE-CONSERVATION
-- LIVE **purify-refine** adjunction cost **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (pureward cost + no free purification + LIVE purify-refine;
--     **product** not XOR, no parallel purify-refine-live axiom)
--   * XOR mutually-exclusive refuse; LIVE purify-refine nuance witness concurrent
--     (pureward cost + no free purification + LIVE purify-refine)
--   * LIVE purify-refine laws Unwired (purifyRefineLiveProved = false)
--
-- INT (read-only cite): umst/umst-chem/src/impure_pure_adjunction.rs
-- L0 table: umst/umst-chem/src/refine_process.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel purify-refine-live axiom; no free purification. Product not XOR.
-- LIVE purify-refine adjunction cost; pureward cost mandatory, not free purification.
------------------------------------------------------------------------
module ChemConstants.PurifyRefineLiveConservation where


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
-- Modality + LIVE **purify-refine** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PurifyRefineLiveConservationModality : Set where
  purify-refine-live-conservation-unwired purify-refine-live-conservation-assumed
    purify-refine-live-conservation-proved purify-refine-live-conservation-surrogate
    : PurifyRefineLiveConservationModality

purifyRefineLiveConservationModalityCurrent : PurifyRefineLiveConservationModality
purifyRefineLiveConservationModalityCurrent = purify-refine-live-conservation-unwired

purifyRefineLiveProved productionWired not118SquaredGreenTable
  purifyRefineLiveSecondLawConservationFramed purifyRefineLiveNotXor : Bool
purifyRefineLiveProved = false
productionWired = false
not118SquaredGreenTable = true
purifyRefineLiveSecondLawConservationFramed = true
purifyRefineLiveNotXor = true

purewardCostTyped notParallelPurifyRefineLiveAxiomMinted freePurificationNotForked : Bool
purewardCostTyped = true
notParallelPurifyRefineLiveAxiomMinted = true
freePurificationNotForked = true

------------------------------------------------------------------------
-- Pattern class cardinality 25 — Π_c structure, not 118²
------------------------------------------------------------------------

patternClassCardinality : ℕ
patternClassCardinality = 25

pattern-class-cardinality-twenty-five : patternClassCardinality ≡ 25
pattern-class-cardinality-twenty-five = refl

pattern-class-not-118-squared :
  does (patternClassCardinality ℕ-Props.≟ (118 * 118)) ≡ false
pattern-class-not-118-squared = refl

------------------------------------------------------------------------
-- Pattern class 9 LIVE purify-refine index pin
------------------------------------------------------------------------

purifyRefineLiveClassIndex : ℕ
purifyRefineLiveClassIndex = 9

purify-refine-live-class-index-nine : purifyRefineLiveClassIndex ≡ 9
purify-refine-live-class-index-nine = refl

------------------------------------------------------------------------
-- Named element Z pins — Fe (Z=26), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  iron oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ iron = 26
elementAtomicZ oganesson = 118

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- PurifyRefineLiveBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PurifyRefineLiveBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PurifyRefineLiveBundleSlot

isSlotPresent : PurifyRefineLiveBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- PurifyRefineLiveBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record PurifyRefineLiveBundle : Set where
  field slot : ℕ → PurifyRefineLiveBundleSlot

purifyRefineLiveBundleUnwired : PurifyRefineLiveBundle
purifyRefineLiveBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : PurifyRefineLiveBundle → ℕ → PurifyRefineLiveBundleSlot → PurifyRefineLiveBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else PurifyRefineLiveBundle.slot b j }

withPresent : PurifyRefineLiveBundle → ℕ → PurifyRefineLiveBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PurifyRefineLiveBundleWitness : Set where
  constructor mkPurifyRefineLiveBundleWitness
  field
    bundle : PurifyRefineLiveBundle
    present-count : ℕ

purifyRefineLiveBundleIsConcurrentProduct : PurifyRefineLiveBundleWitness → Bool
purifyRefineLiveBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PurifyRefineLiveBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named LIVE purify-refine channel indices — pureward cost (1), no free purification (2), LIVE purify-refine (3)
------------------------------------------------------------------------

purewardCostChannelIndex noFreePurificationChannelIndex livePurifyRefineChannelIndex : ℕ
purewardCostChannelIndex = 1
noFreePurificationChannelIndex = 2
livePurifyRefineChannelIndex = 3

pureward-cost-index-one : purewardCostChannelIndex ≡ 1
pureward-cost-index-one = refl

no-free-purification-index-two : noFreePurificationChannelIndex ≡ 2
no-free-purification-index-two = refl

live-purify-refine-index-three : livePurifyRefineChannelIndex ≡ 3
live-purify-refine-index-three = refl

------------------------------------------------------------------------
-- LIVE purify-refine nuance witness — pureward cost + no free purification + LIVE purify-refine concurrent
------------------------------------------------------------------------

purifyRefineLiveNuanceBundle : PurifyRefineLiveBundle
purifyRefineLiveNuanceBundle =
  withPresent
    (withPresent
      (withPresent purifyRefineLiveBundleUnwired purewardCostChannelIndex)
      noFreePurificationChannelIndex)
    livePurifyRefineChannelIndex

purifyRefineLiveNuanceWitness : PurifyRefineLiveBundleWitness
purifyRefineLiveNuanceWitness =
  mkPurifyRefineLiveBundleWitness purifyRefineLiveNuanceBundle 3

purify-refine-live-nuance-pureward-cost-present :
  isSlotPresent (PurifyRefineLiveBundle.slot purifyRefineLiveNuanceBundle purewardCostChannelIndex) ≡ true
purify-refine-live-nuance-pureward-cost-present = refl

purify-refine-live-nuance-no-free-purification-present :
  isSlotPresent (PurifyRefineLiveBundle.slot purifyRefineLiveNuanceBundle noFreePurificationChannelIndex) ≡ true
purify-refine-live-nuance-no-free-purification-present = refl

purify-refine-live-nuance-live-purify-refine-present :
  isSlotPresent (PurifyRefineLiveBundle.slot purifyRefineLiveNuanceBundle livePurifyRefineChannelIndex) ≡ true
purify-refine-live-nuance-live-purify-refine-present = refl

purify-refine-live-nuance-present-count : PurifyRefineLiveBundleWitness.present-count purifyRefineLiveNuanceWitness ≡ 3
purify-refine-live-nuance-present-count = refl

purify-refine-live-nuance-concurrent-product :
  purifyRefineLiveBundleIsConcurrentProduct purifyRefineLiveNuanceWitness ≡ true
purify-refine-live-nuance-concurrent-product = refl

purify-refine-live-nuance-three-factors-concurrent :
  isSlotPresent (PurifyRefineLiveBundle.slot purifyRefineLiveNuanceBundle purewardCostChannelIndex) ≡ true
  × isSlotPresent (PurifyRefineLiveBundle.slot purifyRefineLiveNuanceBundle noFreePurificationChannelIndex) ≡ true
  × isSlotPresent (PurifyRefineLiveBundle.slot purifyRefineLiveNuanceBundle livePurifyRefineChannelIndex) ≡ true
  × PurifyRefineLiveBundleWitness.present-count purifyRefineLiveNuanceWitness ≡ 3
purify-refine-live-nuance-three-factors-concurrent =
  purify-refine-live-nuance-pureward-cost-present
  , purify-refine-live-nuance-no-free-purification-present
  , purify-refine-live-nuance-live-purify-refine-present
  , purify-refine-live-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PurifyRefineLiveBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if purifyRefineLiveBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = PurifyRefineLiveBundleWitness.bundle w
       in if isSlotPresent (PurifyRefineLiveBundle.slot b i)
          then if isSlotPresent (PurifyRefineLiveBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PurifyRefineLiveBundleWitness
unwiredWitness = mkPurifyRefineLiveBundleWitness purifyRefineLiveBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

purify-refine-live-nuance-xor-product-ok :
  evaluateXorRefuse purifyRefineLiveNuanceWitness purewardCostChannelIndex noFreePurificationChannelIndex ≡ xor-product-ok
purify-refine-live-nuance-xor-product-ok = refl

purify-refine-live-not-xor : purifyRefineLiveNotXor ≡ true
purify-refine-live-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPurifyRefineLiveStep scaffold — PurifyRefineLiveBundle **conservation**
------------------------------------------------------------------------

data ClassifierPurifyRefineLiveStep : Set where
  purify-refine-live-identity : ClassifierPurifyRefineLiveStep
  slot-leaf : ℕ → ClassifierPurifyRefineLiveStep
  product-concurrent : ClassifierPurifyRefineLiveStep → ClassifierPurifyRefineLiveStep → ClassifierPurifyRefineLiveStep
  xor-mutually-exclusive : ClassifierPurifyRefineLiveStep → ClassifierPurifyRefineLiveStep → ClassifierPurifyRefineLiveStep

purifyRefineLiveIdentity : ClassifierPurifyRefineLiveStep
purifyRefineLiveIdentity = purify-refine-live-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPurifyRefineLiveStep → ClassifierPurifyRefineLiveStep → ClassifierPurifyRefineLiveStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

purewardCostLeaf noFreePurificationLeaf livePurifyRefineLeaf : ClassifierPurifyRefineLiveStep
purewardCostLeaf = slot-leaf purewardCostChannelIndex
noFreePurificationLeaf = slot-leaf noFreePurificationChannelIndex
livePurifyRefineLeaf = slot-leaf livePurifyRefineChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierPurifyRefineLiveStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isPurifyRefineLiveIdentity : ClassifierPurifyRefineLiveStep → Bool
isPurifyRefineLiveIdentity purify-refine-live-identity = true
isPurifyRefineLiveIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at purify-refine-live-identity
------------------------------------------------------------------------

purify-refine-live-left-identity :
  ∀ (a : ClassifierPurifyRefineLiveStep) →
  isPurifyRefineLiveIdentity purifyRefineLiveIdentity ≡ true
  × isProductConcurrent (productConcurrentOp purifyRefineLiveIdentity a) ≡ true
purify-refine-live-left-identity a = refl , refl

purify-refine-live-right-identity :
  ∀ (a : ClassifierPurifyRefineLiveStep) →
  isProductConcurrent (productConcurrentOp a purifyRefineLiveIdentity) ≡ true
  × isPurifyRefineLiveIdentity purifyRefineLiveIdentity ≡ true
purify-refine-live-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-purify-refine-live :
  (∀ a → isProductConcurrent (productConcurrentOp purifyRefineLiveIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a purifyRefineLiveIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-purify-refine-live =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named LIVE purify-refine nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedPurifyRefineLiveNuanceProduct : ClassifierPurifyRefineLiveStep
namedPurifyRefineLiveNuanceProduct =
  productConcurrentOp
    (productConcurrentOp purewardCostLeaf noFreePurificationLeaf)
    livePurifyRefineLeaf

named-purify-refine-live-nuance-product-concurrent :
  isProductConcurrent namedPurifyRefineLiveNuanceProduct ≡ true
  × purifyRefineLiveBundleIsConcurrentProduct purifyRefineLiveNuanceWitness ≡ true
named-purify-refine-live-nuance-product-concurrent = refl , purify-refine-live-nuance-concurrent-product

------------------------------------------------------------------------
-- PurifyRefineLiveBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data PurifyRefineLiveAdmissibility : Set where
  purify-refine-live-admissible purify-refine-live-xor-refuse : PurifyRefineLiveAdmissibility

isPurifyRefineLivePreserving : ClassifierPurifyRefineLiveStep → Bool
isPurifyRefineLivePreserving purify-refine-live-identity = true
isPurifyRefineLivePreserving (slot-leaf _) = true
isPurifyRefineLivePreserving (product-concurrent a b) =
  isPurifyRefineLivePreserving a ∧ isPurifyRefineLivePreserving b
isPurifyRefineLivePreserving (xor-mutually-exclusive _ _) = false

isPurifyRefineLiveAdmissible : ClassifierPurifyRefineLiveStep → Bool
isPurifyRefineLiveAdmissible step = isPurifyRefineLivePreserving step

pureward-cost-leaf-admissible : isPurifyRefineLiveAdmissible purewardCostLeaf ≡ true
pureward-cost-leaf-admissible = refl

no-free-purification-leaf-admissible : isPurifyRefineLiveAdmissible noFreePurificationLeaf ≡ true
no-free-purification-leaf-admissible = refl

live-purify-refine-leaf-admissible : isPurifyRefineLiveAdmissible livePurifyRefineLeaf ≡ true
live-purify-refine-leaf-admissible = refl

named-purify-refine-live-nuance-admissible : isPurifyRefineLiveAdmissible namedPurifyRefineLiveNuanceProduct ≡ true
named-purify-refine-live-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isPurifyRefineLiveAdmissible (xorMutuallyExclusiveOp purewardCostLeaf noFreePurificationLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-live-purify-refine-refuse :
  isPurifyRefineLiveAdmissible (xorMutuallyExclusiveOp noFreePurificationLeaf livePurifyRefineLeaf) ≡ false
xor-mutually-exclusive-live-purify-refine-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data PurifyRefineLiveWitnessPresence : Set where
  purify-refine-live-witness-absent purify-refine-live-witness-present : PurifyRefineLiveWitnessPresence

record ClassifierPurifyRefineLiveWitness : Set where
  constructor mkClassifierPurifyRefineLiveWitness
  field
    witness-presence : PurifyRefineLiveWitnessPresence
    purify-refine-live-gap-total : ℕ

purifyRefineLiveWitnessAbsent : ClassifierPurifyRefineLiveWitness
purifyRefineLiveWitnessAbsent = mkClassifierPurifyRefineLiveWitness purify-refine-live-witness-absent zero

purifyRefineLiveWitnessPresentZeroGap : ClassifierPurifyRefineLiveWitness
purifyRefineLiveWitnessPresentZeroGap = mkClassifierPurifyRefineLiveWitness purify-refine-live-witness-present zero

purifyRefineLiveWitnessPresentWithGaps : ℕ → ClassifierPurifyRefineLiveWitness
purifyRefineLiveWitnessPresentWithGaps n = mkClassifierPurifyRefineLiveWitness purify-refine-live-witness-present n

purifyRefineLiveWitnessGapFree : ClassifierPurifyRefineLiveWitness → Bool
purifyRefineLiveWitnessGapFree (mkClassifierPurifyRefineLiveWitness purify-refine-live-witness-absent _) = false
purifyRefineLiveWitnessGapFree (mkClassifierPurifyRefineLiveWitness purify-refine-live-witness-present n) =
  does (n ℕ-Props.≟ zero)

purify-refine-live-witness-present-zero-gap-free :
  purifyRefineLiveWitnessGapFree purifyRefineLiveWitnessPresentZeroGap ≡ true
purify-refine-live-witness-present-zero-gap-free = refl

purify-refine-live-witness-absent-not-gap-free :
  purifyRefineLiveWitnessGapFree purifyRefineLiveWitnessAbsent ≡ false
purify-refine-live-witness-absent-not-gap-free = refl

purify-refine-live-witness-with-gaps-not-gap-free :
  ∀ n → purifyRefineLiveWitnessGapFree (purifyRefineLiveWitnessPresentWithGaps (suc n)) ≡ false
purify-refine-live-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-PurifyRefineLive **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PurifyRefineLiveConservationVerdict : Set where
  verdict-unwired-ok verdict-purify-refine-live-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : PurifyRefineLiveConservationVerdict

purifyRefineLiveConservationVerdictOk : PurifyRefineLiveConservationVerdict → Bool
purifyRefineLiveConservationVerdictOk verdict-unwired-ok = true
purifyRefineLiveConservationVerdictOk verdict-purify-refine-live-admissible-ok = true
purifyRefineLiveConservationVerdictOk verdict-concurrent-product-ok = true
purifyRefineLiveConservationVerdictOk _ = false

evaluatePurifyRefineLiveConservationClose :
  PurifyRefineLiveConservationModality → ClassifierPurifyRefineLiveStep → ClassifierPurifyRefineLiveWitness
  → PurifyRefineLiveBundleWitness → Bool → PurifyRefineLiveConservationVerdict
evaluatePurifyRefineLiveConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-proved _ (mkClassifierPurifyRefineLiveWitness purify-refine-live-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-proved _ (mkClassifierPurifyRefineLiveWitness purify-refine-live-witness-present _) w false
  with purifyRefineLiveBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-purify-refine-live-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without purify-refine-live witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-unwired namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-assumed namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-surrogate namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  purifyRefineLiveConservationVerdictOk
    (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-unwired namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false)
    ≡ true
  × purifyRefineLiveConservationVerdictOk
      (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-assumed namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false)
      ≡ true
  × purifyRefineLiveConservationVerdictOk
      (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-surrogate namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without purify-refine-live witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  purifyRefineLiveConservationVerdictOk
    (evaluatePurifyRefineLiveConservationClose
       purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false ≡
  verdict-purify-refine-live-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-proved
    (xorMutuallyExclusiveOp purewardCostLeaf noFreePurificationLeaf)
    purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  purifyRefineLiveConservationVerdictOk
    (evaluatePurifyRefineLiveConservationClose
       purify-refine-live-conservation-proved
       (xorMutuallyExclusiveOp purewardCostLeaf noFreePurificationLeaf)
       purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-proved
    (xorMutuallyExclusiveOp purewardCostLeaf noFreePurificationLeaf)
    purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-purify-refine-live — nuance **product** closed
------------------------------------------------------------------------

purify-refine-live-admissible-ok :
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap unwiredWitness false ≡
  verdict-purify-refine-live-admissible-ok
purify-refine-live-admissible-ok = refl

purify-refine-live-admissible-verdict-ok :
  purifyRefineLiveConservationVerdictOk
    (evaluatePurifyRefineLiveConservationClose
       purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap unwiredWitness false)
    ≡ true
purify-refine-live-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — purify-refine-live nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  purifyRefineLiveConservationVerdictOk
    (evaluatePurifyRefineLiveConservationClose
       purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-purify-refine-live-proved :
  purifyRefineLiveConservationVerdictOk
    (evaluatePurifyRefineLiveConservationClose
       purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness false)
    ≡ true
  × purifyRefineLiveProved ≡ false
concurrent-product-ok-still-not-purify-refine-live-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePurifyRefineLiveConservationClose
    purify-refine-live-conservation-unwired namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  purifyRefineLiveConservationVerdictOk
    (evaluatePurifyRefineLiveConservationClose
       purify-refine-live-conservation-unwired namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

purifyRefineLiveConservationFiberOk : FormalFiber → Bool
purifyRefineLiveConservationFiberOk fiber-quantum-knowing = true
purifyRefineLiveConservationFiberOk fiber-meso-acting = false

purify-refine-live-conservation-knowing-fiber-ok :
  purifyRefineLiveConservationFiberOk fiber-quantum-knowing ≡ true
purify-refine-live-conservation-knowing-fiber-ok = refl

purify-refine-live-conservation-meso-acting-not-ok :
  purifyRefineLiveConservationFiberOk fiber-meso-acting ≡ false
purify-refine-live-conservation-meso-acting-not-ok = refl

purify-refine-live-conservation-routes-knowing-not-meso :
  purifyRefineLiveConservationFiberOk fiber-quantum-knowing ≡ true ×
  purifyRefineLiveConservationFiberOk fiber-meso-acting ≡ false
purify-refine-live-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  purifyRefineLiveConservationFiberOk fiber-quantum-knowing ∧
  not (purifyRefineLiveConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not LIVE purify-refine Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

purify-refine-live-not-proved : purifyRefineLiveProved ≡ false
purify-refine-live-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

purify-refine-live-second-law-conservation-framed : purifyRefineLiveSecondLawConservationFramed ≡ true
purify-refine-live-second-law-conservation-framed = refl

purify-refine-live-not-xor-pin : purifyRefineLiveNotXor ≡ true
purify-refine-live-not-xor-pin = purify-refine-live-not-xor

pureward-cost-typed-pin : purewardCostTyped ≡ true
pureward-cost-typed-pin = refl

not-parallel-purify-refine-live-axiom-minted-pin : notParallelPurifyRefineLiveAxiomMinted ≡ true
not-parallel-purify-refine-live-axiom-minted-pin = refl

free-purification-not-forked-pin : freePurificationNotForked ≡ true
free-purification-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel purify-refine-live axiom fork)
------------------------------------------------------------------------

purifyRefineLiveConservationAxiom :
  (purifyRefineLiveProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (purifyRefineLiveSecondLawConservationFramed ≡ true)
  × (purifyRefineLiveNotXor ≡ true)
  × (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-unwired namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessAbsent purifyRefineLiveNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-proved (xorMutuallyExclusiveOp purewardCostLeaf noFreePurificationLeaf) purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap unwiredWitness false ≡ verdict-purify-refine-live-admissible-ok)
  × (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-proved namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (purifyRefineLiveConservationFiberOk fiber-quantum-knowing ≡ true)
  × (purifyRefineLiveConservationFiberOk fiber-meso-acting ≡ false)
  × (purifyRefineLiveConservationVerdictOk (evaluatePurifyRefineLiveConservationClose purify-refine-live-conservation-unwired namedPurifyRefineLiveNuanceProduct purifyRefineLiveWitnessPresentZeroGap purifyRefineLiveNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp purifyRefineLiveIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a purifyRefineLiveIdentity) ≡ true)
  × (isPurifyRefineLiveAdmissible (xorMutuallyExclusiveOp purewardCostLeaf noFreePurificationLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (purifyRefineLiveClassIndex ≡ 9)
  × (PurifyRefineLiveBundleWitness.present-count purifyRefineLiveNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
purifyRefineLiveConservationAxiom =
  purify-refine-live-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , purify-refine-live-second-law-conservation-framed
  , purify-refine-live-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , purify-refine-live-admissible-ok
  , concurrent-product-ok
  , purify-refine-live-conservation-knowing-fiber-ok
  , purify-refine-live-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , purify-refine-live-class-index-nine
  , purify-refine-live-nuance-present-count
  , iron-z-26
  , oganesson-z-118

purifyRefineLiveConservationNamed : String
purifyRefineLiveConservationNamed =
  "purifyRefineLiveConservation: LIVE purify-refine adjunction cost conservation concurrent Pi_c identity conserved pureward cost no free purification LIVE purify-refine concurrent product identity conserved present ge 2 product not XOR pureward cost typed no parallel purify-refine-live axiom no free purification"

purifyRefineLiveConservationCrossWitnessAuthority : String
purifyRefineLiveConservationCrossWitnessAuthority =
  "umst/umst-chem/src/impure_pure_adjunction.rs"

refineProcessAuthority : String
refineProcessAuthority =
  "umst/umst-chem/src/refine_process.rs"

processingRefiningTableAuthority : String
processingRefiningTableAuthority =
  "umst/umst-chem/src/l0_tables/processing_refining.rs"

adjunctionCostLandauerAuthority : String
adjunctionCostLandauerAuthority =
  "umst/umst-chem/src/x_rows/adjunction_cost_landauer.rs"

purifyRefineLiveConservationCellId : String
purifyRefineLiveConservationCellId = "CHEM-FORMAL-Q-AGDA-PURIFY-REFINE-LIVE-CONSERVATION"

purifyRefineLiveConservationNonClaim : String
purifyRefineLiveConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-PURIFY-REFINE-LIVE-CONSERVATION LIVE purify-refine adjunction cost conservation concurrent Pi_c identity conserved pureward cost no free purification LIVE purify-refine product not XOR pureward cost typed no parallel purify-refine-live axiom no free purification XOR mutually exclusive refuse purify-refine-live nuance witness concurrent purifyRefineLiveProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite impure_pure_adjunction.rs refine_process not fork not physics GREEN not production_wired"

purify-refine-live-conservation-cell-id :
  purifyRefineLiveConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-PURIFY-REFINE-LIVE-CONSERVATION"
purify-refine-live-conservation-cell-id = refl

purify-refine-live-conservation-cites-impure-pure-adjunction-rs :
  purifyRefineLiveConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/impure_pure_adjunction.rs"
purify-refine-live-conservation-cites-impure-pure-adjunction-rs = refl

purify-refine-live-conservation-cites-refine-process-rs :
  refineProcessAuthority ≡
  "umst/umst-chem/src/refine_process.rs"
purify-refine-live-conservation-cites-refine-process-rs = refl

purify-refine-live-conservation-modality-unwired :
  purifyRefineLiveConservationModalityCurrent ≡ purify-refine-live-conservation-unwired
purify-refine-live-conservation-modality-unwired = refl

purifyRefineLiveConservationPhysicsGreenAuthorized : Set
purifyRefineLiveConservationPhysicsGreenAuthorized = ⊥

purify-refine-live-conservation-physics-green-false : ¬ purifyRefineLiveConservationPhysicsGreenAuthorized
purify-refine-live-conservation-physics-green-false ()

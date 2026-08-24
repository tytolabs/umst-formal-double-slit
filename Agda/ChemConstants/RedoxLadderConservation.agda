-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.RedoxLadderConservation.agda
--
-- Pattern class 17 **redox_ladder** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (redox interact ladder + Pourbaix ≠ corrosion rate +
--     class 17 redox_ladder; **product** not XOR, no parallel redox axiom)
--   * XOR mutually-exclusive refuse; redox-ladder nuance witness concurrent
--     (redox interact ladder + Pourbaix ≠ corrosion rate + class 17 redox_ladder)
--   * **redox_ladder** laws Unwired (redoxLadderConservationProved = false)
--   * Pourbaix G(pH,E) equilibrium ≠ corrosion rate kinetics remainder
--   * μ/T/P graph functions on Interact graph (v14) — not bare float pins
--
-- INT (read-only cite): umst/umst-chem/src/redox_interact_ladder.rs
-- L0 table: umst/umst-chem/src/l0_tables/redox_ladder.rs
-- Pourbaix≠rate: umst/umst-chem/src/cross_classifier/pourbaix_is_not_corrosion_rate.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel redox axiom; Pourbaix ≠ corrosion rate. Product not XOR.
-- Class 17 redox_ladder as Interact restriction, not parallel axiom.
------------------------------------------------------------------------
module ChemConstants.RedoxLadderConservation where

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
-- Modality + pattern class 17 **redox_ladder** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data RedoxLadderConservationModality : Set where
  redox-ladder-conservation-unwired redox-ladder-conservation-assumed
    redox-ladder-conservation-proved redox-ladder-conservation-surrogate
    : RedoxLadderConservationModality

redoxLadderConservationModalityCurrent : RedoxLadderConservationModality
redoxLadderConservationModalityCurrent = redox-ladder-conservation-unwired

redoxLadderConservationProved productionWired not118SquaredGreenTable
  redoxLadderSecondLawConservationFramed redoxLadderNotXor : Bool
redoxLadderConservationProved = false
productionWired = false
not118SquaredGreenTable = true
redoxLadderSecondLawConservationFramed = true
redoxLadderNotXor = true

pourbaixNeCorrosionRate notParallelRedoxAxiomMinted mtpGraphFunctionNotFloatPin : Bool
pourbaixNeCorrosionRate = true
notParallelRedoxAxiomMinted = true
mtpGraphFunctionNotFloatPin = true

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
-- Pattern class 17 redox_ladder index pin
------------------------------------------------------------------------

redoxLadderClassIndex : ℕ
redoxLadderClassIndex = 17

redox-ladder-class-index-seventeen : redoxLadderClassIndex ≡ 17
redox-ladder-class-index-seventeen = refl

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
-- RedoxLadderBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data RedoxLadderBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : RedoxLadderBundleSlot

isSlotPresent : RedoxLadderBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- RedoxLadderBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record RedoxLadderBundle : Set where
  field slot : ℕ → RedoxLadderBundleSlot

redoxLadderBundleUnwired : RedoxLadderBundle
redoxLadderBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : RedoxLadderBundle → ℕ → RedoxLadderBundleSlot → RedoxLadderBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else RedoxLadderBundle.slot b j }

withPresent : RedoxLadderBundle → ℕ → RedoxLadderBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record RedoxLadderBundleWitness : Set where
  constructor mkRedoxLadderBundleWitness
  field
    bundle : RedoxLadderBundle
    present-count : ℕ

redoxLadderBundleIsConcurrentProduct : RedoxLadderBundleWitness → Bool
redoxLadderBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? RedoxLadderBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named redox-ladder channel indices — redox interact ladder (1), Pourbaix ≠ corrosion rate (2), class 17 redox_ladder (3)
------------------------------------------------------------------------

redoxInteractLadderChannelIndex pourbaixNeCorrosionRateChannelIndex class17RedoxLadderChannelIndex : ℕ
redoxInteractLadderChannelIndex = 1
pourbaixNeCorrosionRateChannelIndex = 2
class17RedoxLadderChannelIndex = 3

redox-interact-ladder-index-one : redoxInteractLadderChannelIndex ≡ 1
redox-interact-ladder-index-one = refl

pourbaix-ne-corrosion-rate-index-two : pourbaixNeCorrosionRateChannelIndex ≡ 2
pourbaix-ne-corrosion-rate-index-two = refl

class17-redox-ladder-index-three : class17RedoxLadderChannelIndex ≡ 3
class17-redox-ladder-index-three = refl

------------------------------------------------------------------------
-- Redox-ladder nuance witness — redox interact ladder + Pourbaix ≠ corrosion rate + class 17 redox_ladder concurrent
------------------------------------------------------------------------

redoxLadderNuanceBundle : RedoxLadderBundle
redoxLadderNuanceBundle =
  withPresent
    (withPresent
      (withPresent redoxLadderBundleUnwired redoxInteractLadderChannelIndex)
      pourbaixNeCorrosionRateChannelIndex)
    class17RedoxLadderChannelIndex

redoxLadderNuanceWitness : RedoxLadderBundleWitness
redoxLadderNuanceWitness =
  mkRedoxLadderBundleWitness redoxLadderNuanceBundle 3

redox_ladder-nuance-interact-restriction-present :
  isSlotPresent (RedoxLadderBundle.slot redoxLadderNuanceBundle redoxInteractLadderChannelIndex) ≡ true
redox_ladder-nuance-interact-restriction-present = refl

redox_ladder-nuance-not-extra-force-present :
  isSlotPresent (RedoxLadderBundle.slot redoxLadderNuanceBundle pourbaixNeCorrosionRateChannelIndex) ≡ true
redox_ladder-nuance-not-extra-force-present = refl

redox_ladder-nuance-class17-redox_ladder-present :
  isSlotPresent (RedoxLadderBundle.slot redoxLadderNuanceBundle class17RedoxLadderChannelIndex) ≡ true
redox_ladder-nuance-class17-redox_ladder-present = refl

redox_ladder-nuance-present-count : RedoxLadderBundleWitness.present-count redoxLadderNuanceWitness ≡ 3
redox_ladder-nuance-present-count = refl

redox_ladder-nuance-concurrent-product :
  redoxLadderBundleIsConcurrentProduct redoxLadderNuanceWitness ≡ true
redox_ladder-nuance-concurrent-product = refl

redox_ladder-nuance-three-factors-concurrent :
  isSlotPresent (RedoxLadderBundle.slot redoxLadderNuanceBundle redoxInteractLadderChannelIndex) ≡ true
  × isSlotPresent (RedoxLadderBundle.slot redoxLadderNuanceBundle pourbaixNeCorrosionRateChannelIndex) ≡ true
  × isSlotPresent (RedoxLadderBundle.slot redoxLadderNuanceBundle class17RedoxLadderChannelIndex) ≡ true
  × RedoxLadderBundleWitness.present-count redoxLadderNuanceWitness ≡ 3
redox_ladder-nuance-three-factors-concurrent =
  redox_ladder-nuance-interact-restriction-present
  , redox_ladder-nuance-not-extra-force-present
  , redox_ladder-nuance-class17-redox_ladder-present
  , redox_ladder-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : RedoxLadderBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if redoxLadderBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = RedoxLadderBundleWitness.bundle w
       in if isSlotPresent (RedoxLadderBundle.slot b i)
          then if isSlotPresent (RedoxLadderBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : RedoxLadderBundleWitness
unwiredWitness = mkRedoxLadderBundleWitness redoxLadderBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

redox_ladder-nuance-xor-product-ok :
  evaluateXorRefuse redoxLadderNuanceWitness redoxInteractLadderChannelIndex pourbaixNeCorrosionRateChannelIndex ≡ xor-product-ok
redox_ladder-nuance-xor-product-ok = refl

redox-ladder-not-xor : redoxLadderNotXor ≡ true
redox-ladder-not-xor = refl

------------------------------------------------------------------------
-- ClassifierRedoxLadderStep scaffold — RedoxLadderBundle **conservation** — RedoxLadderBundle **conservation**
------------------------------------------------------------------------

data ClassifierRedoxLadderStep : Set where
  redox-ladder-identity : ClassifierRedoxLadderStep
  slot-leaf : ℕ → ClassifierRedoxLadderStep
  product-concurrent : ClassifierRedoxLadderStep → ClassifierRedoxLadderStep → ClassifierRedoxLadderStep
  xor-mutually-exclusive : ClassifierRedoxLadderStep → ClassifierRedoxLadderStep → ClassifierRedoxLadderStep

redoxLadderIdentity : ClassifierRedoxLadderStep
redoxLadderIdentity = redox-ladder-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierRedoxLadderStep → ClassifierRedoxLadderStep → ClassifierRedoxLadderStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

redoxInteractLadderLeaf pourbaixNeCorrosionRateLeaf class17RedoxLadderLeaf : ClassifierRedoxLadderStep
redoxInteractLadderLeaf = slot-leaf redoxInteractLadderChannelIndex
pourbaixNeCorrosionRateLeaf = slot-leaf pourbaixNeCorrosionRateChannelIndex
class17RedoxLadderLeaf = slot-leaf class17RedoxLadderChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierRedoxLadderStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isRedoxLadderIdentity : ClassifierRedoxLadderStep → Bool
isRedoxLadderIdentity redox-ladder-identity = true
isRedoxLadderIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at redox-ladder-identity
------------------------------------------------------------------------

redox-ladder-left-identity :
  ∀ (a : ClassifierRedoxLadderStep) →
  isRedoxLadderIdentity redoxLadderIdentity ≡ true
  × isProductConcurrent (productConcurrentOp redoxLadderIdentity a) ≡ true
redox-ladder-left-identity a = refl , refl

redox-ladder-right-identity :
  ∀ (a : ClassifierRedoxLadderStep) →
  isProductConcurrent (productConcurrentOp a redoxLadderIdentity) ≡ true
  × isRedoxLadderIdentity redoxLadderIdentity ≡ true
redox-ladder-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-redox-ladder :
  (∀ a → isProductConcurrent (productConcurrentOp redoxLadderIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a redoxLadderIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-redox-ladder =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named redox-ladder nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedRedoxLadderNuanceProduct : ClassifierRedoxLadderStep
namedRedoxLadderNuanceProduct =
  productConcurrentOp
    (productConcurrentOp redoxInteractLadderLeaf pourbaixNeCorrosionRateLeaf)
    class17RedoxLadderLeaf

named-redox-ladder-nuance-product-concurrent :
  isProductConcurrent namedRedoxLadderNuanceProduct ≡ true
  × redoxLadderBundleIsConcurrentProduct redoxLadderNuanceWitness ≡ true
named-redox-ladder-nuance-product-concurrent = refl , redox_ladder-nuance-concurrent-product

------------------------------------------------------------------------
-- RedoxLadderBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data RedoxLadderAdmissibility : Set where
  redox-ladder-admissible redox-ladder-xor-refuse : RedoxLadderAdmissibility

isRedoxLadderPreserving : ClassifierRedoxLadderStep → Bool
isRedoxLadderPreserving redox-ladder-identity = true
isRedoxLadderPreserving (slot-leaf _) = true
isRedoxLadderPreserving (product-concurrent a b) =
  isRedoxLadderPreserving a ∧ isRedoxLadderPreserving b
isRedoxLadderPreserving (xor-mutually-exclusive _ _) = false

isRedoxLadderAdmissible : ClassifierRedoxLadderStep → Bool
isRedoxLadderAdmissible step = isRedoxLadderPreserving step

redox-interact-ladder-leaf-admissible : isRedoxLadderAdmissible redoxInteractLadderLeaf ≡ true
redox-interact-ladder-leaf-admissible = refl

pourbaix-ne-corrosion-rate-leaf-admissible : isRedoxLadderAdmissible pourbaixNeCorrosionRateLeaf ≡ true
pourbaix-ne-corrosion-rate-leaf-admissible = refl

class17-redox-ladder-leaf-admissible : isRedoxLadderAdmissible class17RedoxLadderLeaf ≡ true
class17-redox-ladder-leaf-admissible = refl

named-redox-ladder-nuance-admissible : isRedoxLadderAdmissible namedRedoxLadderNuanceProduct ≡ true
named-redox-ladder-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isRedoxLadderAdmissible (xorMutuallyExclusiveOp redoxInteractLadderLeaf pourbaixNeCorrosionRateLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class17-redox-ladder-refuse :
  isRedoxLadderAdmissible (xorMutuallyExclusiveOp pourbaixNeCorrosionRateLeaf class17RedoxLadderLeaf) ≡ false
xor-mutually-exclusive-class17-redox-ladder-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data RedoxLadderWitnessPresence : Set where
  redox-ladder-witness-absent redox-ladder-witness-present : RedoxLadderWitnessPresence

record ClassifierRedoxLadderWitness : Set where
  constructor mkClassifierRedoxLadderWitness
  field
    witness-presence : RedoxLadderWitnessPresence
    redox_ladder-gap-total : ℕ

redoxLadderWitnessAbsent : ClassifierRedoxLadderWitness
redoxLadderWitnessAbsent = mkClassifierRedoxLadderWitness redox-ladder-witness-absent zero

redoxLadderWitnessPresentZeroGap : ClassifierRedoxLadderWitness
redoxLadderWitnessPresentZeroGap = mkClassifierRedoxLadderWitness redox-ladder-witness-present zero

redoxLadderWitnessPresentWithGaps : ℕ → ClassifierRedoxLadderWitness
redoxLadderWitnessPresentWithGaps n = mkClassifierRedoxLadderWitness redox-ladder-witness-present n

redoxLadderWitnessGapFree : ClassifierRedoxLadderWitness → Bool
redoxLadderWitnessGapFree (mkClassifierRedoxLadderWitness redox-ladder-witness-absent _) = false
redoxLadderWitnessGapFree (mkClassifierRedoxLadderWitness redox-ladder-witness-present n) =
  does (n ℕ-Props.≟ zero)

redox-ladder-witness-present-zero-gap-free :
  redoxLadderWitnessGapFree redoxLadderWitnessPresentZeroGap ≡ true
redox-ladder-witness-present-zero-gap-free = refl

redox-ladder-witness-absent-not-gap-free :
  redoxLadderWitnessGapFree redoxLadderWitnessAbsent ≡ false
redox-ladder-witness-absent-not-gap-free = refl

redox-ladder-witness-with-gaps-not-gap-free :
  ∀ n → redoxLadderWitnessGapFree (redoxLadderWitnessPresentWithGaps (suc n)) ≡ false
redox-ladder-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-redox-ladder **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data RedoxLadderConservationVerdict : Set where
  verdict-unwired-ok verdict-redox-ladder-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : RedoxLadderConservationVerdict

redoxLadderConservationVerdictOk : RedoxLadderConservationVerdict → Bool
redoxLadderConservationVerdictOk verdict-unwired-ok = true
redoxLadderConservationVerdictOk verdict-redox-ladder-admissible-ok = true
redoxLadderConservationVerdictOk verdict-concurrent-product-ok = true
redoxLadderConservationVerdictOk _ = false

evaluateRedoxLadderConservationClose :
  RedoxLadderConservationModality → ClassifierRedoxLadderStep → ClassifierRedoxLadderWitness
  → RedoxLadderBundleWitness → Bool → RedoxLadderConservationVerdict
evaluateRedoxLadderConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateRedoxLadderConservationClose redox-ladder-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateRedoxLadderConservationClose redox-ladder-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateRedoxLadderConservationClose redox-ladder-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateRedoxLadderConservationClose redox-ladder-conservation-proved _ (mkClassifierRedoxLadderWitness redox-ladder-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateRedoxLadderConservationClose redox-ladder-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateRedoxLadderConservationClose redox-ladder-conservation-proved _ (mkClassifierRedoxLadderWitness redox-ladder-witness-present _) w false
  with redoxLadderBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-redox-ladder-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without redox_ladder witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-unwired namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-assumed namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-surrogate namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  redoxLadderConservationVerdictOk
    (evaluateRedoxLadderConservationClose redox-ladder-conservation-unwired namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false)
    ≡ true
  × redoxLadderConservationVerdictOk
      (evaluateRedoxLadderConservationClose redox-ladder-conservation-assumed namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false)
      ≡ true
  × redoxLadderConservationVerdictOk
      (evaluateRedoxLadderConservationClose redox-ladder-conservation-surrogate namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without redox_ladder witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  redoxLadderConservationVerdictOk
    (evaluateRedoxLadderConservationClose
       redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false ≡
  verdict-redox-ladder-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-proved
    (xorMutuallyExclusiveOp redoxInteractLadderLeaf pourbaixNeCorrosionRateLeaf)
    redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  redoxLadderConservationVerdictOk
    (evaluateRedoxLadderConservationClose
       redox-ladder-conservation-proved
       (xorMutuallyExclusiveOp redoxInteractLadderLeaf pourbaixNeCorrosionRateLeaf)
       redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-proved
    (xorMutuallyExclusiveOp redoxInteractLadderLeaf pourbaixNeCorrosionRateLeaf)
    redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-redox-ladder — nuance **product** closed
------------------------------------------------------------------------

redox-ladder-admissible-ok :
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap unwiredWitness false ≡
  verdict-redox-ladder-admissible-ok
redox-ladder-admissible-ok = refl

redox-ladder-admissible-verdict-ok :
  redoxLadderConservationVerdictOk
    (evaluateRedoxLadderConservationClose
       redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap unwiredWitness false)
    ≡ true
redox-ladder-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — redox-ladder nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  redoxLadderConservationVerdictOk
    (evaluateRedoxLadderConservationClose
       redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-redox-ladder-conservation-proved :
  redoxLadderConservationVerdictOk
    (evaluateRedoxLadderConservationClose
       redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness false)
    ≡ true
  × redoxLadderConservationProved ≡ false
concurrent-product-ok-still-not-redox-ladder-conservation-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateRedoxLadderConservationClose
    redox-ladder-conservation-unwired namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  redoxLadderConservationVerdictOk
    (evaluateRedoxLadderConservationClose
       redox-ladder-conservation-unwired namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

redoxLadderConservationFiberOk : FormalFiber → Bool
redoxLadderConservationFiberOk fiber-quantum-knowing = true
redoxLadderConservationFiberOk fiber-meso-acting = false

redox-ladder-conservation-knowing-fiber-ok :
  redoxLadderConservationFiberOk fiber-quantum-knowing ≡ true
redox-ladder-conservation-knowing-fiber-ok = refl

redox-ladder-conservation-meso-acting-not-ok :
  redoxLadderConservationFiberOk fiber-meso-acting ≡ false
redox-ladder-conservation-meso-acting-not-ok = refl

redox-ladder-conservation-routes-knowing-not-meso :
  redoxLadderConservationFiberOk fiber-quantum-knowing ≡ true ×
  redoxLadderConservationFiberOk fiber-meso-acting ≡ false
redox-ladder-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  redoxLadderConservationFiberOk fiber-quantum-knowing ∧
  not (redoxLadderConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 17 redox_ladder Proved, not physics GREEN, **product** not XOR, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

redox-ladder-conservation-not-proved : redoxLadderConservationProved ≡ false
redox-ladder-conservation-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

redox-ladder-second-law-conservation-framed : redoxLadderSecondLawConservationFramed ≡ true
redox-ladder-second-law-conservation-framed = refl

redox-ladder-not-xor-pin : redoxLadderNotXor ≡ true
redox-ladder-not-xor-pin = redox-ladder-not-xor

pourbaix-ne-corrosion-rate-pin : pourbaixNeCorrosionRate ≡ true
pourbaix-ne-corrosion-rate-pin = refl

not-parallel-redox-axiom-minted-pin : notParallelRedoxAxiomMinted ≡ true
not-parallel-redox-axiom-minted-pin = refl

mtp-graph-function-not-float-pin : mtpGraphFunctionNotFloatPin ≡ true
mtp-graph-function-not-float-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel redox axiom fork)
------------------------------------------------------------------------

redoxLadderConservationAxiom :
  (redoxLadderConservationProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (redoxLadderSecondLawConservationFramed ≡ true)
  × (redoxLadderNotXor ≡ true)
  × (evaluateRedoxLadderConservationClose redox-ladder-conservation-unwired namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateRedoxLadderConservationClose redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessAbsent redoxLadderNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateRedoxLadderConservationClose redox-ladder-conservation-proved (xorMutuallyExclusiveOp redoxInteractLadderLeaf pourbaixNeCorrosionRateLeaf) redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateRedoxLadderConservationClose redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap unwiredWitness false ≡ verdict-redox-ladder-admissible-ok)
  × (evaluateRedoxLadderConservationClose redox-ladder-conservation-proved namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (redoxLadderConservationFiberOk fiber-quantum-knowing ≡ true)
  × (redoxLadderConservationFiberOk fiber-meso-acting ≡ false)
  × (redoxLadderConservationVerdictOk (evaluateRedoxLadderConservationClose redox-ladder-conservation-unwired namedRedoxLadderNuanceProduct redoxLadderWitnessPresentZeroGap redoxLadderNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp redoxLadderIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a redoxLadderIdentity) ≡ true)
  × (isRedoxLadderAdmissible (xorMutuallyExclusiveOp redoxInteractLadderLeaf pourbaixNeCorrosionRateLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (redoxLadderClassIndex ≡ 17)
  × (RedoxLadderBundleWitness.present-count redoxLadderNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
redoxLadderConservationAxiom =
  redox-ladder-conservation-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , redox-ladder-second-law-conservation-framed
  , redox-ladder-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , redox-ladder-admissible-ok
  , concurrent-product-ok
  , redox-ladder-conservation-knowing-fiber-ok
  , redox-ladder-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , redox-ladder-class-index-seventeen
  , redox_ladder-nuance-present-count
  , iron-z-26
  , oganesson-z-118

redoxLadderConservationNamed : String
redoxLadderConservationNamed =
  "redoxLadderConservation: pattern class 17 redox_ladder conservation concurrent Pi_c identity conserved redox interact ladder Pourbaix ne corrosion rate class 17 redox_ladder concurrent product identity conserved present ge 2 product not XOR Pourbaix ne corrosion rate no parallel redox axiom mu T P graph functions not float pins"

redoxLadderConservationCrossWitnessAuthority : String
redoxLadderConservationCrossWitnessAuthority =
  "umst/umst-chem/src/redox_interact_ladder.rs"

redoxLadderTableAuthority : String
redoxLadderTableAuthority =
  "umst/umst-chem/src/l0_tables/redox_ladder.rs"


chemicalPotentialGraphFunctionAuthority : String
chemicalPotentialGraphFunctionAuthority =
  "umst/umst-chem/src/chemical_potential_is_graph_function.rs"

pourbaixNotCorrosionRateAuthority : String
pourbaixNotCorrosionRateAuthority =
  "umst/umst-chem/src/cross_classifier/pourbaix_is_not_corrosion_rate.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

redoxLadderConservationCellId : String
redoxLadderConservationCellId = "CHEM-FORMAL-Q-AGDA-REDOX-LADDER-CONSERVATION"

redoxLadderConservationNonClaim : String
redoxLadderConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-REDOX-LADDER-CONSERVATION pattern class 17 redox_ladder conservation concurrent Pi_c identity conserved redox interact ladder Pourbaix ne corrosion rate class 17 redox_ladder product not XOR Pourbaix ne corrosion rate no parallel redox axiom mu T P graph functions not float pins XOR mutually exclusive refuse redox ladder nuance witness concurrent redoxLadderConservationProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite redox_interact_ladder.rs l0_tables redox_ladder not fork not physics GREEN not production_wired"

redox-ladder-conservation-cell-id :
  redoxLadderConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-REDOX-LADDER-CONSERVATION"
redox-ladder-conservation-cell-id = refl

redox-ladder-conservation-cites-redox_ladder-barrier-rs :
  redoxLadderConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/redox_interact_ladder.rs"
redox-ladder-conservation-cites-redox_ladder-barrier-rs = refl

redox-ladder-conservation-cites-l0-table-rs :
  redoxLadderTableAuthority ≡
  "umst/umst-chem/src/l0_tables/redox_ladder.rs"
redox-ladder-conservation-cites-l0-table-rs = refl

redox-ladder-conservation-modality-unwired :
  redoxLadderConservationModalityCurrent ≡ redox-ladder-conservation-unwired
redox-ladder-conservation-modality-unwired = refl

redoxLadderConservationPhysicsGreenAuthorized : Set
redoxLadderConservationPhysicsGreenAuthorized = ⊥

redox-ladder-conservation-physics-green-false : ¬ redoxLadderConservationPhysicsGreenAuthorized
redox-ladder-conservation-physics-green-false ()

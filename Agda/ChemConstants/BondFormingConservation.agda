-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.BondFormingConservation.agda
--
-- PATTERN-00 class 2 Bond-forming **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (cardinality 25; ≥2 Present is **product** not XOR)
--   * QTAIM BCP + Mayer/DDEC; forming arrow is Kleisli Interact Apply not Refine
--   * XOR mutually-exclusive refuse; H–O bond nuance witness concurrent
--     (bond-forming + QTAIM BCP + Interact Apply)
--   * **bond-forming** laws Unwired (bondFormingProved = false)
--
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- INT: umst/umst-chem/src/x_rows/bond_forming_conservation.rs (read-only cite)
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.BondFormingConservation where

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
-- Modality + class 2 Bond-forming **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data BondFormingConservationModality : Set where
  bond-forming-conservation-unwired bond-forming-conservation-assumed
    bond-forming-conservation-proved bond-forming-conservation-surrogate
    : BondFormingConservationModality

bondFormingConservationModalityCurrent : BondFormingConservationModality
bondFormingConservationModalityCurrent = bond-forming-conservation-unwired

bondFormingProved productionWired not118SquaredGreenTable
  bondSecondLawConservationFramed productNotXor interactNotRefine : Bool
bondFormingProved = false
productionWired = false
not118SquaredGreenTable = true
bondSecondLawConservationFramed = true
productNotXor = true
interactNotRefine = true

------------------------------------------------------------------------
-- PatternBundle class cardinality 25 — Π_c structure, not 118²
------------------------------------------------------------------------

patternClassCardinality : ℕ
patternClassCardinality = 25

pattern-class-cardinality-twenty-five : patternClassCardinality ≡ 25
pattern-class-cardinality-twenty-five = refl

pattern-class-not-118-squared :
  does (patternClassCardinality ℕ-Props.≟ (118 * 118)) ≡ false
pattern-class-not-118-squared = refl

------------------------------------------------------------------------
-- North-star §2 class 2 Bond-forming pattern index
------------------------------------------------------------------------

bondFormingClassIndex : ℕ
bondFormingClassIndex = 2

bond-forming-class-index-two : bondFormingClassIndex ≡ 2
bond-forming-class-index-two = refl

qtaimBcpFactorIndex interactApplyFactorIndex mayerDdecFactorIndex : ℕ
qtaimBcpFactorIndex = 18
interactApplyFactorIndex = 19
mayerDdecFactorIndex = 20

qtaim-bcp-index-eighteen : qtaimBcpFactorIndex ≡ 18
qtaim-bcp-index-eighteen = refl

interact-apply-index-nineteen : interactApplyFactorIndex ≡ 19
interact-apply-index-nineteen = refl

mayer-ddec-index-twenty : mayerDdecFactorIndex ≡ 20
mayer-ddec-index-twenty = refl

------------------------------------------------------------------------
-- Forming channel — Kleisli Interact Apply not Refine separation
------------------------------------------------------------------------

data FormingChannel : Set where
  interact-apply refine-separation : FormingChannel

isInteractApplyChannel isRefineSeparationChannel : FormingChannel → Bool
isInteractApplyChannel interact-apply = true
isInteractApplyChannel _ = false

isRefineSeparationChannel refine-separation = true
isRefineSeparationChannel _ = false

interact-not-refine-forming :
  isInteractApplyChannel interact-apply ≡ true ×
  isRefineSeparationChannel interact-apply ≡ false
interact-not-refine-forming = refl , refl

refine-not-forming-channel :
  isRefineSeparationChannel refine-separation ≡ true ×
  isInteractApplyChannel refine-separation ≡ false
refine-not-forming-channel = refl , refl

interact-distinct-from-refine : interact-apply ≢ refine-separation
interact-distinct-from-refine ()

interact-not-refine-pin : interactNotRefine ≡ true
interact-not-refine-pin = refl

qtaimBcpTag interactApplyTag mayerDdecTag : String
qtaimBcpTag = "QTAIM BCP"
interactApplyTag = "Kleisli Interact Apply"
mayerDdecTag = "Mayer/DDEC"

------------------------------------------------------------------------
-- Named element Z pins — H (Z=1), O (Z=8), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  hydrogen oxygen oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ hydrogen = 1
elementAtomicZ oxygen = 8
elementAtomicZ oganesson = 118

ho-bond-z-pins : elementAtomicZ hydrogen ≡ 1 × elementAtomicZ oxygen ≡ 8
ho-bond-z-pins = refl , refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- BondFormingBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data BondFormingBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : BondFormingBundleSlot

isSlotPresent : BondFormingBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- BondFormingBundle_25 — many classes may hold at once (Π_c **product**)
------------------------------------------------------------------------

record BondFormingBundle : Set where
  field slot : ℕ → BondFormingBundleSlot

bondFormingBundleUnwired : BondFormingBundle
bondFormingBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : BondFormingBundle → ℕ → BondFormingBundleSlot → BondFormingBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else BondFormingBundle.slot b j }

withPresent : BondFormingBundle → ℕ → BondFormingBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record BondFormingBundleWitness : Set where
  constructor mkBondFormingBundleWitness
  field
    bundle : BondFormingBundle
    present-count : ℕ

bondFormingBundleIsConcurrentProduct : BondFormingBundleWitness → Bool
bondFormingBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? BondFormingBundleWitness.present-count w)

------------------------------------------------------------------------
-- H–O bond nuance witness — bond-forming + QTAIM BCP + Interact Apply concurrent
------------------------------------------------------------------------

hoBondNuanceBundle : BondFormingBundle
hoBondNuanceBundle =
  withPresent
    (withPresent
      (withPresent bondFormingBundleUnwired bondFormingClassIndex)
      qtaimBcpFactorIndex)
    interactApplyFactorIndex

hoBondNuanceWitness : BondFormingBundleWitness
hoBondNuanceWitness =
  mkBondFormingBundleWitness hoBondNuanceBundle 3

ho-nuance-bond-forming-present :
  isSlotPresent (BondFormingBundle.slot hoBondNuanceBundle bondFormingClassIndex) ≡ true
ho-nuance-bond-forming-present = refl

ho-nuance-qtaim-bcp-present :
  isSlotPresent (BondFormingBundle.slot hoBondNuanceBundle qtaimBcpFactorIndex) ≡ true
ho-nuance-qtaim-bcp-present = refl

ho-nuance-interact-apply-present :
  isSlotPresent (BondFormingBundle.slot hoBondNuanceBundle interactApplyFactorIndex) ≡ true
ho-nuance-interact-apply-present = refl

ho-nuance-present-count : BondFormingBundleWitness.present-count hoBondNuanceWitness ≡ 3
ho-nuance-present-count = refl

ho-nuance-concurrent-product :
  bondFormingBundleIsConcurrentProduct hoBondNuanceWitness ≡ true
ho-nuance-concurrent-product = refl

ho-nuance-three-factors-concurrent :
  isSlotPresent (BondFormingBundle.slot hoBondNuanceBundle bondFormingClassIndex) ≡ true
  × isSlotPresent (BondFormingBundle.slot hoBondNuanceBundle qtaimBcpFactorIndex) ≡ true
  × isSlotPresent (BondFormingBundle.slot hoBondNuanceBundle interactApplyFactorIndex) ≡ true
  × BondFormingBundleWitness.present-count hoBondNuanceWitness ≡ 3
ho-nuance-three-factors-concurrent =
  ho-nuance-bond-forming-present
  , ho-nuance-qtaim-bcp-present
  , ho-nuance-interact-apply-present
  , ho-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : BondFormingBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if bondFormingBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = BondFormingBundleWitness.bundle w
       in if isSlotPresent (BondFormingBundle.slot b i)
          then if isSlotPresent (BondFormingBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : BondFormingBundleWitness
unwiredWitness = mkBondFormingBundleWitness bondFormingBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

ho-nuance-xor-product-ok :
  evaluateXorRefuse hoBondNuanceWitness bondFormingClassIndex qtaimBcpFactorIndex ≡ xor-product-ok
ho-nuance-xor-product-ok = refl

product-not-xor : productNotXor ≡ true
product-not-xor = refl

------------------------------------------------------------------------
-- ClassifierBondFormingStep scaffold — Bond-forming **conservation**
------------------------------------------------------------------------

data ClassifierBondFormingStep : Set where
  bond-forming-identity : ClassifierBondFormingStep
  slot-leaf : ℕ → ClassifierBondFormingStep
  product-concurrent : ClassifierBondFormingStep → ClassifierBondFormingStep → ClassifierBondFormingStep
  xor-mutually-exclusive : ClassifierBondFormingStep → ClassifierBondFormingStep → ClassifierBondFormingStep
  refine-separation-forming : ClassifierBondFormingStep → ClassifierBondFormingStep

bondFormingIdentity : ClassifierBondFormingStep
bondFormingIdentity = bond-forming-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierBondFormingStep → ClassifierBondFormingStep → ClassifierBondFormingStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

refineSeparationFormingOp : ClassifierBondFormingStep → ClassifierBondFormingStep
refineSeparationFormingOp = refine-separation-forming

bondFormingLeaf qtaimBcpLeaf interactApplyLeaf mayerDdecLeaf : ClassifierBondFormingStep
bondFormingLeaf = slot-leaf bondFormingClassIndex
qtaimBcpLeaf = slot-leaf qtaimBcpFactorIndex
interactApplyLeaf = slot-leaf interactApplyFactorIndex
mayerDdecLeaf = slot-leaf mayerDdecFactorIndex

isProductConcurrent isXorMutuallyExclusive isRefineSeparationForming : ClassifierBondFormingStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isRefineSeparationForming (refine-separation-forming _) = true
isRefineSeparationForming _ = false

isBondFormingIdentity : ClassifierBondFormingStep → Bool
isBondFormingIdentity bond-forming-identity = true
isBondFormingIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at bond-forming-identity
------------------------------------------------------------------------

bond-forming-left-identity :
  ∀ (a : ClassifierBondFormingStep) →
  isBondFormingIdentity bondFormingIdentity ≡ true
  × isProductConcurrent (productConcurrentOp bondFormingIdentity a) ≡ true
bond-forming-left-identity a = refl , refl

bond-forming-right-identity :
  ∀ (a : ClassifierBondFormingStep) →
  isProductConcurrent (productConcurrentOp a bondFormingIdentity) ≡ true
  × isBondFormingIdentity bondFormingIdentity ≡ true
bond-forming-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-bond-forming :
  (∀ a → isProductConcurrent (productConcurrentOp bondFormingIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a bondFormingIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-bond-forming =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named H–O bond nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedHoBondNuanceProduct : ClassifierBondFormingStep
namedHoBondNuanceProduct =
  productConcurrentOp
    (productConcurrentOp bondFormingLeaf qtaimBcpLeaf)
    interactApplyLeaf

named-ho-bond-nuance-product-concurrent :
  isProductConcurrent namedHoBondNuanceProduct ≡ true
  × bondFormingBundleIsConcurrentProduct hoBondNuanceWitness ≡ true
named-ho-bond-nuance-product-concurrent = refl , ho-nuance-concurrent-product

------------------------------------------------------------------------
-- Bond-forming admissibility — XOR refuse + Refine forming refuse fail-closed
------------------------------------------------------------------------

data BondFormingAdmissibility : Set where
  bond-forming-admissible bond-forming-xor-refuse bond-forming-refine-refuse : BondFormingAdmissibility

isBondFormingPreserving : ClassifierBondFormingStep → Bool
isBondFormingPreserving bond-forming-identity = true
isBondFormingPreserving (slot-leaf _) = true
isBondFormingPreserving (product-concurrent a b) =
  isBondFormingPreserving a ∧ isBondFormingPreserving b
isBondFormingPreserving (xor-mutually-exclusive _ _) = false
isBondFormingPreserving (refine-separation-forming _) = false

isBondFormingAdmissible : ClassifierBondFormingStep → Bool
isBondFormingAdmissible step = isBondFormingPreserving step

bond-forming-leaf-admissible : isBondFormingAdmissible bondFormingLeaf ≡ true
bond-forming-leaf-admissible = refl

qtaim-bcp-leaf-admissible : isBondFormingAdmissible qtaimBcpLeaf ≡ true
qtaim-bcp-leaf-admissible = refl

interact-apply-leaf-admissible : isBondFormingAdmissible interactApplyLeaf ≡ true
interact-apply-leaf-admissible = refl

named-ho-bond-nuance-admissible : isBondFormingAdmissible namedHoBondNuanceProduct ≡ true
named-ho-bond-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isBondFormingAdmissible (xorMutuallyExclusiveOp bondFormingLeaf qtaimBcpLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

refine-separation-forming-refuse :
  isBondFormingAdmissible (refineSeparationFormingOp interactApplyLeaf) ≡ false
refine-separation-forming-refuse = refl

interact-not-refine-admissible :
  isBondFormingAdmissible interactApplyLeaf ≡ true ×
  isBondFormingAdmissible (refineSeparationFormingOp bondFormingLeaf) ≡ false
interact-not-refine-admissible = interact-apply-leaf-admissible , refine-separation-forming-refuse

------------------------------------------------------------------------
-- Bond-forming witness — total-claim refuse without witness
------------------------------------------------------------------------

data BondFormingWitnessPresence : Set where
  bond-forming-witness-absent bond-forming-witness-present : BondFormingWitnessPresence

record ClassifierBondFormingWitness : Set where
  constructor mkClassifierBondFormingWitness
  field
    witness-presence : BondFormingWitnessPresence
    bond-forming-gap-total : ℕ

bondFormingWitnessAbsent : ClassifierBondFormingWitness
bondFormingWitnessAbsent = mkClassifierBondFormingWitness bond-forming-witness-absent zero

bondFormingWitnessPresentZeroGap : ClassifierBondFormingWitness
bondFormingWitnessPresentZeroGap = mkClassifierBondFormingWitness bond-forming-witness-present zero

bondFormingWitnessPresentWithGaps : ℕ → ClassifierBondFormingWitness
bondFormingWitnessPresentWithGaps n = mkClassifierBondFormingWitness bond-forming-witness-present n

bondFormingWitnessGapFree : ClassifierBondFormingWitness → Bool
bondFormingWitnessGapFree (mkClassifierBondFormingWitness bond-forming-witness-absent _) = false
bondFormingWitnessGapFree (mkClassifierBondFormingWitness bond-forming-witness-present n) =
  does (n ℕ-Props.≟ zero)

bond-forming-witness-present-zero-gap-free :
  bondFormingWitnessGapFree bondFormingWitnessPresentZeroGap ≡ true
bond-forming-witness-present-zero-gap-free = refl

bond-forming-witness-absent-not-gap-free :
  bondFormingWitnessGapFree bondFormingWitnessAbsent ≡ false
bond-forming-witness-absent-not-gap-free = refl

bond-forming-witness-with-gaps-not-gap-free :
  ∀ n → bondFormingWitnessGapFree (bondFormingWitnessPresentWithGaps (suc n)) ≡ false
bond-forming-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier class 2 Bond-forming **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data BondFormingConservationVerdict : Set where
  verdict-unwired-ok verdict-bond-forming-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-refine-separation-forming-refuse verdict-total-claim-refuse
    verdict-green-invent-refuse
    : BondFormingConservationVerdict

bondFormingConservationVerdictOk : BondFormingConservationVerdict → Bool
bondFormingConservationVerdictOk verdict-unwired-ok = true
bondFormingConservationVerdictOk verdict-bond-forming-admissible-ok = true
bondFormingConservationVerdictOk verdict-concurrent-product-ok = true
bondFormingConservationVerdictOk _ = false

evaluateBondFormingConservationClose :
  BondFormingConservationModality → ClassifierBondFormingStep → ClassifierBondFormingWitness
  → BondFormingBundleWitness → Bool → BondFormingConservationVerdict
evaluateBondFormingConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateBondFormingConservationClose bond-forming-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateBondFormingConservationClose bond-forming-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateBondFormingConservationClose bond-forming-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateBondFormingConservationClose bond-forming-conservation-proved _ (mkClassifierBondFormingWitness bond-forming-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateBondFormingConservationClose bond-forming-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateBondFormingConservationClose bond-forming-conservation-proved (refine-separation-forming _) _ _ false =
  verdict-refine-separation-forming-refuse
evaluateBondFormingConservationClose bond-forming-conservation-proved _ (mkClassifierBondFormingWitness bond-forming-witness-present _) w false
  with bondFormingBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-bond-forming-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without bond-forming witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateBondFormingConservationClose
    bond-forming-conservation-unwired namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateBondFormingConservationClose
    bond-forming-conservation-assumed namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateBondFormingConservationClose
    bond-forming-conservation-surrogate namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  bondFormingConservationVerdictOk
    (evaluateBondFormingConservationClose bond-forming-conservation-unwired namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false)
    ≡ true
  × bondFormingConservationVerdictOk
      (evaluateBondFormingConservationClose bond-forming-conservation-assumed namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false)
      ≡ true
  × bondFormingConservationVerdictOk
      (evaluateBondFormingConservationClose bond-forming-conservation-surrogate namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without bond-forming witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateBondFormingConservationClose
    bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  bondFormingConservationVerdictOk
    (evaluateBondFormingConservationClose
       bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateBondFormingConservationClose
    bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false ≡
  verdict-bond-forming-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateBondFormingConservationClose
    bond-forming-conservation-proved
    (xorMutuallyExclusiveOp bondFormingLeaf qtaimBcpLeaf)
    bondFormingWitnessPresentZeroGap hoBondNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  bondFormingConservationVerdictOk
    (evaluateBondFormingConservationClose
       bond-forming-conservation-proved
       (xorMutuallyExclusiveOp bondFormingLeaf qtaimBcpLeaf)
       bondFormingWitnessPresentZeroGap hoBondNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

------------------------------------------------------------------------
-- Refine separation forming refuse — Interact not Refine fail-closed
------------------------------------------------------------------------

refine-separation-forming-refuse-verdict :
  evaluateBondFormingConservationClose
    bond-forming-conservation-proved
    (refineSeparationFormingOp interactApplyLeaf)
    bondFormingWitnessPresentZeroGap hoBondNuanceWitness false ≡
  verdict-refine-separation-forming-refuse
refine-separation-forming-refuse-verdict = refl

refine-separation-forming-refuse-not-ok :
  bondFormingConservationVerdictOk
    (evaluateBondFormingConservationClose
       bond-forming-conservation-proved
       (refineSeparationFormingOp interactApplyLeaf)
       bondFormingWitnessPresentZeroGap hoBondNuanceWitness false)
    ≡ false
refine-separation-forming-refuse-not-ok = refl

------------------------------------------------------------------------
-- Admissible classifier — H–O bond nuance **product** closed
------------------------------------------------------------------------

bond-forming-admissible-ok :
  evaluateBondFormingConservationClose
    bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap unwiredWitness false ≡
  verdict-bond-forming-admissible-ok
bond-forming-admissible-ok = refl

bond-forming-admissible-verdict-ok :
  bondFormingConservationVerdictOk
    (evaluateBondFormingConservationClose
       bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap unwiredWitness false)
    ≡ true
bond-forming-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — H–O bond nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateBondFormingConservationClose
    bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap hoBondNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  bondFormingConservationVerdictOk
    (evaluateBondFormingConservationClose
       bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap hoBondNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-bond-forming-proved :
  bondFormingConservationVerdictOk
    (evaluateBondFormingConservationClose
       bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap hoBondNuanceWitness false)
    ≡ true
  × bondFormingProved ≡ false
concurrent-product-ok-still-not-bond-forming-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateBondFormingConservationClose
    bond-forming-conservation-unwired namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap hoBondNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  bondFormingConservationVerdictOk
    (evaluateBondFormingConservationClose
       bond-forming-conservation-unwired namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap hoBondNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

bondFormingConservationFiberOk : FormalFiber → Bool
bondFormingConservationFiberOk fiber-quantum-knowing = true
bondFormingConservationFiberOk fiber-meso-acting = false

bond-forming-conservation-knowing-fiber-ok :
  bondFormingConservationFiberOk fiber-quantum-knowing ≡ true
bond-forming-conservation-knowing-fiber-ok = refl

bond-forming-conservation-meso-acting-not-ok :
  bondFormingConservationFiberOk fiber-meso-acting ≡ false
bond-forming-conservation-meso-acting-not-ok = refl

bond-forming-conservation-routes-knowing-not-meso :
  bondFormingConservationFiberOk fiber-quantum-knowing ≡ true ×
  bondFormingConservationFiberOk fiber-meso-acting ≡ false
bond-forming-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  bondFormingConservationFiberOk fiber-quantum-knowing ∧
  not (bondFormingConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 2 Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

bond-forming-not-proved : bondFormingProved ≡ false
bond-forming-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

bond-second-law-conservation-framed : bondSecondLawConservationFramed ≡ true
bond-second-law-conservation-framed = refl

product-not-xor-pin : productNotXor ≡ true
product-not-xor-pin = product-not-xor

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second bond-forming axiom fork)
------------------------------------------------------------------------

bondFormingConservationAxiom :
  (bondFormingProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (bondSecondLawConservationFramed ≡ true)
  × (productNotXor ≡ true)
  × (interactNotRefine ≡ true)
  × (evaluateBondFormingConservationClose bond-forming-conservation-unwired namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateBondFormingConservationClose bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessAbsent hoBondNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateBondFormingConservationClose bond-forming-conservation-proved (xorMutuallyExclusiveOp bondFormingLeaf qtaimBcpLeaf) bondFormingWitnessPresentZeroGap hoBondNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateBondFormingConservationClose bond-forming-conservation-proved (refineSeparationFormingOp interactApplyLeaf) bondFormingWitnessPresentZeroGap hoBondNuanceWitness false ≡ verdict-refine-separation-forming-refuse)
  × (evaluateBondFormingConservationClose bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap unwiredWitness false ≡ verdict-bond-forming-admissible-ok)
  × (evaluateBondFormingConservationClose bond-forming-conservation-proved namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap hoBondNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (bondFormingConservationFiberOk fiber-quantum-knowing ≡ true)
  × (bondFormingConservationFiberOk fiber-meso-acting ≡ false)
  × (bondFormingConservationVerdictOk (evaluateBondFormingConservationClose bond-forming-conservation-unwired namedHoBondNuanceProduct bondFormingWitnessPresentZeroGap hoBondNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp bondFormingIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a bondFormingIdentity) ≡ true)
  × (isBondFormingAdmissible (xorMutuallyExclusiveOp bondFormingLeaf qtaimBcpLeaf) ≡ false)
  × (isBondFormingAdmissible (refineSeparationFormingOp interactApplyLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (BondFormingBundleWitness.present-count hoBondNuanceWitness ≡ 3)
  × (bondFormingClassIndex ≡ 2)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oganesson ≡ 118)
bondFormingConservationAxiom =
  bond-forming-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , bond-second-law-conservation-framed
  , product-not-xor-pin
  , interact-not-refine-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , refine-separation-forming-refuse-verdict
  , bond-forming-admissible-ok
  , concurrent-product-ok
  , bond-forming-conservation-knowing-fiber-ok
  , bond-forming-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , refine-separation-forming-refuse
  , pattern-class-cardinality-twenty-five
  , ho-nuance-present-count
  , bond-forming-class-index-two
  , refl
  , oganesson-z-118

bondFormingConservationNamed : String
bondFormingConservationNamed =
  "bondFormingConservation: class 2 Bond-forming QTAIM BCP concurrent Pi_c identity conserved product not XOR forming arrow Kleisli Interact Apply not Refine H-O bond nuance witness concurrent"

bondFormingConservationCrossWitnessAuthority : String
bondFormingConservationCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/bond_forming_conservation.rs"

bondFormingTableAuthority : String
bondFormingTableAuthority =
  "umst/umst-chem/src/l0_tables/bond_forming.rs"

kleisliInteractAuthority : String
kleisliInteractAuthority =
  "umst/umst-chem/src/kleisli_interact.rs"

bondFormingConservationCellId : String
bondFormingConservationCellId = "CHEM-FORMAL-Q-AGDA-BOND-FORMING-CONSERVATION"

bondFormingConservationNonClaim : String
bondFormingConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-BOND-FORMING-CONSERVATION class 2 Bond-forming QTAIM BCP Mayer DDEC concurrent Pi_c identity conserved cardinality 25 present product not XOR XOR mutually exclusive refuse forming arrow Kleisli Interact Apply not Refine separation refuse H-O bond nuance witness concurrent bondFormingProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second bond-forming axiom not physics GREEN not production_wired"

bond-forming-conservation-cell-id :
  bondFormingConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-BOND-FORMING-CONSERVATION"
bond-forming-conservation-cell-id = refl

bond-forming-conservation-cites-cross-witness-rs :
  bondFormingConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/bond_forming_conservation.rs"
bond-forming-conservation-cites-cross-witness-rs = refl

bond-forming-conservation-modality-unwired :
  bondFormingConservationModalityCurrent ≡ bond-forming-conservation-unwired
bond-forming-conservation-modality-unwired = refl

bondFormingConservationPhysicsGreenAuthorized : Set
bondFormingConservationPhysicsGreenAuthorized = ⊥

bond-forming-conservation-physics-green-false : ¬ bondFormingConservationPhysicsGreenAuthorized
bond-forming-conservation-physics-green-false ()

bondFormingConservationMarker : String
bondFormingConservationMarker = "chem_int_cross_bond_forming_conservation_v1"

bondFormingConservationSurface : String
bondFormingConservationSurface = "bond_forming_conservation_surface"

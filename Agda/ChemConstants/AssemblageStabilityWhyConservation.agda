-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.AssemblageStabilityWhyConservation.agda
--
-- Pattern class 7 **assemblage_stability_why** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (G-min equilibrium + phase boundary + ore predicate;
--     **product** not XOR, not Goldschmidt XOR enum)
--   * XOR mutually-exclusive refuse; assemblage stability why nuance witness concurrent
--     (equilibrium basin + phase boundary common tangent + ore predicate why)
--   * **assemblage_stability_why** laws Unwired (assemblageStabilityWhy07Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/assemblage_stability.rs
-- L0 table: umst/umst-chem/src/l0_tables/assemblage_stability_why.rs
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- Not 26th axiom; not Goldschmidt XOR. Product not XOR.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.AssemblageStabilityWhyConservation where


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
-- Modality + pattern class 7 **assemblage_stability_why** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data AssemblageStabilityWhyConservationModality : Set where
  assemblage-stability-why-conservation-unwired assemblage-stability-why-conservation-assumed
    assemblage-stability-why-conservation-proved assemblage-stability-why-conservation-surrogate
    : AssemblageStabilityWhyConservationModality

assemblageStabilityWhyConservationModalityCurrent : AssemblageStabilityWhyConservationModality
assemblageStabilityWhyConservationModalityCurrent = assemblage-stability-why-conservation-unwired

assemblageStabilityWhy07Proved productionWired not118SquaredGreenTable
  assemblageStabilityWhySecondLawConservationFramed assemblageStabilityWhyNotXor : Bool
assemblageStabilityWhy07Proved = false
productionWired = false
not118SquaredGreenTable = true
assemblageStabilityWhySecondLawConservationFramed = true
assemblageStabilityWhyNotXor = true

notGoldschmidtXor not26thAxiomMinted : Bool
notGoldschmidtXor = true
not26thAxiomMinted = true

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
-- Pattern class 7 Assemblage-stability-why index pin
------------------------------------------------------------------------

assemblageStabilityWhyClassIndex : ℕ
assemblageStabilityWhyClassIndex = 7

assemblage-stability-why-class-index-seven : assemblageStabilityWhyClassIndex ≡ 7
assemblage-stability-why-class-index-seven = refl

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
-- AssemblageStabilityWhyBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data AssemblageStabilityWhyBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : AssemblageStabilityWhyBundleSlot

isSlotPresent : AssemblageStabilityWhyBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- AssemblageStabilityWhyBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record AssemblageStabilityWhyBundle : Set where
  field slot : ℕ → AssemblageStabilityWhyBundleSlot

assemblageStabilityWhyBundleUnwired : AssemblageStabilityWhyBundle
assemblageStabilityWhyBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : AssemblageStabilityWhyBundle → ℕ → AssemblageStabilityWhyBundleSlot → AssemblageStabilityWhyBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else AssemblageStabilityWhyBundle.slot b j }

withPresent : AssemblageStabilityWhyBundle → ℕ → AssemblageStabilityWhyBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record AssemblageStabilityWhyBundleWitness : Set where
  constructor mkAssemblageStabilityWhyBundleWitness
  field
    bundle : AssemblageStabilityWhyBundle
    present-count : ℕ

assemblageStabilityWhyBundleIsConcurrentProduct : AssemblageStabilityWhyBundleWitness → Bool
assemblageStabilityWhyBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? AssemblageStabilityWhyBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named assemblage-stability-why channel indices — connectivity (1), enablement (2), nets (3)
------------------------------------------------------------------------

gMinEquilibriumBasinChannelIndex phaseBoundaryCommonTangentChannelIndex orePredicateWhyChannelIndex : ℕ
gMinEquilibriumBasinChannelIndex = 1
phaseBoundaryCommonTangentChannelIndex = 2
orePredicateWhyChannelIndex = 3

g-min-equilibrium-basin-index-one : gMinEquilibriumBasinChannelIndex ≡ 1
g-min-equilibrium-basin-index-one = refl

phase-boundary-common-tangent-index-two : phaseBoundaryCommonTangentChannelIndex ≡ 2
phase-boundary-common-tangent-index-two = refl

ore-predicate-why-index-three : orePredicateWhyChannelIndex ≡ 3
ore-predicate-why-index-three = refl

------------------------------------------------------------------------
-- Assemblage-stability-why nuance witness — connectivity + enablement + nets concurrent
------------------------------------------------------------------------

assemblageStabilityWhyNuanceBundle : AssemblageStabilityWhyBundle
assemblageStabilityWhyNuanceBundle =
  withPresent
    (withPresent
      (withPresent assemblageStabilityWhyBundleUnwired gMinEquilibriumBasinChannelIndex)
      phaseBoundaryCommonTangentChannelIndex)
    orePredicateWhyChannelIndex

assemblageStabilityWhyNuanceWitness : AssemblageStabilityWhyBundleWitness
assemblageStabilityWhyNuanceWitness =
  mkAssemblageStabilityWhyBundleWitness assemblageStabilityWhyNuanceBundle 3

assemblage-stability-why-nuance-connectivity-present :
  isSlotPresent (AssemblageStabilityWhyBundle.slot assemblageStabilityWhyNuanceBundle gMinEquilibriumBasinChannelIndex) ≡ true
assemblage-stability-why-nuance-connectivity-present = refl

assemblage-stability-why-nuance-enablement-present :
  isSlotPresent (AssemblageStabilityWhyBundle.slot assemblageStabilityWhyNuanceBundle phaseBoundaryCommonTangentChannelIndex) ≡ true
assemblage-stability-why-nuance-enablement-present = refl

assemblage-stability-why-nuance-nets-present :
  isSlotPresent (AssemblageStabilityWhyBundle.slot assemblageStabilityWhyNuanceBundle orePredicateWhyChannelIndex) ≡ true
assemblage-stability-why-nuance-nets-present = refl

assemblage-stability-why-nuance-present-count : AssemblageStabilityWhyBundleWitness.present-count assemblageStabilityWhyNuanceWitness ≡ 3
assemblage-stability-why-nuance-present-count = refl

assemblage-stability-why-nuance-concurrent-product :
  assemblageStabilityWhyBundleIsConcurrentProduct assemblageStabilityWhyNuanceWitness ≡ true
assemblage-stability-why-nuance-concurrent-product = refl

assemblage-stability-why-nuance-three-factors-concurrent :
  isSlotPresent (AssemblageStabilityWhyBundle.slot assemblageStabilityWhyNuanceBundle gMinEquilibriumBasinChannelIndex) ≡ true
  × isSlotPresent (AssemblageStabilityWhyBundle.slot assemblageStabilityWhyNuanceBundle phaseBoundaryCommonTangentChannelIndex) ≡ true
  × isSlotPresent (AssemblageStabilityWhyBundle.slot assemblageStabilityWhyNuanceBundle orePredicateWhyChannelIndex) ≡ true
  × AssemblageStabilityWhyBundleWitness.present-count assemblageStabilityWhyNuanceWitness ≡ 3
assemblage-stability-why-nuance-three-factors-concurrent =
  assemblage-stability-why-nuance-connectivity-present
  , assemblage-stability-why-nuance-enablement-present
  , assemblage-stability-why-nuance-nets-present
  , assemblage-stability-why-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : AssemblageStabilityWhyBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if assemblageStabilityWhyBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = AssemblageStabilityWhyBundleWitness.bundle w
       in if isSlotPresent (AssemblageStabilityWhyBundle.slot b i)
          then if isSlotPresent (AssemblageStabilityWhyBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : AssemblageStabilityWhyBundleWitness
unwiredWitness = mkAssemblageStabilityWhyBundleWitness assemblageStabilityWhyBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

assemblage-stability-why-nuance-xor-product-ok :
  evaluateXorRefuse assemblageStabilityWhyNuanceWitness gMinEquilibriumBasinChannelIndex phaseBoundaryCommonTangentChannelIndex ≡ xor-product-ok
assemblage-stability-why-nuance-xor-product-ok = refl

assemblage-stability-why-not-xor : assemblageStabilityWhyNotXor ≡ true
assemblage-stability-why-not-xor = refl

------------------------------------------------------------------------
-- ClassifierAssemblageStabilityWhyStep scaffold — AssemblageStabilityWhyBundle **conservation**
------------------------------------------------------------------------

data ClassifierAssemblageStabilityWhyStep : Set where
  assemblage-stability-why-identity : ClassifierAssemblageStabilityWhyStep
  slot-leaf : ℕ → ClassifierAssemblageStabilityWhyStep
  product-concurrent : ClassifierAssemblageStabilityWhyStep → ClassifierAssemblageStabilityWhyStep → ClassifierAssemblageStabilityWhyStep
  xor-mutually-exclusive : ClassifierAssemblageStabilityWhyStep → ClassifierAssemblageStabilityWhyStep → ClassifierAssemblageStabilityWhyStep

assemblageStabilityWhyIdentity : ClassifierAssemblageStabilityWhyStep
assemblageStabilityWhyIdentity = assemblage-stability-why-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierAssemblageStabilityWhyStep → ClassifierAssemblageStabilityWhyStep → ClassifierAssemblageStabilityWhyStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

gMinEquilibriumBasinLeaf phaseBoundaryCommonTangentLeaf orePredicateWhyLeaf : ClassifierAssemblageStabilityWhyStep
gMinEquilibriumBasinLeaf = slot-leaf gMinEquilibriumBasinChannelIndex
phaseBoundaryCommonTangentLeaf = slot-leaf phaseBoundaryCommonTangentChannelIndex
orePredicateWhyLeaf = slot-leaf orePredicateWhyChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierAssemblageStabilityWhyStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isAssemblageStabilityWhyIdentity : ClassifierAssemblageStabilityWhyStep → Bool
isAssemblageStabilityWhyIdentity assemblage-stability-why-identity = true
isAssemblageStabilityWhyIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at assemblage-stability-why-identity
------------------------------------------------------------------------

assemblage-stability-why-left-identity :
  ∀ (a : ClassifierAssemblageStabilityWhyStep) →
  isAssemblageStabilityWhyIdentity assemblageStabilityWhyIdentity ≡ true
  × isProductConcurrent (productConcurrentOp assemblageStabilityWhyIdentity a) ≡ true
assemblage-stability-why-left-identity a = refl , refl

assemblage-stability-why-right-identity :
  ∀ (a : ClassifierAssemblageStabilityWhyStep) →
  isProductConcurrent (productConcurrentOp a assemblageStabilityWhyIdentity) ≡ true
  × isAssemblageStabilityWhyIdentity assemblageStabilityWhyIdentity ≡ true
assemblage-stability-why-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-assemblage-stability-why :
  (∀ a → isProductConcurrent (productConcurrentOp assemblageStabilityWhyIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a assemblageStabilityWhyIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-assemblage-stability-why =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named assemblage-stability-why nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedAssemblageStabilityWhyNuanceProduct : ClassifierAssemblageStabilityWhyStep
namedAssemblageStabilityWhyNuanceProduct =
  productConcurrentOp
    (productConcurrentOp gMinEquilibriumBasinLeaf phaseBoundaryCommonTangentLeaf)
    orePredicateWhyLeaf

named-assemblage-stability-why-nuance-product-concurrent :
  isProductConcurrent namedAssemblageStabilityWhyNuanceProduct ≡ true
  × assemblageStabilityWhyBundleIsConcurrentProduct assemblageStabilityWhyNuanceWitness ≡ true
named-assemblage-stability-why-nuance-product-concurrent = refl , assemblage-stability-why-nuance-concurrent-product

------------------------------------------------------------------------
-- AssemblageStabilityWhyBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data AssemblageStabilityWhyAdmissibility : Set where
  assemblage-stability-why-admissible assemblage-stability-why-xor-refuse : AssemblageStabilityWhyAdmissibility

isAssemblageStabilityWhyPreserving : ClassifierAssemblageStabilityWhyStep → Bool
isAssemblageStabilityWhyPreserving assemblage-stability-why-identity = true
isAssemblageStabilityWhyPreserving (slot-leaf _) = true
isAssemblageStabilityWhyPreserving (product-concurrent a b) =
  isAssemblageStabilityWhyPreserving a ∧ isAssemblageStabilityWhyPreserving b
isAssemblageStabilityWhyPreserving (xor-mutually-exclusive _ _) = false

isAssemblageStabilityWhyAdmissible : ClassifierAssemblageStabilityWhyStep → Bool
isAssemblageStabilityWhyAdmissible step = isAssemblageStabilityWhyPreserving step

g-min-equilibrium-basin-leaf-admissible : isAssemblageStabilityWhyAdmissible gMinEquilibriumBasinLeaf ≡ true
g-min-equilibrium-basin-leaf-admissible = refl

phase-boundary-common-tangent-leaf-admissible : isAssemblageStabilityWhyAdmissible phaseBoundaryCommonTangentLeaf ≡ true
phase-boundary-common-tangent-leaf-admissible = refl

ore-predicate-why-leaf-admissible : isAssemblageStabilityWhyAdmissible orePredicateWhyLeaf ≡ true
ore-predicate-why-leaf-admissible = refl

named-assemblage-stability-why-nuance-admissible : isAssemblageStabilityWhyAdmissible namedAssemblageStabilityWhyNuanceProduct ≡ true
named-assemblage-stability-why-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isAssemblageStabilityWhyAdmissible (xorMutuallyExclusiveOp gMinEquilibriumBasinLeaf phaseBoundaryCommonTangentLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-ore-predicate-why-refuse :
  isAssemblageStabilityWhyAdmissible (xorMutuallyExclusiveOp phaseBoundaryCommonTangentLeaf orePredicateWhyLeaf) ≡ false
xor-mutually-exclusive-ore-predicate-why-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data AssemblageStabilityWhyWitnessPresence : Set where
  assemblage-stability-why-witness-absent assemblage-stability-why-witness-present : AssemblageStabilityWhyWitnessPresence

record ClassifierAssemblageStabilityWhyWitness : Set where
  constructor mkClassifierAssemblageStabilityWhyWitness
  field
    witness-presence : AssemblageStabilityWhyWitnessPresence
    assemblage-stability-why-gap-total : ℕ

assemblageStabilityWhyWitnessAbsent : ClassifierAssemblageStabilityWhyWitness
assemblageStabilityWhyWitnessAbsent = mkClassifierAssemblageStabilityWhyWitness assemblage-stability-why-witness-absent zero

assemblageStabilityWhyWitnessPresentZeroGap : ClassifierAssemblageStabilityWhyWitness
assemblageStabilityWhyWitnessPresentZeroGap = mkClassifierAssemblageStabilityWhyWitness assemblage-stability-why-witness-present zero

assemblageStabilityWhyWitnessPresentWithGaps : ℕ → ClassifierAssemblageStabilityWhyWitness
assemblageStabilityWhyWitnessPresentWithGaps n = mkClassifierAssemblageStabilityWhyWitness assemblage-stability-why-witness-present n

assemblageStabilityWhyWitnessGapFree : ClassifierAssemblageStabilityWhyWitness → Bool
assemblageStabilityWhyWitnessGapFree (mkClassifierAssemblageStabilityWhyWitness assemblage-stability-why-witness-absent _) = false
assemblageStabilityWhyWitnessGapFree (mkClassifierAssemblageStabilityWhyWitness assemblage-stability-why-witness-present n) =
  does (n ℕ-Props.≟ zero)

assemblage-stability-why-witness-present-zero-gap-free :
  assemblageStabilityWhyWitnessGapFree assemblageStabilityWhyWitnessPresentZeroGap ≡ true
assemblage-stability-why-witness-present-zero-gap-free = refl

assemblage-stability-why-witness-absent-not-gap-free :
  assemblageStabilityWhyWitnessGapFree assemblageStabilityWhyWitnessAbsent ≡ false
assemblage-stability-why-witness-absent-not-gap-free = refl

assemblage-stability-why-witness-with-gaps-not-gap-free :
  ∀ n → assemblageStabilityWhyWitnessGapFree (assemblageStabilityWhyWitnessPresentWithGaps (suc n)) ≡ false
assemblage-stability-why-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Assemblage-stability-why **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data AssemblageStabilityWhyConservationVerdict : Set where
  verdict-unwired-ok verdict-assemblage-stability-why-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : AssemblageStabilityWhyConservationVerdict

assemblageStabilityWhyConservationVerdictOk : AssemblageStabilityWhyConservationVerdict → Bool
assemblageStabilityWhyConservationVerdictOk verdict-unwired-ok = true
assemblageStabilityWhyConservationVerdictOk verdict-assemblage-stability-why-admissible-ok = true
assemblageStabilityWhyConservationVerdictOk verdict-concurrent-product-ok = true
assemblageStabilityWhyConservationVerdictOk _ = false

evaluateAssemblageStabilityWhyConservationClose :
  AssemblageStabilityWhyConservationModality → ClassifierAssemblageStabilityWhyStep → ClassifierAssemblageStabilityWhyWitness
  → AssemblageStabilityWhyBundleWitness → Bool → AssemblageStabilityWhyConservationVerdict
evaluateAssemblageStabilityWhyConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-proved _ (mkClassifierAssemblageStabilityWhyWitness assemblage-stability-why-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-proved _ (mkClassifierAssemblageStabilityWhyWitness assemblage-stability-why-witness-present _) w false
  with assemblageStabilityWhyBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-assemblage-stability-why-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without assemblage-stability-why witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-unwired namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-assumed namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-surrogate namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  assemblageStabilityWhyConservationVerdictOk
    (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-unwired namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false)
    ≡ true
  × assemblageStabilityWhyConservationVerdictOk
      (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-assumed namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false)
      ≡ true
  × assemblageStabilityWhyConservationVerdictOk
      (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-surrogate namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without assemblage-stability-why witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  assemblageStabilityWhyConservationVerdictOk
    (evaluateAssemblageStabilityWhyConservationClose
       assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false ≡
  verdict-assemblage-stability-why-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-proved
    (xorMutuallyExclusiveOp gMinEquilibriumBasinLeaf phaseBoundaryCommonTangentLeaf)
    assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  assemblageStabilityWhyConservationVerdictOk
    (evaluateAssemblageStabilityWhyConservationClose
       assemblage-stability-why-conservation-proved
       (xorMutuallyExclusiveOp gMinEquilibriumBasinLeaf phaseBoundaryCommonTangentLeaf)
       assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-proved
    (xorMutuallyExclusiveOp gMinEquilibriumBasinLeaf phaseBoundaryCommonTangentLeaf)
    assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-assemblage-stability-why — nuance **product** closed
------------------------------------------------------------------------

assemblage-stability-why-admissible-ok :
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap unwiredWitness false ≡
  verdict-assemblage-stability-why-admissible-ok
assemblage-stability-why-admissible-ok = refl

assemblage-stability-why-admissible-verdict-ok :
  assemblageStabilityWhyConservationVerdictOk
    (evaluateAssemblageStabilityWhyConservationClose
       assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap unwiredWitness false)
    ≡ true
assemblage-stability-why-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — assemblage-stability-why nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  assemblageStabilityWhyConservationVerdictOk
    (evaluateAssemblageStabilityWhyConservationClose
       assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-assemblage-stability-why04-proved :
  assemblageStabilityWhyConservationVerdictOk
    (evaluateAssemblageStabilityWhyConservationClose
       assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness false)
    ≡ true
  × assemblageStabilityWhy07Proved ≡ false
concurrent-product-ok-still-not-assemblage-stability-why04-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateAssemblageStabilityWhyConservationClose
    assemblage-stability-why-conservation-unwired namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  assemblageStabilityWhyConservationVerdictOk
    (evaluateAssemblageStabilityWhyConservationClose
       assemblage-stability-why-conservation-unwired namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

assemblageStabilityWhyConservationFiberOk : FormalFiber → Bool
assemblageStabilityWhyConservationFiberOk fiber-quantum-knowing = true
assemblageStabilityWhyConservationFiberOk fiber-meso-acting = false

assemblage-stability-why-conservation-knowing-fiber-ok :
  assemblageStabilityWhyConservationFiberOk fiber-quantum-knowing ≡ true
assemblage-stability-why-conservation-knowing-fiber-ok = refl

assemblage-stability-why-conservation-meso-acting-not-ok :
  assemblageStabilityWhyConservationFiberOk fiber-meso-acting ≡ false
assemblage-stability-why-conservation-meso-acting-not-ok = refl

assemblage-stability-why-conservation-routes-knowing-not-meso :
  assemblageStabilityWhyConservationFiberOk fiber-quantum-knowing ≡ true ×
  assemblageStabilityWhyConservationFiberOk fiber-meso-acting ≡ false
assemblage-stability-why-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  assemblageStabilityWhyConservationFiberOk fiber-quantum-knowing ∧
  not (assemblageStabilityWhyConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 7 assemblage_stability_why Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

assemblage-stability-why-07-not-proved : assemblageStabilityWhy07Proved ≡ false
assemblage-stability-why-07-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

assemblage-stability-why-second-law-conservation-framed : assemblageStabilityWhySecondLawConservationFramed ≡ true
assemblage-stability-why-second-law-conservation-framed = refl

assemblage-stability-why-not-xor-pin : assemblageStabilityWhyNotXor ≡ true
assemblage-stability-why-not-xor-pin = assemblage-stability-why-not-xor

not-goldschmidt-xor-pin : notGoldschmidtXor ≡ true
not-goldschmidt-xor-pin = refl

not-26th-axiom-minted-pin : not26thAxiomMinted ≡ true
not-26th-axiom-minted-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second Assemblage-stability-why axiom fork)
------------------------------------------------------------------------

assemblageStabilityWhyConservationAxiom :
  (assemblageStabilityWhy07Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (assemblageStabilityWhySecondLawConservationFramed ≡ true)
  × (assemblageStabilityWhyNotXor ≡ true)
  × (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-unwired namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessAbsent assemblageStabilityWhyNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-proved (xorMutuallyExclusiveOp gMinEquilibriumBasinLeaf phaseBoundaryCommonTangentLeaf) assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap unwiredWitness false ≡ verdict-assemblage-stability-why-admissible-ok)
  × (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-proved namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (assemblageStabilityWhyConservationFiberOk fiber-quantum-knowing ≡ true)
  × (assemblageStabilityWhyConservationFiberOk fiber-meso-acting ≡ false)
  × (assemblageStabilityWhyConservationVerdictOk (evaluateAssemblageStabilityWhyConservationClose assemblage-stability-why-conservation-unwired namedAssemblageStabilityWhyNuanceProduct assemblageStabilityWhyWitnessPresentZeroGap assemblageStabilityWhyNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp assemblageStabilityWhyIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a assemblageStabilityWhyIdentity) ≡ true)
  × (isAssemblageStabilityWhyAdmissible (xorMutuallyExclusiveOp gMinEquilibriumBasinLeaf phaseBoundaryCommonTangentLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (assemblageStabilityWhyClassIndex ≡ 7)
  × (AssemblageStabilityWhyBundleWitness.present-count assemblageStabilityWhyNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
assemblageStabilityWhyConservationAxiom =
  assemblage-stability-why-07-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , assemblage-stability-why-second-law-conservation-framed
  , assemblage-stability-why-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , assemblage-stability-why-admissible-ok
  , concurrent-product-ok
  , assemblage-stability-why-conservation-knowing-fiber-ok
  , assemblage-stability-why-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , assemblage-stability-why-class-index-seven
  , assemblage-stability-why-nuance-present-count
  , iron-z-26
  , oganesson-z-118

assemblageStabilityWhyConservationNamed : String
assemblageStabilityWhyConservationNamed =
  "assemblageStabilityWhyConservation: pattern class 7 assemblage_stability_why conservation concurrent Pi_c identity conserved G-min equilibrium basin phase boundary common tangent ore predicate why XOR refuse assemblagestabilitywhyconservation nuance witness concurrent product not Goldschmidt XOR"

assemblageStabilityWhyConservationCrossWitnessAuthority : String
assemblageStabilityWhyConservationCrossWitnessAuthority =
  "umst/umst-chem/src/assemblage_stability.rs"

assemblageStabilityWhyTableAuthority : String
assemblageStabilityWhyTableAuthority =
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs"

oreAssemblageAuthority : String
oreAssemblageAuthority =
  "umst/umst-chem/src/ore_assemblage.rs"

gibbsConvexHullAuthority : String
gibbsConvexHullAuthority =
  "umst/umst-chem/src/theorem_import/gibbs_convex_hull.rs"

assemblageStabilityWhyConservationCellId : String
assemblageStabilityWhyConservationCellId = "CHEM-FORMAL-Q-AGDA-ASSEMBLAGE-STABILITY-WHY-CONSERVATION"

assemblageStabilityWhyConservationNonClaim : String
assemblageStabilityWhyConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-ASSEMBLAGE-STABILITY-WHY-CONSERVATION pattern class 7 assemblage_stability_why conservation concurrent Pi_c identity conserved G-min equilibrium basin phase boundary common tangent ore predicate why product not XOR not Goldschmidt XOR not 26th axiom XOR mutually exclusive refuse assemblage stability why nuance witness concurrent assemblageStabilityWhy07Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite assemblage_stability.rs l0_tables assemblage_stability_why not fork not physics GREEN not production_wired assemblagestabilitywhyconservation"

assemblage-stability-why-conservation-cell-id :
  assemblageStabilityWhyConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-ASSEMBLAGE-STABILITY-WHY-CONSERVATION"
assemblage-stability-why-conservation-cell-id = refl

assemblage-stability-why-conservation-cites-assemblage-stability-rs :
  assemblageStabilityWhyConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/assemblage_stability.rs"
assemblage-stability-why-conservation-cites-assemblage-stability-rs = refl

assemblage-stability-why-conservation-cites-l0-table-rs :
  assemblageStabilityWhyTableAuthority ≡
  "umst/umst-chem/src/l0_tables/assemblage_stability_why.rs"
assemblage-stability-why-conservation-cites-l0-table-rs = refl

assemblage-stability-why-conservation-modality-unwired :
  assemblageStabilityWhyConservationModalityCurrent ≡ assemblage-stability-why-conservation-unwired
assemblage-stability-why-conservation-modality-unwired = refl

assemblageStabilityWhyConservationPhysicsGreenAuthorized : Set
assemblageStabilityWhyConservationPhysicsGreenAuthorized = ⊥

assemblage-stability-why-conservation-physics-green-false : ¬ assemblageStabilityWhyConservationPhysicsGreenAuthorized
assemblage-stability-why-conservation-physics-green-false ()

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.HomeostasisGminConservation.agda
--
-- CHEM-FORMAL-Q-AGDA-HOMEOSTASIS-GMIN-CONSERVATION
-- Constitutive **homeostasis_gmin** chart **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (local G-min equilibrium + negative feedback typed +
--     homeostasis gmin chart; **product** not XOR, not biology axiom)
--   * XOR mutually-exclusive refuse; homeostasis G-min nuance witness concurrent
--     (local G-min equilibrium + negative feedback typed + homeostasis gmin chart)
--   * **homeostasis_gmin** laws Unwired (homeostasisGminProved = false)
--   * homeostasis as local G-min — second law + conservation only; not a 26th axiom
--
-- INT (read-only cite): umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs
-- G-min cite: umst/umst-chem/src/assemblage_stability.rs
-- Mirrors sibling `ChemConstants/HomeostasisGminConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- Not biology axiom; not 26th axiom. Product not XOR.
-- WAVE100: no lib.rs / eos.rs / nano wiring.
------------------------------------------------------------------------
module ChemConstants.HomeostasisGminConservation where

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
-- Modality + constitutive **homeostasis_gmin** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data HomeostasisGminConservationModality : Set where
  homeostasis-gmin-conservation-unwired homeostasis-gmin-conservation-assumed
    homeostasis-gmin-conservation-proved homeostasis-gmin-conservation-surrogate
    : HomeostasisGminConservationModality

homeostasisGminConservationModalityCurrent : HomeostasisGminConservationModality
homeostasisGminConservationModalityCurrent = homeostasis-gmin-conservation-unwired

homeostasisGminProved productionWired not118SquaredGreenTable
  homeostasisGminSecondLawConservationFramed homeostasisGminNotXor : Bool
homeostasisGminProved = false
productionWired = false
not118SquaredGreenTable = true
homeostasisGminSecondLawConservationFramed = true
homeostasisGminNotXor = true

localGMinEquilibriumTyped notBiologyAxiomMinted not26thAxiomMinted : Bool
localGMinEquilibriumTyped = true
notBiologyAxiomMinted = true
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
-- Homeostasis G-min conservation index pin (class 7 G-stability)
------------------------------------------------------------------------

homeostasisGminConservationIndex : ℕ
homeostasisGminConservationIndex = 7

homeostasis-gmin-conservation-index-seven : homeostasisGminConservationIndex ≡ 7
homeostasis-gmin-conservation-index-seven = refl

------------------------------------------------------------------------
-- Named element Z pins — Pt (Z=78), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  platinum oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ platinum = 78
elementAtomicZ oganesson = 118

platinum-z-78 : elementAtomicZ platinum ≡ 78
platinum-z-78 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- HomeostasisGminBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data HomeostasisGminBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : HomeostasisGminBundleSlot

isSlotPresent : HomeostasisGminBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- HomeostasisGminBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record HomeostasisGminBundle : Set where
  field slot : ℕ → HomeostasisGminBundleSlot

homeostasisGminBundleUnwired : HomeostasisGminBundle
homeostasisGminBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : HomeostasisGminBundle → ℕ → HomeostasisGminBundleSlot → HomeostasisGminBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else HomeostasisGminBundle.slot b j }

withPresent : HomeostasisGminBundle → ℕ → HomeostasisGminBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record HomeostasisGminBundleWitness : Set where
  constructor mkHomeostasisGminBundleWitness
  field
    bundle : HomeostasisGminBundle
    present-count : ℕ

homeostasisGminBundleIsConcurrentProduct : HomeostasisGminBundleWitness → Bool
homeostasisGminBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? HomeostasisGminBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named homeostasis G-min channel indices — local G-min equilibrium (1), negative feedback typed (2), homeostasis gmin chart (3)
------------------------------------------------------------------------

localGMinEquilibriumChannelIndex negativeFeedbackTypedChannelIndex homeostasisGminChartChannelIndex : ℕ
localGMinEquilibriumChannelIndex = 1
negativeFeedbackTypedChannelIndex = 2
homeostasisGminChartChannelIndex = 3

local-g-min-equilibrium-index-one : localGMinEquilibriumChannelIndex ≡ 1
local-g-min-equilibrium-index-one = refl

negative-feedback-typed-index-two : negativeFeedbackTypedChannelIndex ≡ 2
negative-feedback-typed-index-two = refl

homeostasis-gmin-chart-index-three : homeostasisGminChartChannelIndex ≡ 3
homeostasis-gmin-chart-index-three = refl

------------------------------------------------------------------------
-- Homeostasis G-min nuance witness — local G-min equilibrium + negative feedback typed + homeostasis gmin chart concurrent
------------------------------------------------------------------------

homeostasisGminNuanceBundle : HomeostasisGminBundle
homeostasisGminNuanceBundle =
  withPresent
    (withPresent
      (withPresent homeostasisGminBundleUnwired localGMinEquilibriumChannelIndex)
      negativeFeedbackTypedChannelIndex)
    homeostasisGminChartChannelIndex

homeostasisGminNuanceWitness : HomeostasisGminBundleWitness
homeostasisGminNuanceWitness =
  mkHomeostasisGminBundleWitness homeostasisGminNuanceBundle 3

homeostasis-gmin-nuance-local-g-min-equilibrium-present :
  isSlotPresent (HomeostasisGminBundle.slot homeostasisGminNuanceBundle localGMinEquilibriumChannelIndex) ≡ true
homeostasis-gmin-nuance-local-g-min-equilibrium-present = refl

homeostasis-gmin-nuance-negative-feedback-typed-present :
  isSlotPresent (HomeostasisGminBundle.slot homeostasisGminNuanceBundle negativeFeedbackTypedChannelIndex) ≡ true
homeostasis-gmin-nuance-negative-feedback-typed-present = refl

homeostasis-gmin-nuance-homeostasis-gmin-chart-present :
  isSlotPresent (HomeostasisGminBundle.slot homeostasisGminNuanceBundle homeostasisGminChartChannelIndex) ≡ true
homeostasis-gmin-nuance-homeostasis-gmin-chart-present = refl

homeostasis-gmin-nuance-present-count : HomeostasisGminBundleWitness.present-count homeostasisGminNuanceWitness ≡ 3
homeostasis-gmin-nuance-present-count = refl

homeostasis-gmin-nuance-concurrent-product :
  homeostasisGminBundleIsConcurrentProduct homeostasisGminNuanceWitness ≡ true
homeostasis-gmin-nuance-concurrent-product = refl

homeostasis-gmin-nuance-three-factors-concurrent :
  isSlotPresent (HomeostasisGminBundle.slot homeostasisGminNuanceBundle localGMinEquilibriumChannelIndex) ≡ true
  × isSlotPresent (HomeostasisGminBundle.slot homeostasisGminNuanceBundle negativeFeedbackTypedChannelIndex) ≡ true
  × isSlotPresent (HomeostasisGminBundle.slot homeostasisGminNuanceBundle homeostasisGminChartChannelIndex) ≡ true
  × HomeostasisGminBundleWitness.present-count homeostasisGminNuanceWitness ≡ 3
homeostasis-gmin-nuance-three-factors-concurrent =
  homeostasis-gmin-nuance-local-g-min-equilibrium-present
  , homeostasis-gmin-nuance-negative-feedback-typed-present
  , homeostasis-gmin-nuance-homeostasis-gmin-chart-present
  , homeostasis-gmin-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : HomeostasisGminBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if homeostasisGminBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = HomeostasisGminBundleWitness.bundle w
       in if isSlotPresent (HomeostasisGminBundle.slot b i)
          then if isSlotPresent (HomeostasisGminBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : HomeostasisGminBundleWitness
unwiredWitness = mkHomeostasisGminBundleWitness homeostasisGminBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

homeostasis-gmin-nuance-xor-product-ok :
  evaluateXorRefuse homeostasisGminNuanceWitness localGMinEquilibriumChannelIndex negativeFeedbackTypedChannelIndex ≡ xor-product-ok
homeostasis-gmin-nuance-xor-product-ok = refl

homeostasis-gmin-not-xor : homeostasisGminNotXor ≡ true
homeostasis-gmin-not-xor = refl

------------------------------------------------------------------------
-- ClassifierHomeostasisGminStep scaffold — HomeostasisGminBundle **conservation**
------------------------------------------------------------------------

data ClassifierHomeostasisGminStep : Set where
  homeostasis-gmin-identity : ClassifierHomeostasisGminStep
  slot-leaf : ℕ → ClassifierHomeostasisGminStep
  product-concurrent : ClassifierHomeostasisGminStep → ClassifierHomeostasisGminStep → ClassifierHomeostasisGminStep
  xor-mutually-exclusive : ClassifierHomeostasisGminStep → ClassifierHomeostasisGminStep → ClassifierHomeostasisGminStep

homeostasisGminIdentity : ClassifierHomeostasisGminStep
homeostasisGminIdentity = homeostasis-gmin-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierHomeostasisGminStep → ClassifierHomeostasisGminStep → ClassifierHomeostasisGminStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

localGMinEquilibriumLeaf negativeFeedbackTypedLeaf homeostasisGminChartLeaf : ClassifierHomeostasisGminStep
localGMinEquilibriumLeaf = slot-leaf localGMinEquilibriumChannelIndex
negativeFeedbackTypedLeaf = slot-leaf negativeFeedbackTypedChannelIndex
homeostasisGminChartLeaf = slot-leaf homeostasisGminChartChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierHomeostasisGminStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isHomeostasisGminIdentity : ClassifierHomeostasisGminStep → Bool
isHomeostasisGminIdentity homeostasis-gmin-identity = true
isHomeostasisGminIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at homeostasis-gmin-identity
------------------------------------------------------------------------

homeostasis-gmin-left-identity :
  ∀ (a : ClassifierHomeostasisGminStep) →
  isHomeostasisGminIdentity homeostasisGminIdentity ≡ true
  × isProductConcurrent (productConcurrentOp homeostasisGminIdentity a) ≡ true
homeostasis-gmin-left-identity a = refl , refl

homeostasis-gmin-right-identity :
  ∀ (a : ClassifierHomeostasisGminStep) →
  isProductConcurrent (productConcurrentOp a homeostasisGminIdentity) ≡ true
  × isHomeostasisGminIdentity homeostasisGminIdentity ≡ true
homeostasis-gmin-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-homeostasis-gmin :
  (∀ a → isProductConcurrent (productConcurrentOp homeostasisGminIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a homeostasisGminIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-homeostasis-gmin =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named homeostasis G-min nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedHomeostasisGminNuanceProduct : ClassifierHomeostasisGminStep
namedHomeostasisGminNuanceProduct =
  productConcurrentOp
    (productConcurrentOp localGMinEquilibriumLeaf negativeFeedbackTypedLeaf)
    homeostasisGminChartLeaf

named-homeostasis-gmin-nuance-product-concurrent :
  isProductConcurrent namedHomeostasisGminNuanceProduct ≡ true
  × homeostasisGminBundleIsConcurrentProduct homeostasisGminNuanceWitness ≡ true
named-homeostasis-gmin-nuance-product-concurrent = refl , homeostasis-gmin-nuance-concurrent-product

------------------------------------------------------------------------
-- HomeostasisGminBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data HomeostasisGminAdmissibility : Set where
  homeostasis-gmin-admissible homeostasis-gmin-xor-refuse : HomeostasisGminAdmissibility

isHomeostasisGminPreserving : ClassifierHomeostasisGminStep → Bool
isHomeostasisGminPreserving homeostasis-gmin-identity = true
isHomeostasisGminPreserving (slot-leaf _) = true
isHomeostasisGminPreserving (product-concurrent a b) =
  isHomeostasisGminPreserving a ∧ isHomeostasisGminPreserving b
isHomeostasisGminPreserving (xor-mutually-exclusive _ _) = false

isHomeostasisGminAdmissible : ClassifierHomeostasisGminStep → Bool
isHomeostasisGminAdmissible step = isHomeostasisGminPreserving step

local-g-min-equilibrium-leaf-admissible : isHomeostasisGminAdmissible localGMinEquilibriumLeaf ≡ true
local-g-min-equilibrium-leaf-admissible = refl

negative-feedback-typed-leaf-admissible : isHomeostasisGminAdmissible negativeFeedbackTypedLeaf ≡ true
negative-feedback-typed-leaf-admissible = refl

homeostasis-gmin-chart-leaf-admissible : isHomeostasisGminAdmissible homeostasisGminChartLeaf ≡ true
homeostasis-gmin-chart-leaf-admissible = refl

named-homeostasis-gmin-nuance-admissible : isHomeostasisGminAdmissible namedHomeostasisGminNuanceProduct ≡ true
named-homeostasis-gmin-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isHomeostasisGminAdmissible (xorMutuallyExclusiveOp localGMinEquilibriumLeaf negativeFeedbackTypedLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-homeostasis-gmin-chart-refuse :
  isHomeostasisGminAdmissible (xorMutuallyExclusiveOp negativeFeedbackTypedLeaf homeostasisGminChartLeaf) ≡ false
xor-mutually-exclusive-homeostasis-gmin-chart-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data HomeostasisGminWitnessPresence : Set where
  homeostasis-gmin-witness-absent homeostasis-gmin-witness-present : HomeostasisGminWitnessPresence

record ClassifierHomeostasisGminWitness : Set where
  constructor mkClassifierHomeostasisGminWitness
  field
    witness-presence : HomeostasisGminWitnessPresence
    homeostasis-gmin-gap-total : ℕ

homeostasisGminWitnessAbsent : ClassifierHomeostasisGminWitness
homeostasisGminWitnessAbsent = mkClassifierHomeostasisGminWitness homeostasis-gmin-witness-absent zero

homeostasisGminWitnessPresentZeroGap : ClassifierHomeostasisGminWitness
homeostasisGminWitnessPresentZeroGap = mkClassifierHomeostasisGminWitness homeostasis-gmin-witness-present zero

homeostasisGminWitnessPresentWithGaps : ℕ → ClassifierHomeostasisGminWitness
homeostasisGminWitnessPresentWithGaps n = mkClassifierHomeostasisGminWitness homeostasis-gmin-witness-present n

homeostasisGminWitnessGapFree : ClassifierHomeostasisGminWitness → Bool
homeostasisGminWitnessGapFree (mkClassifierHomeostasisGminWitness homeostasis-gmin-witness-absent _) = false
homeostasisGminWitnessGapFree (mkClassifierHomeostasisGminWitness homeostasis-gmin-witness-present n) =
  does (n ℕ-Props.≟ zero)

homeostasis-gmin-witness-present-zero-gap-free :
  homeostasisGminWitnessGapFree homeostasisGminWitnessPresentZeroGap ≡ true
homeostasis-gmin-witness-present-zero-gap-free = refl

homeostasis-gmin-witness-absent-not-gap-free :
  homeostasisGminWitnessGapFree homeostasisGminWitnessAbsent ≡ false
homeostasis-gmin-witness-absent-not-gap-free = refl

homeostasis-gmin-witness-with-gaps-not-gap-free :
  ∀ n → homeostasisGminWitnessGapFree (homeostasisGminWitnessPresentWithGaps (suc n)) ≡ false
homeostasis-gmin-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-HomeostasisGmin **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data HomeostasisGminConservationVerdict : Set where
  verdict-unwired-ok verdict-homeostasis-gmin-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : HomeostasisGminConservationVerdict

homeostasisGminConservationVerdictOk : HomeostasisGminConservationVerdict → Bool
homeostasisGminConservationVerdictOk verdict-unwired-ok = true
homeostasisGminConservationVerdictOk verdict-homeostasis-gmin-admissible-ok = true
homeostasisGminConservationVerdictOk verdict-concurrent-product-ok = true
homeostasisGminConservationVerdictOk _ = false

evaluateHomeostasisGminConservationClose :
  HomeostasisGminConservationModality → ClassifierHomeostasisGminStep → ClassifierHomeostasisGminWitness
  → HomeostasisGminBundleWitness → Bool → HomeostasisGminConservationVerdict
evaluateHomeostasisGminConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-proved _ (mkClassifierHomeostasisGminWitness homeostasis-gmin-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-proved _ (mkClassifierHomeostasisGminWitness homeostasis-gmin-witness-present _) w false
  with homeostasisGminBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-homeostasis-gmin-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without homeostasis G-min witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-unwired namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-assumed namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-surrogate namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  homeostasisGminConservationVerdictOk
    (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-unwired namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false)
    ≡ true
  × homeostasisGminConservationVerdictOk
      (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-assumed namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false)
      ≡ true
  × homeostasisGminConservationVerdictOk
      (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-surrogate namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without homeostasis G-min witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  homeostasisGminConservationVerdictOk
    (evaluateHomeostasisGminConservationClose
       homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false ≡
  verdict-homeostasis-gmin-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-proved
    (xorMutuallyExclusiveOp localGMinEquilibriumLeaf negativeFeedbackTypedLeaf)
    homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  homeostasisGminConservationVerdictOk
    (evaluateHomeostasisGminConservationClose
       homeostasis-gmin-conservation-proved
       (xorMutuallyExclusiveOp localGMinEquilibriumLeaf negativeFeedbackTypedLeaf)
       homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-proved
    (xorMutuallyExclusiveOp localGMinEquilibriumLeaf negativeFeedbackTypedLeaf)
    homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-homeostasis-gmin — nuance **product** closed
------------------------------------------------------------------------

homeostasis-gmin-admissible-ok :
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap unwiredWitness false ≡
  verdict-homeostasis-gmin-admissible-ok
homeostasis-gmin-admissible-ok = refl

homeostasis-gmin-admissible-verdict-ok :
  homeostasisGminConservationVerdictOk
    (evaluateHomeostasisGminConservationClose
       homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap unwiredWitness false)
    ≡ true
homeostasis-gmin-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — homeostasis G-min nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  homeostasisGminConservationVerdictOk
    (evaluateHomeostasisGminConservationClose
       homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-homeostasis-gmin-proved :
  homeostasisGminConservationVerdictOk
    (evaluateHomeostasisGminConservationClose
       homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness false)
    ≡ true
  × homeostasisGminProved ≡ false
concurrent-product-ok-still-not-homeostasis-gmin-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateHomeostasisGminConservationClose
    homeostasis-gmin-conservation-unwired namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  homeostasisGminConservationVerdictOk
    (evaluateHomeostasisGminConservationClose
       homeostasis-gmin-conservation-unwired namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

homeostasisGminConservationFiberOk : FormalFiber → Bool
homeostasisGminConservationFiberOk fiber-quantum-knowing = true
homeostasisGminConservationFiberOk fiber-meso-acting = false

homeostasis-gmin-conservation-knowing-fiber-ok :
  homeostasisGminConservationFiberOk fiber-quantum-knowing ≡ true
homeostasis-gmin-conservation-knowing-fiber-ok = refl

homeostasis-gmin-conservation-meso-acting-not-ok :
  homeostasisGminConservationFiberOk fiber-meso-acting ≡ false
homeostasis-gmin-conservation-meso-acting-not-ok = refl

homeostasis-gmin-conservation-routes-knowing-not-meso :
  homeostasisGminConservationFiberOk fiber-quantum-knowing ≡ true ×
  homeostasisGminConservationFiberOk fiber-meso-acting ≡ false
homeostasis-gmin-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  homeostasisGminConservationFiberOk fiber-quantum-knowing ∧
  not (homeostasisGminConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not homeostasis G-min Proved, not biology axiom, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

homeostasis-gmin-not-proved : homeostasisGminProved ≡ false
homeostasis-gmin-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

homeostasis-gmin-second-law-conservation-framed : homeostasisGminSecondLawConservationFramed ≡ true
homeostasis-gmin-second-law-conservation-framed = refl

homeostasis-gmin-not-xor-pin : homeostasisGminNotXor ≡ true
homeostasis-gmin-not-xor-pin = homeostasis-gmin-not-xor

local-g-min-equilibrium-typed-pin : localGMinEquilibriumTyped ≡ true
local-g-min-equilibrium-typed-pin = refl

not-biology-axiom-minted-pin : notBiologyAxiomMinted ≡ true
not-biology-axiom-minted-pin = refl

not-26th-axiom-minted-pin : not26thAxiomMinted ≡ true
not-26th-axiom-minted-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not biology axiom; not 26th axiom)
------------------------------------------------------------------------

homeostasisGminConservationAxiom :
  (homeostasisGminProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (homeostasisGminSecondLawConservationFramed ≡ true)
  × (homeostasisGminNotXor ≡ true)
  × (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-unwired namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessAbsent homeostasisGminNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-proved (xorMutuallyExclusiveOp localGMinEquilibriumLeaf negativeFeedbackTypedLeaf) homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap unwiredWitness false ≡ verdict-homeostasis-gmin-admissible-ok)
  × (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-proved namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (homeostasisGminConservationFiberOk fiber-quantum-knowing ≡ true)
  × (homeostasisGminConservationFiberOk fiber-meso-acting ≡ false)
  × (homeostasisGminConservationVerdictOk (evaluateHomeostasisGminConservationClose homeostasis-gmin-conservation-unwired namedHomeostasisGminNuanceProduct homeostasisGminWitnessPresentZeroGap homeostasisGminNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp homeostasisGminIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a homeostasisGminIdentity) ≡ true)
  × (isHomeostasisGminAdmissible (xorMutuallyExclusiveOp localGMinEquilibriumLeaf negativeFeedbackTypedLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (homeostasisGminConservationIndex ≡ 7)
  × (HomeostasisGminBundleWitness.present-count homeostasisGminNuanceWitness ≡ 3)
  × (elementAtomicZ platinum ≡ 78)
  × (elementAtomicZ oganesson ≡ 118)
homeostasisGminConservationAxiom =
  homeostasis-gmin-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , homeostasis-gmin-second-law-conservation-framed
  , homeostasis-gmin-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , homeostasis-gmin-admissible-ok
  , concurrent-product-ok
  , homeostasis-gmin-conservation-knowing-fiber-ok
  , homeostasis-gmin-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , homeostasis-gmin-conservation-index-seven
  , homeostasis-gmin-nuance-present-count
  , platinum-z-78
  , oganesson-z-118

homeostasisGminConservationNamed : String
homeostasisGminConservationNamed =
  "homeostasisGminConservation: constitutive homeostasis_gmin chart conservation concurrent Pi_c identity conserved local G-min equilibrium negative feedback typed homeostasis gmin chart concurrent product identity conserved present ge 2 product not XOR local G-min equilibrium typed not biology axiom not 26th axiom second law conservation only"

homeostasisGminConservationCrossWitnessAuthority : String
homeostasisGminConservationCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"

homeostasisGminChartAuthority : String
homeostasisGminChartAuthority =
  "umst/umst-chem/src/assemblage_stability.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/thermo_g.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/x_rows/assemblage_stability_why_conservation.rs"

homeostasisGminConservationCellId : String
homeostasisGminConservationCellId = "CHEM-FORMAL-Q-AGDA-HOMEOSTASIS-GMIN-CONSERVATION"

homeostasisGminConservationNonClaim : String
homeostasisGminConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-HOMEOSTASIS-GMIN-CONSERVATION constitutive homeostasis_gmin chart conservation concurrent Pi_c identity conserved local G-min equilibrium negative feedback typed homeostasis gmin chart product not XOR local G-min equilibrium typed not biology axiom not 26th axiom XOR mutually exclusive refuse homeostasis G-min nuance witness concurrent homeostasisGminProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite chem_physics_chart_isomorphism.rs assemblage_stability not fork not physics GREEN not production_wired not biology axiom"

homeostasis-gmin-conservation-cell-id :
  homeostasisGminConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-HOMEOSTASIS-GMIN-CONSERVATION"
homeostasis-gmin-conservation-cell-id = refl

homeostasis-gmin-conservation-cites-chart-isomorphism-rs :
  homeostasisGminConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"
homeostasis-gmin-conservation-cites-chart-isomorphism-rs = refl

homeostasis-gmin-conservation-cites-l0-table-rs :
  homeostasisGminChartAuthority ≡
  "umst/umst-chem/src/assemblage_stability.rs"
homeostasis-gmin-conservation-cites-l0-table-rs = refl

homeostasis-gmin-conservation-modality-unwired :
  homeostasisGminConservationModalityCurrent ≡ homeostasis-gmin-conservation-unwired
homeostasis-gmin-conservation-modality-unwired = refl

homeostasisGminConservationPhysicsGreenAuthorized : Set
homeostasisGminConservationPhysicsGreenAuthorized = ⊥

homeostasis-gmin-conservation-physics-green-false : ¬ homeostasisGminConservationPhysicsGreenAuthorized
homeostasis-gmin-conservation-physics-green-false ()

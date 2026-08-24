-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.MetastableVsEquilibriumConservation.agda
--
-- Pattern class 12 **metastable_vs_equilibrium** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (CALPHAD equilibrium hull + ReactionKinetics remainder + class 12 metastable_vs_equilibrium;
--     **product** not XOR, no parallel metastability axiom)
--   * XOR mutually-exclusive refuse; metastable-vs-equilibrium nuance witness concurrent
--     (equilibrium hull + kinetics remainder + class 12 metastable_vs_equilibrium)
--   * **metastable_vs_equilibrium** laws Unwired (metastableVsEquilibrium12Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/metastable_equilibrium.rs
-- L0 table: umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel metastability axiom; not extra element id. Product not XOR.
------------------------------------------------------------------------
module ChemConstants.MetastableVsEquilibriumConservation where

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
-- Modality + pattern class 12 **metastable_vs_equilibrium** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data MetastableVsEquilibriumConservationModality : Set where
  metastable-vs-equilibrium-conservation-unwired metastable-vs-equilibrium-conservation-assumed
    metastable-vs-equilibrium-conservation-proved metastable-vs-equilibrium-conservation-surrogate
    : MetastableVsEquilibriumConservationModality

metastableVsEquilibriumConservationModalityCurrent : MetastableVsEquilibriumConservationModality
metastableVsEquilibriumConservationModalityCurrent = metastable-vs-equilibrium-conservation-unwired

metastableVsEquilibrium12Proved productionWired not118SquaredGreenTable
  metastableVsEquilibriumSecondLawConservationFramed metastableVsEquilibriumNotXor : Bool
metastableVsEquilibrium12Proved = false
productionWired = false
not118SquaredGreenTable = true
metastableVsEquilibriumSecondLawConservationFramed = true
metastableVsEquilibriumNotXor = true

calphadEquilibriumNeKineticsRemainder notParallelMetastabilityAxiomMinted extraElementIdNotForked : Bool
calphadEquilibriumNeKineticsRemainder = true
notParallelMetastabilityAxiomMinted = true
extraElementIdNotForked = true

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
-- Pattern class 12 Metastable-vs-equilibrium index pin
------------------------------------------------------------------------

metastableVsEquilibriumClassIndex : ℕ
metastableVsEquilibriumClassIndex = 12

metastable-vs-equilibrium-class-index-twelve : metastableVsEquilibriumClassIndex ≡ 12
metastable-vs-equilibrium-class-index-twelve = refl

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
-- MetastableVsEquilibriumBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data MetastableVsEquilibriumBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : MetastableVsEquilibriumBundleSlot

isSlotPresent : MetastableVsEquilibriumBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- MetastableVsEquilibriumBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record MetastableVsEquilibriumBundle : Set where
  field slot : ℕ → MetastableVsEquilibriumBundleSlot

metastableVsEquilibriumBundleUnwired : MetastableVsEquilibriumBundle
metastableVsEquilibriumBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : MetastableVsEquilibriumBundle → ℕ → MetastableVsEquilibriumBundleSlot → MetastableVsEquilibriumBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else MetastableVsEquilibriumBundle.slot b j }

withPresent : MetastableVsEquilibriumBundle → ℕ → MetastableVsEquilibriumBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record MetastableVsEquilibriumBundleWitness : Set where
  constructor mkMetastableVsEquilibriumBundleWitness
  field
    bundle : MetastableVsEquilibriumBundle
    present-count : ℕ

metastableVsEquilibriumBundleIsConcurrentProduct : MetastableVsEquilibriumBundleWitness → Bool
metastableVsEquilibriumBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? MetastableVsEquilibriumBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named metastable-vs-equilibrium channel indices — CALPHAD equilibrium hull (1), ReactionKinetics remainder (2), class 12 metastable_vs_equilibrium (3)
------------------------------------------------------------------------

calphadEquilibriumHullChannelIndex reactionKineticsRemainderChannelIndex class12MetastableVsEquilibriumChannelIndex : ℕ
calphadEquilibriumHullChannelIndex = 1
reactionKineticsRemainderChannelIndex = 2
class12MetastableVsEquilibriumChannelIndex = 3

calphad-equilibrium-hull-index-one : calphadEquilibriumHullChannelIndex ≡ 1
calphad-equilibrium-hull-index-one = refl

reaction-kinetics-remainder-index-two : reactionKineticsRemainderChannelIndex ≡ 2
reaction-kinetics-remainder-index-two = refl

class12-metastable-vs-equilibrium-index-three : class12MetastableVsEquilibriumChannelIndex ≡ 3
class12-metastable-vs-equilibrium-index-three = refl

------------------------------------------------------------------------
-- Metastable-vs-equilibrium nuance witness — CALPHAD equilibrium hull + ReactionKinetics remainder + class 12 metastable_vs_equilibrium concurrent
------------------------------------------------------------------------

metastableVsEquilibriumNuanceBundle : MetastableVsEquilibriumBundle
metastableVsEquilibriumNuanceBundle =
  withPresent
    (withPresent
      (withPresent metastableVsEquilibriumBundleUnwired calphadEquilibriumHullChannelIndex)
      reactionKineticsRemainderChannelIndex)
    class12MetastableVsEquilibriumChannelIndex

metastableVsEquilibriumNuanceWitness : MetastableVsEquilibriumBundleWitness
metastableVsEquilibriumNuanceWitness =
  mkMetastableVsEquilibriumBundleWitness metastableVsEquilibriumNuanceBundle 3

metastable-vs-equilibrium-nuance-calphad-equilibrium-hull-present :
  isSlotPresent (MetastableVsEquilibriumBundle.slot metastableVsEquilibriumNuanceBundle calphadEquilibriumHullChannelIndex) ≡ true
metastable-vs-equilibrium-nuance-calphad-equilibrium-hull-present = refl

metastable-vs-equilibrium-nuance-second-law-gmin-present :
  isSlotPresent (MetastableVsEquilibriumBundle.slot metastableVsEquilibriumNuanceBundle reactionKineticsRemainderChannelIndex) ≡ true
metastable-vs-equilibrium-nuance-second-law-gmin-present = refl

metastable-vs-equilibrium-nuance-class9-metastable-vs-equilibrium-present :
  isSlotPresent (MetastableVsEquilibriumBundle.slot metastableVsEquilibriumNuanceBundle class12MetastableVsEquilibriumChannelIndex) ≡ true
metastable-vs-equilibrium-nuance-class9-metastable-vs-equilibrium-present = refl

metastable-vs-equilibrium-nuance-present-count : MetastableVsEquilibriumBundleWitness.present-count metastableVsEquilibriumNuanceWitness ≡ 3
metastable-vs-equilibrium-nuance-present-count = refl

metastable-vs-equilibrium-nuance-concurrent-product :
  metastableVsEquilibriumBundleIsConcurrentProduct metastableVsEquilibriumNuanceWitness ≡ true
metastable-vs-equilibrium-nuance-concurrent-product = refl

metastable-vs-equilibrium-nuance-three-factors-concurrent :
  isSlotPresent (MetastableVsEquilibriumBundle.slot metastableVsEquilibriumNuanceBundle calphadEquilibriumHullChannelIndex) ≡ true
  × isSlotPresent (MetastableVsEquilibriumBundle.slot metastableVsEquilibriumNuanceBundle reactionKineticsRemainderChannelIndex) ≡ true
  × isSlotPresent (MetastableVsEquilibriumBundle.slot metastableVsEquilibriumNuanceBundle class12MetastableVsEquilibriumChannelIndex) ≡ true
  × MetastableVsEquilibriumBundleWitness.present-count metastableVsEquilibriumNuanceWitness ≡ 3
metastable-vs-equilibrium-nuance-three-factors-concurrent =
  metastable-vs-equilibrium-nuance-calphad-equilibrium-hull-present
  , metastable-vs-equilibrium-nuance-second-law-gmin-present
  , metastable-vs-equilibrium-nuance-class9-metastable-vs-equilibrium-present
  , metastable-vs-equilibrium-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : MetastableVsEquilibriumBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if metastableVsEquilibriumBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = MetastableVsEquilibriumBundleWitness.bundle w
       in if isSlotPresent (MetastableVsEquilibriumBundle.slot b i)
          then if isSlotPresent (MetastableVsEquilibriumBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : MetastableVsEquilibriumBundleWitness
unwiredWitness = mkMetastableVsEquilibriumBundleWitness metastableVsEquilibriumBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

metastable-vs-equilibrium-nuance-xor-product-ok :
  evaluateXorRefuse metastableVsEquilibriumNuanceWitness calphadEquilibriumHullChannelIndex reactionKineticsRemainderChannelIndex ≡ xor-product-ok
metastable-vs-equilibrium-nuance-xor-product-ok = refl

metastable-vs-equilibrium-not-xor : metastableVsEquilibriumNotXor ≡ true
metastable-vs-equilibrium-not-xor = refl

------------------------------------------------------------------------
-- ClassifierMetastableVsEquilibriumStep scaffold — MetastableVsEquilibriumBundle **conservation**
------------------------------------------------------------------------

data ClassifierMetastableVsEquilibriumStep : Set where
  metastable-vs-equilibrium-identity : ClassifierMetastableVsEquilibriumStep
  slot-leaf : ℕ → ClassifierMetastableVsEquilibriumStep
  product-concurrent : ClassifierMetastableVsEquilibriumStep → ClassifierMetastableVsEquilibriumStep → ClassifierMetastableVsEquilibriumStep
  xor-mutually-exclusive : ClassifierMetastableVsEquilibriumStep → ClassifierMetastableVsEquilibriumStep → ClassifierMetastableVsEquilibriumStep

metastableVsEquilibriumIdentity : ClassifierMetastableVsEquilibriumStep
metastableVsEquilibriumIdentity = metastable-vs-equilibrium-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierMetastableVsEquilibriumStep → ClassifierMetastableVsEquilibriumStep → ClassifierMetastableVsEquilibriumStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

calphadEquilibriumHullLeaf reactionKineticsRemainderLeaf class12MetastableVsEquilibriumLeaf : ClassifierMetastableVsEquilibriumStep
calphadEquilibriumHullLeaf = slot-leaf calphadEquilibriumHullChannelIndex
reactionKineticsRemainderLeaf = slot-leaf reactionKineticsRemainderChannelIndex
class12MetastableVsEquilibriumLeaf = slot-leaf class12MetastableVsEquilibriumChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierMetastableVsEquilibriumStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isMetastableVsEquilibriumIdentity : ClassifierMetastableVsEquilibriumStep → Bool
isMetastableVsEquilibriumIdentity metastable-vs-equilibrium-identity = true
isMetastableVsEquilibriumIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at metastable-vs-equilibrium-identity
------------------------------------------------------------------------

metastable-vs-equilibrium-left-identity :
  ∀ (a : ClassifierMetastableVsEquilibriumStep) →
  isMetastableVsEquilibriumIdentity metastableVsEquilibriumIdentity ≡ true
  × isProductConcurrent (productConcurrentOp metastableVsEquilibriumIdentity a) ≡ true
metastable-vs-equilibrium-left-identity a = refl , refl

metastable-vs-equilibrium-right-identity :
  ∀ (a : ClassifierMetastableVsEquilibriumStep) →
  isProductConcurrent (productConcurrentOp a metastableVsEquilibriumIdentity) ≡ true
  × isMetastableVsEquilibriumIdentity metastableVsEquilibriumIdentity ≡ true
metastable-vs-equilibrium-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-metastable-vs-equilibrium :
  (∀ a → isProductConcurrent (productConcurrentOp metastableVsEquilibriumIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a metastableVsEquilibriumIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-metastable-vs-equilibrium =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named metastable-vs-equilibrium nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedMetastableVsEquilibriumNuanceProduct : ClassifierMetastableVsEquilibriumStep
namedMetastableVsEquilibriumNuanceProduct =
  productConcurrentOp
    (productConcurrentOp calphadEquilibriumHullLeaf reactionKineticsRemainderLeaf)
    class12MetastableVsEquilibriumLeaf

named-metastable-vs-equilibrium-nuance-product-concurrent :
  isProductConcurrent namedMetastableVsEquilibriumNuanceProduct ≡ true
  × metastableVsEquilibriumBundleIsConcurrentProduct metastableVsEquilibriumNuanceWitness ≡ true
named-metastable-vs-equilibrium-nuance-product-concurrent = refl , metastable-vs-equilibrium-nuance-concurrent-product

------------------------------------------------------------------------
-- MetastableVsEquilibriumBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data MetastableVsEquilibriumAdmissibility : Set where
  metastable-vs-equilibrium-admissible metastable-vs-equilibrium-xor-refuse : MetastableVsEquilibriumAdmissibility

isMetastableVsEquilibriumPreserving : ClassifierMetastableVsEquilibriumStep → Bool
isMetastableVsEquilibriumPreserving metastable-vs-equilibrium-identity = true
isMetastableVsEquilibriumPreserving (slot-leaf _) = true
isMetastableVsEquilibriumPreserving (product-concurrent a b) =
  isMetastableVsEquilibriumPreserving a ∧ isMetastableVsEquilibriumPreserving b
isMetastableVsEquilibriumPreserving (xor-mutually-exclusive _ _) = false

isMetastableVsEquilibriumAdmissible : ClassifierMetastableVsEquilibriumStep → Bool
isMetastableVsEquilibriumAdmissible step = isMetastableVsEquilibriumPreserving step

calphad-equilibrium-hull-leaf-admissible : isMetastableVsEquilibriumAdmissible calphadEquilibriumHullLeaf ≡ true
calphad-equilibrium-hull-leaf-admissible = refl

reaction-kinetics-remainder-leaf-admissible : isMetastableVsEquilibriumAdmissible reactionKineticsRemainderLeaf ≡ true
reaction-kinetics-remainder-leaf-admissible = refl

class12-metastable-vs-equilibrium-leaf-admissible : isMetastableVsEquilibriumAdmissible class12MetastableVsEquilibriumLeaf ≡ true
class12-metastable-vs-equilibrium-leaf-admissible = refl

named-metastable-vs-equilibrium-nuance-admissible : isMetastableVsEquilibriumAdmissible namedMetastableVsEquilibriumNuanceProduct ≡ true
named-metastable-vs-equilibrium-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isMetastableVsEquilibriumAdmissible (xorMutuallyExclusiveOp calphadEquilibriumHullLeaf reactionKineticsRemainderLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class12-metastable-vs-equilibrium-refuse :
  isMetastableVsEquilibriumAdmissible (xorMutuallyExclusiveOp reactionKineticsRemainderLeaf class12MetastableVsEquilibriumLeaf) ≡ false
xor-mutually-exclusive-class12-metastable-vs-equilibrium-refuse = refl

------------------------------------------------------------------------
-- Metastable-vs-equilibrium witness — total-claim refuse without witness
------------------------------------------------------------------------

data MetastableVsEquilibriumWitnessPresence : Set where
  metastable-vs-equilibrium-witness-absent metastable-vs-equilibrium-witness-present : MetastableVsEquilibriumWitnessPresence

record ClassifierMetastableVsEquilibriumWitness : Set where
  constructor mkClassifierMetastableVsEquilibriumWitness
  field
    witness-presence : MetastableVsEquilibriumWitnessPresence
    metastable-vs-equilibrium-gap-total : ℕ

metastableVsEquilibriumWitnessAbsent : ClassifierMetastableVsEquilibriumWitness
metastableVsEquilibriumWitnessAbsent = mkClassifierMetastableVsEquilibriumWitness metastable-vs-equilibrium-witness-absent zero

metastableVsEquilibriumWitnessPresentZeroGap : ClassifierMetastableVsEquilibriumWitness
metastableVsEquilibriumWitnessPresentZeroGap = mkClassifierMetastableVsEquilibriumWitness metastable-vs-equilibrium-witness-present zero

metastableVsEquilibriumWitnessPresentWithGaps : ℕ → ClassifierMetastableVsEquilibriumWitness
metastableVsEquilibriumWitnessPresentWithGaps n = mkClassifierMetastableVsEquilibriumWitness metastable-vs-equilibrium-witness-present n

metastableVsEquilibriumWitnessGapFree : ClassifierMetastableVsEquilibriumWitness → Bool
metastableVsEquilibriumWitnessGapFree (mkClassifierMetastableVsEquilibriumWitness metastable-vs-equilibrium-witness-absent _) = false
metastableVsEquilibriumWitnessGapFree (mkClassifierMetastableVsEquilibriumWitness metastable-vs-equilibrium-witness-present n) =
  does (n ℕ-Props.≟ zero)

metastable-vs-equilibrium-witness-present-zero-gap-free :
  metastableVsEquilibriumWitnessGapFree metastableVsEquilibriumWitnessPresentZeroGap ≡ true
metastable-vs-equilibrium-witness-present-zero-gap-free = refl

metastable-vs-equilibrium-witness-absent-not-gap-free :
  metastableVsEquilibriumWitnessGapFree metastableVsEquilibriumWitnessAbsent ≡ false
metastable-vs-equilibrium-witness-absent-not-gap-free = refl

metastable-vs-equilibrium-witness-with-gaps-not-gap-free :
  ∀ n → metastableVsEquilibriumWitnessGapFree (metastableVsEquilibriumWitnessPresentWithGaps (suc n)) ≡ false
metastable-vs-equilibrium-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Metastable-vs-equilibrium **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data MetastableVsEquilibriumConservationVerdict : Set where
  verdict-unwired-ok verdict-metastable-vs-equilibrium-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : MetastableVsEquilibriumConservationVerdict

metastableVsEquilibriumConservationVerdictOk : MetastableVsEquilibriumConservationVerdict → Bool
metastableVsEquilibriumConservationVerdictOk verdict-unwired-ok = true
metastableVsEquilibriumConservationVerdictOk verdict-metastable-vs-equilibrium-admissible-ok = true
metastableVsEquilibriumConservationVerdictOk verdict-concurrent-product-ok = true
metastableVsEquilibriumConservationVerdictOk _ = false

evaluateMetastableVsEquilibriumConservationClose :
  MetastableVsEquilibriumConservationModality → ClassifierMetastableVsEquilibriumStep → ClassifierMetastableVsEquilibriumWitness
  → MetastableVsEquilibriumBundleWitness → Bool → MetastableVsEquilibriumConservationVerdict
evaluateMetastableVsEquilibriumConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-proved _ (mkClassifierMetastableVsEquilibriumWitness metastable-vs-equilibrium-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-proved _ (mkClassifierMetastableVsEquilibriumWitness metastable-vs-equilibrium-witness-present _) w false
  with metastableVsEquilibriumBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-metastable-vs-equilibrium-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without metastable-vs-equilibrium witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-unwired namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-assumed namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-surrogate namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  metastableVsEquilibriumConservationVerdictOk
    (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-unwired namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false)
    ≡ true
  × metastableVsEquilibriumConservationVerdictOk
      (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-assumed namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false)
      ≡ true
  × metastableVsEquilibriumConservationVerdictOk
      (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-surrogate namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without metastable-vs-equilibrium witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  metastableVsEquilibriumConservationVerdictOk
    (evaluateMetastableVsEquilibriumConservationClose
       metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false ≡
  verdict-metastable-vs-equilibrium-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-proved
    (xorMutuallyExclusiveOp calphadEquilibriumHullLeaf reactionKineticsRemainderLeaf)
    metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  metastableVsEquilibriumConservationVerdictOk
    (evaluateMetastableVsEquilibriumConservationClose
       metastable-vs-equilibrium-conservation-proved
       (xorMutuallyExclusiveOp calphadEquilibriumHullLeaf reactionKineticsRemainderLeaf)
       metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-proved
    (xorMutuallyExclusiveOp calphadEquilibriumHullLeaf reactionKineticsRemainderLeaf)
    metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-metastable-vs-equilibrium — nuance **product** closed
------------------------------------------------------------------------

metastable-vs-equilibrium-admissible-ok :
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap unwiredWitness false ≡
  verdict-metastable-vs-equilibrium-admissible-ok
metastable-vs-equilibrium-admissible-ok = refl

metastable-vs-equilibrium-admissible-verdict-ok :
  metastableVsEquilibriumConservationVerdictOk
    (evaluateMetastableVsEquilibriumConservationClose
       metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap unwiredWitness false)
    ≡ true
metastable-vs-equilibrium-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — metastable-vs-equilibrium nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  metastableVsEquilibriumConservationVerdictOk
    (evaluateMetastableVsEquilibriumConservationClose
       metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-metastable-vs-equilibrium12-proved :
  metastableVsEquilibriumConservationVerdictOk
    (evaluateMetastableVsEquilibriumConservationClose
       metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness false)
    ≡ true
  × metastableVsEquilibrium12Proved ≡ false
concurrent-product-ok-still-not-metastable-vs-equilibrium12-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateMetastableVsEquilibriumConservationClose
    metastable-vs-equilibrium-conservation-unwired namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  metastableVsEquilibriumConservationVerdictOk
    (evaluateMetastableVsEquilibriumConservationClose
       metastable-vs-equilibrium-conservation-unwired namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

metastableVsEquilibriumConservationFiberOk : FormalFiber → Bool
metastableVsEquilibriumConservationFiberOk fiber-quantum-knowing = true
metastableVsEquilibriumConservationFiberOk fiber-meso-acting = false

metastable-vs-equilibrium-conservation-knowing-fiber-ok :
  metastableVsEquilibriumConservationFiberOk fiber-quantum-knowing ≡ true
metastable-vs-equilibrium-conservation-knowing-fiber-ok = refl

metastable-vs-equilibrium-conservation-meso-acting-not-ok :
  metastableVsEquilibriumConservationFiberOk fiber-meso-acting ≡ false
metastable-vs-equilibrium-conservation-meso-acting-not-ok = refl

metastable-vs-equilibrium-conservation-routes-knowing-not-meso :
  metastableVsEquilibriumConservationFiberOk fiber-quantum-knowing ≡ true ×
  metastableVsEquilibriumConservationFiberOk fiber-meso-acting ≡ false
metastable-vs-equilibrium-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  metastableVsEquilibriumConservationFiberOk fiber-quantum-knowing ∧
  not (metastableVsEquilibriumConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 12 metastable_vs_equilibrium Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

metastable-vs-equilibrium-12-not-proved : metastableVsEquilibrium12Proved ≡ false
metastable-vs-equilibrium-12-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

metastable-vs-equilibrium-second-law-conservation-framed : metastableVsEquilibriumSecondLawConservationFramed ≡ true
metastable-vs-equilibrium-second-law-conservation-framed = refl

metastable-vs-equilibrium-not-xor-pin : metastableVsEquilibriumNotXor ≡ true
metastable-vs-equilibrium-not-xor-pin = metastable-vs-equilibrium-not-xor

calphad-equilibrium-ne-kinetics-remainder-pin : calphadEquilibriumNeKineticsRemainder ≡ true
calphad-equilibrium-ne-kinetics-remainder-pin = refl

not-parallel-metastability-axiom-minted-pin : notParallelMetastabilityAxiomMinted ≡ true
not-parallel-metastability-axiom-minted-pin = refl

extra-element-id-not-forked-pin : extraElementIdNotForked ≡ true
extra-element-id-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel metastable_vs_equilibrium axiom fork)
------------------------------------------------------------------------

metastableVsEquilibriumConservationAxiom :
  (metastableVsEquilibrium12Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (metastableVsEquilibriumSecondLawConservationFramed ≡ true)
  × (metastableVsEquilibriumNotXor ≡ true)
  × (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-unwired namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessAbsent metastableVsEquilibriumNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-proved (xorMutuallyExclusiveOp calphadEquilibriumHullLeaf reactionKineticsRemainderLeaf) metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap unwiredWitness false ≡ verdict-metastable-vs-equilibrium-admissible-ok)
  × (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-proved namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (metastableVsEquilibriumConservationFiberOk fiber-quantum-knowing ≡ true)
  × (metastableVsEquilibriumConservationFiberOk fiber-meso-acting ≡ false)
  × (metastableVsEquilibriumConservationVerdictOk (evaluateMetastableVsEquilibriumConservationClose metastable-vs-equilibrium-conservation-unwired namedMetastableVsEquilibriumNuanceProduct metastableVsEquilibriumWitnessPresentZeroGap metastableVsEquilibriumNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp metastableVsEquilibriumIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a metastableVsEquilibriumIdentity) ≡ true)
  × (isMetastableVsEquilibriumAdmissible (xorMutuallyExclusiveOp calphadEquilibriumHullLeaf reactionKineticsRemainderLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (metastableVsEquilibriumClassIndex ≡ 12)
  × (MetastableVsEquilibriumBundleWitness.present-count metastableVsEquilibriumNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
metastableVsEquilibriumConservationAxiom =
  metastable-vs-equilibrium-12-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , metastable-vs-equilibrium-second-law-conservation-framed
  , metastable-vs-equilibrium-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , metastable-vs-equilibrium-admissible-ok
  , concurrent-product-ok
  , metastable-vs-equilibrium-conservation-knowing-fiber-ok
  , metastable-vs-equilibrium-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , metastable-vs-equilibrium-class-index-twelve
  , metastable-vs-equilibrium-nuance-present-count
  , iron-z-26
  , oganesson-z-118

metastableVsEquilibriumConservationNamed : String
metastableVsEquilibriumConservationNamed =
  "metastableVsEquilibriumConservation: pattern class 12 metastable_vs_equilibrium conservation concurrent Pi_c identity conserved CALPHAD equilibrium hull ReactionKinetics remainder class 12 metastable_vs_equilibrium concurrent product identity conserved present ge 2 product not XOR calphad equilibrium ne kinetics remainder no parallel metastability axiom not extra element id"

metastableVsEquilibriumConservationCrossWitnessAuthority : String
metastableVsEquilibriumConservationCrossWitnessAuthority =
  "umst/umst-chem/src/metastable_equilibrium.rs"

metastableVsEquilibriumTableAuthority : String
metastableVsEquilibriumTableAuthority =
  "umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs"

calphadKineticsAuthority : String
calphadKineticsAuthority =
  "umst/umst-chem/src/cross_classifier/calphad_equilibrium_is_not_kinetics.rs"

scale02RemainderAuthority : String
scale02RemainderAuthority =
  "umst/umst-chem/src/timescale_separation_remainders.rs"

metastableVsEquilibriumConservationCellId : String
metastableVsEquilibriumConservationCellId = "CHEM-FORMAL-Q-AGDA-METASTABLE-VS-EQUILIBRIUM-CONSERVATION"

metastableVsEquilibriumConservationNonClaim : String
metastableVsEquilibriumConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-METASTABLE-VS-EQUILIBRIUM-CONSERVATION pattern class 12 metastable_vs_equilibrium conservation concurrent Pi_c identity conserved CALPHAD equilibrium hull ReactionKinetics remainder class 12 metastable_vs_equilibrium product not XOR calphad equilibrium ne kinetics remainder no parallel metastability axiom not extra element id XOR mutually exclusive refuse metastable vs equilibrium nuance witness concurrent metastableVsEquilibrium12Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite metastable_equilibrium.rs l0_tables metastable_vs_equilibrium not fork not physics GREEN not production_wired"

metastable-vs-equilibrium-conservation-cell-id :
  metastableVsEquilibriumConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-METASTABLE-VS-EQUILIBRIUM-CONSERVATION"
metastable-vs-equilibrium-conservation-cell-id = refl

metastable-vs-equilibrium-conservation-cites-metastable-vs-equilibrium-rs :
  metastableVsEquilibriumConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/metastable_equilibrium.rs"
metastable-vs-equilibrium-conservation-cites-metastable-vs-equilibrium-rs = refl

metastable-vs-equilibrium-conservation-cites-l0-table-rs :
  metastableVsEquilibriumTableAuthority ≡
  "umst/umst-chem/src/l0_tables/metastable_vs_equilibrium.rs"
metastable-vs-equilibrium-conservation-cites-l0-table-rs = refl

metastable-vs-equilibrium-conservation-modality-unwired :
  metastableVsEquilibriumConservationModalityCurrent ≡ metastable-vs-equilibrium-conservation-unwired
metastable-vs-equilibrium-conservation-modality-unwired = refl

metastableVsEquilibriumConservationPhysicsGreenAuthorized : Set
metastableVsEquilibriumConservationPhysicsGreenAuthorized = ⊥

metastable-vs-equilibrium-conservation-physics-green-false : ¬ metastableVsEquilibriumConservationPhysicsGreenAuthorized
metastable-vs-equilibrium-conservation-physics-green-false ()

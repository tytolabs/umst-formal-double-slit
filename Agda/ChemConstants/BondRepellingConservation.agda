-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.BondRepellingConservation.agda
--
-- PATTERN-00 PatternBundle **bond-repelling** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (cardinality 25; ≥2 Present is **concurrent product** not XOR)
--   * XOR mutually-exclusive refuse; Pauli/steric + Ore-blocking TYPE-05 partiality witness concurrent
--   * Exchange repulsion ≠ 26th chemistry axiom; not a parallel bond-repelling axiom
--   * **bond-repelling** laws Unwired (class03BondRepellingProved = false)
--
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- INT: umst/umst-chem/src/x_rows/bond_repelling_conservation.rs
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.BondRepellingConservation where

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
-- Modality + PATTERN-00 PatternBundle **bond-repelling** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data BondRepellingConservationModality : Set where
  bond-repelling-conservation-unwired bond-repelling-conservation-assumed
    bond-repelling-conservation-proved bond-repelling-conservation-surrogate
    : BondRepellingConservationModality

bondRepellingConservationModalityCurrent : BondRepellingConservationModality
bondRepellingConservationModalityCurrent = bond-repelling-conservation-unwired

class03BondRepellingProved productionWired not118SquaredGreenTable
  patternSecondLawConservationFramed concurrentPiCNotXor
  refuse26thChemAxiom type05PartialityNamed : Bool
class03BondRepellingProved = false
productionWired = false
not118SquaredGreenTable = true
patternSecondLawConservationFramed = true
concurrentPiCNotXor = true
refuse26thChemAxiom = true
type05PartialityNamed = true

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
-- Named element Z pins — H (Z=1), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  hydrogen oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ hydrogen = 1
elementAtomicZ oganesson = 118

hydrogen-z-1 : elementAtomicZ hydrogen ≡ 1
hydrogen-z-1 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- PatternBundle slot modality — concurrent **bond-repelling** factor, not XOR bucket
------------------------------------------------------------------------

data PatternBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PatternBundleSlot

isSlotPresent : PatternBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- PatternBundle_25 — many classes may hold at once (Π_c **concurrent product**)
------------------------------------------------------------------------

record PatternBundle : Set where
  field slot : ℕ → PatternBundleSlot

patternBundleUnwired : PatternBundle
patternBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : PatternBundle → ℕ → PatternBundleSlot → PatternBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else PatternBundle.slot b j }

withPresent : PatternBundle → ℕ → PatternBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **bond-repelling** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PatternBundleWitness : Set where
  constructor mkPatternBundleWitness
  field
    bundle : PatternBundle
    present-count : ℕ

patternBundleIsConcurrentProduct : PatternBundleWitness → Bool
patternBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PatternBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named pattern class indices — bond-repelling (3), Pauli/steric (4), Ore-blocking (5)
------------------------------------------------------------------------

bondRepellingClassIndex pauliStericPartialIndex oreBlockingPartialIndex : ℕ
bondRepellingClassIndex = 3
pauliStericPartialIndex = 4
oreBlockingPartialIndex = 5

bond-repelling-index-three : bondRepellingClassIndex ≡ 3
bond-repelling-index-three = refl

pauli-steric-partial-index-four : pauliStericPartialIndex ≡ 4
pauli-steric-partial-index-four = refl

ore-blocking-partial-index-five : oreBlockingPartialIndex ≡ 5
ore-blocking-partial-index-five = refl

------------------------------------------------------------------------
-- Bond-repelling nuance witness — class 3 + Pauli/steric + Ore-blocking concurrent
------------------------------------------------------------------------

bondRepellingNuanceBundle : PatternBundle
bondRepellingNuanceBundle =
  withPresent
    (withPresent
      (withPresent patternBundleUnwired bondRepellingClassIndex)
      pauliStericPartialIndex)
    oreBlockingPartialIndex

bondRepellingNuanceWitness : PatternBundleWitness
bondRepellingNuanceWitness =
  mkPatternBundleWitness bondRepellingNuanceBundle 3

bond-repelling-nuance-class-present :
  isSlotPresent (PatternBundle.slot bondRepellingNuanceBundle bondRepellingClassIndex) ≡ true
bond-repelling-nuance-class-present = refl

bond-repelling-nuance-pauli-steric-present :
  isSlotPresent (PatternBundle.slot bondRepellingNuanceBundle pauliStericPartialIndex) ≡ true
bond-repelling-nuance-pauli-steric-present = refl

bond-repelling-nuance-ore-blocking-present :
  isSlotPresent (PatternBundle.slot bondRepellingNuanceBundle oreBlockingPartialIndex) ≡ true
bond-repelling-nuance-ore-blocking-present = refl

bond-repelling-nuance-present-count : PatternBundleWitness.present-count bondRepellingNuanceWitness ≡ 3
bond-repelling-nuance-present-count = refl

bond-repelling-nuance-concurrent-product :
  patternBundleIsConcurrentProduct bondRepellingNuanceWitness ≡ true
bond-repelling-nuance-concurrent-product = refl

bond-repelling-nuance-three-factors-concurrent :
  isSlotPresent (PatternBundle.slot bondRepellingNuanceBundle bondRepellingClassIndex) ≡ true
  × isSlotPresent (PatternBundle.slot bondRepellingNuanceBundle pauliStericPartialIndex) ≡ true
  × isSlotPresent (PatternBundle.slot bondRepellingNuanceBundle oreBlockingPartialIndex) ≡ true
  × PatternBundleWitness.present-count bondRepellingNuanceWitness ≡ 3
bond-repelling-nuance-three-factors-concurrent =
  bond-repelling-nuance-class-present
  , bond-repelling-nuance-pauli-steric-present
  , bond-repelling-nuance-ore-blocking-present
  , bond-repelling-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PatternBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if patternBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = PatternBundleWitness.bundle w
       in if isSlotPresent (PatternBundle.slot b i)
          then if isSlotPresent (PatternBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PatternBundleWitness
unwiredWitness = mkPatternBundleWitness patternBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

bond-repelling-nuance-xor-product-ok :
  evaluateXorRefuse bondRepellingNuanceWitness bondRepellingClassIndex pauliStericPartialIndex ≡ xor-product-ok
bond-repelling-nuance-xor-product-ok = refl

concurrent-pi-c-not-xor : concurrentPiCNotXor ≡ true
concurrent-pi-c-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPatternStep scaffold — PatternBundle **bond-repelling** **conservation**
------------------------------------------------------------------------

data ClassifierPatternStep : Set where
  pattern-identity : ClassifierPatternStep
  slot-leaf : ℕ → ClassifierPatternStep
  product-concurrent : ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep
  xor-mutually-exclusive : ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep

patternIdentity : ClassifierPatternStep
patternIdentity = pattern-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPatternStep → ClassifierPatternStep → ClassifierPatternStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

bondRepellingLeaf pauliStericLeaf oreBlockingLeaf : ClassifierPatternStep
bondRepellingLeaf = slot-leaf bondRepellingClassIndex
pauliStericLeaf = slot-leaf pauliStericPartialIndex
oreBlockingLeaf = slot-leaf oreBlockingPartialIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierPatternStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isPatternIdentity : ClassifierPatternStep → Bool
isPatternIdentity pattern-identity = true
isPatternIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at pattern-identity
------------------------------------------------------------------------

pattern-left-identity :
  ∀ (a : ClassifierPatternStep) →
  isPatternIdentity patternIdentity ≡ true
  × isProductConcurrent (productConcurrentOp patternIdentity a) ≡ true
pattern-left-identity a = refl , refl

pattern-right-identity :
  ∀ (a : ClassifierPatternStep) →
  isProductConcurrent (productConcurrentOp a patternIdentity) ≡ true
  × isPatternIdentity patternIdentity ≡ true
pattern-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-pattern :
  (∀ a → isProductConcurrent (productConcurrentOp patternIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a patternIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-pattern =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named bond-repelling nuance **concurrent** closed — concurrent classifiers
------------------------------------------------------------------------

namedBondRepellingNuanceConcurrent : ClassifierPatternStep
namedBondRepellingNuanceConcurrent =
  productConcurrentOp
    (productConcurrentOp bondRepellingLeaf pauliStericLeaf)
    oreBlockingLeaf

named-bond-repelling-nuance-product-concurrent :
  isProductConcurrent namedBondRepellingNuanceConcurrent ≡ true
  × patternBundleIsConcurrentProduct bondRepellingNuanceWitness ≡ true
named-bond-repelling-nuance-product-concurrent = refl , bond-repelling-nuance-concurrent-product

------------------------------------------------------------------------
-- PatternBundle **bond-repelling** admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data BondRepellingAdmissibility : Set where
  bond-repelling-admissible bond-repelling-xor-refuse : BondRepellingAdmissibility

isPatternPreserving : ClassifierPatternStep → Bool
isPatternPreserving pattern-identity = true
isPatternPreserving (slot-leaf _) = true
isPatternPreserving (product-concurrent a b) =
  isPatternPreserving a ∧ isPatternPreserving b
isPatternPreserving (xor-mutually-exclusive _ _) = false

isBondRepellingAdmissible : ClassifierPatternStep → Bool
isBondRepellingAdmissible step = isPatternPreserving step

bond-repelling-leaf-admissible : isBondRepellingAdmissible bondRepellingLeaf ≡ true
bond-repelling-leaf-admissible = refl

pauli-steric-leaf-admissible : isBondRepellingAdmissible pauliStericLeaf ≡ true
pauli-steric-leaf-admissible = refl

ore-blocking-leaf-admissible : isBondRepellingAdmissible oreBlockingLeaf ≡ true
ore-blocking-leaf-admissible = refl

named-bond-repelling-nuance-admissible : isBondRepellingAdmissible namedBondRepellingNuanceConcurrent ≡ true
named-bond-repelling-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isBondRepellingAdmissible (xorMutuallyExclusiveOp bondRepellingLeaf pauliStericLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-continuum-refuse :
  isBondRepellingAdmissible (xorMutuallyExclusiveOp pauliStericLeaf oreBlockingLeaf) ≡ false
xor-mutually-exclusive-continuum-refuse = refl

------------------------------------------------------------------------
-- PatternBundle witness — total-claim refuse without witness
------------------------------------------------------------------------

data PatternWitnessPresence : Set where
  pattern-witness-absent pattern-witness-present : PatternWitnessPresence

record ClassifierPatternWitness : Set where
  constructor mkClassifierPatternWitness
  field
    witness-presence : PatternWitnessPresence
    pattern-gap-total : ℕ

patternWitnessAbsent : ClassifierPatternWitness
patternWitnessAbsent = mkClassifierPatternWitness pattern-witness-absent zero

patternWitnessPresentZeroGap : ClassifierPatternWitness
patternWitnessPresentZeroGap = mkClassifierPatternWitness pattern-witness-present zero

patternWitnessPresentWithGaps : ℕ → ClassifierPatternWitness
patternWitnessPresentWithGaps n = mkClassifierPatternWitness pattern-witness-present n

patternWitnessGapFree : ClassifierPatternWitness → Bool
patternWitnessGapFree (mkClassifierPatternWitness pattern-witness-absent _) = false
patternWitnessGapFree (mkClassifierPatternWitness pattern-witness-present n) =
  does (n ℕ-Props.≟ zero)

pattern-witness-present-zero-gap-free :
  patternWitnessGapFree patternWitnessPresentZeroGap ≡ true
pattern-witness-present-zero-gap-free = refl

pattern-witness-absent-not-gap-free :
  patternWitnessGapFree patternWitnessAbsent ≡ false
pattern-witness-absent-not-gap-free = refl

pattern-witness-with-gaps-not-gap-free :
  ∀ n → patternWitnessGapFree (patternWitnessPresentWithGaps (suc n)) ≡ false
pattern-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-PATTERN-00 **bond-repelling** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data BondRepellingConservationVerdict : Set where
  verdict-unwired-ok verdict-bond-repelling-admissible-ok
    verdict-concurrent-bond-repelling-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : BondRepellingConservationVerdict

bondRepellingConservationVerdictOk : BondRepellingConservationVerdict → Bool
bondRepellingConservationVerdictOk verdict-unwired-ok = true
bondRepellingConservationVerdictOk verdict-bond-repelling-admissible-ok = true
bondRepellingConservationVerdictOk verdict-concurrent-bond-repelling-ok = true
bondRepellingConservationVerdictOk _ = false

evaluateBondRepellingConservationClose :
  BondRepellingConservationModality → ClassifierPatternStep → ClassifierPatternWitness
  → PatternBundleWitness → Bool → BondRepellingConservationVerdict
evaluateBondRepellingConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateBondRepellingConservationClose bond-repelling-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateBondRepellingConservationClose bond-repelling-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateBondRepellingConservationClose bond-repelling-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateBondRepellingConservationClose bond-repelling-conservation-proved _ (mkClassifierPatternWitness pattern-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateBondRepellingConservationClose bond-repelling-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateBondRepellingConservationClose bond-repelling-conservation-proved _ (mkClassifierPatternWitness pattern-witness-present _) w false
  with patternBundleIsConcurrentProduct w
... | true  = verdict-concurrent-bond-repelling-ok
... | false = verdict-bond-repelling-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without pattern witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-unwired namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-assumed namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-surrogate namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  bondRepellingConservationVerdictOk
    (evaluateBondRepellingConservationClose bond-repelling-conservation-unwired namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false)
    ≡ true
  × bondRepellingConservationVerdictOk
      (evaluateBondRepellingConservationClose bond-repelling-conservation-assumed namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false)
      ≡ true
  × bondRepellingConservationVerdictOk
      (evaluateBondRepellingConservationClose bond-repelling-conservation-surrogate namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without pattern witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  bondRepellingConservationVerdictOk
    (evaluateBondRepellingConservationClose
       bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false ≡
  verdict-bond-repelling-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-proved
    (xorMutuallyExclusiveOp bondRepellingLeaf pauliStericLeaf)
    patternWitnessPresentZeroGap bondRepellingNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  bondRepellingConservationVerdictOk
    (evaluateBondRepellingConservationClose
       bond-repelling-conservation-proved
       (xorMutuallyExclusiveOp bondRepellingLeaf pauliStericLeaf)
       patternWitnessPresentZeroGap bondRepellingNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-proved
    (xorMutuallyExclusiveOp bondRepellingLeaf pauliStericLeaf)
    patternWitnessPresentZeroGap bondRepellingNuanceWitness false ≡
  verdict-concurrent-bond-repelling-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-pattern — bond-repelling nuance **concurrent** closed
------------------------------------------------------------------------

bond-repelling-admissible-ok :
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap unwiredWitness false ≡
  verdict-bond-repelling-admissible-ok
bond-repelling-admissible-ok = refl

bond-repelling-admissible-verdict-ok :
  bondRepellingConservationVerdictOk
    (evaluateBondRepellingConservationClose
       bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap unwiredWitness false)
    ≡ true
bond-repelling-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **bond-repelling** ok — bond-repelling nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-bond-repelling-ok :
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap bondRepellingNuanceWitness false ≡
  verdict-concurrent-bond-repelling-ok
concurrent-bond-repelling-ok = refl

concurrent-bond-repelling-verdict-ok :
  bondRepellingConservationVerdictOk
    (evaluateBondRepellingConservationClose
       bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap bondRepellingNuanceWitness false)
    ≡ true
concurrent-bond-repelling-verdict-ok = refl

concurrent-bond-repelling-ok-still-not-pattern00-proved :
  bondRepellingConservationVerdictOk
    (evaluateBondRepellingConservationClose
       bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap bondRepellingNuanceWitness false)
    ≡ true
  × class03BondRepellingProved ≡ false
concurrent-bond-repelling-ok-still-not-pattern00-proved = concurrent-bond-repelling-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateBondRepellingConservationClose
    bond-repelling-conservation-unwired namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap bondRepellingNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  bondRepellingConservationVerdictOk
    (evaluateBondRepellingConservationClose
       bond-repelling-conservation-unwired namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap bondRepellingNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

bondRepellingConservationFiberOk : FormalFiber → Bool
bondRepellingConservationFiberOk fiber-quantum-knowing = true
bondRepellingConservationFiberOk fiber-meso-acting = false

bond-repelling-conservation-knowing-fiber-ok :
  bondRepellingConservationFiberOk fiber-quantum-knowing ≡ true
bond-repelling-conservation-knowing-fiber-ok = refl

bond-repelling-conservation-meso-acting-not-ok :
  bondRepellingConservationFiberOk fiber-meso-acting ≡ false
bond-repelling-conservation-meso-acting-not-ok = refl

bond-repelling-conservation-routes-knowing-not-meso :
  bondRepellingConservationFiberOk fiber-quantum-knowing ≡ true ×
  bondRepellingConservationFiberOk fiber-meso-acting ≡ false
bond-repelling-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  bondRepellingConservationFiberOk fiber-quantum-knowing ∧
  not (bondRepellingConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class-3 Proved, not physics GREEN, concurrent Π_c not XOR, not 26th law
------------------------------------------------------------------------

class03-bond-repelling-not-proved : class03BondRepellingProved ≡ false
class03-bond-repelling-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

pattern-second-law-conservation-framed : patternSecondLawConservationFramed ≡ true
pattern-second-law-conservation-framed = refl

concurrent-pi-c-not-xor-pin : concurrentPiCNotXor ≡ true
concurrent-pi-c-not-xor-pin = concurrent-pi-c-not-xor

refuse-26th-chem-axiom : refuse26thChemAxiom ≡ true
refuse-26th-chem-axiom = refl

type05-partiality-named : type05PartialityNamed ≡ true
type05-partiality-named = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second PATTERN-00 axiom fork)
------------------------------------------------------------------------

bondRepellingConservationAxiom :
  (class03BondRepellingProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (patternSecondLawConservationFramed ≡ true)
  × (concurrentPiCNotXor ≡ true)
  × (refuse26thChemAxiom ≡ true)
  × (type05PartialityNamed ≡ true)
  × (evaluateBondRepellingConservationClose bond-repelling-conservation-unwired namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateBondRepellingConservationClose bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessAbsent bondRepellingNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateBondRepellingConservationClose bond-repelling-conservation-proved (xorMutuallyExclusiveOp bondRepellingLeaf pauliStericLeaf) patternWitnessPresentZeroGap bondRepellingNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateBondRepellingConservationClose bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap unwiredWitness false ≡ verdict-bond-repelling-admissible-ok)
  × (evaluateBondRepellingConservationClose bond-repelling-conservation-proved namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap bondRepellingNuanceWitness false ≡ verdict-concurrent-bond-repelling-ok)
  × (bondRepellingConservationFiberOk fiber-quantum-knowing ≡ true)
  × (bondRepellingConservationFiberOk fiber-meso-acting ≡ false)
  × (bondRepellingConservationVerdictOk (evaluateBondRepellingConservationClose bond-repelling-conservation-unwired namedBondRepellingNuanceConcurrent patternWitnessPresentZeroGap bondRepellingNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp patternIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a patternIdentity) ≡ true)
  × (isBondRepellingAdmissible (xorMutuallyExclusiveOp bondRepellingLeaf pauliStericLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (PatternBundleWitness.present-count bondRepellingNuanceWitness ≡ 3)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oganesson ≡ 118)
  × (bondRepellingClassIndex ≡ 3)
bondRepellingConservationAxiom =
  class03-bond-repelling-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , pattern-second-law-conservation-framed
  , concurrent-pi-c-not-xor-pin
  , refuse-26th-chem-axiom
  , type05-partiality-named
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , bond-repelling-admissible-ok
  , concurrent-bond-repelling-ok
  , bond-repelling-conservation-knowing-fiber-ok
  , bond-repelling-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , bond-repelling-nuance-present-count
  , hydrogen-z-1
  , oganesson-z-118
  , bond-repelling-index-three

bondRepellingConservationNamed : String
bondRepellingConservationNamed =
  "bondRepellingConservation: PATTERN-00 PatternBundle bond-repelling conservation concurrent Pi_c identity conserved class 3 Pauli steric TYPE-05 partiality not 26th law XOR refuse"


type05PartialityAuthority : String
type05PartialityAuthority = "umst/umst-chem/src/interact_partiality.rs"

l0BondRepellingTableAuthority : String
l0BondRepellingTableAuthority = "umst/umst-chem/src/l0_tables/bond_repelling.rs"

bondRepellingConservationCrossWitnessAuthority : String
bondRepellingConservationCrossWitnessAuthority =
  "umst/umst-chem/src/x_rows/bond_repelling_conservation.rs"

bond-repelling-conservation-cites-cross-witness-rs :
  bondRepellingConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/x_rows/bond_repelling_conservation.rs"
bond-repelling-conservation-cites-cross-witness-rs = refl

bond-repelling-conservation-cites-type05-partiality :
  type05PartialityAuthority ≡
  "umst/umst-chem/src/interact_partiality.rs"
bond-repelling-conservation-cites-type05-partiality = refl

bondRepellingConservationCellId : String
bondRepellingConservationCellId = "CHEM-FORMAL-Q-AGDA-BOND-REPELLING-CONSERVATION"

bondRepellingConservationNonClaim : String
bondRepellingConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-BOND-REPELLING-CONSERVATION PATTERN-00 PatternBundle bond-repelling conservation concurrent Pi_c identity conserved cardinality 25 class 3 Pauli steric Ore blocking TYPE-05 partiality not 26th chem axiom concurrentPiCNotXor class03BondRepellingProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not 26th chemistry axiom not second PATTERN axiom not physics GREEN not production_wired"

bond-repelling-conservation-modality-unwired :
  bondRepellingConservationModalityCurrent ≡ bond-repelling-conservation-unwired
bond-repelling-conservation-modality-unwired = refl

bondRepellingConservationPhysicsGreenAuthorized : Set
bondRepellingConservationPhysicsGreenAuthorized = ⊥

bond-repelling-conservation-physics-green-false : ¬ bondRepellingConservationPhysicsGreenAuthorized
bond-repelling-conservation-physics-green-false ()

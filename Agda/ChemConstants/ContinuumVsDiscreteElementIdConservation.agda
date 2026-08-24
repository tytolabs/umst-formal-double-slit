-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ContinuumVsDiscreteElementIdConservation.agda
--
-- Pattern class 23 **continuum_vs_discrete_element_id** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (continuum field presentation + discrete ElementId presentation + class 23 continuum_vs_discrete_element_id;
--     **product** not XOR, no parallel continuum_vs_discrete_element_id axiom)
--   * XOR mutually-exclusive refuse; continuum-vs-discrete ElementId nuance witness concurrent
--     (continuum field presentation + discrete ElementId presentation + class 23 continuum_vs_discrete_element_id)
--   * **continuum_vs_discrete_element_id** laws Unwired (continuumVsDiscrete23Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/continuum_discrete_element.rs
-- L0 table: umst/umst-chem/src/l0_tables/continuum_vs_discrete_element_id.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel continuum_vs_discrete_element_id axiom; conflation not forked. Product not XOR.
-- Class 23 continuum_vs_discrete_element_id as two presentations not two chemistries; conflation refuse-closed.
------------------------------------------------------------------------
module ChemConstants.ContinuumVsDiscreteElementIdConservation where


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
-- Modality + pattern class 23 **continuum_vs_discrete_element_id** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ContinuumVsDiscreteElementIdConservationModality : Set where
  continuum-vs-discrete-element-id-conservation-unwired continuum-vs-discrete-element-id-conservation-assumed
    continuum-vs-discrete-element-id-conservation-proved continuum-vs-discrete-element-id-conservation-surrogate
    : ContinuumVsDiscreteElementIdConservationModality

continuumVsDiscreteElementIdConservationModalityCurrent : ContinuumVsDiscreteElementIdConservationModality
continuumVsDiscreteElementIdConservationModalityCurrent = continuum-vs-discrete-element-id-conservation-unwired

continuumVsDiscrete23Proved productionWired not118SquaredGreenTable
  continuumVsDiscreteSecondLawConservationFramed continuumVsDiscreteNotXor : Bool
continuumVsDiscrete23Proved = false
productionWired = false
not118SquaredGreenTable = true
continuumVsDiscreteSecondLawConservationFramed = true
continuumVsDiscreteNotXor = true

continuumFieldDistinct notParallelContinuumDiscreteAxiomMinted conflationNotForked : Bool
continuumFieldDistinct = true
notParallelContinuumDiscreteAxiomMinted = true
conflationNotForked = true

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
-- Pattern class 23 Continuum-vs-discrete-ElementId index pin
------------------------------------------------------------------------

continuumVsDiscreteClassIndex : ℕ
continuumVsDiscreteClassIndex = 23

continuum-vs-discrete-class-index-twenty-three : continuumVsDiscreteClassIndex ≡ 23
continuum-vs-discrete-class-index-twenty-three = refl

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
-- ContinuumVsDiscreteBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data ContinuumVsDiscreteBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : ContinuumVsDiscreteBundleSlot

isSlotPresent : ContinuumVsDiscreteBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- ContinuumVsDiscreteBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record ContinuumVsDiscreteBundle : Set where
  field slot : ℕ → ContinuumVsDiscreteBundleSlot

continuumVsDiscreteBundleUnwired : ContinuumVsDiscreteBundle
continuumVsDiscreteBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : ContinuumVsDiscreteBundle → ℕ → ContinuumVsDiscreteBundleSlot → ContinuumVsDiscreteBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else ContinuumVsDiscreteBundle.slot b j }

withPresent : ContinuumVsDiscreteBundle → ℕ → ContinuumVsDiscreteBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record ContinuumVsDiscreteBundleWitness : Set where
  constructor mkContinuumVsDiscreteBundleWitness
  field
    bundle : ContinuumVsDiscreteBundle
    present-count : ℕ

continuumVsDiscreteBundleIsConcurrentProduct : ContinuumVsDiscreteBundleWitness → Bool
continuumVsDiscreteBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? ContinuumVsDiscreteBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named continuum-vs-discrete channel indices — continuum field presentation (1), discrete ElementId presentation (2), class 23 continuum_vs_discrete_element_id (3)
------------------------------------------------------------------------

continuumFieldPresentationChannelIndex discreteElementIdPresentationChannelIndex class23ContinuumVsDiscreteChannelIndex : ℕ
continuumFieldPresentationChannelIndex = 1
discreteElementIdPresentationChannelIndex = 2
class23ContinuumVsDiscreteChannelIndex = 3

continuum-field-presentation-index-one : continuumFieldPresentationChannelIndex ≡ 1
continuum-field-presentation-index-one = refl

discrete-element-id-presentation-index-two : discreteElementIdPresentationChannelIndex ≡ 2
discrete-element-id-presentation-index-two = refl

class23-continuum-vs-discrete-index-three : class23ContinuumVsDiscreteChannelIndex ≡ 3
class23-continuum-vs-discrete-index-three = refl

------------------------------------------------------------------------
-- Continuum-vs-discrete nuance witness — continuum field + discrete ElementId + class 23 concurrent
------------------------------------------------------------------------

continuumVsDiscreteNuanceBundle : ContinuumVsDiscreteBundle
continuumVsDiscreteNuanceBundle =
  withPresent
    (withPresent
      (withPresent continuumVsDiscreteBundleUnwired continuumFieldPresentationChannelIndex)
      discreteElementIdPresentationChannelIndex)
    class23ContinuumVsDiscreteChannelIndex

continuumVsDiscreteNuanceWitness : ContinuumVsDiscreteBundleWitness
continuumVsDiscreteNuanceWitness =
  mkContinuumVsDiscreteBundleWitness continuumVsDiscreteNuanceBundle 3

continuum-vs-discrete-nuance-continuum-field-present :
  isSlotPresent (ContinuumVsDiscreteBundle.slot continuumVsDiscreteNuanceBundle continuumFieldPresentationChannelIndex) ≡ true
continuum-vs-discrete-nuance-continuum-field-present = refl

continuum-vs-discrete-nuance-discrete-element-id-present :
  isSlotPresent (ContinuumVsDiscreteBundle.slot continuumVsDiscreteNuanceBundle discreteElementIdPresentationChannelIndex) ≡ true
continuum-vs-discrete-nuance-discrete-element-id-present = refl

continuum-vs-discrete-nuance-class23-continuum-vs-discrete-present :
  isSlotPresent (ContinuumVsDiscreteBundle.slot continuumVsDiscreteNuanceBundle class23ContinuumVsDiscreteChannelIndex) ≡ true
continuum-vs-discrete-nuance-class23-continuum-vs-discrete-present = refl

continuum-vs-discrete-nuance-present-count : ContinuumVsDiscreteBundleWitness.present-count continuumVsDiscreteNuanceWitness ≡ 3
continuum-vs-discrete-nuance-present-count = refl

continuum-vs-discrete-nuance-concurrent-product :
  continuumVsDiscreteBundleIsConcurrentProduct continuumVsDiscreteNuanceWitness ≡ true
continuum-vs-discrete-nuance-concurrent-product = refl

continuum-vs-discrete-nuance-three-factors-concurrent :
  isSlotPresent (ContinuumVsDiscreteBundle.slot continuumVsDiscreteNuanceBundle continuumFieldPresentationChannelIndex) ≡ true
  × isSlotPresent (ContinuumVsDiscreteBundle.slot continuumVsDiscreteNuanceBundle discreteElementIdPresentationChannelIndex) ≡ true
  × isSlotPresent (ContinuumVsDiscreteBundle.slot continuumVsDiscreteNuanceBundle class23ContinuumVsDiscreteChannelIndex) ≡ true
  × ContinuumVsDiscreteBundleWitness.present-count continuumVsDiscreteNuanceWitness ≡ 3
continuum-vs-discrete-nuance-three-factors-concurrent =
  continuum-vs-discrete-nuance-continuum-field-present
  , continuum-vs-discrete-nuance-discrete-element-id-present
  , continuum-vs-discrete-nuance-class23-continuum-vs-discrete-present
  , continuum-vs-discrete-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : ContinuumVsDiscreteBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if continuumVsDiscreteBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = ContinuumVsDiscreteBundleWitness.bundle w
       in if isSlotPresent (ContinuumVsDiscreteBundle.slot b i)
          then if isSlotPresent (ContinuumVsDiscreteBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : ContinuumVsDiscreteBundleWitness
unwiredWitness = mkContinuumVsDiscreteBundleWitness continuumVsDiscreteBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

continuum-vs-discrete-nuance-xor-product-ok :
  evaluateXorRefuse continuumVsDiscreteNuanceWitness continuumFieldPresentationChannelIndex discreteElementIdPresentationChannelIndex ≡ xor-product-ok
continuum-vs-discrete-nuance-xor-product-ok = refl

continuum-vs-discrete-not-xor : continuumVsDiscreteNotXor ≡ true
continuum-vs-discrete-not-xor = refl

------------------------------------------------------------------------
-- ClassifierContinuumVsDiscreteStep scaffold — ContinuumVsDiscreteBundle **conservation**
------------------------------------------------------------------------

data ClassifierContinuumVsDiscreteStep : Set where
  continuum-vs-discrete-identity : ClassifierContinuumVsDiscreteStep
  slot-leaf : ℕ → ClassifierContinuumVsDiscreteStep
  product-concurrent : ClassifierContinuumVsDiscreteStep → ClassifierContinuumVsDiscreteStep → ClassifierContinuumVsDiscreteStep
  xor-mutually-exclusive : ClassifierContinuumVsDiscreteStep → ClassifierContinuumVsDiscreteStep → ClassifierContinuumVsDiscreteStep

continuumVsDiscreteIdentity : ClassifierContinuumVsDiscreteStep
continuumVsDiscreteIdentity = continuum-vs-discrete-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierContinuumVsDiscreteStep → ClassifierContinuumVsDiscreteStep → ClassifierContinuumVsDiscreteStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

continuumFieldPresentationLeaf discreteElementIdPresentationLeaf class23ContinuumVsDiscreteLeaf : ClassifierContinuumVsDiscreteStep
continuumFieldPresentationLeaf = slot-leaf continuumFieldPresentationChannelIndex
discreteElementIdPresentationLeaf = slot-leaf discreteElementIdPresentationChannelIndex
class23ContinuumVsDiscreteLeaf = slot-leaf class23ContinuumVsDiscreteChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierContinuumVsDiscreteStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isContinuumVsDiscreteIdentity : ClassifierContinuumVsDiscreteStep → Bool
isContinuumVsDiscreteIdentity continuum-vs-discrete-identity = true
isContinuumVsDiscreteIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at continuum-vs-discrete-identity
------------------------------------------------------------------------

continuum-vs-discrete-left-identity :
  ∀ (a : ClassifierContinuumVsDiscreteStep) →
  isContinuumVsDiscreteIdentity continuumVsDiscreteIdentity ≡ true
  × isProductConcurrent (productConcurrentOp continuumVsDiscreteIdentity a) ≡ true
continuum-vs-discrete-left-identity a = refl , refl

continuum-vs-discrete-right-identity :
  ∀ (a : ClassifierContinuumVsDiscreteStep) →
  isProductConcurrent (productConcurrentOp a continuumVsDiscreteIdentity) ≡ true
  × isContinuumVsDiscreteIdentity continuumVsDiscreteIdentity ≡ true
continuum-vs-discrete-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-continuum-vs-discrete :
  (∀ a → isProductConcurrent (productConcurrentOp continuumVsDiscreteIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a continuumVsDiscreteIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-continuum-vs-discrete =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named continuum-vs-discrete nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedContinuumVsDiscreteNuanceProduct : ClassifierContinuumVsDiscreteStep
namedContinuumVsDiscreteNuanceProduct =
  productConcurrentOp
    (productConcurrentOp continuumFieldPresentationLeaf discreteElementIdPresentationLeaf)
    class23ContinuumVsDiscreteLeaf

named-continuum-vs-discrete-nuance-product-concurrent :
  isProductConcurrent namedContinuumVsDiscreteNuanceProduct ≡ true
  × continuumVsDiscreteBundleIsConcurrentProduct continuumVsDiscreteNuanceWitness ≡ true
named-continuum-vs-discrete-nuance-product-concurrent = refl , continuum-vs-discrete-nuance-concurrent-product

------------------------------------------------------------------------
-- ContinuumVsDiscreteBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data ContinuumVsDiscreteAdmissibility : Set where
  continuum-vs-discrete-admissible continuum-vs-discrete-xor-refuse : ContinuumVsDiscreteAdmissibility

isContinuumVsDiscretePreserving : ClassifierContinuumVsDiscreteStep → Bool
isContinuumVsDiscretePreserving continuum-vs-discrete-identity = true
isContinuumVsDiscretePreserving (slot-leaf _) = true
isContinuumVsDiscretePreserving (product-concurrent a b) =
  isContinuumVsDiscretePreserving a ∧ isContinuumVsDiscretePreserving b
isContinuumVsDiscretePreserving (xor-mutually-exclusive _ _) = false

isContinuumVsDiscreteAdmissible : ClassifierContinuumVsDiscreteStep → Bool
isContinuumVsDiscreteAdmissible step = isContinuumVsDiscretePreserving step

continuum-field-presentation-leaf-admissible : isContinuumVsDiscreteAdmissible continuumFieldPresentationLeaf ≡ true
continuum-field-presentation-leaf-admissible = refl

discrete-element-id-presentation-leaf-admissible : isContinuumVsDiscreteAdmissible discreteElementIdPresentationLeaf ≡ true
discrete-element-id-presentation-leaf-admissible = refl

class23-continuum-vs-discrete-leaf-admissible : isContinuumVsDiscreteAdmissible class23ContinuumVsDiscreteLeaf ≡ true
class23-continuum-vs-discrete-leaf-admissible = refl

named-continuum-vs-discrete-nuance-admissible : isContinuumVsDiscreteAdmissible namedContinuumVsDiscreteNuanceProduct ≡ true
named-continuum-vs-discrete-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isContinuumVsDiscreteAdmissible (xorMutuallyExclusiveOp continuumFieldPresentationLeaf discreteElementIdPresentationLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class23-continuum-vs-discrete-refuse :
  isContinuumVsDiscreteAdmissible (xorMutuallyExclusiveOp discreteElementIdPresentationLeaf class23ContinuumVsDiscreteLeaf) ≡ false
xor-mutually-exclusive-class23-continuum-vs-discrete-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data ContinuumVsDiscreteWitnessPresence : Set where
  continuum-vs-discrete-witness-absent continuum-vs-discrete-witness-present : ContinuumVsDiscreteWitnessPresence

record ClassifierContinuumVsDiscreteWitness : Set where
  constructor mkClassifierContinuumVsDiscreteWitness
  field
    witness-presence : ContinuumVsDiscreteWitnessPresence
    continuum-vs-discrete-gap-total : ℕ

continuumVsDiscreteWitnessAbsent : ClassifierContinuumVsDiscreteWitness
continuumVsDiscreteWitnessAbsent = mkClassifierContinuumVsDiscreteWitness continuum-vs-discrete-witness-absent zero

continuumVsDiscreteWitnessPresentZeroGap : ClassifierContinuumVsDiscreteWitness
continuumVsDiscreteWitnessPresentZeroGap = mkClassifierContinuumVsDiscreteWitness continuum-vs-discrete-witness-present zero

continuumVsDiscreteWitnessPresentWithGaps : ℕ → ClassifierContinuumVsDiscreteWitness
continuumVsDiscreteWitnessPresentWithGaps n = mkClassifierContinuumVsDiscreteWitness continuum-vs-discrete-witness-present n

continuumVsDiscreteWitnessGapFree : ClassifierContinuumVsDiscreteWitness → Bool
continuumVsDiscreteWitnessGapFree (mkClassifierContinuumVsDiscreteWitness continuum-vs-discrete-witness-absent _) = false
continuumVsDiscreteWitnessGapFree (mkClassifierContinuumVsDiscreteWitness continuum-vs-discrete-witness-present n) =
  does (n ℕ-Props.≟ zero)

continuum-vs-discrete-witness-present-zero-gap-free :
  continuumVsDiscreteWitnessGapFree continuumVsDiscreteWitnessPresentZeroGap ≡ true
continuum-vs-discrete-witness-present-zero-gap-free = refl

continuum-vs-discrete-witness-absent-not-gap-free :
  continuumVsDiscreteWitnessGapFree continuumVsDiscreteWitnessAbsent ≡ false
continuum-vs-discrete-witness-absent-not-gap-free = refl

continuum-vs-discrete-witness-with-gaps-not-gap-free :
  ∀ n → continuumVsDiscreteWitnessGapFree (continuumVsDiscreteWitnessPresentWithGaps (suc n)) ≡ false
continuum-vs-discrete-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-continuum-vs-discrete **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data ContinuumVsDiscreteElementIdConservationVerdict : Set where
  verdict-unwired-ok verdict-continuum-vs-discrete-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : ContinuumVsDiscreteElementIdConservationVerdict

continuumVsDiscreteElementIdConservationVerdictOk : ContinuumVsDiscreteElementIdConservationVerdict → Bool
continuumVsDiscreteElementIdConservationVerdictOk verdict-unwired-ok = true
continuumVsDiscreteElementIdConservationVerdictOk verdict-continuum-vs-discrete-admissible-ok = true
continuumVsDiscreteElementIdConservationVerdictOk verdict-concurrent-product-ok = true
continuumVsDiscreteElementIdConservationVerdictOk _ = false

evaluateContinuumVsDiscreteElementIdConservationClose :
  ContinuumVsDiscreteElementIdConservationModality → ClassifierContinuumVsDiscreteStep → ClassifierContinuumVsDiscreteWitness
  → ContinuumVsDiscreteBundleWitness → Bool → ContinuumVsDiscreteElementIdConservationVerdict
evaluateContinuumVsDiscreteElementIdConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-proved _ (mkClassifierContinuumVsDiscreteWitness continuum-vs-discrete-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-proved _ (mkClassifierContinuumVsDiscreteWitness continuum-vs-discrete-witness-present _) w false
  with continuumVsDiscreteBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-continuum-vs-discrete-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without continuum-vs-discrete witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-unwired namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-assumed namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-surrogate namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  continuumVsDiscreteElementIdConservationVerdictOk
    (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-unwired namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false)
    ≡ true
  × continuumVsDiscreteElementIdConservationVerdictOk
      (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-assumed namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false)
      ≡ true
  × continuumVsDiscreteElementIdConservationVerdictOk
      (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-surrogate namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without continuum-vs-discrete witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  continuumVsDiscreteElementIdConservationVerdictOk
    (evaluateContinuumVsDiscreteElementIdConservationClose
       continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false ≡
  verdict-continuum-vs-discrete-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-proved
    (xorMutuallyExclusiveOp continuumFieldPresentationLeaf discreteElementIdPresentationLeaf)
    continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  continuumVsDiscreteElementIdConservationVerdictOk
    (evaluateContinuumVsDiscreteElementIdConservationClose
       continuum-vs-discrete-element-id-conservation-proved
       (xorMutuallyExclusiveOp continuumFieldPresentationLeaf discreteElementIdPresentationLeaf)
       continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-proved
    (xorMutuallyExclusiveOp continuumFieldPresentationLeaf discreteElementIdPresentationLeaf)
    continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-continuum-vs-discrete — nuance **product** closed
------------------------------------------------------------------------

continuum-vs-discrete-admissible-ok :
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap unwiredWitness false ≡
  verdict-continuum-vs-discrete-admissible-ok
continuum-vs-discrete-admissible-ok = refl

continuum-vs-discrete-admissible-verdict-ok :
  continuumVsDiscreteElementIdConservationVerdictOk
    (evaluateContinuumVsDiscreteElementIdConservationClose
       continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap unwiredWitness false)
    ≡ true
continuum-vs-discrete-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — continuum-vs-discrete nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  continuumVsDiscreteElementIdConservationVerdictOk
    (evaluateContinuumVsDiscreteElementIdConservationClose
       continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-continuum-vs-discrete23-proved :
  continuumVsDiscreteElementIdConservationVerdictOk
    (evaluateContinuumVsDiscreteElementIdConservationClose
       continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness false)
    ≡ true
  × continuumVsDiscrete23Proved ≡ false
concurrent-product-ok-still-not-continuum-vs-discrete23-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateContinuumVsDiscreteElementIdConservationClose
    continuum-vs-discrete-element-id-conservation-unwired namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  continuumVsDiscreteElementIdConservationVerdictOk
    (evaluateContinuumVsDiscreteElementIdConservationClose
       continuum-vs-discrete-element-id-conservation-unwired namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

continuumVsDiscreteElementIdConservationFiberOk : FormalFiber → Bool
continuumVsDiscreteElementIdConservationFiberOk fiber-quantum-knowing = true
continuumVsDiscreteElementIdConservationFiberOk fiber-meso-acting = false

continuum-vs-discrete-element-id-conservation-knowing-fiber-ok :
  continuumVsDiscreteElementIdConservationFiberOk fiber-quantum-knowing ≡ true
continuum-vs-discrete-element-id-conservation-knowing-fiber-ok = refl

continuum-vs-discrete-element-id-conservation-meso-acting-not-ok :
  continuumVsDiscreteElementIdConservationFiberOk fiber-meso-acting ≡ false
continuum-vs-discrete-element-id-conservation-meso-acting-not-ok = refl

continuum-vs-discrete-element-id-conservation-routes-knowing-not-meso :
  continuumVsDiscreteElementIdConservationFiberOk fiber-quantum-knowing ≡ true ×
  continuumVsDiscreteElementIdConservationFiberOk fiber-meso-acting ≡ false
continuum-vs-discrete-element-id-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  continuumVsDiscreteElementIdConservationFiberOk fiber-quantum-knowing ∧
  not (continuumVsDiscreteElementIdConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 23 continuum_vs_discrete_element_id Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

continuum-vs-discrete-23-not-proved : continuumVsDiscrete23Proved ≡ false
continuum-vs-discrete-23-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

continuum-vs-discrete-second-law-conservation-framed : continuumVsDiscreteSecondLawConservationFramed ≡ true
continuum-vs-discrete-second-law-conservation-framed = refl

continuum-vs-discrete-not-xor-pin : continuumVsDiscreteNotXor ≡ true
continuum-vs-discrete-not-xor-pin = continuum-vs-discrete-not-xor

continuum-field-distinct-pin : continuumFieldDistinct ≡ true
continuum-field-distinct-pin = refl

not-parallel-continuum-discrete-axiom-minted-pin : notParallelContinuumDiscreteAxiomMinted ≡ true
not-parallel-continuum-discrete-axiom-minted-pin = refl

conflation-not-forked-pin : conflationNotForked ≡ true
conflation-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel continuum_vs_discrete_element_id axiom fork)
------------------------------------------------------------------------

continuumVsDiscreteElementIdConservationAxiom :
  (continuumVsDiscrete23Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (continuumVsDiscreteSecondLawConservationFramed ≡ true)
  × (continuumVsDiscreteNotXor ≡ true)
  × (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-unwired namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessAbsent continuumVsDiscreteNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-proved (xorMutuallyExclusiveOp continuumFieldPresentationLeaf discreteElementIdPresentationLeaf) continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap unwiredWitness false ≡ verdict-continuum-vs-discrete-admissible-ok)
  × (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-proved namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (continuumVsDiscreteElementIdConservationFiberOk fiber-quantum-knowing ≡ true)
  × (continuumVsDiscreteElementIdConservationFiberOk fiber-meso-acting ≡ false)
  × (continuumVsDiscreteElementIdConservationVerdictOk (evaluateContinuumVsDiscreteElementIdConservationClose continuum-vs-discrete-element-id-conservation-unwired namedContinuumVsDiscreteNuanceProduct continuumVsDiscreteWitnessPresentZeroGap continuumVsDiscreteNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp continuumVsDiscreteIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a continuumVsDiscreteIdentity) ≡ true)
  × (isContinuumVsDiscreteAdmissible (xorMutuallyExclusiveOp continuumFieldPresentationLeaf discreteElementIdPresentationLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (continuumVsDiscreteClassIndex ≡ 23)
  × (ContinuumVsDiscreteBundleWitness.present-count continuumVsDiscreteNuanceWitness ≡ 3)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oganesson ≡ 118)
continuumVsDiscreteElementIdConservationAxiom =
  continuum-vs-discrete-23-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , continuum-vs-discrete-second-law-conservation-framed
  , continuum-vs-discrete-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , continuum-vs-discrete-admissible-ok
  , concurrent-product-ok
  , continuum-vs-discrete-element-id-conservation-knowing-fiber-ok
  , continuum-vs-discrete-element-id-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , continuum-vs-discrete-class-index-twenty-three
  , continuum-vs-discrete-nuance-present-count
  , hydrogen-z-1
  , oganesson-z-118

continuumVsDiscreteElementIdConservationNamed : String
continuumVsDiscreteElementIdConservationNamed =
  "continuumVsDiscreteElementIdConservation: pattern class 23 continuum_vs_discrete_element_id conservation concurrent Pi_c identity conserved continuum field presentation discrete ElementId presentation class 23 continuum_vs_discrete_element_id concurrent product identity conserved present ge 2 product not XOR continuum field distinct no parallel continuum_vs_discrete_element_id axiom conflation not forked"

continuumVsDiscreteElementIdConservationCrossWitnessAuthority : String
continuumVsDiscreteElementIdConservationCrossWitnessAuthority =
  "umst/umst-chem/src/continuum_discrete_element.rs"

continuumVsDiscreteTableAuthority : String
continuumVsDiscreteTableAuthority =
  "umst/umst-chem/src/l0_tables/continuum_vs_discrete_element_id.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

continuumVsDiscreteElementIdConservationCellId : String
continuumVsDiscreteElementIdConservationCellId = "CHEM-FORMAL-Q-AGDA-CONTINUUM-VS-DISCRETE-ELEMENT-ID-CONSERVATION"

continuumVsDiscreteElementIdConservationNonClaim : String
continuumVsDiscreteElementIdConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-CONTINUUM-VS-DISCRETE-ELEMENT-ID-CONSERVATION pattern class 23 continuum_vs_discrete_element_id conservation concurrent Pi_c identity conserved continuum field presentation discrete ElementId presentation class 23 continuum_vs_discrete_element_id product not XOR continuum field distinct no parallel continuum_vs_discrete_element_id axiom conflation not forked XOR mutually exclusive refuse continuum-vs-discrete nuance witness concurrent continuumVsDiscrete23Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite continuum_discrete_element.rs l0_tables continuum_vs_discrete_element_id not fork not physics GREEN not production_wired"

continuum-vs-discrete-element-id-conservation-cell-id :
  continuumVsDiscreteElementIdConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-CONTINUUM-VS-DISCRETE-ELEMENT-ID-CONSERVATION"
continuum-vs-discrete-element-id-conservation-cell-id = refl

continuum-vs-discrete-element-id-conservation-cites-continuum-discrete-element-rs :
  continuumVsDiscreteElementIdConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/continuum_discrete_element.rs"
continuum-vs-discrete-element-id-conservation-cites-continuum-discrete-element-rs = refl

continuum-vs-discrete-element-id-conservation-cites-l0-table-rs :
  continuumVsDiscreteTableAuthority ≡
  "umst/umst-chem/src/l0_tables/continuum_vs_discrete_element_id.rs"
continuum-vs-discrete-element-id-conservation-cites-l0-table-rs = refl

continuum-vs-discrete-element-id-conservation-modality-unwired :
  continuumVsDiscreteElementIdConservationModalityCurrent ≡ continuum-vs-discrete-element-id-conservation-unwired
continuum-vs-discrete-element-id-conservation-modality-unwired = refl

continuumVsDiscreteElementIdConservationPhysicsGreenAuthorized : Set
continuumVsDiscreteElementIdConservationPhysicsGreenAuthorized = ⊥

continuum-vs-discrete-element-id-conservation-physics-green-false : ¬ continuumVsDiscreteElementIdConservationPhysicsGreenAuthorized
continuum-vs-discrete-element-id-conservation-physics-green-false ()

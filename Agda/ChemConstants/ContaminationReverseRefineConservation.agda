-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ContaminationReverseRefineConservation.agda
--
-- Pattern class 20 **contamination_reverse_refine** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (reverse Refine direction + inverse morphism typed + class 20 contamination_reverse_refine;
--     **product** not XOR, no parallel contamination axiom)
--   * XOR mutually-exclusive refuse; contamination-reverse-refine nuance witness concurrent
--     (reverse Refine direction + inverse morphism typed + class 20 contamination_reverse_refine)
--   * **contamination_reverse_refine** laws Unwired (contaminationReverseRefine20Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/contamination_reverse_refine.rs
-- L0 table: umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel contamination axiom; free purification not forked. Product not XOR.
-- Class 20 contamination_reverse_refine as reverse Refine direction, inverse morphism typed.
------------------------------------------------------------------------
module ChemConstants.ContaminationReverseRefineConservation where


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
-- Modality + pattern class 20 **contamination_reverse_refine** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ContaminationReverseRefineConservationModality : Set where
  contamination-reverse-refine-conservation-unwired contamination-reverse-refine-conservation-assumed
    contamination-reverse-refine-conservation-proved contamination-reverse-refine-conservation-surrogate
    : ContaminationReverseRefineConservationModality

contaminationReverseRefineConservationModalityCurrent : ContaminationReverseRefineConservationModality
contaminationReverseRefineConservationModalityCurrent = contamination-reverse-refine-conservation-unwired

contaminationReverseRefine20Proved productionWired not118SquaredGreenTable
  contaminationReverseRefineSecondLawConservationFramed contaminationReverseRefineNotXor : Bool
contaminationReverseRefine20Proved = false
productionWired = false
not118SquaredGreenTable = true
contaminationReverseRefineSecondLawConservationFramed = true
contaminationReverseRefineNotXor = true

reverseRefineDirectionTyped notParallelContaminationAxiomMinted freePurificationNotForked : Bool
reverseRefineDirectionTyped = true
notParallelContaminationAxiomMinted = true
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
-- Pattern class 20 Catalysis index pin
------------------------------------------------------------------------

contaminationReverseRefineClassIndex : ℕ
contaminationReverseRefineClassIndex = 20

contamination-reverse-refine-class-index-twenty : contaminationReverseRefineClassIndex ≡ 20
contamination-reverse-refine-class-index-twenty = refl

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
-- ContaminationReverseRefineBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data ContaminationReverseRefineBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : ContaminationReverseRefineBundleSlot

isSlotPresent : ContaminationReverseRefineBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- ContaminationReverseRefineBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record ContaminationReverseRefineBundle : Set where
  field slot : ℕ → ContaminationReverseRefineBundleSlot

contaminationReverseRefineBundleUnwired : ContaminationReverseRefineBundle
contaminationReverseRefineBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : ContaminationReverseRefineBundle → ℕ → ContaminationReverseRefineBundleSlot → ContaminationReverseRefineBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else ContaminationReverseRefineBundle.slot b j }

withPresent : ContaminationReverseRefineBundle → ℕ → ContaminationReverseRefineBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record ContaminationReverseRefineBundleWitness : Set where
  constructor mkContaminationReverseRefineBundleWitness
  field
    bundle : ContaminationReverseRefineBundle
    present-count : ℕ

contaminationReverseRefineBundleIsConcurrentProduct : ContaminationReverseRefineBundleWitness → Bool
contaminationReverseRefineBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? ContaminationReverseRefineBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named contamination-reverse-refine channel indices — reverse Refine direction (1), inverse morphism typed (2), class 20 contamination_reverse_refine (3)
------------------------------------------------------------------------

reverseRefineDirectionChannelIndex inverseMorphismTypedChannelIndex class20ContaminationReverseRefineChannelIndex : ℕ
reverseRefineDirectionChannelIndex = 1
inverseMorphismTypedChannelIndex = 2
class20ContaminationReverseRefineChannelIndex = 3

reverse-refine-direction-index-one : reverseRefineDirectionChannelIndex ≡ 1
reverse-refine-direction-index-one = refl

inverse-morphism-typed-index-two : inverseMorphismTypedChannelIndex ≡ 2
inverse-morphism-typed-index-two = refl

class20-contamination-reverse-refine-index-three : class20ContaminationReverseRefineChannelIndex ≡ 3
class20-contamination-reverse-refine-index-three = refl

------------------------------------------------------------------------
-- Contamination-reverse-refine nuance witness — reverse Refine direction + inverse morphism typed + class 20 contamination_reverse_refine concurrent
------------------------------------------------------------------------

contaminationReverseRefineNuanceBundle : ContaminationReverseRefineBundle
contaminationReverseRefineNuanceBundle =
  withPresent
    (withPresent
      (withPresent contaminationReverseRefineBundleUnwired reverseRefineDirectionChannelIndex)
      inverseMorphismTypedChannelIndex)
    class20ContaminationReverseRefineChannelIndex

contaminationReverseRefineNuanceWitness : ContaminationReverseRefineBundleWitness
contaminationReverseRefineNuanceWitness =
  mkContaminationReverseRefineBundleWitness contaminationReverseRefineNuanceBundle 3

contamination-reverse-refine-nuance-reverse-refine-direction-present :
  isSlotPresent (ContaminationReverseRefineBundle.slot contaminationReverseRefineNuanceBundle reverseRefineDirectionChannelIndex) ≡ true
contamination-reverse-refine-nuance-reverse-refine-direction-present = refl

contamination-reverse-refine-nuance-inverse-morphism-present :
  isSlotPresent (ContaminationReverseRefineBundle.slot contaminationReverseRefineNuanceBundle inverseMorphismTypedChannelIndex) ≡ true
contamination-reverse-refine-nuance-inverse-morphism-present = refl

contamination-reverse-refine-nuance-class20-present :
  isSlotPresent (ContaminationReverseRefineBundle.slot contaminationReverseRefineNuanceBundle class20ContaminationReverseRefineChannelIndex) ≡ true
contamination-reverse-refine-nuance-class20-present = refl

contamination-reverse-refine-nuance-present-count : ContaminationReverseRefineBundleWitness.present-count contaminationReverseRefineNuanceWitness ≡ 3
contamination-reverse-refine-nuance-present-count = refl

contamination-reverse-refine-nuance-concurrent-product :
  contaminationReverseRefineBundleIsConcurrentProduct contaminationReverseRefineNuanceWitness ≡ true
contamination-reverse-refine-nuance-concurrent-product = refl

contamination-reverse-refine-nuance-three-factors-concurrent :
  isSlotPresent (ContaminationReverseRefineBundle.slot contaminationReverseRefineNuanceBundle reverseRefineDirectionChannelIndex) ≡ true
  × isSlotPresent (ContaminationReverseRefineBundle.slot contaminationReverseRefineNuanceBundle inverseMorphismTypedChannelIndex) ≡ true
  × isSlotPresent (ContaminationReverseRefineBundle.slot contaminationReverseRefineNuanceBundle class20ContaminationReverseRefineChannelIndex) ≡ true
  × ContaminationReverseRefineBundleWitness.present-count contaminationReverseRefineNuanceWitness ≡ 3
contamination-reverse-refine-nuance-three-factors-concurrent =
  contamination-reverse-refine-nuance-reverse-refine-direction-present
  , contamination-reverse-refine-nuance-inverse-morphism-present
  , contamination-reverse-refine-nuance-class20-present
  , contamination-reverse-refine-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : ContaminationReverseRefineBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if contaminationReverseRefineBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = ContaminationReverseRefineBundleWitness.bundle w
       in if isSlotPresent (ContaminationReverseRefineBundle.slot b i)
          then if isSlotPresent (ContaminationReverseRefineBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : ContaminationReverseRefineBundleWitness
unwiredWitness = mkContaminationReverseRefineBundleWitness contaminationReverseRefineBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

contamination-reverse-refine-nuance-xor-product-ok :
  evaluateXorRefuse contaminationReverseRefineNuanceWitness reverseRefineDirectionChannelIndex inverseMorphismTypedChannelIndex ≡ xor-product-ok
contamination-reverse-refine-nuance-xor-product-ok = refl

contamination-reverse-refine-not-xor : contaminationReverseRefineNotXor ≡ true
contamination-reverse-refine-not-xor = refl

------------------------------------------------------------------------
-- ClassifierContaminationReverseRefineStep scaffold — ContaminationReverseRefineBundle **conservation**
------------------------------------------------------------------------

data ClassifierContaminationReverseRefineStep : Set where
  contamination-reverse-refine-identity : ClassifierContaminationReverseRefineStep
  slot-leaf : ℕ → ClassifierContaminationReverseRefineStep
  product-concurrent : ClassifierContaminationReverseRefineStep → ClassifierContaminationReverseRefineStep → ClassifierContaminationReverseRefineStep
  xor-mutually-exclusive : ClassifierContaminationReverseRefineStep → ClassifierContaminationReverseRefineStep → ClassifierContaminationReverseRefineStep

contaminationReverseRefineIdentity : ClassifierContaminationReverseRefineStep
contaminationReverseRefineIdentity = contamination-reverse-refine-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierContaminationReverseRefineStep → ClassifierContaminationReverseRefineStep → ClassifierContaminationReverseRefineStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

reverseRefineDirectionLeaf inverseMorphismTypedLeaf class20ContaminationReverseRefineLeaf : ClassifierContaminationReverseRefineStep
reverseRefineDirectionLeaf = slot-leaf reverseRefineDirectionChannelIndex
inverseMorphismTypedLeaf = slot-leaf inverseMorphismTypedChannelIndex
class20ContaminationReverseRefineLeaf = slot-leaf class20ContaminationReverseRefineChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierContaminationReverseRefineStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isContaminationReverseRefineIdentity : ClassifierContaminationReverseRefineStep → Bool
isContaminationReverseRefineIdentity contamination-reverse-refine-identity = true
isContaminationReverseRefineIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at contamination-reverse-refine-identity
------------------------------------------------------------------------

contamination-reverse-refine-left-identity :
  ∀ (a : ClassifierContaminationReverseRefineStep) →
  isContaminationReverseRefineIdentity contaminationReverseRefineIdentity ≡ true
  × isProductConcurrent (productConcurrentOp contaminationReverseRefineIdentity a) ≡ true
contamination-reverse-refine-left-identity a = refl , refl

contamination-reverse-refine-right-identity :
  ∀ (a : ClassifierContaminationReverseRefineStep) →
  isProductConcurrent (productConcurrentOp a contaminationReverseRefineIdentity) ≡ true
  × isContaminationReverseRefineIdentity contaminationReverseRefineIdentity ≡ true
contamination-reverse-refine-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-contamination-reverse-refine :
  (∀ a → isProductConcurrent (productConcurrentOp contaminationReverseRefineIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a contaminationReverseRefineIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-contamination-reverse-refine =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named contamination-reverse-refine nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedContaminationReverseRefineNuanceProduct : ClassifierContaminationReverseRefineStep
namedContaminationReverseRefineNuanceProduct =
  productConcurrentOp
    (productConcurrentOp reverseRefineDirectionLeaf inverseMorphismTypedLeaf)
    class20ContaminationReverseRefineLeaf

named-contamination-reverse-refine-nuance-product-concurrent :
  isProductConcurrent namedContaminationReverseRefineNuanceProduct ≡ true
  × contaminationReverseRefineBundleIsConcurrentProduct contaminationReverseRefineNuanceWitness ≡ true
named-contamination-reverse-refine-nuance-product-concurrent = refl , contamination-reverse-refine-nuance-concurrent-product

------------------------------------------------------------------------
-- ContaminationReverseRefineBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data ContaminationReverseRefineAdmissibility : Set where
  contamination-reverse-refine-admissible contamination-reverse-refine-xor-refuse : ContaminationReverseRefineAdmissibility

isContaminationReverseRefinePreserving : ClassifierContaminationReverseRefineStep → Bool
isContaminationReverseRefinePreserving contamination-reverse-refine-identity = true
isContaminationReverseRefinePreserving (slot-leaf _) = true
isContaminationReverseRefinePreserving (product-concurrent a b) =
  isContaminationReverseRefinePreserving a ∧ isContaminationReverseRefinePreserving b
isContaminationReverseRefinePreserving (xor-mutually-exclusive _ _) = false

isContaminationReverseRefineAdmissible : ClassifierContaminationReverseRefineStep → Bool
isContaminationReverseRefineAdmissible step = isContaminationReverseRefinePreserving step

reverse-refine-direction-leaf-admissible : isContaminationReverseRefineAdmissible reverseRefineDirectionLeaf ≡ true
reverse-refine-direction-leaf-admissible = refl

inverse-morphism-typed-leaf-admissible : isContaminationReverseRefineAdmissible inverseMorphismTypedLeaf ≡ true
inverse-morphism-typed-leaf-admissible = refl

class20-contamination-reverse-refine-leaf-admissible : isContaminationReverseRefineAdmissible class20ContaminationReverseRefineLeaf ≡ true
class20-contamination-reverse-refine-leaf-admissible = refl

named-contamination-reverse-refine-nuance-admissible : isContaminationReverseRefineAdmissible namedContaminationReverseRefineNuanceProduct ≡ true
named-contamination-reverse-refine-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isContaminationReverseRefineAdmissible (xorMutuallyExclusiveOp reverseRefineDirectionLeaf inverseMorphismTypedLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class20-contamination-reverse-refine-refuse :
  isContaminationReverseRefineAdmissible (xorMutuallyExclusiveOp inverseMorphismTypedLeaf class20ContaminationReverseRefineLeaf) ≡ false
xor-mutually-exclusive-class20-contamination-reverse-refine-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data ContaminationReverseRefineWitnessPresence : Set where
  contamination-reverse-refine-witness-absent contamination-reverse-refine-witness-present : ContaminationReverseRefineWitnessPresence

record ClassifierContaminationReverseRefineWitness : Set where
  constructor mkClassifierContaminationReverseRefineWitness
  field
    witness-presence : ContaminationReverseRefineWitnessPresence
    contamination-reverse-refine-gap-total : ℕ

contaminationReverseRefineWitnessAbsent : ClassifierContaminationReverseRefineWitness
contaminationReverseRefineWitnessAbsent = mkClassifierContaminationReverseRefineWitness contamination-reverse-refine-witness-absent zero

contaminationReverseRefineWitnessPresentZeroGap : ClassifierContaminationReverseRefineWitness
contaminationReverseRefineWitnessPresentZeroGap = mkClassifierContaminationReverseRefineWitness contamination-reverse-refine-witness-present zero

contaminationReverseRefineWitnessPresentWithGaps : ℕ → ClassifierContaminationReverseRefineWitness
contaminationReverseRefineWitnessPresentWithGaps n = mkClassifierContaminationReverseRefineWitness contamination-reverse-refine-witness-present n

contaminationReverseRefineWitnessGapFree : ClassifierContaminationReverseRefineWitness → Bool
contaminationReverseRefineWitnessGapFree (mkClassifierContaminationReverseRefineWitness contamination-reverse-refine-witness-absent _) = false
contaminationReverseRefineWitnessGapFree (mkClassifierContaminationReverseRefineWitness contamination-reverse-refine-witness-present n) =
  does (n ℕ-Props.≟ zero)

contamination-reverse-refine-witness-present-zero-gap-free :
  contaminationReverseRefineWitnessGapFree contaminationReverseRefineWitnessPresentZeroGap ≡ true
contamination-reverse-refine-witness-present-zero-gap-free = refl

contamination-reverse-refine-witness-absent-not-gap-free :
  contaminationReverseRefineWitnessGapFree contaminationReverseRefineWitnessAbsent ≡ false
contamination-reverse-refine-witness-absent-not-gap-free = refl

contamination-reverse-refine-witness-with-gaps-not-gap-free :
  ∀ n → contaminationReverseRefineWitnessGapFree (contaminationReverseRefineWitnessPresentWithGaps (suc n)) ≡ false
contamination-reverse-refine-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Contamination-reverse-refine **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data ContaminationReverseRefineConservationVerdict : Set where
  verdict-unwired-ok verdict-contamination-reverse-refine-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : ContaminationReverseRefineConservationVerdict

contaminationReverseRefineConservationVerdictOk : ContaminationReverseRefineConservationVerdict → Bool
contaminationReverseRefineConservationVerdictOk verdict-unwired-ok = true
contaminationReverseRefineConservationVerdictOk verdict-contamination-reverse-refine-admissible-ok = true
contaminationReverseRefineConservationVerdictOk verdict-concurrent-product-ok = true
contaminationReverseRefineConservationVerdictOk _ = false

evaluateContaminationReverseRefineConservationClose :
  ContaminationReverseRefineConservationModality → ClassifierContaminationReverseRefineStep → ClassifierContaminationReverseRefineWitness
  → ContaminationReverseRefineBundleWitness → Bool → ContaminationReverseRefineConservationVerdict
evaluateContaminationReverseRefineConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-proved _ (mkClassifierContaminationReverseRefineWitness contamination-reverse-refine-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-proved _ (mkClassifierContaminationReverseRefineWitness contamination-reverse-refine-witness-present _) w false
  with contaminationReverseRefineBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-contamination-reverse-refine-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without contamination-reverse-refine witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-unwired namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-assumed namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-surrogate namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  contaminationReverseRefineConservationVerdictOk
    (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-unwired namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false)
    ≡ true
  × contaminationReverseRefineConservationVerdictOk
      (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-assumed namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false)
      ≡ true
  × contaminationReverseRefineConservationVerdictOk
      (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-surrogate namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without contamination-reverse-refine witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  contaminationReverseRefineConservationVerdictOk
    (evaluateContaminationReverseRefineConservationClose
       contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false ≡
  verdict-contamination-reverse-refine-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-proved
    (xorMutuallyExclusiveOp reverseRefineDirectionLeaf inverseMorphismTypedLeaf)
    contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  contaminationReverseRefineConservationVerdictOk
    (evaluateContaminationReverseRefineConservationClose
       contamination-reverse-refine-conservation-proved
       (xorMutuallyExclusiveOp reverseRefineDirectionLeaf inverseMorphismTypedLeaf)
       contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-proved
    (xorMutuallyExclusiveOp reverseRefineDirectionLeaf inverseMorphismTypedLeaf)
    contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-contamination-reverse-refine — nuance **product** closed
------------------------------------------------------------------------

contamination-reverse-refine-admissible-ok :
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap unwiredWitness false ≡
  verdict-contamination-reverse-refine-admissible-ok
contamination-reverse-refine-admissible-ok = refl

contamination-reverse-refine-admissible-verdict-ok :
  contaminationReverseRefineConservationVerdictOk
    (evaluateContaminationReverseRefineConservationClose
       contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap unwiredWitness false)
    ≡ true
contamination-reverse-refine-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — contamination-reverse-refine nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  contaminationReverseRefineConservationVerdictOk
    (evaluateContaminationReverseRefineConservationClose
       contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-contamination-reverse-refine20-proved :
  contaminationReverseRefineConservationVerdictOk
    (evaluateContaminationReverseRefineConservationClose
       contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness false)
    ≡ true
  × contaminationReverseRefine20Proved ≡ false
concurrent-product-ok-still-not-contamination-reverse-refine20-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateContaminationReverseRefineConservationClose
    contamination-reverse-refine-conservation-unwired namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  contaminationReverseRefineConservationVerdictOk
    (evaluateContaminationReverseRefineConservationClose
       contamination-reverse-refine-conservation-unwired namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

contaminationReverseRefineConservationFiberOk : FormalFiber → Bool
contaminationReverseRefineConservationFiberOk fiber-quantum-knowing = true
contaminationReverseRefineConservationFiberOk fiber-meso-acting = false

contamination-reverse-refine-conservation-knowing-fiber-ok :
  contaminationReverseRefineConservationFiberOk fiber-quantum-knowing ≡ true
contamination-reverse-refine-conservation-knowing-fiber-ok = refl

contamination-reverse-refine-conservation-meso-acting-not-ok :
  contaminationReverseRefineConservationFiberOk fiber-meso-acting ≡ false
contamination-reverse-refine-conservation-meso-acting-not-ok = refl

contamination-reverse-refine-conservation-routes-knowing-not-meso :
  contaminationReverseRefineConservationFiberOk fiber-quantum-knowing ≡ true ×
  contaminationReverseRefineConservationFiberOk fiber-meso-acting ≡ false
contamination-reverse-refine-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  contaminationReverseRefineConservationFiberOk fiber-quantum-knowing ∧
  not (contaminationReverseRefineConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 20 contamination_reverse_refine Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

contamination-reverse-refine-20-not-proved : contaminationReverseRefine20Proved ≡ false
contamination-reverse-refine-20-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

contamination-reverse-refine-second-law-conservation-framed : contaminationReverseRefineSecondLawConservationFramed ≡ true
contamination-reverse-refine-second-law-conservation-framed = refl

contamination-reverse-refine-not-xor-pin : contaminationReverseRefineNotXor ≡ true
contamination-reverse-refine-not-xor-pin = contamination-reverse-refine-not-xor

reverse-refine-direction-typed-pin : reverseRefineDirectionTyped ≡ true
reverse-refine-direction-typed-pin = refl

not-parallel-contamination-axiom-minted-pin : notParallelContaminationAxiomMinted ≡ true
not-parallel-contamination-axiom-minted-pin = refl

free-purification-not-forked-pin : freePurificationNotForked ≡ true
free-purification-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel contamination axiom fork)
------------------------------------------------------------------------

contaminationReverseRefineConservationAxiom :
  (contaminationReverseRefine20Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (contaminationReverseRefineSecondLawConservationFramed ≡ true)
  × (contaminationReverseRefineNotXor ≡ true)
  × (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-unwired namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessAbsent contaminationReverseRefineNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-proved (xorMutuallyExclusiveOp reverseRefineDirectionLeaf inverseMorphismTypedLeaf) contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap unwiredWitness false ≡ verdict-contamination-reverse-refine-admissible-ok)
  × (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-proved namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (contaminationReverseRefineConservationFiberOk fiber-quantum-knowing ≡ true)
  × (contaminationReverseRefineConservationFiberOk fiber-meso-acting ≡ false)
  × (contaminationReverseRefineConservationVerdictOk (evaluateContaminationReverseRefineConservationClose contamination-reverse-refine-conservation-unwired namedContaminationReverseRefineNuanceProduct contaminationReverseRefineWitnessPresentZeroGap contaminationReverseRefineNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp contaminationReverseRefineIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a contaminationReverseRefineIdentity) ≡ true)
  × (isContaminationReverseRefineAdmissible (xorMutuallyExclusiveOp reverseRefineDirectionLeaf inverseMorphismTypedLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (contaminationReverseRefineClassIndex ≡ 20)
  × (ContaminationReverseRefineBundleWitness.present-count contaminationReverseRefineNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
contaminationReverseRefineConservationAxiom =
  contamination-reverse-refine-20-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , contamination-reverse-refine-second-law-conservation-framed
  , contamination-reverse-refine-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , contamination-reverse-refine-admissible-ok
  , concurrent-product-ok
  , contamination-reverse-refine-conservation-knowing-fiber-ok
  , contamination-reverse-refine-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , contamination-reverse-refine-class-index-twenty
  , contamination-reverse-refine-nuance-present-count
  , iron-z-26
  , oganesson-z-118

contaminationReverseRefineConservationNamed : String
contaminationReverseRefineConservationNamed =
  "contaminationReverseRefineConservation: pattern class 20 contamination_reverse_refine conservation concurrent Pi_c identity conserved reverse Refine direction inverse morphism typed class 20 contamination concurrent product identity conserved present ge 2 product not XOR reverse Refine direction typed no parallel contamination axiom free purification not forked"

contaminationReverseRefineConservationCrossWitnessAuthority : String
contaminationReverseRefineConservationCrossWitnessAuthority =
  "umst/umst-chem/src/contamination_reverse_refine.rs"

contaminationReverseRefineTableAuthority : String
contaminationReverseRefineTableAuthority =
  "umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

contaminationReverseRefineConservationCellId : String
contaminationReverseRefineConservationCellId = "CHEM-FORMAL-Q-AGDA-CONTAMINATION-REVERSE-REFINE-CONSERVATION"

contaminationReverseRefineConservationNonClaim : String
contaminationReverseRefineConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-CONTAMINATION-REVERSE-REFINE-CONSERVATION pattern class 20 contamination_reverse_refine conservation concurrent Pi_c identity conserved reverse Refine direction inverse morphism typed class 20 contamination product not XOR reverse Refine direction typed no parallel contamination axiom free purification not forked XOR mutually exclusive refuse contamination-reverse-refine nuance witness concurrent contaminationReverseRefine20Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite contamination_reverse_refine.rs l0_tables contamination_reverse_refine not fork not physics GREEN not production_wired"

contamination-reverse-refine-conservation-cell-id :
  contaminationReverseRefineConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-CONTAMINATION-REVERSE-REFINE-CONSERVATION"
contamination-reverse-refine-conservation-cell-id = refl

contamination-reverse-refine-conservation-cites-edge-contam-rs :
  contaminationReverseRefineConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/contamination_reverse_refine.rs"
contamination-reverse-refine-conservation-cites-edge-contam-rs = refl

contamination-reverse-refine-conservation-cites-l0-table-rs :
  contaminationReverseRefineTableAuthority ≡
  "umst/umst-chem/src/l0_tables/contamination_reverse_refine.rs"
contamination-reverse-refine-conservation-cites-l0-table-rs = refl

contamination-reverse-refine-conservation-modality-unwired :
  contaminationReverseRefineConservationModalityCurrent ≡ contamination-reverse-refine-conservation-unwired
contamination-reverse-refine-conservation-modality-unwired = refl

contaminationReverseRefineConservationPhysicsGreenAuthorized : Set
contaminationReverseRefineConservationPhysicsGreenAuthorized = ⊥

contamination-reverse-refine-conservation-physics-green-false : ¬ contaminationReverseRefineConservationPhysicsGreenAuthorized
contamination-reverse-refine-conservation-physics-green-false ()

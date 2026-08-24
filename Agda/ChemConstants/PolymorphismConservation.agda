-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PolymorphismConservation.agda
-- polymorphismconservation polymorphismconservation polymorphismconservation
-- polymorphism_conservation polymorphism_conservation polymorphism_conservation
-- chem_formal_q_agda_polymorphism_conservation chem_formal_q_agda_polymorphism_conservation
--
-- Pattern class 18 **polymorphism** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (stoichiometry invariant + lattice geometry variant +
--     class 18 polymorphism PatternBundle concurrent factor; **product** not XOR,
--     no parallel polymorphism axiom)
--   * Same stoichiometry distinct lattices (α/β/γ) — **not** allotrope class 10, not new ElementId
--   * XOR mutually-exclusive refuse; polymorphism nuance witness concurrent
--     (stoichiometry invariant + lattice geometry variant + class 18 polymorphism)
--   * **polymorphism** laws Unwired (polymorphismConservationProved = false)
--   * T/P when named are graph functions on Interact graph — not bare float pins
--
-- INT (read-only cite): umst/umst-chem/src/polymorphism_geometry.rs
-- L0 table: umst/umst-chem/src/l0_tables/polymorphism.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel polymorphism axiom; not allotrope class 10; not new ElementId. Product not XOR.
-- Class 18 polymorphism as stoichiometry-invariant vs lattice-geometry-variant, not allotrope.
------------------------------------------------------------------------
module ChemConstants.PolymorphismConservation where

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
-- Modality + pattern class 18 **polymorphism** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PolymorphismConservationModality : Set where
  polymorphism-conservation-unwired polymorphism-conservation-assumed
    polymorphism-conservation-proved polymorphism-conservation-surrogate
    : PolymorphismConservationModality

polymorphismConservationModalityCurrent : PolymorphismConservationModality
polymorphismConservationModalityCurrent = polymorphism-conservation-unwired

polymorphismConservationProved productionWired not118SquaredGreenTable
  polymorphismSecondLawConservationFramed polymorphismNotXor : Bool
polymorphismConservationProved = false
productionWired = false
not118SquaredGreenTable = true
polymorphismSecondLawConservationFramed = true
polymorphismNotXor = true

notAllotropeClass10 notParallelPolymorphismAxiomMinted notNewElementId : Bool
notAllotropeClass10 = true
notParallelPolymorphismAxiomMinted = true
notNewElementId = true

tpGraphFunctionNotFloatPin : Bool
tpGraphFunctionNotFloatPin = true

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
-- Pattern class 18 Polymorphism index pin
------------------------------------------------------------------------

polymorphismClassIndex : ℕ
polymorphismClassIndex = 18

polymorphism-class-index-eighteen : polymorphismClassIndex ≡ 18
polymorphism-class-index-eighteen = refl

allotropeClass10Index : ℕ
allotropeClass10Index = 10

allotrope-class10-index-ten : allotropeClass10Index ≡ 10
allotrope-class10-index-ten = refl

polymorphism-ne-allotrope-class10 :
  does (polymorphismClassIndex ℕ-Props.≟ allotropeClass10Index) ≡ false
polymorphism-ne-allotrope-class10 = refl

------------------------------------------------------------------------
-- Named element Z pins — Ca (Z=20) CaCO3, Si (Z=14) SiO2 polymorphs
------------------------------------------------------------------------

data ElementTag : Set where
  calcium silicon : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ calcium = 20
elementAtomicZ silicon = 14

calcium-z-20 : elementAtomicZ calcium ≡ 20
calcium-z-20 = refl

silicon-z-14 : elementAtomicZ silicon ≡ 14
silicon-z-14 = refl

------------------------------------------------------------------------
-- PolymorphismBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PolymorphismBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PolymorphismBundleSlot

isSlotPresent : PolymorphismBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- PolymorphismBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record PolymorphismBundle : Set where
  field slot : ℕ → PolymorphismBundleSlot

polymorphismBundleUnwired : PolymorphismBundle
polymorphismBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : PolymorphismBundle → ℕ → PolymorphismBundleSlot → PolymorphismBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else PolymorphismBundle.slot b j }

withPresent : PolymorphismBundle → ℕ → PolymorphismBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PolymorphismBundleWitness : Set where
  constructor mkPolymorphismBundleWitness
  field
    bundle : PolymorphismBundle
    present-count : ℕ

polymorphismBundleIsConcurrentProduct : PolymorphismBundleWitness → Bool
polymorphismBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PolymorphismBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named polymorphism channel indices — stoichiometry invariant (1), lattice geometry variant (2), class 18 polymorphism (3)
------------------------------------------------------------------------

stoichiometryInvariantChannelIndex latticeGeometryVariantChannelIndex class18PolymorphismChannelIndex : ℕ
stoichiometryInvariantChannelIndex = 1
latticeGeometryVariantChannelIndex = 2
class18PolymorphismChannelIndex = 3

stoichiometry-invariant-index-one : stoichiometryInvariantChannelIndex ≡ 1
stoichiometry-invariant-index-one = refl

lattice-geometry-variant-index-two : latticeGeometryVariantChannelIndex ≡ 2
lattice-geometry-variant-index-two = refl

class18-polymorphism-index-three : class18PolymorphismChannelIndex ≡ 3
class18-polymorphism-index-three = refl

------------------------------------------------------------------------
-- Polymorphism nuance witness — stoichiometry invariant + lattice geometry variant + class 18 polymorphism concurrent
------------------------------------------------------------------------

polymorphismNuanceBundle : PolymorphismBundle
polymorphismNuanceBundle =
  withPresent
    (withPresent
      (withPresent polymorphismBundleUnwired stoichiometryInvariantChannelIndex)
      latticeGeometryVariantChannelIndex)
    class18PolymorphismChannelIndex

polymorphismNuanceWitness : PolymorphismBundleWitness
polymorphismNuanceWitness =
  mkPolymorphismBundleWitness polymorphismNuanceBundle 3

polymorphism-nuance-stoichiometry-invariant-present :
  isSlotPresent (PolymorphismBundle.slot polymorphismNuanceBundle stoichiometryInvariantChannelIndex) ≡ true
polymorphism-nuance-stoichiometry-invariant-present = refl

polymorphism-nuance-lattice-geometry-variant-present :
  isSlotPresent (PolymorphismBundle.slot polymorphismNuanceBundle latticeGeometryVariantChannelIndex) ≡ true
polymorphism-nuance-lattice-geometry-variant-present = refl

polymorphism-nuance-class18-polymorphism-present :
  isSlotPresent (PolymorphismBundle.slot polymorphismNuanceBundle class18PolymorphismChannelIndex) ≡ true
polymorphism-nuance-class18-polymorphism-present = refl

polymorphism-nuance-present-count : PolymorphismBundleWitness.present-count polymorphismNuanceWitness ≡ 3
polymorphism-nuance-present-count = refl

polymorphism-nuance-concurrent-product :
  polymorphismBundleIsConcurrentProduct polymorphismNuanceWitness ≡ true
polymorphism-nuance-concurrent-product = refl

polymorphism-nuance-three-factors-concurrent :
  isSlotPresent (PolymorphismBundle.slot polymorphismNuanceBundle stoichiometryInvariantChannelIndex) ≡ true
  × isSlotPresent (PolymorphismBundle.slot polymorphismNuanceBundle latticeGeometryVariantChannelIndex) ≡ true
  × isSlotPresent (PolymorphismBundle.slot polymorphismNuanceBundle class18PolymorphismChannelIndex) ≡ true
  × PolymorphismBundleWitness.present-count polymorphismNuanceWitness ≡ 3
polymorphism-nuance-three-factors-concurrent =
  polymorphism-nuance-stoichiometry-invariant-present
  , polymorphism-nuance-lattice-geometry-variant-present
  , polymorphism-nuance-class18-polymorphism-present
  , polymorphism-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PolymorphismBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if polymorphismBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = PolymorphismBundleWitness.bundle w
       in if isSlotPresent (PolymorphismBundle.slot b i)
          then if isSlotPresent (PolymorphismBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PolymorphismBundleWitness
unwiredWitness = mkPolymorphismBundleWitness polymorphismBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

polymorphism-nuance-xor-product-ok :
  evaluateXorRefuse polymorphismNuanceWitness stoichiometryInvariantChannelIndex latticeGeometryVariantChannelIndex ≡ xor-product-ok
polymorphism-nuance-xor-product-ok = refl

polymorphism-not-xor : polymorphismNotXor ≡ true
polymorphism-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPolymorphismStep scaffold — PolymorphismBundle **conservation**
------------------------------------------------------------------------

data ClassifierPolymorphismStep : Set where
  polymorphism-identity : ClassifierPolymorphismStep
  slot-leaf : ℕ → ClassifierPolymorphismStep
  product-concurrent : ClassifierPolymorphismStep → ClassifierPolymorphismStep → ClassifierPolymorphismStep
  xor-mutually-exclusive : ClassifierPolymorphismStep → ClassifierPolymorphismStep → ClassifierPolymorphismStep

polymorphismIdentity : ClassifierPolymorphismStep
polymorphismIdentity = polymorphism-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPolymorphismStep → ClassifierPolymorphismStep → ClassifierPolymorphismStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

stoichiometryInvariantLeaf latticeGeometryVariantLeaf class18PolymorphismLeaf : ClassifierPolymorphismStep
stoichiometryInvariantLeaf = slot-leaf stoichiometryInvariantChannelIndex
latticeGeometryVariantLeaf = slot-leaf latticeGeometryVariantChannelIndex
class18PolymorphismLeaf = slot-leaf class18PolymorphismChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierPolymorphismStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isPolymorphismIdentity : ClassifierPolymorphismStep → Bool
isPolymorphismIdentity polymorphism-identity = true
isPolymorphismIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at polymorphism-identity
------------------------------------------------------------------------

polymorphism-left-identity :
  ∀ (a : ClassifierPolymorphismStep) →
  isPolymorphismIdentity polymorphismIdentity ≡ true
  × isProductConcurrent (productConcurrentOp polymorphismIdentity a) ≡ true
polymorphism-left-identity a = refl , refl

polymorphism-right-identity :
  ∀ (a : ClassifierPolymorphismStep) →
  isProductConcurrent (productConcurrentOp a polymorphismIdentity) ≡ true
  × isPolymorphismIdentity polymorphismIdentity ≡ true
polymorphism-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-polymorphism :
  (∀ a → isProductConcurrent (productConcurrentOp polymorphismIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a polymorphismIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-polymorphism =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named polymorphism nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedPolymorphismNuanceProduct : ClassifierPolymorphismStep
namedPolymorphismNuanceProduct =
  productConcurrentOp
    (productConcurrentOp stoichiometryInvariantLeaf latticeGeometryVariantLeaf)
    class18PolymorphismLeaf

named-polymorphism-nuance-product-concurrent :
  isProductConcurrent namedPolymorphismNuanceProduct ≡ true
  × polymorphismBundleIsConcurrentProduct polymorphismNuanceWitness ≡ true
named-polymorphism-nuance-product-concurrent = refl , polymorphism-nuance-concurrent-product

------------------------------------------------------------------------
-- PolymorphismBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data PolymorphismAdmissibility : Set where
  polymorphism-admissible polymorphism-xor-refuse : PolymorphismAdmissibility

isPolymorphismPreserving : ClassifierPolymorphismStep → Bool
isPolymorphismPreserving polymorphism-identity = true
isPolymorphismPreserving (slot-leaf _) = true
isPolymorphismPreserving (product-concurrent a b) =
  isPolymorphismPreserving a ∧ isPolymorphismPreserving b
isPolymorphismPreserving (xor-mutually-exclusive _ _) = false

isPolymorphismAdmissible : ClassifierPolymorphismStep → Bool
isPolymorphismAdmissible step = isPolymorphismPreserving step

stoichiometry-invariant-leaf-admissible : isPolymorphismAdmissible stoichiometryInvariantLeaf ≡ true
stoichiometry-invariant-leaf-admissible = refl

lattice-geometry-variant-leaf-admissible : isPolymorphismAdmissible latticeGeometryVariantLeaf ≡ true
lattice-geometry-variant-leaf-admissible = refl

class18-polymorphism-leaf-admissible : isPolymorphismAdmissible class18PolymorphismLeaf ≡ true
class18-polymorphism-leaf-admissible = refl

named-polymorphism-nuance-admissible : isPolymorphismAdmissible namedPolymorphismNuanceProduct ≡ true
named-polymorphism-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isPolymorphismAdmissible (xorMutuallyExclusiveOp stoichiometryInvariantLeaf latticeGeometryVariantLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class18-polymorphism-refuse :
  isPolymorphismAdmissible (xorMutuallyExclusiveOp latticeGeometryVariantLeaf class18PolymorphismLeaf) ≡ false
xor-mutually-exclusive-class18-polymorphism-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data PolymorphismWitnessPresence : Set where
  polymorphism-witness-absent polymorphism-witness-present : PolymorphismWitnessPresence

record ClassifierPolymorphismWitness : Set where
  constructor mkClassifierPolymorphismWitness
  field
    witness-presence : PolymorphismWitnessPresence
    polymorphism-gap-total : ℕ

polymorphismWitnessAbsent : ClassifierPolymorphismWitness
polymorphismWitnessAbsent = mkClassifierPolymorphismWitness polymorphism-witness-absent zero

polymorphismWitnessPresentZeroGap : ClassifierPolymorphismWitness
polymorphismWitnessPresentZeroGap = mkClassifierPolymorphismWitness polymorphism-witness-present zero

polymorphismWitnessPresentWithGaps : ℕ → ClassifierPolymorphismWitness
polymorphismWitnessPresentWithGaps n = mkClassifierPolymorphismWitness polymorphism-witness-present n

polymorphismWitnessGapFree : ClassifierPolymorphismWitness → Bool
polymorphismWitnessGapFree (mkClassifierPolymorphismWitness polymorphism-witness-absent _) = false
polymorphismWitnessGapFree (mkClassifierPolymorphismWitness polymorphism-witness-present n) =
  does (n ℕ-Props.≟ zero)

polymorphism-witness-present-zero-gap-free :
  polymorphismWitnessGapFree polymorphismWitnessPresentZeroGap ≡ true
polymorphism-witness-present-zero-gap-free = refl

polymorphism-witness-absent-not-gap-free :
  polymorphismWitnessGapFree polymorphismWitnessAbsent ≡ false
polymorphism-witness-absent-not-gap-free = refl

polymorphism-witness-with-gaps-not-gap-free :
  ∀ n → polymorphismWitnessGapFree (polymorphismWitnessPresentWithGaps (suc n)) ≡ false
polymorphism-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Polymorphism **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PolymorphismConservationVerdict : Set where
  verdict-unwired-ok verdict-polymorphism-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : PolymorphismConservationVerdict

polymorphismConservationVerdictOk : PolymorphismConservationVerdict → Bool
polymorphismConservationVerdictOk verdict-unwired-ok = true
polymorphismConservationVerdictOk verdict-polymorphism-admissible-ok = true
polymorphismConservationVerdictOk verdict-concurrent-product-ok = true
polymorphismConservationVerdictOk _ = false

evaluatePolymorphismConservationClose :
  PolymorphismConservationModality → ClassifierPolymorphismStep → ClassifierPolymorphismWitness
  → PolymorphismBundleWitness → Bool → PolymorphismConservationVerdict
evaluatePolymorphismConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluatePolymorphismConservationClose polymorphism-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluatePolymorphismConservationClose polymorphism-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluatePolymorphismConservationClose polymorphism-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluatePolymorphismConservationClose polymorphism-conservation-proved _ (mkClassifierPolymorphismWitness polymorphism-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluatePolymorphismConservationClose polymorphism-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluatePolymorphismConservationClose polymorphism-conservation-proved _ (mkClassifierPolymorphismWitness polymorphism-witness-present _) w false
  with polymorphismBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-polymorphism-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without polymorphism witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePolymorphismConservationClose
    polymorphism-conservation-unwired namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePolymorphismConservationClose
    polymorphism-conservation-assumed namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePolymorphismConservationClose
    polymorphism-conservation-surrogate namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  polymorphismConservationVerdictOk
    (evaluatePolymorphismConservationClose polymorphism-conservation-unwired namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false)
    ≡ true
  × polymorphismConservationVerdictOk
      (evaluatePolymorphismConservationClose polymorphism-conservation-assumed namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false)
      ≡ true
  × polymorphismConservationVerdictOk
      (evaluatePolymorphismConservationClose polymorphism-conservation-surrogate namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without polymorphism witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePolymorphismConservationClose
    polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  polymorphismConservationVerdictOk
    (evaluatePolymorphismConservationClose
       polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluatePolymorphismConservationClose
    polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false ≡
  verdict-polymorphism-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluatePolymorphismConservationClose
    polymorphism-conservation-proved
    (xorMutuallyExclusiveOp stoichiometryInvariantLeaf latticeGeometryVariantLeaf)
    polymorphismWitnessPresentZeroGap polymorphismNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  polymorphismConservationVerdictOk
    (evaluatePolymorphismConservationClose
       polymorphism-conservation-proved
       (xorMutuallyExclusiveOp stoichiometryInvariantLeaf latticeGeometryVariantLeaf)
       polymorphismWitnessPresentZeroGap polymorphismNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluatePolymorphismConservationClose
    polymorphism-conservation-proved
    (xorMutuallyExclusiveOp stoichiometryInvariantLeaf latticeGeometryVariantLeaf)
    polymorphismWitnessPresentZeroGap polymorphismNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-polymorphism — nuance **product** closed
------------------------------------------------------------------------

polymorphism-admissible-ok :
  evaluatePolymorphismConservationClose
    polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap unwiredWitness false ≡
  verdict-polymorphism-admissible-ok
polymorphism-admissible-ok = refl

polymorphism-admissible-verdict-ok :
  polymorphismConservationVerdictOk
    (evaluatePolymorphismConservationClose
       polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap unwiredWitness false)
    ≡ true
polymorphism-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — polymorphism nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluatePolymorphismConservationClose
    polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap polymorphismNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  polymorphismConservationVerdictOk
    (evaluatePolymorphismConservationClose
       polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap polymorphismNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-polymorphism14-proved :
  polymorphismConservationVerdictOk
    (evaluatePolymorphismConservationClose
       polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap polymorphismNuanceWitness false)
    ≡ true
  × polymorphismConservationProved ≡ false
concurrent-product-ok-still-not-polymorphism14-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePolymorphismConservationClose
    polymorphism-conservation-unwired namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap polymorphismNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  polymorphismConservationVerdictOk
    (evaluatePolymorphismConservationClose
       polymorphism-conservation-unwired namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap polymorphismNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

polymorphismConservationFiberOk : FormalFiber → Bool
polymorphismConservationFiberOk fiber-quantum-knowing = true
polymorphismConservationFiberOk fiber-meso-acting = false

polymorphism-conservation-knowing-fiber-ok :
  polymorphismConservationFiberOk fiber-quantum-knowing ≡ true
polymorphism-conservation-knowing-fiber-ok = refl

polymorphism-conservation-meso-acting-not-ok :
  polymorphismConservationFiberOk fiber-meso-acting ≡ false
polymorphism-conservation-meso-acting-not-ok = refl

polymorphism-conservation-routes-knowing-not-meso :
  polymorphismConservationFiberOk fiber-quantum-knowing ≡ true ×
  polymorphismConservationFiberOk fiber-meso-acting ≡ false
polymorphism-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  polymorphismConservationFiberOk fiber-quantum-knowing ∧
  not (polymorphismConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 18 polymorphism Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

polymorphism-conservation-not-proved : polymorphismConservationProved ≡ false
polymorphism-conservation-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

polymorphism-second-law-conservation-framed : polymorphismSecondLawConservationFramed ≡ true
polymorphism-second-law-conservation-framed = refl

polymorphism-not-xor-pin : polymorphismNotXor ≡ true
polymorphism-not-xor-pin = polymorphism-not-xor

not-allotrope-class10-pin : notAllotropeClass10 ≡ true
not-allotrope-class10-pin = refl

not-parallel-polymorphism-axiom-minted-pin : notParallelPolymorphismAxiomMinted ≡ true
not-parallel-polymorphism-axiom-minted-pin = refl

not-new-element-id-pin : notNewElementId ≡ true
not-new-element-id-pin = refl

tp-graph-function-not-float-pin : tpGraphFunctionNotFloatPin ≡ true
tp-graph-function-not-float-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel polymorphism axiom fork)
------------------------------------------------------------------------

polymorphismConservationAxiom :
  (polymorphismConservationProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (polymorphismSecondLawConservationFramed ≡ true)
  × (polymorphismNotXor ≡ true)
  × (evaluatePolymorphismConservationClose polymorphism-conservation-unwired namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluatePolymorphismConservationClose polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessAbsent polymorphismNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluatePolymorphismConservationClose polymorphism-conservation-proved (xorMutuallyExclusiveOp stoichiometryInvariantLeaf latticeGeometryVariantLeaf) polymorphismWitnessPresentZeroGap polymorphismNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluatePolymorphismConservationClose polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap unwiredWitness false ≡ verdict-polymorphism-admissible-ok)
  × (evaluatePolymorphismConservationClose polymorphism-conservation-proved namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap polymorphismNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (polymorphismConservationFiberOk fiber-quantum-knowing ≡ true)
  × (polymorphismConservationFiberOk fiber-meso-acting ≡ false)
  × (polymorphismConservationVerdictOk (evaluatePolymorphismConservationClose polymorphism-conservation-unwired namedPolymorphismNuanceProduct polymorphismWitnessPresentZeroGap polymorphismNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp polymorphismIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a polymorphismIdentity) ≡ true)
  × (isPolymorphismAdmissible (xorMutuallyExclusiveOp stoichiometryInvariantLeaf latticeGeometryVariantLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (polymorphismClassIndex ≡ 18)
  × (PolymorphismBundleWitness.present-count polymorphismNuanceWitness ≡ 3)
  × (elementAtomicZ calcium ≡ 20)
  × (elementAtomicZ silicon ≡ 14)
  × (notAllotropeClass10 ≡ true)
  × (notParallelPolymorphismAxiomMinted ≡ true)
  × (notNewElementId ≡ true)
  × (tpGraphFunctionNotFloatPin ≡ true)
  × (does (polymorphismClassIndex ℕ-Props.≟ allotropeClass10Index) ≡ false)
polymorphismConservationAxiom =
  polymorphism-conservation-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , polymorphism-second-law-conservation-framed
  , polymorphism-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , polymorphism-admissible-ok
  , concurrent-product-ok
  , polymorphism-conservation-knowing-fiber-ok
  , polymorphism-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , polymorphism-class-index-eighteen
  , polymorphism-nuance-present-count
  , calcium-z-20
  , silicon-z-14
  , not-allotrope-class10-pin
  , not-parallel-polymorphism-axiom-minted-pin
  , not-new-element-id-pin
  , tp-graph-function-not-float-pin
  , polymorphism-ne-allotrope-class10

polymorphismConservationNamed : String
polymorphismConservationNamed =
  "polymorphismConservation: pattern class 18 polymorphism conservation concurrent Pi_c identity conserved stoichiometry invariant lattice geometry variant class 18 polymorphism concurrent product identity conserved present ge 2 product not XOR same stoichiometry distinct lattices not allotrope class 10 not new ElementId no parallel polymorphism axiom T P graph functions not float pins"

polymorphismConservationCrossWitnessAuthority : String
polymorphismConservationCrossWitnessAuthority =
  "umst/umst-chem/src/polymorphism_geometry.rs"

polymorphismTableAuthority : String
polymorphismTableAuthority =
  "umst/umst-chem/src/l0_tables/polymorphism.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

polymorphismConservationCellId : String
polymorphismConservationCellId = "CHEM-FORMAL-Q-AGDA-POLYMORPHISM-CONSERVATION"

polymorphismConservationNonClaim : String
polymorphismConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-POLYMORPHISM-CONSERVATION pattern class 18 polymorphism conservation concurrent Pi_c identity conserved stoichiometry invariant lattice geometry variant class 18 polymorphism product not XOR same stoichiometry distinct lattices not allotrope class 10 not new ElementId no parallel polymorphism axiom T P graph functions not float pins XOR mutually exclusive refuse polymorphism nuance witness concurrent polymorphismConservationProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite polymorphism_geometry.rs l0_tables polymorphism not fork not physics GREEN not production_wired"

polymorphism-conservation-cell-id :
  polymorphismConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-POLYMORPHISM-CONSERVATION"
polymorphism-conservation-cell-id = refl

polymorphism-conservation-cites-polymorphism-geometry-rs :
  polymorphismConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/polymorphism_geometry.rs"
polymorphism-conservation-cites-polymorphism-geometry-rs = refl

polymorphism-conservation-cites-l0-table-rs :
  polymorphismTableAuthority ≡
  "umst/umst-chem/src/l0_tables/polymorphism.rs"
polymorphism-conservation-cites-l0-table-rs = refl

polymorphism-conservation-modality-unwired :
  polymorphismConservationModalityCurrent ≡ polymorphism-conservation-unwired
polymorphism-conservation-modality-unwired = refl

polymorphismConservationPhysicsGreenAuthorized : Set
polymorphismConservationPhysicsGreenAuthorized = ⊥

polymorphism-conservation-physics-green-false : ¬ polymorphismConservationPhysicsGreenAuthorized
polymorphism-conservation-physics-green-false ()

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.NaturalVsPurifiedEnvConservation.agda
--
-- CHEM-FORMAL-Q-AGDA-NATURAL-VS-PURIFIED-ENV-CONSERVATION
-- Constitutive **natural_vs_purified_env** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (natural messy Env section + purified contained Env section +
--     class 13 natural_vs_purified_env; **product** not XOR, no parallel natural_vs_purified_env axiom)
--   * XOR mutually-exclusive refuse; natural-vs-purified Env nuance witness concurrent
--     (natural Env section + purified Env section + class 13 natural_vs_purified_env)
--   * **natural_vs_purified_env** laws Unwired (naturalVsPurifiedEnvProved = false)
--   * Env restriction along sample sections — not three chemistries; not a 26th axiom
--
-- INT (read-only cite): umst/umst-chem/src/element_restriction_along_environment.rs
-- Env sections: umst/umst-chem/src/environment_three_sample_spaces_not_xor.rs
-- Chart: umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel natural_vs_purified_env axiom; Env restriction not XOR chemistries. Product not XOR.
-- WAVE100: no lib.rs / eos.rs / nano wiring.
------------------------------------------------------------------------
module ChemConstants.NaturalVsPurifiedEnvConservation where


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
-- Modality + class 13 **natural_vs_purified_env** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data NaturalVsPurifiedEnvConservationModality : Set where
  natural-vs-purified-env-conservation-unwired natural-vs-purified-env-conservation-assumed
    natural-vs-purified-env-conservation-proved natural-vs-purified-env-conservation-surrogate
    : NaturalVsPurifiedEnvConservationModality

naturalVsPurifiedEnvConservationModalityCurrent : NaturalVsPurifiedEnvConservationModality
naturalVsPurifiedEnvConservationModalityCurrent = natural-vs-purified-env-conservation-unwired

naturalVsPurifiedEnvProved productionWired not118SquaredGreenTable
  naturalVsPurifiedEnvSecondLawConservationFramed naturalVsPurifiedEnvNotXor : Bool
naturalVsPurifiedEnvProved = false
productionWired = false
not118SquaredGreenTable = true
naturalVsPurifiedEnvSecondLawConservationFramed = true
naturalVsPurifiedEnvNotXor = true

envRestrictionTyped notParallelNaturalVsPurifiedEnvAxiomMinted notThreeChemistriesNotForked : Bool
envRestrictionTyped = true
notParallelNaturalVsPurifiedEnvAxiomMinted = true
notThreeChemistriesNotForked = true

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
-- Class 13 natural_vs_purified_env constitutive chart index pin
------------------------------------------------------------------------

naturalVsPurifiedEnvClassIndex : ℕ
naturalVsPurifiedEnvClassIndex = 13

natural-vs-purified-env-class-index-thirteen : naturalVsPurifiedEnvClassIndex ≡ 13
natural-vs-purified-env-class-index-thirteen = refl

------------------------------------------------------------------------
-- Named element Z pins — Pt (Z=78), Og (Z=118)
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
-- NaturalVsPurifiedEnvBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data NaturalVsPurifiedEnvBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : NaturalVsPurifiedEnvBundleSlot

isSlotPresent : NaturalVsPurifiedEnvBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- NaturalVsPurifiedEnvBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record NaturalVsPurifiedEnvBundle : Set where
  field slot : ℕ → NaturalVsPurifiedEnvBundleSlot

naturalVsPurifiedEnvBundleUnwired : NaturalVsPurifiedEnvBundle
naturalVsPurifiedEnvBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : NaturalVsPurifiedEnvBundle → ℕ → NaturalVsPurifiedEnvBundleSlot → NaturalVsPurifiedEnvBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else NaturalVsPurifiedEnvBundle.slot b j }

withPresent : NaturalVsPurifiedEnvBundle → ℕ → NaturalVsPurifiedEnvBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record NaturalVsPurifiedEnvBundleWitness : Set where
  constructor mkNaturalVsPurifiedEnvBundleWitness
  field
    bundle : NaturalVsPurifiedEnvBundle
    present-count : ℕ

naturalVsPurifiedEnvBundleIsConcurrentProduct : NaturalVsPurifiedEnvBundleWitness → Bool
naturalVsPurifiedEnvBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? NaturalVsPurifiedEnvBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named natural-vs-purified Env channel indices — natural Env section (1), purified Env section (2), class 13 natural_vs_purified_env (3)
------------------------------------------------------------------------

naturalEnvSectionChannelIndex purifiedEnvSectionChannelIndex class13NaturalVsPurifiedEnvChannelIndex : ℕ
naturalEnvSectionChannelIndex = 1
purifiedEnvSectionChannelIndex = 2
class13NaturalVsPurifiedEnvChannelIndex = 3

natural-env-section-index-one : naturalEnvSectionChannelIndex ≡ 1
natural-env-section-index-one = refl

purified-env-section-index-two : purifiedEnvSectionChannelIndex ≡ 2
purified-env-section-index-two = refl

class13-natural-vs-purified-env-index-three : class13NaturalVsPurifiedEnvChannelIndex ≡ 3
class13-natural-vs-purified-env-index-three = refl

------------------------------------------------------------------------
-- Natural-vs-purified Env nuance witness — natural Env section + purified Env section + class 13 natural_vs_purified_env concurrent
------------------------------------------------------------------------

naturalVsPurifiedEnvNuanceBundle : NaturalVsPurifiedEnvBundle
naturalVsPurifiedEnvNuanceBundle =
  withPresent
    (withPresent
      (withPresent naturalVsPurifiedEnvBundleUnwired naturalEnvSectionChannelIndex)
      purifiedEnvSectionChannelIndex)
    class13NaturalVsPurifiedEnvChannelIndex

naturalVsPurifiedEnvNuanceWitness : NaturalVsPurifiedEnvBundleWitness
naturalVsPurifiedEnvNuanceWitness =
  mkNaturalVsPurifiedEnvBundleWitness naturalVsPurifiedEnvNuanceBundle 3

natural-vs-purified-env-nuance-natural-env-section-present :
  isSlotPresent (NaturalVsPurifiedEnvBundle.slot naturalVsPurifiedEnvNuanceBundle naturalEnvSectionChannelIndex) ≡ true
natural-vs-purified-env-nuance-natural-env-section-present = refl

natural-vs-purified-env-nuance-purified-env-section-present :
  isSlotPresent (NaturalVsPurifiedEnvBundle.slot naturalVsPurifiedEnvNuanceBundle purifiedEnvSectionChannelIndex) ≡ true
natural-vs-purified-env-nuance-purified-env-section-present = refl

natural-vs-purified-env-nuance-class13-natural-vs-purified-env-present :
  isSlotPresent (NaturalVsPurifiedEnvBundle.slot naturalVsPurifiedEnvNuanceBundle class13NaturalVsPurifiedEnvChannelIndex) ≡ true
natural-vs-purified-env-nuance-class13-natural-vs-purified-env-present = refl

natural-vs-purified-env-nuance-present-count : NaturalVsPurifiedEnvBundleWitness.present-count naturalVsPurifiedEnvNuanceWitness ≡ 3
natural-vs-purified-env-nuance-present-count = refl

natural-vs-purified-env-nuance-concurrent-product :
  naturalVsPurifiedEnvBundleIsConcurrentProduct naturalVsPurifiedEnvNuanceWitness ≡ true
natural-vs-purified-env-nuance-concurrent-product = refl

natural-vs-purified-env-nuance-three-factors-concurrent :
  isSlotPresent (NaturalVsPurifiedEnvBundle.slot naturalVsPurifiedEnvNuanceBundle naturalEnvSectionChannelIndex) ≡ true
  × isSlotPresent (NaturalVsPurifiedEnvBundle.slot naturalVsPurifiedEnvNuanceBundle purifiedEnvSectionChannelIndex) ≡ true
  × isSlotPresent (NaturalVsPurifiedEnvBundle.slot naturalVsPurifiedEnvNuanceBundle class13NaturalVsPurifiedEnvChannelIndex) ≡ true
  × NaturalVsPurifiedEnvBundleWitness.present-count naturalVsPurifiedEnvNuanceWitness ≡ 3
natural-vs-purified-env-nuance-three-factors-concurrent =
  natural-vs-purified-env-nuance-natural-env-section-present
  , natural-vs-purified-env-nuance-purified-env-section-present
  , natural-vs-purified-env-nuance-class13-natural-vs-purified-env-present
  , natural-vs-purified-env-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : NaturalVsPurifiedEnvBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if naturalVsPurifiedEnvBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = NaturalVsPurifiedEnvBundleWitness.bundle w
       in if isSlotPresent (NaturalVsPurifiedEnvBundle.slot b i)
          then if isSlotPresent (NaturalVsPurifiedEnvBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : NaturalVsPurifiedEnvBundleWitness
unwiredWitness = mkNaturalVsPurifiedEnvBundleWitness naturalVsPurifiedEnvBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

natural-vs-purified-env-nuance-xor-product-ok :
  evaluateXorRefuse naturalVsPurifiedEnvNuanceWitness naturalEnvSectionChannelIndex purifiedEnvSectionChannelIndex ≡ xor-product-ok
natural-vs-purified-env-nuance-xor-product-ok = refl

natural-vs-purified-env-not-xor : naturalVsPurifiedEnvNotXor ≡ true
natural-vs-purified-env-not-xor = refl

------------------------------------------------------------------------
-- ClassifierNaturalVsPurifiedEnvStep scaffold — NaturalVsPurifiedEnvBundle **conservation**
------------------------------------------------------------------------

data ClassifierNaturalVsPurifiedEnvStep : Set where
  natural-vs-purified-env-identity : ClassifierNaturalVsPurifiedEnvStep
  slot-leaf : ℕ → ClassifierNaturalVsPurifiedEnvStep
  product-concurrent : ClassifierNaturalVsPurifiedEnvStep → ClassifierNaturalVsPurifiedEnvStep → ClassifierNaturalVsPurifiedEnvStep
  xor-mutually-exclusive : ClassifierNaturalVsPurifiedEnvStep → ClassifierNaturalVsPurifiedEnvStep → ClassifierNaturalVsPurifiedEnvStep

naturalVsPurifiedEnvIdentity : ClassifierNaturalVsPurifiedEnvStep
naturalVsPurifiedEnvIdentity = natural-vs-purified-env-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierNaturalVsPurifiedEnvStep → ClassifierNaturalVsPurifiedEnvStep → ClassifierNaturalVsPurifiedEnvStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

naturalEnvSectionLeaf purifiedEnvSectionLeaf class13NaturalVsPurifiedEnvLeaf : ClassifierNaturalVsPurifiedEnvStep
naturalEnvSectionLeaf = slot-leaf naturalEnvSectionChannelIndex
purifiedEnvSectionLeaf = slot-leaf purifiedEnvSectionChannelIndex
class13NaturalVsPurifiedEnvLeaf = slot-leaf class13NaturalVsPurifiedEnvChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierNaturalVsPurifiedEnvStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isNaturalVsPurifiedEnvIdentity : ClassifierNaturalVsPurifiedEnvStep → Bool
isNaturalVsPurifiedEnvIdentity natural-vs-purified-env-identity = true
isNaturalVsPurifiedEnvIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at natural-vs-purified-env-identity
------------------------------------------------------------------------

natural-vs-purified-env-left-identity :
  ∀ (a : ClassifierNaturalVsPurifiedEnvStep) →
  isNaturalVsPurifiedEnvIdentity naturalVsPurifiedEnvIdentity ≡ true
  × isProductConcurrent (productConcurrentOp naturalVsPurifiedEnvIdentity a) ≡ true
natural-vs-purified-env-left-identity a = refl , refl

natural-vs-purified-env-right-identity :
  ∀ (a : ClassifierNaturalVsPurifiedEnvStep) →
  isProductConcurrent (productConcurrentOp a naturalVsPurifiedEnvIdentity) ≡ true
  × isNaturalVsPurifiedEnvIdentity naturalVsPurifiedEnvIdentity ≡ true
natural-vs-purified-env-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-natural-vs-purified-env :
  (∀ a → isProductConcurrent (productConcurrentOp naturalVsPurifiedEnvIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a naturalVsPurifiedEnvIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-natural-vs-purified-env =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named natural-vs-purified Env nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedNaturalVsPurifiedEnvNuanceProduct : ClassifierNaturalVsPurifiedEnvStep
namedNaturalVsPurifiedEnvNuanceProduct =
  productConcurrentOp
    (productConcurrentOp naturalEnvSectionLeaf purifiedEnvSectionLeaf)
    class13NaturalVsPurifiedEnvLeaf

named-natural-vs-purified-env-product-concurrent :
  isProductConcurrent namedNaturalVsPurifiedEnvNuanceProduct ≡ true
  × naturalVsPurifiedEnvBundleIsConcurrentProduct naturalVsPurifiedEnvNuanceWitness ≡ true
named-natural-vs-purified-env-product-concurrent = refl , natural-vs-purified-env-nuance-concurrent-product

------------------------------------------------------------------------
-- NaturalVsPurifiedEnvBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data NaturalVsPurifiedEnvAdmissibility : Set where
  natural-vs-purified-env-admissible natural-vs-purified-env-xor-refuse : NaturalVsPurifiedEnvAdmissibility

isNaturalVsPurifiedEnvPreserving : ClassifierNaturalVsPurifiedEnvStep → Bool
isNaturalVsPurifiedEnvPreserving natural-vs-purified-env-identity = true
isNaturalVsPurifiedEnvPreserving (slot-leaf _) = true
isNaturalVsPurifiedEnvPreserving (product-concurrent a b) =
  isNaturalVsPurifiedEnvPreserving a ∧ isNaturalVsPurifiedEnvPreserving b
isNaturalVsPurifiedEnvPreserving (xor-mutually-exclusive _ _) = false

isNaturalVsPurifiedEnvAdmissible : ClassifierNaturalVsPurifiedEnvStep → Bool
isNaturalVsPurifiedEnvAdmissible step = isNaturalVsPurifiedEnvPreserving step

natural-env-section-leaf-admissible : isNaturalVsPurifiedEnvAdmissible naturalEnvSectionLeaf ≡ true
natural-env-section-leaf-admissible = refl

purified-env-section-leaf-admissible : isNaturalVsPurifiedEnvAdmissible purifiedEnvSectionLeaf ≡ true
purified-env-section-leaf-admissible = refl

class13-natural-vs-purified-env-leaf-admissible : isNaturalVsPurifiedEnvAdmissible class13NaturalVsPurifiedEnvLeaf ≡ true
class13-natural-vs-purified-env-leaf-admissible = refl

named-natural-vs-purified-env-admissible : isNaturalVsPurifiedEnvAdmissible namedNaturalVsPurifiedEnvNuanceProduct ≡ true
named-natural-vs-purified-env-admissible = refl

xor-mutually-exclusive-refuse :
  isNaturalVsPurifiedEnvAdmissible (xorMutuallyExclusiveOp naturalEnvSectionLeaf purifiedEnvSectionLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class13-natural-vs-purified-env-refuse :
  isNaturalVsPurifiedEnvAdmissible (xorMutuallyExclusiveOp purifiedEnvSectionLeaf class13NaturalVsPurifiedEnvLeaf) ≡ false
xor-mutually-exclusive-class13-natural-vs-purified-env-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data NaturalVsPurifiedEnvWitnessPresence : Set where
  natural-vs-purified-env-witness-absent natural-vs-purified-env-witness-present : NaturalVsPurifiedEnvWitnessPresence

record ClassifierNaturalVsPurifiedEnvWitness : Set where
  constructor mkClassifierNaturalVsPurifiedEnvWitness
  field
    witness-presence : NaturalVsPurifiedEnvWitnessPresence
    natural-vs-purified-env-gap-total : ℕ

naturalVsPurifiedEnvWitnessAbsent : ClassifierNaturalVsPurifiedEnvWitness
naturalVsPurifiedEnvWitnessAbsent = mkClassifierNaturalVsPurifiedEnvWitness natural-vs-purified-env-witness-absent zero

naturalVsPurifiedEnvWitnessPresentZeroGap : ClassifierNaturalVsPurifiedEnvWitness
naturalVsPurifiedEnvWitnessPresentZeroGap = mkClassifierNaturalVsPurifiedEnvWitness natural-vs-purified-env-witness-present zero

naturalVsPurifiedEnvWitnessPresentWithGaps : ℕ → ClassifierNaturalVsPurifiedEnvWitness
naturalVsPurifiedEnvWitnessPresentWithGaps n = mkClassifierNaturalVsPurifiedEnvWitness natural-vs-purified-env-witness-present n

naturalVsPurifiedEnvWitnessGapFree : ClassifierNaturalVsPurifiedEnvWitness → Bool
naturalVsPurifiedEnvWitnessGapFree (mkClassifierNaturalVsPurifiedEnvWitness natural-vs-purified-env-witness-absent _) = false
naturalVsPurifiedEnvWitnessGapFree (mkClassifierNaturalVsPurifiedEnvWitness natural-vs-purified-env-witness-present n) =
  does (n ℕ-Props.≟ zero)

natural-vs-purified-env-witness-present-zero-gap-free :
  naturalVsPurifiedEnvWitnessGapFree naturalVsPurifiedEnvWitnessPresentZeroGap ≡ true
natural-vs-purified-env-witness-present-zero-gap-free = refl

natural-vs-purified-env-witness-absent-not-gap-free :
  naturalVsPurifiedEnvWitnessGapFree naturalVsPurifiedEnvWitnessAbsent ≡ false
natural-vs-purified-env-witness-absent-not-gap-free = refl

natural-vs-purified-env-witness-with-gaps-not-gap-free :
  ∀ n → naturalVsPurifiedEnvWitnessGapFree (naturalVsPurifiedEnvWitnessPresentWithGaps (suc n)) ≡ false
natural-vs-purified-env-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-NaturalVsPurifiedEnv **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data NaturalVsPurifiedEnvConservationVerdict : Set where
  verdict-unwired-ok verdict-natural-vs-purified-env-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : NaturalVsPurifiedEnvConservationVerdict

naturalVsPurifiedEnvConservationVerdictOk : NaturalVsPurifiedEnvConservationVerdict → Bool
naturalVsPurifiedEnvConservationVerdictOk verdict-unwired-ok = true
naturalVsPurifiedEnvConservationVerdictOk verdict-natural-vs-purified-env-admissible-ok = true
naturalVsPurifiedEnvConservationVerdictOk verdict-concurrent-product-ok = true
naturalVsPurifiedEnvConservationVerdictOk _ = false

evaluateNaturalVsPurifiedEnvConservationClose :
  NaturalVsPurifiedEnvConservationModality → ClassifierNaturalVsPurifiedEnvStep → ClassifierNaturalVsPurifiedEnvWitness
  → NaturalVsPurifiedEnvBundleWitness → Bool → NaturalVsPurifiedEnvConservationVerdict
evaluateNaturalVsPurifiedEnvConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-proved _ (mkClassifierNaturalVsPurifiedEnvWitness natural-vs-purified-env-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-proved _ (mkClassifierNaturalVsPurifiedEnvWitness natural-vs-purified-env-witness-present _) w false
  with naturalVsPurifiedEnvBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-natural-vs-purified-env-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without natural-vs-purified Env witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-unwired namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-assumed namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-surrogate namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  naturalVsPurifiedEnvConservationVerdictOk
    (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-unwired namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false)
    ≡ true
  × naturalVsPurifiedEnvConservationVerdictOk
      (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-assumed namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false)
      ≡ true
  × naturalVsPurifiedEnvConservationVerdictOk
      (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-surrogate namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without natural-vs-purified Env witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  naturalVsPurifiedEnvConservationVerdictOk
    (evaluateNaturalVsPurifiedEnvConservationClose
       natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false ≡
  verdict-natural-vs-purified-env-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-proved
    (xorMutuallyExclusiveOp naturalEnvSectionLeaf purifiedEnvSectionLeaf)
    naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  naturalVsPurifiedEnvConservationVerdictOk
    (evaluateNaturalVsPurifiedEnvConservationClose
       natural-vs-purified-env-conservation-proved
       (xorMutuallyExclusiveOp naturalEnvSectionLeaf purifiedEnvSectionLeaf)
       naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-proved
    (xorMutuallyExclusiveOp naturalEnvSectionLeaf purifiedEnvSectionLeaf)
    naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-natural-vs-purified-env — nuance **product** closed
------------------------------------------------------------------------

natural-vs-purified-env-admissible-ok :
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap unwiredWitness false ≡
  verdict-natural-vs-purified-env-admissible-ok
natural-vs-purified-env-admissible-ok = refl

natural-vs-purified-env-admissible-verdict-ok :
  naturalVsPurifiedEnvConservationVerdictOk
    (evaluateNaturalVsPurifiedEnvConservationClose
       natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap unwiredWitness false)
    ≡ true
natural-vs-purified-env-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — natural-vs-purified Env nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  naturalVsPurifiedEnvConservationVerdictOk
    (evaluateNaturalVsPurifiedEnvConservationClose
       natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-natural-vs-purified-env-proved :
  naturalVsPurifiedEnvConservationVerdictOk
    (evaluateNaturalVsPurifiedEnvConservationClose
       natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness false)
    ≡ true
  × naturalVsPurifiedEnvProved ≡ false
concurrent-product-ok-still-not-natural-vs-purified-env-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateNaturalVsPurifiedEnvConservationClose
    natural-vs-purified-env-conservation-unwired namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  naturalVsPurifiedEnvConservationVerdictOk
    (evaluateNaturalVsPurifiedEnvConservationClose
       natural-vs-purified-env-conservation-unwired namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

naturalVsPurifiedEnvConservationFiberOk : FormalFiber → Bool
naturalVsPurifiedEnvConservationFiberOk fiber-quantum-knowing = true
naturalVsPurifiedEnvConservationFiberOk fiber-meso-acting = false

natural-vs-purified-env-conservation-knowing-fiber-ok :
  naturalVsPurifiedEnvConservationFiberOk fiber-quantum-knowing ≡ true
natural-vs-purified-env-conservation-knowing-fiber-ok = refl

natural-vs-purified-env-conservation-meso-acting-not-ok :
  naturalVsPurifiedEnvConservationFiberOk fiber-meso-acting ≡ false
natural-vs-purified-env-conservation-meso-acting-not-ok = refl

natural-vs-purified-env-conservation-routes-knowing-not-meso :
  naturalVsPurifiedEnvConservationFiberOk fiber-quantum-knowing ≡ true ×
  naturalVsPurifiedEnvConservationFiberOk fiber-meso-acting ≡ false
natural-vs-purified-env-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  naturalVsPurifiedEnvConservationFiberOk fiber-quantum-knowing ∧
  not (naturalVsPurifiedEnvConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 13 natural_vs_purified_env Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

natural-vs-purified-env-not-proved : naturalVsPurifiedEnvProved ≡ false
natural-vs-purified-env-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

natural-vs-purified-env-second-law-conservation-framed : naturalVsPurifiedEnvSecondLawConservationFramed ≡ true
natural-vs-purified-env-second-law-conservation-framed = refl

natural-vs-purified-env-not-xor-pin : naturalVsPurifiedEnvNotXor ≡ true
natural-vs-purified-env-not-xor-pin = natural-vs-purified-env-not-xor

env-restriction-typed-pin : envRestrictionTyped ≡ true
env-restriction-typed-pin = refl

not-parallel-natural-vs-purified-env-axiom-minted-pin : notParallelNaturalVsPurifiedEnvAxiomMinted ≡ true
not-parallel-natural-vs-purified-env-axiom-minted-pin = refl

not-three-chemistries-not-forked-pin : notThreeChemistriesNotForked ≡ true
not-three-chemistries-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel natural_vs_purified_env axiom fork)
------------------------------------------------------------------------

naturalVsPurifiedEnvConservationAxiom :
  (naturalVsPurifiedEnvProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (naturalVsPurifiedEnvSecondLawConservationFramed ≡ true)
  × (naturalVsPurifiedEnvNotXor ≡ true)
  × (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-unwired namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessAbsent naturalVsPurifiedEnvNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-proved (xorMutuallyExclusiveOp naturalEnvSectionLeaf purifiedEnvSectionLeaf) naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap unwiredWitness false ≡ verdict-natural-vs-purified-env-admissible-ok)
  × (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-proved namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (naturalVsPurifiedEnvConservationFiberOk fiber-quantum-knowing ≡ true)
  × (naturalVsPurifiedEnvConservationFiberOk fiber-meso-acting ≡ false)
  × (naturalVsPurifiedEnvConservationVerdictOk (evaluateNaturalVsPurifiedEnvConservationClose natural-vs-purified-env-conservation-unwired namedNaturalVsPurifiedEnvNuanceProduct naturalVsPurifiedEnvWitnessPresentZeroGap naturalVsPurifiedEnvNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp naturalVsPurifiedEnvIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a naturalVsPurifiedEnvIdentity) ≡ true)
  × (isNaturalVsPurifiedEnvAdmissible (xorMutuallyExclusiveOp naturalEnvSectionLeaf purifiedEnvSectionLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (naturalVsPurifiedEnvClassIndex ≡ 13)
  × (NaturalVsPurifiedEnvBundleWitness.present-count naturalVsPurifiedEnvNuanceWitness ≡ 3)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oganesson ≡ 118)
naturalVsPurifiedEnvConservationAxiom =
  natural-vs-purified-env-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , natural-vs-purified-env-second-law-conservation-framed
  , natural-vs-purified-env-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , natural-vs-purified-env-admissible-ok
  , concurrent-product-ok
  , natural-vs-purified-env-conservation-knowing-fiber-ok
  , natural-vs-purified-env-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , natural-vs-purified-env-class-index-thirteen
  , natural-vs-purified-env-nuance-present-count
  , hydrogen-z-1
  , oganesson-z-118

naturalVsPurifiedEnvConservationNamed : String
naturalVsPurifiedEnvConservationNamed =
  "naturalVsPurifiedEnvConservation: class 13 natural_vs_purified_env conservation concurrent Pi_c identity conserved natural Env section purified Env section class 13 natural_vs_purified_env concurrent product identity conserved present ge 2 product not XOR env restriction typed no parallel natural_vs_purified_env axiom not three chemistries"

naturalVsPurifiedEnvConservationCrossWitnessAuthority : String
naturalVsPurifiedEnvConservationCrossWitnessAuthority =
  "umst/umst-chem/src/element_restriction_along_environment.rs"

naturalVsPurifiedEnvEnvSectionsAuthority : String
naturalVsPurifiedEnvEnvSectionsAuthority =
  "umst/umst-chem/src/environment_three_sample_spaces_not_xor.rs"

chemPhysicsChartAuthority : String
chemPhysicsChartAuthority =
  "umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs"

goldschmidtAuthority : String
goldschmidtAuthority =
  "umst/umst-chem/src/l0_tables/goldschmidt.rs"

naturalVsPurifiedEnvConservationCellId : String
naturalVsPurifiedEnvConservationCellId = "CHEM-FORMAL-Q-AGDA-NATURAL-VS-PURIFIED-ENV-CONSERVATION"

naturalVsPurifiedEnvConservationNonClaim : String
naturalVsPurifiedEnvConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-NATURAL-VS-PURIFIED-ENV-CONSERVATION class 13 natural_vs_purified_env conservation concurrent Pi_c identity conserved natural Env section purified Env section class 13 natural_vs_purified_env product not XOR env restriction typed no parallel natural_vs_purified_env axiom not three chemistries XOR mutually exclusive refuse natural-vs-purified Env nuance witness concurrent naturalVsPurifiedEnvProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite element_restriction_along_environment.rs environment_three_sample_spaces_not_xor.rs chem_physics_chart_isomorphism.rs not fork not physics GREEN not production_wired not 26th axiom"

natural-vs-purified-env-conservation-cell-id :
  naturalVsPurifiedEnvConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-NATURAL-VS-PURIFIED-ENV-CONSERVATION"
natural-vs-purified-env-conservation-cell-id = refl

natural-vs-purified-env-conservation-cites-element-restriction-rs :
  naturalVsPurifiedEnvConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/element_restriction_along_environment.rs"
natural-vs-purified-env-conservation-cites-element-restriction-rs = refl

natural-vs-purified-env-conservation-cites-l0-table-rs :
  naturalVsPurifiedEnvEnvSectionsAuthority ≡
  "umst/umst-chem/src/environment_three_sample_spaces_not_xor.rs"
natural-vs-purified-env-conservation-cites-l0-table-rs = refl

natural-vs-purified-env-conservation-modality-unwired :
  naturalVsPurifiedEnvConservationModalityCurrent ≡ natural-vs-purified-env-conservation-unwired
natural-vs-purified-env-conservation-modality-unwired = refl

naturalVsPurifiedEnvConservationPhysicsGreenAuthorized : Set
naturalVsPurifiedEnvConservationPhysicsGreenAuthorized = ⊥

natural-vs-purified-env-conservation-physics-green-false : ¬ naturalVsPurifiedEnvConservationPhysicsGreenAuthorized
natural-vs-purified-env-conservation-physics-green-false ()

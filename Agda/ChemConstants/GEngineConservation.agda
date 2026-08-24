-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.GEngineConservation.agda
--
-- CHEM-FORMAL-Q-AGDA-G-ENGINE-CONSERVATION
-- Constitutive **G-engine** L0 **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (L0 constitutive + not L1 cement copy +
--     G-engine may sort not mint; **product** not XOR, no parallel G-engine axiom)
--   * XOR mutually-exclusive refuse; G-engine nuance witness concurrent
--     (L0 constitutive + not L1 cement copy + may sort not mint)
--   * **G-engine** laws Unwired (gEngineProved = false)
--   * constitutive G-engine L0, not L1 cement copy — not a 26th axiom
--
-- INT (read-only cite): umst/umst-chem/src/x_rows/chem_physics_chart_isomorphism.rs
-- L1 fence: umst/umst-chem/src/x_rows/cement_hydration_not_l0_g.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- G-engine may sort not mint; not L1 cement copy. Product not XOR.
-- WAVE100: no lib.rs / eos.rs / nano wiring.
------------------------------------------------------------------------
module ChemConstants.GEngineConservation where


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
-- Modality + constitutive **G-engine** L0 **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data GEngineConservationModality : Set where
  g-engine-conservation-unwired g-engine-conservation-assumed
    g-engine-conservation-proved g-engine-conservation-surrogate
    : GEngineConservationModality

gEngineConservationModalityCurrent : GEngineConservationModality
gEngineConservationModalityCurrent = g-engine-conservation-unwired

gEngineProved productionWired not118SquaredGreenTable
  gEngineSecondLawConservationFramed gEngineNotXor : Bool
gEngineProved = false
productionWired = false
not118SquaredGreenTable = true
gEngineSecondLawConservationFramed = true
gEngineNotXor = true

l0ConstitutiveTyped gEngineMaySortNotMint notL1CementCopy : Bool
l0ConstitutiveTyped = true
gEngineMaySortNotMint = true
notL1CementCopy = true

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
-- G-engine conservation index pin
------------------------------------------------------------------------

gEngineConservationIndex : ℕ
gEngineConservationIndex = 14

g-engine-conservation-index-one : gEngineConservationIndex ≡ 14
g-engine-conservation-index-one = refl

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
-- GEngineBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data GEngineBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : GEngineBundleSlot

isSlotPresent : GEngineBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- GEngineBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record GEngineBundle : Set where
  field slot : ℕ → GEngineBundleSlot

gEngineBundleUnwired : GEngineBundle
gEngineBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : GEngineBundle → ℕ → GEngineBundleSlot → GEngineBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else GEngineBundle.slot b j }

withPresent : GEngineBundle → ℕ → GEngineBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record GEngineBundleWitness : Set where
  constructor mkGEngineBundleWitness
  field
    bundle : GEngineBundle
    present-count : ℕ

gEngineBundleIsConcurrentProduct : GEngineBundleWitness → Bool
gEngineBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? GEngineBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named catalysis channel indices — interact restriction (1), not extra force (2), class 14 catalysis (3)
------------------------------------------------------------------------

l0ConstitutiveChannelIndex notL1CementCopyChannelIndex gEngineMaySortNotMintChannelIndex : ℕ
l0ConstitutiveChannelIndex = 1
notL1CementCopyChannelIndex = 2
gEngineMaySortNotMintChannelIndex = 3

l0-constitutive-index-one : l0ConstitutiveChannelIndex ≡ 1
l0-constitutive-index-one = refl

not-l1-cement-copy-index-two : notL1CementCopyChannelIndex ≡ 2
not-l1-cement-copy-index-two = refl

g-engine-may-sort-not-mint-index-three : gEngineMaySortNotMintChannelIndex ≡ 3
g-engine-may-sort-not-mint-index-three = refl

------------------------------------------------------------------------
-- Catalysis nuance witness — interact restriction + not extra force + class 14 catalysis concurrent
------------------------------------------------------------------------

gEngineNuanceBundle : GEngineBundle
gEngineNuanceBundle =
  withPresent
    (withPresent
      (withPresent gEngineBundleUnwired l0ConstitutiveChannelIndex)
      notL1CementCopyChannelIndex)
    gEngineMaySortNotMintChannelIndex

gEngineNuanceWitness : GEngineBundleWitness
gEngineNuanceWitness =
  mkGEngineBundleWitness gEngineNuanceBundle 3

g-engine-nuance-interact-restriction-present :
  isSlotPresent (GEngineBundle.slot gEngineNuanceBundle l0ConstitutiveChannelIndex) ≡ true
g-engine-nuance-interact-restriction-present = refl

g-engine-nuance-not-extra-force-present :
  isSlotPresent (GEngineBundle.slot gEngineNuanceBundle notL1CementCopyChannelIndex) ≡ true
g-engine-nuance-not-extra-force-present = refl

g-engine-nuance-class14-catalysis-present :
  isSlotPresent (GEngineBundle.slot gEngineNuanceBundle gEngineMaySortNotMintChannelIndex) ≡ true
g-engine-nuance-class14-catalysis-present = refl

g-engine-nuance-present-count : GEngineBundleWitness.present-count gEngineNuanceWitness ≡ 3
g-engine-nuance-present-count = refl

g-engine-nuance-concurrent-product :
  gEngineBundleIsConcurrentProduct gEngineNuanceWitness ≡ true
g-engine-nuance-concurrent-product = refl

g-engine-nuance-three-factors-concurrent :
  isSlotPresent (GEngineBundle.slot gEngineNuanceBundle l0ConstitutiveChannelIndex) ≡ true
  × isSlotPresent (GEngineBundle.slot gEngineNuanceBundle notL1CementCopyChannelIndex) ≡ true
  × isSlotPresent (GEngineBundle.slot gEngineNuanceBundle gEngineMaySortNotMintChannelIndex) ≡ true
  × GEngineBundleWitness.present-count gEngineNuanceWitness ≡ 3
g-engine-nuance-three-factors-concurrent =
  g-engine-nuance-interact-restriction-present
  , g-engine-nuance-not-extra-force-present
  , g-engine-nuance-class14-catalysis-present
  , g-engine-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : GEngineBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if gEngineBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = GEngineBundleWitness.bundle w
       in if isSlotPresent (GEngineBundle.slot b i)
          then if isSlotPresent (GEngineBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : GEngineBundleWitness
unwiredWitness = mkGEngineBundleWitness gEngineBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

g-engine-nuance-xor-product-ok :
  evaluateXorRefuse gEngineNuanceWitness l0ConstitutiveChannelIndex notL1CementCopyChannelIndex ≡ xor-product-ok
g-engine-nuance-xor-product-ok = refl

g-engine-not-xor : gEngineNotXor ≡ true
g-engine-not-xor = refl

------------------------------------------------------------------------
-- ClassifierGEngineStep scaffold — GEngineBundle **conservation**
------------------------------------------------------------------------

data ClassifierGEngineStep : Set where
  g-engine-identity : ClassifierGEngineStep
  slot-leaf : ℕ → ClassifierGEngineStep
  product-concurrent : ClassifierGEngineStep → ClassifierGEngineStep → ClassifierGEngineStep
  xor-mutually-exclusive : ClassifierGEngineStep → ClassifierGEngineStep → ClassifierGEngineStep

gEngineIdentity : ClassifierGEngineStep
gEngineIdentity = g-engine-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierGEngineStep → ClassifierGEngineStep → ClassifierGEngineStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

l0ConstitutiveLeaf notL1CementCopyLeaf gEngineMaySortNotMintLeaf : ClassifierGEngineStep
l0ConstitutiveLeaf = slot-leaf l0ConstitutiveChannelIndex
notL1CementCopyLeaf = slot-leaf notL1CementCopyChannelIndex
gEngineMaySortNotMintLeaf = slot-leaf gEngineMaySortNotMintChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierGEngineStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isGEngineIdentity : ClassifierGEngineStep → Bool
isGEngineIdentity g-engine-identity = true
isGEngineIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at g-engine-identity
------------------------------------------------------------------------

g-engine-left-identity :
  ∀ (a : ClassifierGEngineStep) →
  isGEngineIdentity gEngineIdentity ≡ true
  × isProductConcurrent (productConcurrentOp gEngineIdentity a) ≡ true
g-engine-left-identity a = refl , refl

g-engine-right-identity :
  ∀ (a : ClassifierGEngineStep) →
  isProductConcurrent (productConcurrentOp a gEngineIdentity) ≡ true
  × isGEngineIdentity gEngineIdentity ≡ true
g-engine-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-g-engine :
  (∀ a → isProductConcurrent (productConcurrentOp gEngineIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a gEngineIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-g-engine =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named catalysis nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedGEngineNuanceProduct : ClassifierGEngineStep
namedGEngineNuanceProduct =
  productConcurrentOp
    (productConcurrentOp l0ConstitutiveLeaf notL1CementCopyLeaf)
    gEngineMaySortNotMintLeaf

named-g-engine-nuance-product-concurrent :
  isProductConcurrent namedGEngineNuanceProduct ≡ true
  × gEngineBundleIsConcurrentProduct gEngineNuanceWitness ≡ true
named-g-engine-nuance-product-concurrent = refl , g-engine-nuance-concurrent-product

------------------------------------------------------------------------
-- GEngineBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data GEngineAdmissibility : Set where
  g-engine-admissible g-engine-xor-refuse : GEngineAdmissibility

isGEnginePreserving : ClassifierGEngineStep → Bool
isGEnginePreserving g-engine-identity = true
isGEnginePreserving (slot-leaf _) = true
isGEnginePreserving (product-concurrent a b) =
  isGEnginePreserving a ∧ isGEnginePreserving b
isGEnginePreserving (xor-mutually-exclusive _ _) = false

isGEngineAdmissible : ClassifierGEngineStep → Bool
isGEngineAdmissible step = isGEnginePreserving step

interact-restriction-leaf-admissible : isGEngineAdmissible l0ConstitutiveLeaf ≡ true
interact-restriction-leaf-admissible = refl

not-extra-force-leaf-admissible : isGEngineAdmissible notL1CementCopyLeaf ≡ true
not-extra-force-leaf-admissible = refl

class14-catalysis-leaf-admissible : isGEngineAdmissible gEngineMaySortNotMintLeaf ≡ true
class14-catalysis-leaf-admissible = refl

named-g-engine-nuance-admissible : isGEngineAdmissible namedGEngineNuanceProduct ≡ true
named-g-engine-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isGEngineAdmissible (xorMutuallyExclusiveOp l0ConstitutiveLeaf notL1CementCopyLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class14-catalysis-refuse :
  isGEngineAdmissible (xorMutuallyExclusiveOp notL1CementCopyLeaf gEngineMaySortNotMintLeaf) ≡ false
xor-mutually-exclusive-class14-catalysis-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data GEngineWitnessPresence : Set where
  g-engine-witness-absent g-engine-witness-present : GEngineWitnessPresence

record ClassifierGEngineWitness : Set where
  constructor mkClassifierGEngineWitness
  field
    witness-presence : GEngineWitnessPresence
    catalysis-gap-total : ℕ

gEngineWitnessAbsent : ClassifierGEngineWitness
gEngineWitnessAbsent = mkClassifierGEngineWitness g-engine-witness-absent zero

gEngineWitnessPresentZeroGap : ClassifierGEngineWitness
gEngineWitnessPresentZeroGap = mkClassifierGEngineWitness g-engine-witness-present zero

gEngineWitnessPresentWithGaps : ℕ → ClassifierGEngineWitness
gEngineWitnessPresentWithGaps n = mkClassifierGEngineWitness g-engine-witness-present n

gEngineWitnessGapFree : ClassifierGEngineWitness → Bool
gEngineWitnessGapFree (mkClassifierGEngineWitness g-engine-witness-absent _) = false
gEngineWitnessGapFree (mkClassifierGEngineWitness g-engine-witness-present n) =
  does (n ℕ-Props.≟ zero)

g-engine-witness-present-zero-gap-free :
  gEngineWitnessGapFree gEngineWitnessPresentZeroGap ≡ true
g-engine-witness-present-zero-gap-free = refl

g-engine-witness-absent-not-gap-free :
  gEngineWitnessGapFree gEngineWitnessAbsent ≡ false
g-engine-witness-absent-not-gap-free = refl

g-engine-witness-with-gaps-not-gap-free :
  ∀ n → gEngineWitnessGapFree (gEngineWitnessPresentWithGaps (suc n)) ≡ false
g-engine-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Catalysis **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data GEngineConservationVerdict : Set where
  verdict-unwired-ok verdict-g-engine-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : GEngineConservationVerdict

gEngineConservationVerdictOk : GEngineConservationVerdict → Bool
gEngineConservationVerdictOk verdict-unwired-ok = true
gEngineConservationVerdictOk verdict-g-engine-admissible-ok = true
gEngineConservationVerdictOk verdict-concurrent-product-ok = true
gEngineConservationVerdictOk _ = false

evaluateGEngineConservationClose :
  GEngineConservationModality → ClassifierGEngineStep → ClassifierGEngineWitness
  → GEngineBundleWitness → Bool → GEngineConservationVerdict
evaluateGEngineConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateGEngineConservationClose g-engine-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateGEngineConservationClose g-engine-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateGEngineConservationClose g-engine-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateGEngineConservationClose g-engine-conservation-proved _ (mkClassifierGEngineWitness g-engine-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateGEngineConservationClose g-engine-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateGEngineConservationClose g-engine-conservation-proved _ (mkClassifierGEngineWitness g-engine-witness-present _) w false
  with gEngineBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-g-engine-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without catalysis witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateGEngineConservationClose
    g-engine-conservation-unwired namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateGEngineConservationClose
    g-engine-conservation-assumed namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateGEngineConservationClose
    g-engine-conservation-surrogate namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  gEngineConservationVerdictOk
    (evaluateGEngineConservationClose g-engine-conservation-unwired namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false)
    ≡ true
  × gEngineConservationVerdictOk
      (evaluateGEngineConservationClose g-engine-conservation-assumed namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false)
      ≡ true
  × gEngineConservationVerdictOk
      (evaluateGEngineConservationClose g-engine-conservation-surrogate namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without catalysis witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateGEngineConservationClose
    g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  gEngineConservationVerdictOk
    (evaluateGEngineConservationClose
       g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateGEngineConservationClose
    g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false ≡
  verdict-g-engine-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateGEngineConservationClose
    g-engine-conservation-proved
    (xorMutuallyExclusiveOp l0ConstitutiveLeaf notL1CementCopyLeaf)
    gEngineWitnessPresentZeroGap gEngineNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  gEngineConservationVerdictOk
    (evaluateGEngineConservationClose
       g-engine-conservation-proved
       (xorMutuallyExclusiveOp l0ConstitutiveLeaf notL1CementCopyLeaf)
       gEngineWitnessPresentZeroGap gEngineNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateGEngineConservationClose
    g-engine-conservation-proved
    (xorMutuallyExclusiveOp l0ConstitutiveLeaf notL1CementCopyLeaf)
    gEngineWitnessPresentZeroGap gEngineNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-catalysis — nuance **product** closed
------------------------------------------------------------------------

g-engine-admissible-ok :
  evaluateGEngineConservationClose
    g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessPresentZeroGap unwiredWitness false ≡
  verdict-g-engine-admissible-ok
g-engine-admissible-ok = refl

g-engine-admissible-verdict-ok :
  gEngineConservationVerdictOk
    (evaluateGEngineConservationClose
       g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessPresentZeroGap unwiredWitness false)
    ≡ true
g-engine-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — catalysis nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateGEngineConservationClose
    g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessPresentZeroGap gEngineNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  gEngineConservationVerdictOk
    (evaluateGEngineConservationClose
       g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessPresentZeroGap gEngineNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-catalysis14-proved :
  gEngineConservationVerdictOk
    (evaluateGEngineConservationClose
       g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessPresentZeroGap gEngineNuanceWitness false)
    ≡ true
  × gEngineProved ≡ false
concurrent-product-ok-still-not-catalysis14-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateGEngineConservationClose
    g-engine-conservation-unwired namedGEngineNuanceProduct gEngineWitnessPresentZeroGap gEngineNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  gEngineConservationVerdictOk
    (evaluateGEngineConservationClose
       g-engine-conservation-unwired namedGEngineNuanceProduct gEngineWitnessPresentZeroGap gEngineNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

gEngineConservationFiberOk : FormalFiber → Bool
gEngineConservationFiberOk fiber-quantum-knowing = true
gEngineConservationFiberOk fiber-meso-acting = false

g-engine-conservation-knowing-fiber-ok :
  gEngineConservationFiberOk fiber-quantum-knowing ≡ true
g-engine-conservation-knowing-fiber-ok = refl

g-engine-conservation-meso-acting-not-ok :
  gEngineConservationFiberOk fiber-meso-acting ≡ false
g-engine-conservation-meso-acting-not-ok = refl

g-engine-conservation-routes-knowing-not-meso :
  gEngineConservationFiberOk fiber-quantum-knowing ≡ true ×
  gEngineConservationFiberOk fiber-meso-acting ≡ false
g-engine-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  gEngineConservationFiberOk fiber-quantum-knowing ∧
  not (gEngineConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 14 catalysis Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

g-engine-not-proved : gEngineProved ≡ false
g-engine-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

g-engine-second-law-conservation-framed : gEngineSecondLawConservationFramed ≡ true
g-engine-second-law-conservation-framed = refl

g-engine-not-xor-pin : gEngineNotXor ≡ true
g-engine-not-xor-pin = g-engine-not-xor

l0-constitutive-typed-pin : l0ConstitutiveTyped ≡ true
l0-constitutive-typed-pin = refl

g-engine-may-sort-not-mint-pin : gEngineMaySortNotMint ≡ true
g-engine-may-sort-not-mint-pin = refl

not-l1-cement-copy-pin : notL1CementCopy ≡ true
not-l1-cement-copy-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel catalysis axiom fork)
------------------------------------------------------------------------

gEngineConservationAxiom :
  (gEngineProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (gEngineSecondLawConservationFramed ≡ true)
  × (gEngineNotXor ≡ true)
  × (evaluateGEngineConservationClose g-engine-conservation-unwired namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateGEngineConservationClose g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessAbsent gEngineNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateGEngineConservationClose g-engine-conservation-proved (xorMutuallyExclusiveOp l0ConstitutiveLeaf notL1CementCopyLeaf) gEngineWitnessPresentZeroGap gEngineNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateGEngineConservationClose g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessPresentZeroGap unwiredWitness false ≡ verdict-g-engine-admissible-ok)
  × (evaluateGEngineConservationClose g-engine-conservation-proved namedGEngineNuanceProduct gEngineWitnessPresentZeroGap gEngineNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (gEngineConservationFiberOk fiber-quantum-knowing ≡ true)
  × (gEngineConservationFiberOk fiber-meso-acting ≡ false)
  × (gEngineConservationVerdictOk (evaluateGEngineConservationClose g-engine-conservation-unwired namedGEngineNuanceProduct gEngineWitnessPresentZeroGap gEngineNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp gEngineIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a gEngineIdentity) ≡ true)
  × (isGEngineAdmissible (xorMutuallyExclusiveOp l0ConstitutiveLeaf notL1CementCopyLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (gEngineConservationIndex ≡ 14)
  × (GEngineBundleWitness.present-count gEngineNuanceWitness ≡ 3)
  × (elementAtomicZ platinum ≡ 78)
  × (elementAtomicZ oganesson ≡ 118)
gEngineConservationAxiom =
  g-engine-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , g-engine-second-law-conservation-framed
  , g-engine-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , g-engine-admissible-ok
  , concurrent-product-ok
  , g-engine-conservation-knowing-fiber-ok
  , g-engine-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , g-engine-conservation-index-one
  , g-engine-nuance-present-count
  , platinum-z-78
  , oganesson-z-118

gEngineConservationNamed : String
gEngineConservationNamed =
  "gEngineConservation: constitutive G-engine L0 conservation concurrent Pi_c identity conserved L0 constitutive not L1 cement copy may sort not mint concurrent product identity conserved present ge 2 product not XOR L0 constitutive typed G-engine may sort not mint not L1 cement copy"

gEngineConservationCrossWitnessAuthority : String
gEngineConservationCrossWitnessAuthority =
  "umst/umst-chem/src/chem_physics_chart_isomorphism.rs"

gEngineChartAuthority : String
gEngineChartAuthority =
  "umst/umst-chem/src/x_rows/cement_hydration_not_l0_g.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/thermo_g.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/x_rows/heavy_z_relativistic_continuum.rs"

gEngineConservationCellId : String
gEngineConservationCellId = "CHEM-FORMAL-Q-AGDA-G-ENGINE-CONSERVATION"

gEngineConservationNonClaim : String
gEngineConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-G-ENGINE-CONSERVATION constitutive G-engine L0 conservation concurrent Pi_c identity conserved L0 constitutive not L1 cement copy may sort not mint product not XOR L0 constitutive typed G-engine may sort not mint not L1 cement copy XOR mutually exclusive refuse G-engine nuance witness concurrent gEngineProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite chem_physics_chart_isomorphism.rs cement_hydration_not_l0_g not fork not physics GREEN not production_wired not 26th axiom"

g-engine-conservation-cell-id :
  gEngineConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-G-ENGINE-CONSERVATION"
g-engine-conservation-cell-id = refl

g-engine-conservation-cites-catalysis-barrier-rs :
  gEngineConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/chem_physics_chart_isomorphism.rs"
g-engine-conservation-cites-catalysis-barrier-rs = refl

g-engine-conservation-cites-l0-table-rs :
  gEngineChartAuthority ≡
  "umst/umst-chem/src/x_rows/cement_hydration_not_l0_g.rs"
g-engine-conservation-cites-l0-table-rs = refl

g-engine-conservation-modality-unwired :
  gEngineConservationModalityCurrent ≡ g-engine-conservation-unwired
g-engine-conservation-modality-unwired = refl

gEngineConservationPhysicsGreenAuthorized : Set
gEngineConservationPhysicsGreenAuthorized = ⊥

g-engine-conservation-physics-green-false : ¬ gEngineConservationPhysicsGreenAuthorized
g-engine-conservation-physics-green-false ()

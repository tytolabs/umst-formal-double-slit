-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.OtherNamedNuanceConservation.agda
--
-- Pattern class 24 **other named nuance** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (Interact restriction + not XOR + class 24 other named nuance;
--     **product** not XOR, no parallel other_named_nuance axiom)
--   * XOR mutually-exclusive refuse; other named nuance witness concurrent
--     (Interact restriction + not XOR + class 24 other named nuance)
--   * **other named nuance** laws Unwired (otherNamedNuance24Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/l0_tables/other_named_nuance.rs
-- L0 factors: umst/umst-chem/src/l0_tables/pattern_named_factors.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel other_named_nuance axiom; product not XOR.
-- Class 24 other named nuance as concurrent Π_c factor, not XOR enum growth.
module ChemConstants.OtherNamedNuanceConservation where


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
-- Modality + pattern class 24 **other named nuance** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data OtherNamedNuanceConservationModality : Set where
  other-named-nuance-conservation-unwired other-named-nuance-conservation-assumed
    other-named-nuance-conservation-proved other-named-nuance-conservation-surrogate
    : OtherNamedNuanceConservationModality

otherNamedNuanceConservationModalityCurrent : OtherNamedNuanceConservationModality
otherNamedNuanceConservationModalityCurrent = other-named-nuance-conservation-unwired

otherNamedNuance24Proved productionWired not118SquaredGreenTable
  otherNamedNuanceSecondLawConservationFramed otherNamedNuanceNotXor : Bool
otherNamedNuance24Proved = false
productionWired = false
not118SquaredGreenTable = true
otherNamedNuanceSecondLawConservationFramed = true
otherNamedNuanceNotXor = true

interactRestrictionTyped notParallelOtherNamedNuanceAxiomMinted extraForceNotForked : Bool
interactRestrictionTyped = true
notParallelOtherNamedNuanceAxiomMinted = true
extraForceNotForked = true

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
-- Pattern class 24 other named nuance index pin
------------------------------------------------------------------------

otherNamedNuanceClassIndex : ℕ
otherNamedNuanceClassIndex = 24

other-named-nuance-class-index-twenty-four : otherNamedNuanceClassIndex ≡ 24
other-named-nuance-class-index-twenty-four = refl

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
-- OtherNamedNuanceBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data OtherNamedNuanceBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : OtherNamedNuanceBundleSlot

isSlotPresent : OtherNamedNuanceBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- OtherNamedNuanceBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record OtherNamedNuanceBundle : Set where
  field slot : ℕ → OtherNamedNuanceBundleSlot

otherNamedNuanceBundleUnwired : OtherNamedNuanceBundle
otherNamedNuanceBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : OtherNamedNuanceBundle → ℕ → OtherNamedNuanceBundleSlot → OtherNamedNuanceBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else OtherNamedNuanceBundle.slot b j }

withPresent : OtherNamedNuanceBundle → ℕ → OtherNamedNuanceBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record OtherNamedNuanceBundleWitness : Set where
  constructor mkOtherNamedNuanceBundleWitness
  field
    bundle : OtherNamedNuanceBundle
    present-count : ℕ

otherNamedNuanceBundleIsConcurrentProduct : OtherNamedNuanceBundleWitness → Bool
otherNamedNuanceBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? OtherNamedNuanceBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named other named nuance channel indices — interact restriction (1), not extra force (2), class 24 other named nuance (3)
------------------------------------------------------------------------

interactRestrictionChannelIndex notExtraForceChannelIndex class24OtherNamedNuanceChannelIndex : ℕ
interactRestrictionChannelIndex = 1
notExtraForceChannelIndex = 2
class24OtherNamedNuanceChannelIndex = 3

interact-restriction-index-one : interactRestrictionChannelIndex ≡ 1
interact-restriction-index-one = refl

not-extra-force-index-two : notExtraForceChannelIndex ≡ 2
not-extra-force-index-two = refl

class24-other-named-nuance-index-three : class24OtherNamedNuanceChannelIndex ≡ 3
class24-other-named-nuance-index-three = refl

------------------------------------------------------------------------
-- Other named nuance witness — interact restriction + not extra force + class 24 other named nuance concurrent
------------------------------------------------------------------------

otherNamedNuanceBundle : OtherNamedNuanceBundle
otherNamedNuanceBundle =
  withPresent
    (withPresent
      (withPresent otherNamedNuanceBundleUnwired interactRestrictionChannelIndex)
      notExtraForceChannelIndex)
    class24OtherNamedNuanceChannelIndex

otherNamedNuanceWitness : OtherNamedNuanceBundleWitness
otherNamedNuanceWitness =
  mkOtherNamedNuanceBundleWitness otherNamedNuanceBundle 3

other-named-nuance-interact-restriction-present :
  isSlotPresent (OtherNamedNuanceBundle.slot otherNamedNuanceBundle interactRestrictionChannelIndex) ≡ true
other-named-nuance-interact-restriction-present = refl

other-named-nuance-not-extra-force-present :
  isSlotPresent (OtherNamedNuanceBundle.slot otherNamedNuanceBundle notExtraForceChannelIndex) ≡ true
other-named-nuance-not-extra-force-present = refl

other-named-nuance-class24-other-named-nuance-present :
  isSlotPresent (OtherNamedNuanceBundle.slot otherNamedNuanceBundle class24OtherNamedNuanceChannelIndex) ≡ true
other-named-nuance-class24-other-named-nuance-present = refl

other-named-nuance-present-count : OtherNamedNuanceBundleWitness.present-count otherNamedNuanceWitness ≡ 3
other-named-nuance-present-count = refl

other-named-nuance-concurrent-product :
  otherNamedNuanceBundleIsConcurrentProduct otherNamedNuanceWitness ≡ true
other-named-nuance-concurrent-product = refl

other-named-nuance-three-factors-concurrent :
  isSlotPresent (OtherNamedNuanceBundle.slot otherNamedNuanceBundle interactRestrictionChannelIndex) ≡ true
  × isSlotPresent (OtherNamedNuanceBundle.slot otherNamedNuanceBundle notExtraForceChannelIndex) ≡ true
  × isSlotPresent (OtherNamedNuanceBundle.slot otherNamedNuanceBundle class24OtherNamedNuanceChannelIndex) ≡ true
  × OtherNamedNuanceBundleWitness.present-count otherNamedNuanceWitness ≡ 3
other-named-nuance-three-factors-concurrent =
  other-named-nuance-interact-restriction-present
  , other-named-nuance-not-extra-force-present
  , other-named-nuance-class24-other-named-nuance-present
  , other-named-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : OtherNamedNuanceBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if otherNamedNuanceBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = OtherNamedNuanceBundleWitness.bundle w
       in if isSlotPresent (OtherNamedNuanceBundle.slot b i)
          then if isSlotPresent (OtherNamedNuanceBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : OtherNamedNuanceBundleWitness
unwiredWitness = mkOtherNamedNuanceBundleWitness otherNamedNuanceBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

other-named-nuance-xor-product-ok :
  evaluateXorRefuse otherNamedNuanceWitness interactRestrictionChannelIndex notExtraForceChannelIndex ≡ xor-product-ok
other-named-nuance-xor-product-ok = refl

other-named-nuance-not-xor : otherNamedNuanceNotXor ≡ true
other-named-nuance-not-xor = refl

------------------------------------------------------------------------
-- ClassifierOtherNamedNuanceStep scaffold — OtherNamedNuanceBundle **conservation**
------------------------------------------------------------------------

data ClassifierOtherNamedNuanceStep : Set where
  other-named-nuance-identity : ClassifierOtherNamedNuanceStep
  slot-leaf : ℕ → ClassifierOtherNamedNuanceStep
  product-concurrent : ClassifierOtherNamedNuanceStep → ClassifierOtherNamedNuanceStep → ClassifierOtherNamedNuanceStep
  xor-mutually-exclusive : ClassifierOtherNamedNuanceStep → ClassifierOtherNamedNuanceStep → ClassifierOtherNamedNuanceStep

otherNamedNuanceIdentity : ClassifierOtherNamedNuanceStep
otherNamedNuanceIdentity = other-named-nuance-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierOtherNamedNuanceStep → ClassifierOtherNamedNuanceStep → ClassifierOtherNamedNuanceStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

interactRestrictionLeaf notExtraForceLeaf class24OtherNamedNuanceLeaf : ClassifierOtherNamedNuanceStep
interactRestrictionLeaf = slot-leaf interactRestrictionChannelIndex
notExtraForceLeaf = slot-leaf notExtraForceChannelIndex
class24OtherNamedNuanceLeaf = slot-leaf class24OtherNamedNuanceChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierOtherNamedNuanceStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isOtherNamedNuanceIdentity : ClassifierOtherNamedNuanceStep → Bool
isOtherNamedNuanceIdentity other-named-nuance-identity = true
isOtherNamedNuanceIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at other-named-nuance-identity
------------------------------------------------------------------------

other-named-nuance-left-identity :
  ∀ (a : ClassifierOtherNamedNuanceStep) →
  isOtherNamedNuanceIdentity otherNamedNuanceIdentity ≡ true
  × isProductConcurrent (productConcurrentOp otherNamedNuanceIdentity a) ≡ true
other-named-nuance-left-identity a = refl , refl

other-named-nuance-right-identity :
  ∀ (a : ClassifierOtherNamedNuanceStep) →
  isProductConcurrent (productConcurrentOp a otherNamedNuanceIdentity) ≡ true
  × isOtherNamedNuanceIdentity otherNamedNuanceIdentity ≡ true
other-named-nuance-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-other-named-nuance :
  (∀ a → isProductConcurrent (productConcurrentOp otherNamedNuanceIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a otherNamedNuanceIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-other-named-nuance =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named other named nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedOtherNamedNuanceProduct : ClassifierOtherNamedNuanceStep
namedOtherNamedNuanceProduct =
  productConcurrentOp
    (productConcurrentOp interactRestrictionLeaf notExtraForceLeaf)
    class24OtherNamedNuanceLeaf

named-other-named-nuance-product-concurrent :
  isProductConcurrent namedOtherNamedNuanceProduct ≡ true
  × otherNamedNuanceBundleIsConcurrentProduct otherNamedNuanceWitness ≡ true
named-other-named-nuance-product-concurrent = refl , other-named-nuance-concurrent-product

------------------------------------------------------------------------
-- OtherNamedNuanceBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data OtherNamedNuanceAdmissibility : Set where
  other-named-nuance-admissible other-named-nuance-xor-refuse : OtherNamedNuanceAdmissibility

isOtherNamedNuancePreserving : ClassifierOtherNamedNuanceStep → Bool
isOtherNamedNuancePreserving other-named-nuance-identity = true
isOtherNamedNuancePreserving (slot-leaf _) = true
isOtherNamedNuancePreserving (product-concurrent a b) =
  isOtherNamedNuancePreserving a ∧ isOtherNamedNuancePreserving b
isOtherNamedNuancePreserving (xor-mutually-exclusive _ _) = false

isOtherNamedNuanceAdmissible : ClassifierOtherNamedNuanceStep → Bool
isOtherNamedNuanceAdmissible step = isOtherNamedNuancePreserving step

interact-restriction-leaf-admissible : isOtherNamedNuanceAdmissible interactRestrictionLeaf ≡ true
interact-restriction-leaf-admissible = refl

not-extra-force-leaf-admissible : isOtherNamedNuanceAdmissible notExtraForceLeaf ≡ true
not-extra-force-leaf-admissible = refl

class24-other-named-nuance-leaf-admissible : isOtherNamedNuanceAdmissible class24OtherNamedNuanceLeaf ≡ true
class24-other-named-nuance-leaf-admissible = refl

named-other-named-nuance-admissible : isOtherNamedNuanceAdmissible namedOtherNamedNuanceProduct ≡ true
named-other-named-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isOtherNamedNuanceAdmissible (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class24-other-named-nuance-refuse :
  isOtherNamedNuanceAdmissible (xorMutuallyExclusiveOp notExtraForceLeaf class24OtherNamedNuanceLeaf) ≡ false
xor-mutually-exclusive-class24-other-named-nuance-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data OtherNamedNuanceWitnessPresence : Set where
  other-named-nuance-witness-absent other-named-nuance-witness-present : OtherNamedNuanceWitnessPresence

record ClassifierOtherNamedNuanceWitness : Set where
  constructor mkClassifierOtherNamedNuanceWitness
  field
    witness-presence : OtherNamedNuanceWitnessPresence
    other-named-nuance-gap-total : ℕ

otherNamedNuanceWitnessAbsent : ClassifierOtherNamedNuanceWitness
otherNamedNuanceWitnessAbsent = mkClassifierOtherNamedNuanceWitness other-named-nuance-witness-absent zero

otherNamedNuanceWitnessPresentZeroGap : ClassifierOtherNamedNuanceWitness
otherNamedNuanceWitnessPresentZeroGap = mkClassifierOtherNamedNuanceWitness other-named-nuance-witness-present zero

otherNamedNuanceWitnessPresentWithGaps : ℕ → ClassifierOtherNamedNuanceWitness
otherNamedNuanceWitnessPresentWithGaps n = mkClassifierOtherNamedNuanceWitness other-named-nuance-witness-present n

otherNamedNuanceWitnessGapFree : ClassifierOtherNamedNuanceWitness → Bool
otherNamedNuanceWitnessGapFree (mkClassifierOtherNamedNuanceWitness other-named-nuance-witness-absent _) = false
otherNamedNuanceWitnessGapFree (mkClassifierOtherNamedNuanceWitness other-named-nuance-witness-present n) =
  does (n ℕ-Props.≟ zero)

other-named-nuance-witness-present-zero-gap-free :
  otherNamedNuanceWitnessGapFree otherNamedNuanceWitnessPresentZeroGap ≡ true
other-named-nuance-witness-present-zero-gap-free = refl

other-named-nuance-witness-absent-not-gap-free :
  otherNamedNuanceWitnessGapFree otherNamedNuanceWitnessAbsent ≡ false
other-named-nuance-witness-absent-not-gap-free = refl

other-named-nuance-witness-with-gaps-not-gap-free :
  ∀ n → otherNamedNuanceWitnessGapFree (otherNamedNuanceWitnessPresentWithGaps (suc n)) ≡ false
other-named-nuance-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-OtherNamedNuance **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data OtherNamedNuanceConservationVerdict : Set where
  verdict-unwired-ok verdict-other-named-nuance-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : OtherNamedNuanceConservationVerdict

otherNamedNuanceConservationVerdictOk : OtherNamedNuanceConservationVerdict → Bool
otherNamedNuanceConservationVerdictOk verdict-unwired-ok = true
otherNamedNuanceConservationVerdictOk verdict-other-named-nuance-admissible-ok = true
otherNamedNuanceConservationVerdictOk verdict-concurrent-product-ok = true
otherNamedNuanceConservationVerdictOk _ = false

evaluateOtherNamedNuanceConservationClose :
  OtherNamedNuanceConservationModality → ClassifierOtherNamedNuanceStep → ClassifierOtherNamedNuanceWitness
  → OtherNamedNuanceBundleWitness → Bool → OtherNamedNuanceConservationVerdict
evaluateOtherNamedNuanceConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-proved _ (mkClassifierOtherNamedNuanceWitness other-named-nuance-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-proved _ (mkClassifierOtherNamedNuanceWitness other-named-nuance-witness-present _) w false
  with otherNamedNuanceBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-other-named-nuance-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without other named nuance witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-unwired namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-assumed namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-surrogate namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  otherNamedNuanceConservationVerdictOk
    (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-unwired namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false)
    ≡ true
  × otherNamedNuanceConservationVerdictOk
      (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-assumed namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false)
      ≡ true
  × otherNamedNuanceConservationVerdictOk
      (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-surrogate namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without other named nuance witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  otherNamedNuanceConservationVerdictOk
    (evaluateOtherNamedNuanceConservationClose
       other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false ≡
  verdict-other-named-nuance-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-proved
    (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf)
    otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  otherNamedNuanceConservationVerdictOk
    (evaluateOtherNamedNuanceConservationClose
       other-named-nuance-conservation-proved
       (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf)
       otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-proved
    (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf)
    otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-other-named-nuance — nuance **product** closed
------------------------------------------------------------------------

other-named-nuance-admissible-ok :
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap unwiredWitness false ≡
  verdict-other-named-nuance-admissible-ok
other-named-nuance-admissible-ok = refl

other-named-nuance-admissible-verdict-ok :
  otherNamedNuanceConservationVerdictOk
    (evaluateOtherNamedNuanceConservationClose
       other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap unwiredWitness false)
    ≡ true
other-named-nuance-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — other named nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  otherNamedNuanceConservationVerdictOk
    (evaluateOtherNamedNuanceConservationClose
       other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-other-named-nuance24-proved :
  otherNamedNuanceConservationVerdictOk
    (evaluateOtherNamedNuanceConservationClose
       other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness false)
    ≡ true
  × otherNamedNuance24Proved ≡ false
concurrent-product-ok-still-not-other-named-nuance24-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateOtherNamedNuanceConservationClose
    other-named-nuance-conservation-unwired namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  otherNamedNuanceConservationVerdictOk
    (evaluateOtherNamedNuanceConservationClose
       other-named-nuance-conservation-unwired namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

otherNamedNuanceConservationFiberOk : FormalFiber → Bool
otherNamedNuanceConservationFiberOk fiber-quantum-knowing = true
otherNamedNuanceConservationFiberOk fiber-meso-acting = false

other-named-nuance-conservation-knowing-fiber-ok :
  otherNamedNuanceConservationFiberOk fiber-quantum-knowing ≡ true
other-named-nuance-conservation-knowing-fiber-ok = refl

other-named-nuance-conservation-meso-acting-not-ok :
  otherNamedNuanceConservationFiberOk fiber-meso-acting ≡ false
other-named-nuance-conservation-meso-acting-not-ok = refl

other-named-nuance-conservation-routes-knowing-not-meso :
  otherNamedNuanceConservationFiberOk fiber-quantum-knowing ≡ true ×
  otherNamedNuanceConservationFiberOk fiber-meso-acting ≡ false
other-named-nuance-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  otherNamedNuanceConservationFiberOk fiber-quantum-knowing ∧
  not (otherNamedNuanceConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 24 other named nuance Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

other-named-nuance-24-not-proved : otherNamedNuance24Proved ≡ false
other-named-nuance-24-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

other-named-nuance-second-law-conservation-framed : otherNamedNuanceSecondLawConservationFramed ≡ true
other-named-nuance-second-law-conservation-framed = refl

other-named-nuance-not-xor-pin : otherNamedNuanceNotXor ≡ true
other-named-nuance-not-xor-pin = other-named-nuance-not-xor

interact-restriction-typed-pin : interactRestrictionTyped ≡ true
interact-restriction-typed-pin = refl

not-parallel-other-named-nuance-axiom-minted-pin : notParallelOtherNamedNuanceAxiomMinted ≡ true
not-parallel-other-named-nuance-axiom-minted-pin = refl

extra-force-not-forked-pin : extraForceNotForked ≡ true
extra-force-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel other_named_nuance axiom fork)
------------------------------------------------------------------------

otherNamedNuanceConservationAxiom :
  (otherNamedNuance24Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (otherNamedNuanceSecondLawConservationFramed ≡ true)
  × (otherNamedNuanceNotXor ≡ true)
  × (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-unwired namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessAbsent otherNamedNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-proved (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf) otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap unwiredWitness false ≡ verdict-other-named-nuance-admissible-ok)
  × (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-proved namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (otherNamedNuanceConservationFiberOk fiber-quantum-knowing ≡ true)
  × (otherNamedNuanceConservationFiberOk fiber-meso-acting ≡ false)
  × (otherNamedNuanceConservationVerdictOk (evaluateOtherNamedNuanceConservationClose other-named-nuance-conservation-unwired namedOtherNamedNuanceProduct otherNamedNuanceWitnessPresentZeroGap otherNamedNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp otherNamedNuanceIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a otherNamedNuanceIdentity) ≡ true)
  × (isOtherNamedNuanceAdmissible (xorMutuallyExclusiveOp interactRestrictionLeaf notExtraForceLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (otherNamedNuanceClassIndex ≡ 24)
  × (OtherNamedNuanceBundleWitness.present-count otherNamedNuanceWitness ≡ 3)
  × (elementAtomicZ platinum ≡ 78)
  × (elementAtomicZ oganesson ≡ 118)
otherNamedNuanceConservationAxiom =
  other-named-nuance-24-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , other-named-nuance-second-law-conservation-framed
  , other-named-nuance-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , other-named-nuance-admissible-ok
  , concurrent-product-ok
  , other-named-nuance-conservation-knowing-fiber-ok
  , other-named-nuance-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , other-named-nuance-class-index-twenty-four
  , other-named-nuance-present-count
  , platinum-z-78
  , oganesson-z-118

otherNamedNuanceConservationNamed : String
otherNamedNuanceConservationNamed =
  "otherNamedNuanceConservation: pattern class 24 other named nuance conservation concurrent Pi_c identity conserved Interact restriction not XOR class 24 other named nuance concurrent product identity conserved present ge 2 product not XOR interact restriction typed no parallel other_named_nuance axiom not XOR enum growth"

otherNamedNuanceConservationCrossWitnessAuthority : String
otherNamedNuanceConservationCrossWitnessAuthority =
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs"

otherNamedNuanceTableAuthority : String
otherNamedNuanceTableAuthority =
  "umst/umst-chem/src/l0_tables/pattern_named_factors.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

otherNamedNuanceConservationCellId : String
otherNamedNuanceConservationCellId = "CHEM-FORMAL-Q-AGDA-OTHER-NAMED-NUANCE-CONSERVATION"

otherNamedNuanceConservationNonClaim : String
otherNamedNuanceConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-OTHER-NAMED-NUANCE-CONSERVATION pattern class 24 other named nuance conservation concurrent Pi_c identity conserved Interact restriction not XOR class 24 other named nuance product not XOR interact restriction typed no parallel other_named_nuance axiom not XOR enum growth XOR mutually exclusive refuse other named nuance witness concurrent otherNamedNuance24Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite l0_tables other_named_nuance.rs pattern_named_factors not fork not physics GREEN not production_wired"

other-named-nuance-conservation-cell-id :
  otherNamedNuanceConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-OTHER-NAMED-NUANCE-CONSERVATION"
other-named-nuance-conservation-cell-id = refl

other-named-nuance-conservation-cites-other-named-nuance-rs :
  otherNamedNuanceConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/l0_tables/other_named_nuance.rs"
other-named-nuance-conservation-cites-other-named-nuance-rs = refl

other-named-nuance-conservation-cites-pattern-named-factors-rs :
  otherNamedNuanceTableAuthority ≡
  "umst/umst-chem/src/l0_tables/pattern_named_factors.rs"
other-named-nuance-conservation-cites-pattern-named-factors-rs = refl

other-named-nuance-conservation-modality-unwired :
  otherNamedNuanceConservationModalityCurrent ≡ other-named-nuance-conservation-unwired
other-named-nuance-conservation-modality-unwired = refl

otherNamedNuanceConservationPhysicsGreenAuthorized : Set
otherNamedNuanceConservationPhysicsGreenAuthorized = ⊥

other-named-nuance-conservation-physics-green-false : ¬ otherNamedNuanceConservationPhysicsGreenAuthorized
other-named-nuance-conservation-physics-green-false ()

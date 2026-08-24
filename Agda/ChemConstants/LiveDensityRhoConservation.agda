-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.LiveDensityRhoConservation.agda
--
-- LIVE density rho / TE-SDF **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (TE-SDF rung + SDF≠ρ unless named + freeze-safe
--     conservation until live wire; **product** not XOR, no parallel live-density-rho axiom)
--   * XOR mutually-exclusive refuse; live-density-rho nuance witness concurrent
--     (TE-SDF rung + SDF≠ρ unless named + freeze-safe conservation until live wire)
--   * LIVE density rho laws Unwired (liveDensityRhoProved = false)
--   * SDF rung ≠ ρ unless explicitly named (`ElectronDensityRho` must be explicit)
--
-- INT (read-only cite): umst/umst-chem/src/density_ladder.rs
-- X-row sibling: umst/umst-chem/src/x_rows/density_conservation.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- Freeze-safe identity until live wire — not live ρ/TE-SDF physics wire.
-- No parallel live-density-rho axiom; SDF≠ρ unless named. Product not XOR.
------------------------------------------------------------------------
module ChemConstants.LiveDensityRhoConservation where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + LIVE density rho **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data LiveDensityRhoConservationModality : Set where
  live-density-rho-conservation-unwired live-density-rho-conservation-assumed
    live-density-rho-conservation-proved live-density-rho-conservation-surrogate
    : LiveDensityRhoConservationModality

liveDensityRhoConservationModalityCurrent : LiveDensityRhoConservationModality
liveDensityRhoConservationModalityCurrent = live-density-rho-conservation-unwired

liveDensityRhoProved productionWired not118SquaredGreenTable
  liveDensityRhoSecondLawConservationFramed liveDensityRhoNotXor : Bool
liveDensityRhoProved = false
productionWired = false
not118SquaredGreenTable = true
liveDensityRhoSecondLawConservationFramed = true
liveDensityRhoNotXor = true

teSdfRungTyped notParallelLiveDensityRhoAxiomMinted sdfNotRhoNamingNotForked : Bool
teSdfRungTyped = true
notParallelLiveDensityRhoAxiomMinted = true
sdfNotRhoNamingNotForked = true


------------------------------------------------------------------------
-- SDF rung ≠ ρ unless named — explicit **density** symbol pins
------------------------------------------------------------------------

data DensitySymbolTag : Set where
  sdf-rung rho-density : DensitySymbolTag

isSdfRung isRhoDensity : DensitySymbolTag → Bool
isSdfRung sdf-rung = true
isSdfRung rho-density = false

isRhoDensity rho-density = true
isRhoDensity sdf-rung = false

sdf-rung-not-rho-unless-named :
  isSdfRung sdf-rung ≡ true × isRhoDensity sdf-rung ≡ false
sdf-rung-not-rho-unless-named = refl , refl

rho-density-named :
  isRhoDensity rho-density ≡ true × isSdfRung rho-density ≡ false
rho-density-named = refl , refl

sdf-rung-distinct-from-rho : sdf-rung ≢ rho-density
sdf-rung-distinct-from-rho ()

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
-- LIVE density rho ladder rung count pin
------------------------------------------------------------------------

liveDensityRhoRungCount : ℕ
liveDensityRhoRungCount = 4

live-density-rho-rung-count-four : liveDensityRhoRungCount ≡ 4
live-density-rho-rung-count-four = refl

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
-- LiveDensityRhoBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data LiveDensityRhoBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : LiveDensityRhoBundleSlot

isSlotPresent : LiveDensityRhoBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- LiveDensityRhoBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record LiveDensityRhoBundle : Set where
  field slot : ℕ → LiveDensityRhoBundleSlot

liveDensityRhoBundleUnwired : LiveDensityRhoBundle
liveDensityRhoBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : LiveDensityRhoBundle → ℕ → LiveDensityRhoBundleSlot → LiveDensityRhoBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else LiveDensityRhoBundle.slot b j }

withPresent : LiveDensityRhoBundle → ℕ → LiveDensityRhoBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record LiveDensityRhoBundleWitness : Set where
  constructor mkLiveDensityRhoBundleWitness
  field
    bundle : LiveDensityRhoBundle
    present-count : ℕ

liveDensityRhoBundleIsConcurrentProduct : LiveDensityRhoBundleWitness → Bool
liveDensityRhoBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? LiveDensityRhoBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named live-density-rho channel indices — interact restriction (1), not extra force (2), LIVE density rho TE-SDF (3)
------------------------------------------------------------------------

teSdfRungChannelIndex sdfNotRhoUnlessNamedChannelIndex freezeSafeConservationChannelIndex : ℕ
teSdfRungChannelIndex = 1
sdfNotRhoUnlessNamedChannelIndex = 2
freezeSafeConservationChannelIndex = 3

te-sdf-rung-index-one : teSdfRungChannelIndex ≡ 1
te-sdf-rung-index-one = refl

sdf-not-rho-unless-named-index-two : sdfNotRhoUnlessNamedChannelIndex ≡ 2
sdf-not-rho-unless-named-index-two = refl

freeze-safe-conservation-index-three : freezeSafeConservationChannelIndex ≡ 3
freeze-safe-conservation-index-three = refl

------------------------------------------------------------------------
-- Live-density-rho nuance witness — interact restriction + not extra force + LIVE density rho TE-SDF concurrent
------------------------------------------------------------------------

liveDensityRhoNuanceBundle : LiveDensityRhoBundle
liveDensityRhoNuanceBundle =
  withPresent
    (withPresent
      (withPresent liveDensityRhoBundleUnwired teSdfRungChannelIndex)
      sdfNotRhoUnlessNamedChannelIndex)
    freezeSafeConservationChannelIndex

liveDensityRhoNuanceWitness : LiveDensityRhoBundleWitness
liveDensityRhoNuanceWitness =
  mkLiveDensityRhoBundleWitness liveDensityRhoNuanceBundle 3

live-density-rho-nuance-te-sdf-rung-present :
  isSlotPresent (LiveDensityRhoBundle.slot liveDensityRhoNuanceBundle teSdfRungChannelIndex) ≡ true
live-density-rho-nuance-te-sdf-rung-present = refl

live-density-rho-nuance-sdf-not-rho-unless-named-present :
  isSlotPresent (LiveDensityRhoBundle.slot liveDensityRhoNuanceBundle sdfNotRhoUnlessNamedChannelIndex) ≡ true
live-density-rho-nuance-sdf-not-rho-unless-named-present = refl

live-density-rho-nuance-freeze-safe-conservation-present :
  isSlotPresent (LiveDensityRhoBundle.slot liveDensityRhoNuanceBundle freezeSafeConservationChannelIndex) ≡ true
live-density-rho-nuance-freeze-safe-conservation-present = refl

live-density-rho-nuance-present-count : LiveDensityRhoBundleWitness.present-count liveDensityRhoNuanceWitness ≡ 3
live-density-rho-nuance-present-count = refl

live-density-rho-nuance-concurrent-product :
  liveDensityRhoBundleIsConcurrentProduct liveDensityRhoNuanceWitness ≡ true
live-density-rho-nuance-concurrent-product = refl

live-density-rho-nuance-three-factors-concurrent :
  isSlotPresent (LiveDensityRhoBundle.slot liveDensityRhoNuanceBundle teSdfRungChannelIndex) ≡ true
  × isSlotPresent (LiveDensityRhoBundle.slot liveDensityRhoNuanceBundle sdfNotRhoUnlessNamedChannelIndex) ≡ true
  × isSlotPresent (LiveDensityRhoBundle.slot liveDensityRhoNuanceBundle freezeSafeConservationChannelIndex) ≡ true
  × LiveDensityRhoBundleWitness.present-count liveDensityRhoNuanceWitness ≡ 3
live-density-rho-nuance-three-factors-concurrent =
  live-density-rho-nuance-te-sdf-rung-present
  , live-density-rho-nuance-sdf-not-rho-unless-named-present
  , live-density-rho-nuance-freeze-safe-conservation-present
  , live-density-rho-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : LiveDensityRhoBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if liveDensityRhoBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = LiveDensityRhoBundleWitness.bundle w
       in if isSlotPresent (LiveDensityRhoBundle.slot b i)
          then if isSlotPresent (LiveDensityRhoBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : LiveDensityRhoBundleWitness
unwiredWitness = mkLiveDensityRhoBundleWitness liveDensityRhoBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

live-density-rho-nuance-xor-product-ok :
  evaluateXorRefuse liveDensityRhoNuanceWitness teSdfRungChannelIndex sdfNotRhoUnlessNamedChannelIndex ≡ xor-product-ok
live-density-rho-nuance-xor-product-ok = refl

live-density-rho-not-xor : liveDensityRhoNotXor ≡ true
live-density-rho-not-xor = refl

------------------------------------------------------------------------
-- ClassifierLiveDensityRhoStep scaffold — LiveDensityRhoBundle **conservation**
------------------------------------------------------------------------

data ClassifierLiveDensityRhoStep : Set where
  live-density-rho-identity : ClassifierLiveDensityRhoStep
  slot-leaf : ℕ → ClassifierLiveDensityRhoStep
  product-concurrent : ClassifierLiveDensityRhoStep → ClassifierLiveDensityRhoStep → ClassifierLiveDensityRhoStep
  xor-mutually-exclusive : ClassifierLiveDensityRhoStep → ClassifierLiveDensityRhoStep → ClassifierLiveDensityRhoStep

liveDensityRhoIdentity : ClassifierLiveDensityRhoStep
liveDensityRhoIdentity = live-density-rho-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierLiveDensityRhoStep → ClassifierLiveDensityRhoStep → ClassifierLiveDensityRhoStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

teSdfRungLeaf sdfNotRhoUnlessNamedLeaf freezeSafeConservationLeaf : ClassifierLiveDensityRhoStep
teSdfRungLeaf = slot-leaf teSdfRungChannelIndex
sdfNotRhoUnlessNamedLeaf = slot-leaf sdfNotRhoUnlessNamedChannelIndex
freezeSafeConservationLeaf = slot-leaf freezeSafeConservationChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierLiveDensityRhoStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isLiveDensityRhoIdentity : ClassifierLiveDensityRhoStep → Bool
isLiveDensityRhoIdentity live-density-rho-identity = true
isLiveDensityRhoIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at live-density-rho-identity
------------------------------------------------------------------------

live-density-rho-left-identity :
  ∀ (a : ClassifierLiveDensityRhoStep) →
  isLiveDensityRhoIdentity liveDensityRhoIdentity ≡ true
  × isProductConcurrent (productConcurrentOp liveDensityRhoIdentity a) ≡ true
live-density-rho-left-identity a = refl , refl

live-density-rho-right-identity :
  ∀ (a : ClassifierLiveDensityRhoStep) →
  isProductConcurrent (productConcurrentOp a liveDensityRhoIdentity) ≡ true
  × isLiveDensityRhoIdentity liveDensityRhoIdentity ≡ true
live-density-rho-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-live-density-rho :
  (∀ a → isProductConcurrent (productConcurrentOp liveDensityRhoIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a liveDensityRhoIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-live-density-rho =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named live-density-rho nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedLiveDensityRhoNuanceProduct : ClassifierLiveDensityRhoStep
namedLiveDensityRhoNuanceProduct =
  productConcurrentOp
    (productConcurrentOp teSdfRungLeaf sdfNotRhoUnlessNamedLeaf)
    freezeSafeConservationLeaf

named-live-density-rho-nuance-product-concurrent :
  isProductConcurrent namedLiveDensityRhoNuanceProduct ≡ true
  × liveDensityRhoBundleIsConcurrentProduct liveDensityRhoNuanceWitness ≡ true
named-live-density-rho-nuance-product-concurrent = refl , live-density-rho-nuance-concurrent-product

------------------------------------------------------------------------
-- LiveDensityRhoBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data LiveDensityRhoAdmissibility : Set where
  live-density-rho-admissible live-density-rho-xor-refuse : LiveDensityRhoAdmissibility

isLiveDensityRhoPreserving : ClassifierLiveDensityRhoStep → Bool
isLiveDensityRhoPreserving live-density-rho-identity = true
isLiveDensityRhoPreserving (slot-leaf _) = true
isLiveDensityRhoPreserving (product-concurrent a b) =
  isLiveDensityRhoPreserving a ∧ isLiveDensityRhoPreserving b
isLiveDensityRhoPreserving (xor-mutually-exclusive _ _) = false

isLiveDensityRhoAdmissible : ClassifierLiveDensityRhoStep → Bool
isLiveDensityRhoAdmissible step = isLiveDensityRhoPreserving step

te-sdf-rung-leaf-admissible : isLiveDensityRhoAdmissible teSdfRungLeaf ≡ true
te-sdf-rung-leaf-admissible = refl

sdf-not-rho-unless-named-leaf-admissible : isLiveDensityRhoAdmissible sdfNotRhoUnlessNamedLeaf ≡ true
sdf-not-rho-unless-named-leaf-admissible = refl

freeze-safe-conservation-leaf-admissible : isLiveDensityRhoAdmissible freezeSafeConservationLeaf ≡ true
freeze-safe-conservation-leaf-admissible = refl

named-live-density-rho-nuance-admissible : isLiveDensityRhoAdmissible namedLiveDensityRhoNuanceProduct ≡ true
named-live-density-rho-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isLiveDensityRhoAdmissible (xorMutuallyExclusiveOp teSdfRungLeaf sdfNotRhoUnlessNamedLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-freeze-safe-conservation-refuse :
  isLiveDensityRhoAdmissible (xorMutuallyExclusiveOp sdfNotRhoUnlessNamedLeaf freezeSafeConservationLeaf) ≡ false
xor-mutually-exclusive-freeze-safe-conservation-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data LiveDensityRhoWitnessPresence : Set where
  live-density-rho-witness-absent live-density-rho-witness-present : LiveDensityRhoWitnessPresence

record ClassifierLiveDensityRhoWitness : Set where
  constructor mkClassifierLiveDensityRhoWitness
  field
    witness-presence : LiveDensityRhoWitnessPresence
    live-density-rho-gap-total : ℕ

liveDensityRhoWitnessAbsent : ClassifierLiveDensityRhoWitness
liveDensityRhoWitnessAbsent = mkClassifierLiveDensityRhoWitness live-density-rho-witness-absent zero

liveDensityRhoWitnessPresentZeroGap : ClassifierLiveDensityRhoWitness
liveDensityRhoWitnessPresentZeroGap = mkClassifierLiveDensityRhoWitness live-density-rho-witness-present zero

liveDensityRhoWitnessPresentWithGaps : ℕ → ClassifierLiveDensityRhoWitness
liveDensityRhoWitnessPresentWithGaps n = mkClassifierLiveDensityRhoWitness live-density-rho-witness-present n

liveDensityRhoWitnessGapFree : ClassifierLiveDensityRhoWitness → Bool
liveDensityRhoWitnessGapFree (mkClassifierLiveDensityRhoWitness live-density-rho-witness-absent _) = false
liveDensityRhoWitnessGapFree (mkClassifierLiveDensityRhoWitness live-density-rho-witness-present n) =
  does (n ℕ-Props.≟ zero)

live-density-rho-witness-present-zero-gap-free :
  liveDensityRhoWitnessGapFree liveDensityRhoWitnessPresentZeroGap ≡ true
live-density-rho-witness-present-zero-gap-free = refl

live-density-rho-witness-absent-not-gap-free :
  liveDensityRhoWitnessGapFree liveDensityRhoWitnessAbsent ≡ false
live-density-rho-witness-absent-not-gap-free = refl

live-density-rho-witness-with-gaps-not-gap-free :
  ∀ n → liveDensityRhoWitnessGapFree (liveDensityRhoWitnessPresentWithGaps (suc n)) ≡ false
live-density-rho-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-LiveDensityRho **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data LiveDensityRhoConservationVerdict : Set where
  verdict-unwired-ok verdict-live-density-rho-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : LiveDensityRhoConservationVerdict

liveDensityRhoConservationVerdictOk : LiveDensityRhoConservationVerdict → Bool
liveDensityRhoConservationVerdictOk verdict-unwired-ok = true
liveDensityRhoConservationVerdictOk verdict-live-density-rho-admissible-ok = true
liveDensityRhoConservationVerdictOk verdict-concurrent-product-ok = true
liveDensityRhoConservationVerdictOk _ = false

evaluateLiveDensityRhoConservationClose :
  LiveDensityRhoConservationModality → ClassifierLiveDensityRhoStep → ClassifierLiveDensityRhoWitness
  → LiveDensityRhoBundleWitness → Bool → LiveDensityRhoConservationVerdict
evaluateLiveDensityRhoConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateLiveDensityRhoConservationClose live-density-rho-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateLiveDensityRhoConservationClose live-density-rho-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateLiveDensityRhoConservationClose live-density-rho-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateLiveDensityRhoConservationClose live-density-rho-conservation-proved _ (mkClassifierLiveDensityRhoWitness live-density-rho-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateLiveDensityRhoConservationClose live-density-rho-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateLiveDensityRhoConservationClose live-density-rho-conservation-proved _ (mkClassifierLiveDensityRhoWitness live-density-rho-witness-present _) w false
  with liveDensityRhoBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-live-density-rho-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without live-density-rho witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-unwired namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-assumed namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-surrogate namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  liveDensityRhoConservationVerdictOk
    (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-unwired namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false)
    ≡ true
  × liveDensityRhoConservationVerdictOk
      (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-assumed namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false)
      ≡ true
  × liveDensityRhoConservationVerdictOk
      (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-surrogate namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without live-density-rho witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  liveDensityRhoConservationVerdictOk
    (evaluateLiveDensityRhoConservationClose
       live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false ≡
  verdict-live-density-rho-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-proved
    (xorMutuallyExclusiveOp teSdfRungLeaf sdfNotRhoUnlessNamedLeaf)
    liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  liveDensityRhoConservationVerdictOk
    (evaluateLiveDensityRhoConservationClose
       live-density-rho-conservation-proved
       (xorMutuallyExclusiveOp teSdfRungLeaf sdfNotRhoUnlessNamedLeaf)
       liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-proved
    (xorMutuallyExclusiveOp teSdfRungLeaf sdfNotRhoUnlessNamedLeaf)
    liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-live-density-rho — nuance **product** closed
------------------------------------------------------------------------

live-density-rho-admissible-ok :
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap unwiredWitness false ≡
  verdict-live-density-rho-admissible-ok
live-density-rho-admissible-ok = refl

live-density-rho-admissible-verdict-ok :
  liveDensityRhoConservationVerdictOk
    (evaluateLiveDensityRhoConservationClose
       live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap unwiredWitness false)
    ≡ true
live-density-rho-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — live-density-rho nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  liveDensityRhoConservationVerdictOk
    (evaluateLiveDensityRhoConservationClose
       live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-liveDensityRho-proved :
  liveDensityRhoConservationVerdictOk
    (evaluateLiveDensityRhoConservationClose
       live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness false)
    ≡ true
  × liveDensityRhoProved ≡ false
concurrent-product-ok-still-not-liveDensityRho-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateLiveDensityRhoConservationClose
    live-density-rho-conservation-unwired namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  liveDensityRhoConservationVerdictOk
    (evaluateLiveDensityRhoConservationClose
       live-density-rho-conservation-unwired namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

liveDensityRhoConservationFiberOk : FormalFiber → Bool
liveDensityRhoConservationFiberOk fiber-quantum-knowing = true
liveDensityRhoConservationFiberOk fiber-meso-acting = false

live-density-rho-conservation-knowing-fiber-ok :
  liveDensityRhoConservationFiberOk fiber-quantum-knowing ≡ true
live-density-rho-conservation-knowing-fiber-ok = refl

live-density-rho-conservation-meso-acting-not-ok :
  liveDensityRhoConservationFiberOk fiber-meso-acting ≡ false
live-density-rho-conservation-meso-acting-not-ok = refl

live-density-rho-conservation-routes-knowing-not-meso :
  liveDensityRhoConservationFiberOk fiber-quantum-knowing ≡ true ×
  liveDensityRhoConservationFiberOk fiber-meso-acting ≡ false
live-density-rho-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  liveDensityRhoConservationFiberOk fiber-quantum-knowing ∧
  not (liveDensityRhoConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not LIVE density rho TE-SDF Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

live-density-rho-not-proved : liveDensityRhoProved ≡ false
live-density-rho-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

live-density-rho-second-law-conservation-framed : liveDensityRhoSecondLawConservationFramed ≡ true
live-density-rho-second-law-conservation-framed = refl

live-density-rho-not-xor-pin : liveDensityRhoNotXor ≡ true
live-density-rho-not-xor-pin = live-density-rho-not-xor

te-sdf-rung-typed-pin : teSdfRungTyped ≡ true
te-sdf-rung-typed-pin = refl

not-parallel-live-density-rho-axiom-minted-pin : notParallelLiveDensityRhoAxiomMinted ≡ true
not-parallel-live-density-rho-axiom-minted-pin = refl

sdf-not-rho-naming-not-forked-pin : sdfNotRhoNamingNotForked ≡ true
sdf-not-rho-naming-not-forked-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel live-density-rho axiom fork)
------------------------------------------------------------------------

liveDensityRhoConservationAxiom :
  (liveDensityRhoProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (liveDensityRhoSecondLawConservationFramed ≡ true)
  × (liveDensityRhoNotXor ≡ true)
  × (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-unwired namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessAbsent liveDensityRhoNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-proved (xorMutuallyExclusiveOp teSdfRungLeaf sdfNotRhoUnlessNamedLeaf) liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap unwiredWitness false ≡ verdict-live-density-rho-admissible-ok)
  × (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-proved namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (liveDensityRhoConservationFiberOk fiber-quantum-knowing ≡ true)
  × (liveDensityRhoConservationFiberOk fiber-meso-acting ≡ false)
  × (liveDensityRhoConservationVerdictOk (evaluateLiveDensityRhoConservationClose live-density-rho-conservation-unwired namedLiveDensityRhoNuanceProduct liveDensityRhoWitnessPresentZeroGap liveDensityRhoNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp liveDensityRhoIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a liveDensityRhoIdentity) ≡ true)
  × (isLiveDensityRhoAdmissible (xorMutuallyExclusiveOp teSdfRungLeaf sdfNotRhoUnlessNamedLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (liveDensityRhoRungCount ≡ 4)
  × (LiveDensityRhoBundleWitness.present-count liveDensityRhoNuanceWitness ≡ 3)
  × (isSdfRung sdf-rung ≡ true)
  × (isRhoDensity sdf-rung ≡ false)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
liveDensityRhoConservationAxiom =
  live-density-rho-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , live-density-rho-second-law-conservation-framed
  , live-density-rho-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , live-density-rho-admissible-ok
  , concurrent-product-ok
  , live-density-rho-conservation-knowing-fiber-ok
  , live-density-rho-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , live-density-rho-rung-count-four
  , live-density-rho-nuance-present-count
  , proj₁ sdf-rung-not-rho-unless-named
  , proj₂ sdf-rung-not-rho-unless-named
  , iron-z-26
  , oganesson-z-118

liveDensityRhoConservationNamed : String
liveDensityRhoConservationNamed =
  "liveDensityRhoConservation: LIVE density rho TE-SDF conservation freeze-safe until live wire concurrent Pi_c identity conserved TE-SDF rung SDF not rho unless named freeze-safe conservation concurrent product identity conserved present ge 2 product not XOR TE-SDF rung typed no parallel live-density-rho axiom SDF not rho naming not forked"

liveDensityRhoConservationDensityLadderAuthority : String
liveDensityRhoConservationDensityLadderAuthority =
  "umst/umst-chem/src/density_ladder.rs"

liveDensityRhoConservationXRowAuthority : String
liveDensityRhoConservationXRowAuthority =
  "umst/umst-chem/src/x_rows/density_conservation.rs"

liveDensityRhoConservationDensityConservationAuthority : String
liveDensityRhoConservationDensityConservationAuthority =
  "umst/umst-chem/src/x_rows/live_density_rho_conservation.rs"

liveDensityRhoConservationNotLivePhysicsFence : String
liveDensityRhoConservationNotLivePhysicsFence =
  "umst/umst-chem/src/density_ladder.rs"

liveDensityRhoConservationCellId : String
liveDensityRhoConservationCellId = "CHEM-FORMAL-Q-AGDA-LIVE-DENSITY-RHO-CONSERVATION"

liveDensityRhoConservationNonClaim : String
liveDensityRhoConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-LIVE-DENSITY-RHO-CONSERVATION LIVE density rho TE-SDF conservation freeze-safe until live wire concurrent Pi_c identity conserved TE-SDF rung SDF not rho unless named freeze-safe conservation product not XOR TE-SDF rung typed no parallel live-density-rho axiom SDF not rho naming not forked XOR mutually exclusive refuse live-density-rho nuance witness concurrent liveDensityRhoProved false SDF not rho unless named not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite density_ladder.rs x_rows density_conservation not live rho physics wire not fork not physics GREEN not production_wired"

live-density-rho-conservation-cell-id :
  liveDensityRhoConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-LIVE-DENSITY-RHO-CONSERVATION"
live-density-rho-conservation-cell-id = refl

live-density-rho-conservation-cites-density-ladder-rs :
  liveDensityRhoConservationDensityLadderAuthority ≡
  "umst/umst-chem/src/density_ladder.rs"
live-density-rho-conservation-cites-density-ladder-rs = refl

live-density-rho-conservation-cites-density-conservation-rs :
  liveDensityRhoConservationXRowAuthority ≡
  "umst/umst-chem/src/x_rows/density_conservation.rs"
live-density-rho-conservation-cites-density-conservation-rs = refl

live-density-rho-conservation-modality-unwired :
  liveDensityRhoConservationModalityCurrent ≡ live-density-rho-conservation-unwired
live-density-rho-conservation-modality-unwired = refl

liveDensityRhoConservationPhysicsGreenAuthorized : Set
liveDensityRhoConservationPhysicsGreenAuthorized = ⊥

live-density-rho-conservation-physics-green-false : ¬ liveDensityRhoConservationPhysicsGreenAuthorized
live-density-rho-conservation-physics-green-false ()

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.SurfaceVsBulkSdfConservation.agda
--
-- Pattern class 15 **surface_vs_bulk_sdf** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (bulk interior SDF + interface shell + surface exterior;
--     **product** not XOR, no parallel surface_vs_bulk_sdf axiom)
--   * XOR mutually-exclusive refuse; surface-vs-bulk SDF nuance witness concurrent
--     (bulk interior + interface shell + surface exterior)
--   * **surface_vs_bulk_sdf** laws Unwired (surfaceVsBulkSdf15Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/surface_bulk_sdf.rs
-- L0 table: umst/umst-chem/src/l0_tables/surface_vs_bulk_sdf.rs
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel surface_vs_bulk_sdf axiom; thin-slab ≠ bulk interior. Product not XOR.
------------------------------------------------------------------------
module ChemConstants.SurfaceVsBulkSdfConservation where


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
-- Modality + pattern class 15 **surface_vs_bulk_sdf** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data SurfaceVsBulkSdfConservationModality : Set where
  surface-vs-bulk-sdf-conservation-unwired surface-vs-bulk-sdf-conservation-assumed
    surface-vs-bulk-sdf-conservation-proved surface-vs-bulk-sdf-conservation-surrogate
    : SurfaceVsBulkSdfConservationModality

surfaceVsBulkSdfConservationModalityCurrent : SurfaceVsBulkSdfConservationModality
surfaceVsBulkSdfConservationModalityCurrent = surface-vs-bulk-sdf-conservation-unwired

surfaceVsBulkSdf15Proved productionWired not118SquaredGreenTable
  surfaceVsBulkSdfSecondLawConservationFramed surfaceVsBulkSdfNotXor : Bool
surfaceVsBulkSdf15Proved = false
productionWired = false
not118SquaredGreenTable = true
surfaceVsBulkSdfSecondLawConservationFramed = true
surfaceVsBulkSdfNotXor = true

thinSlabNeBulkInterior notParallelSurfaceBulkSdfAxiomMinted tpGraphFunctionNotFloatPin : Bool
thinSlabNeBulkInterior = true
notParallelSurfaceBulkSdfAxiomMinted = true
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
-- Pattern class 15 Surface-vs-bulk-SDF index pin
------------------------------------------------------------------------

surfaceVsBulkSdfClassIndex : ℕ
surfaceVsBulkSdfClassIndex = 15

surface-vs-bulk-sdf-class-index-fifteen : surfaceVsBulkSdfClassIndex ≡ 15
surface-vs-bulk-sdf-class-index-fifteen = refl

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
-- SurfaceVsBulkSdfBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data SurfaceVsBulkSdfBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : SurfaceVsBulkSdfBundleSlot

isSlotPresent : SurfaceVsBulkSdfBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- SurfaceVsBulkSdfBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record SurfaceVsBulkSdfBundle : Set where
  field slot : ℕ → SurfaceVsBulkSdfBundleSlot

surfaceVsBulkSdfBundleUnwired : SurfaceVsBulkSdfBundle
surfaceVsBulkSdfBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : SurfaceVsBulkSdfBundle → ℕ → SurfaceVsBulkSdfBundleSlot → SurfaceVsBulkSdfBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else SurfaceVsBulkSdfBundle.slot b j }

withPresent : SurfaceVsBulkSdfBundle → ℕ → SurfaceVsBulkSdfBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record SurfaceVsBulkSdfBundleWitness : Set where
  constructor mkSurfaceVsBulkSdfBundleWitness
  field
    bundle : SurfaceVsBulkSdfBundle
    present-count : ℕ

surfaceVsBulkSdfBundleIsConcurrentProduct : SurfaceVsBulkSdfBundleWitness → Bool
surfaceVsBulkSdfBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? SurfaceVsBulkSdfBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named surface-vs-bulk-SDF channel indices — bulk interior SDF (1), interface shell (2), surface exterior SDF (3)
------------------------------------------------------------------------

bulkInteriorSdfChannelIndex interfaceShellChannelIndex surfaceExteriorSdfChannelIndex : ℕ
bulkInteriorSdfChannelIndex = 1
interfaceShellChannelIndex = 2
surfaceExteriorSdfChannelIndex = 3

bulk-interior-sdf-index-one : bulkInteriorSdfChannelIndex ≡ 1
bulk-interior-sdf-index-one = refl

interface-shell-index-two : interfaceShellChannelIndex ≡ 2
interface-shell-index-two = refl

surface-exterior-sdf-index-three : surfaceExteriorSdfChannelIndex ≡ 3
surface-exterior-sdf-index-three = refl

------------------------------------------------------------------------
-- Surface-vs-bulk-SDF nuance witness — bulk interior + interface shell + surface exterior concurrent
------------------------------------------------------------------------

surfaceVsBulkSdfNuanceBundle : SurfaceVsBulkSdfBundle
surfaceVsBulkSdfNuanceBundle =
  withPresent
    (withPresent
      (withPresent surfaceVsBulkSdfBundleUnwired bulkInteriorSdfChannelIndex)
      interfaceShellChannelIndex)
    surfaceExteriorSdfChannelIndex

surfaceVsBulkSdfNuanceWitness : SurfaceVsBulkSdfBundleWitness
surfaceVsBulkSdfNuanceWitness =
  mkSurfaceVsBulkSdfBundleWitness surfaceVsBulkSdfNuanceBundle 3

surface-vs-bulk-sdf-nuance-bulk-interior-present :
  isSlotPresent (SurfaceVsBulkSdfBundle.slot surfaceVsBulkSdfNuanceBundle bulkInteriorSdfChannelIndex) ≡ true
surface-vs-bulk-sdf-nuance-bulk-interior-present = refl

surface-vs-bulk-sdf-nuance-interface-shell-present :
  isSlotPresent (SurfaceVsBulkSdfBundle.slot surfaceVsBulkSdfNuanceBundle interfaceShellChannelIndex) ≡ true
surface-vs-bulk-sdf-nuance-interface-shell-present = refl

surface-vs-bulk-sdf-nuance-surface-exterior-present :
  isSlotPresent (SurfaceVsBulkSdfBundle.slot surfaceVsBulkSdfNuanceBundle surfaceExteriorSdfChannelIndex) ≡ true
surface-vs-bulk-sdf-nuance-surface-exterior-present = refl

surface-vs-bulk-sdf-nuance-present-count : SurfaceVsBulkSdfBundleWitness.present-count surfaceVsBulkSdfNuanceWitness ≡ 3
surface-vs-bulk-sdf-nuance-present-count = refl

surface-vs-bulk-sdf-nuance-concurrent-product :
  surfaceVsBulkSdfBundleIsConcurrentProduct surfaceVsBulkSdfNuanceWitness ≡ true
surface-vs-bulk-sdf-nuance-concurrent-product = refl

surface-vs-bulk-sdf-nuance-three-factors-concurrent :
  isSlotPresent (SurfaceVsBulkSdfBundle.slot surfaceVsBulkSdfNuanceBundle bulkInteriorSdfChannelIndex) ≡ true
  × isSlotPresent (SurfaceVsBulkSdfBundle.slot surfaceVsBulkSdfNuanceBundle interfaceShellChannelIndex) ≡ true
  × isSlotPresent (SurfaceVsBulkSdfBundle.slot surfaceVsBulkSdfNuanceBundle surfaceExteriorSdfChannelIndex) ≡ true
  × SurfaceVsBulkSdfBundleWitness.present-count surfaceVsBulkSdfNuanceWitness ≡ 3
surface-vs-bulk-sdf-nuance-three-factors-concurrent =
  surface-vs-bulk-sdf-nuance-bulk-interior-present
  , surface-vs-bulk-sdf-nuance-interface-shell-present
  , surface-vs-bulk-sdf-nuance-surface-exterior-present
  , surface-vs-bulk-sdf-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : SurfaceVsBulkSdfBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if surfaceVsBulkSdfBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = SurfaceVsBulkSdfBundleWitness.bundle w
       in if isSlotPresent (SurfaceVsBulkSdfBundle.slot b i)
          then if isSlotPresent (SurfaceVsBulkSdfBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : SurfaceVsBulkSdfBundleWitness
unwiredWitness = mkSurfaceVsBulkSdfBundleWitness surfaceVsBulkSdfBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

surface-vs-bulk-sdf-nuance-xor-product-ok :
  evaluateXorRefuse surfaceVsBulkSdfNuanceWitness bulkInteriorSdfChannelIndex interfaceShellChannelIndex ≡ xor-product-ok
surface-vs-bulk-sdf-nuance-xor-product-ok = refl

surface-vs-bulk-sdf-not-xor : surfaceVsBulkSdfNotXor ≡ true
surface-vs-bulk-sdf-not-xor = refl

------------------------------------------------------------------------
-- ClassifierSurfaceVsBulkSdfStep scaffold — SurfaceVsBulkSdfBundle **conservation**
------------------------------------------------------------------------

data ClassifierSurfaceVsBulkSdfStep : Set where
  surface-vs-bulk-sdf-identity : ClassifierSurfaceVsBulkSdfStep
  slot-leaf : ℕ → ClassifierSurfaceVsBulkSdfStep
  product-concurrent : ClassifierSurfaceVsBulkSdfStep → ClassifierSurfaceVsBulkSdfStep → ClassifierSurfaceVsBulkSdfStep
  xor-mutually-exclusive : ClassifierSurfaceVsBulkSdfStep → ClassifierSurfaceVsBulkSdfStep → ClassifierSurfaceVsBulkSdfStep

surfaceVsBulkSdfIdentity : ClassifierSurfaceVsBulkSdfStep
surfaceVsBulkSdfIdentity = surface-vs-bulk-sdf-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierSurfaceVsBulkSdfStep → ClassifierSurfaceVsBulkSdfStep → ClassifierSurfaceVsBulkSdfStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

bulkInteriorSdfLeaf interfaceShellLeaf surfaceExteriorSdfLeaf : ClassifierSurfaceVsBulkSdfStep
bulkInteriorSdfLeaf = slot-leaf bulkInteriorSdfChannelIndex
interfaceShellLeaf = slot-leaf interfaceShellChannelIndex
surfaceExteriorSdfLeaf = slot-leaf surfaceExteriorSdfChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierSurfaceVsBulkSdfStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isSurfaceVsBulkSdfIdentity : ClassifierSurfaceVsBulkSdfStep → Bool
isSurfaceVsBulkSdfIdentity surface-vs-bulk-sdf-identity = true
isSurfaceVsBulkSdfIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at surface-vs-bulk-sdf-identity
------------------------------------------------------------------------

surface-vs-bulk-sdf-left-identity :
  ∀ (a : ClassifierSurfaceVsBulkSdfStep) →
  isSurfaceVsBulkSdfIdentity surfaceVsBulkSdfIdentity ≡ true
  × isProductConcurrent (productConcurrentOp surfaceVsBulkSdfIdentity a) ≡ true
surface-vs-bulk-sdf-left-identity a = refl , refl

surface-vs-bulk-sdf-right-identity :
  ∀ (a : ClassifierSurfaceVsBulkSdfStep) →
  isProductConcurrent (productConcurrentOp a surfaceVsBulkSdfIdentity) ≡ true
  × isSurfaceVsBulkSdfIdentity surfaceVsBulkSdfIdentity ≡ true
surface-vs-bulk-sdf-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-surface-vs-bulk-sdf :
  (∀ a → isProductConcurrent (productConcurrentOp surfaceVsBulkSdfIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a surfaceVsBulkSdfIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-surface-vs-bulk-sdf =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named surface-vs-bulk-SDF nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedSurfaceVsBulkSdfNuanceProduct : ClassifierSurfaceVsBulkSdfStep
namedSurfaceVsBulkSdfNuanceProduct =
  productConcurrentOp
    (productConcurrentOp bulkInteriorSdfLeaf interfaceShellLeaf)
    surfaceExteriorSdfLeaf

named-surface-vs-bulk-sdf-nuance-product-concurrent :
  isProductConcurrent namedSurfaceVsBulkSdfNuanceProduct ≡ true
  × surfaceVsBulkSdfBundleIsConcurrentProduct surfaceVsBulkSdfNuanceWitness ≡ true
named-surface-vs-bulk-sdf-nuance-product-concurrent = refl , surface-vs-bulk-sdf-nuance-concurrent-product

------------------------------------------------------------------------
-- SurfaceVsBulkSdfBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data SurfaceVsBulkSdfAdmissibility : Set where
  surface-vs-bulk-sdf-admissible surface-vs-bulk-sdf-xor-refuse : SurfaceVsBulkSdfAdmissibility

isSurfaceVsBulkSdfPreserving : ClassifierSurfaceVsBulkSdfStep → Bool
isSurfaceVsBulkSdfPreserving surface-vs-bulk-sdf-identity = true
isSurfaceVsBulkSdfPreserving (slot-leaf _) = true
isSurfaceVsBulkSdfPreserving (product-concurrent a b) =
  isSurfaceVsBulkSdfPreserving a ∧ isSurfaceVsBulkSdfPreserving b
isSurfaceVsBulkSdfPreserving (xor-mutually-exclusive _ _) = false

isSurfaceVsBulkSdfAdmissible : ClassifierSurfaceVsBulkSdfStep → Bool
isSurfaceVsBulkSdfAdmissible step = isSurfaceVsBulkSdfPreserving step

bulk-interior-sdf-leaf-admissible : isSurfaceVsBulkSdfAdmissible bulkInteriorSdfLeaf ≡ true
bulk-interior-sdf-leaf-admissible = refl

interface-shell-leaf-admissible : isSurfaceVsBulkSdfAdmissible interfaceShellLeaf ≡ true
interface-shell-leaf-admissible = refl

surface-exterior-sdf-leaf-admissible : isSurfaceVsBulkSdfAdmissible surfaceExteriorSdfLeaf ≡ true
surface-exterior-sdf-leaf-admissible = refl

named-surface-vs-bulk-sdf-nuance-admissible : isSurfaceVsBulkSdfAdmissible namedSurfaceVsBulkSdfNuanceProduct ≡ true
named-surface-vs-bulk-sdf-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isSurfaceVsBulkSdfAdmissible (xorMutuallyExclusiveOp bulkInteriorSdfLeaf interfaceShellLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-surface-exterior-sdf-refuse :
  isSurfaceVsBulkSdfAdmissible (xorMutuallyExclusiveOp interfaceShellLeaf surfaceExteriorSdfLeaf) ≡ false
xor-mutually-exclusive-surface-exterior-sdf-refuse = refl

------------------------------------------------------------------------
-- Surface-vs-bulk-SDF witness — total-claim refuse without witness
------------------------------------------------------------------------

data SurfaceVsBulkSdfWitnessPresence : Set where
  surface-vs-bulk-sdf-witness-absent surface-vs-bulk-sdf-witness-present : SurfaceVsBulkSdfWitnessPresence

record ClassifierSurfaceVsBulkSdfWitness : Set where
  constructor mkClassifierSurfaceVsBulkSdfWitness
  field
    witness-presence : SurfaceVsBulkSdfWitnessPresence
    surface-vs-bulk-sdf-gap-total : ℕ

surfaceVsBulkSdfWitnessAbsent : ClassifierSurfaceVsBulkSdfWitness
surfaceVsBulkSdfWitnessAbsent = mkClassifierSurfaceVsBulkSdfWitness surface-vs-bulk-sdf-witness-absent zero

surfaceVsBulkSdfWitnessPresentZeroGap : ClassifierSurfaceVsBulkSdfWitness
surfaceVsBulkSdfWitnessPresentZeroGap = mkClassifierSurfaceVsBulkSdfWitness surface-vs-bulk-sdf-witness-present zero

surfaceVsBulkSdfWitnessPresentWithGaps : ℕ → ClassifierSurfaceVsBulkSdfWitness
surfaceVsBulkSdfWitnessPresentWithGaps n = mkClassifierSurfaceVsBulkSdfWitness surface-vs-bulk-sdf-witness-present n

surfaceVsBulkSdfWitnessGapFree : ClassifierSurfaceVsBulkSdfWitness → Bool
surfaceVsBulkSdfWitnessGapFree (mkClassifierSurfaceVsBulkSdfWitness surface-vs-bulk-sdf-witness-absent _) = false
surfaceVsBulkSdfWitnessGapFree (mkClassifierSurfaceVsBulkSdfWitness surface-vs-bulk-sdf-witness-present n) =
  does (n ℕ-Props.≟ zero)

surface-vs-bulk-sdf-witness-present-zero-gap-free :
  surfaceVsBulkSdfWitnessGapFree surfaceVsBulkSdfWitnessPresentZeroGap ≡ true
surface-vs-bulk-sdf-witness-present-zero-gap-free = refl

surface-vs-bulk-sdf-witness-absent-not-gap-free :
  surfaceVsBulkSdfWitnessGapFree surfaceVsBulkSdfWitnessAbsent ≡ false
surface-vs-bulk-sdf-witness-absent-not-gap-free = refl

surface-vs-bulk-sdf-witness-with-gaps-not-gap-free :
  ∀ n → surfaceVsBulkSdfWitnessGapFree (surfaceVsBulkSdfWitnessPresentWithGaps (suc n)) ≡ false
surface-vs-bulk-sdf-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Surface-vs-bulk-SDF **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data SurfaceVsBulkSdfConservationVerdict : Set where
  verdict-unwired-ok verdict-surface-vs-bulk-sdf-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : SurfaceVsBulkSdfConservationVerdict

surfaceVsBulkSdfConservationVerdictOk : SurfaceVsBulkSdfConservationVerdict → Bool
surfaceVsBulkSdfConservationVerdictOk verdict-unwired-ok = true
surfaceVsBulkSdfConservationVerdictOk verdict-surface-vs-bulk-sdf-admissible-ok = true
surfaceVsBulkSdfConservationVerdictOk verdict-concurrent-product-ok = true
surfaceVsBulkSdfConservationVerdictOk _ = false

evaluateSurfaceVsBulkSdfConservationClose :
  SurfaceVsBulkSdfConservationModality → ClassifierSurfaceVsBulkSdfStep → ClassifierSurfaceVsBulkSdfWitness
  → SurfaceVsBulkSdfBundleWitness → Bool → SurfaceVsBulkSdfConservationVerdict
evaluateSurfaceVsBulkSdfConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-proved _ (mkClassifierSurfaceVsBulkSdfWitness surface-vs-bulk-sdf-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-proved _ (mkClassifierSurfaceVsBulkSdfWitness surface-vs-bulk-sdf-witness-present _) w false
  with surfaceVsBulkSdfBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-surface-vs-bulk-sdf-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without surface-vs-bulk-SDF witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-unwired namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-assumed namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-surrogate namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  surfaceVsBulkSdfConservationVerdictOk
    (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-unwired namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false)
    ≡ true
  × surfaceVsBulkSdfConservationVerdictOk
      (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-assumed namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false)
      ≡ true
  × surfaceVsBulkSdfConservationVerdictOk
      (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-surrogate namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without surface-vs-bulk-SDF witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  surfaceVsBulkSdfConservationVerdictOk
    (evaluateSurfaceVsBulkSdfConservationClose
       surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false ≡
  verdict-surface-vs-bulk-sdf-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-proved
    (xorMutuallyExclusiveOp bulkInteriorSdfLeaf interfaceShellLeaf)
    surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  surfaceVsBulkSdfConservationVerdictOk
    (evaluateSurfaceVsBulkSdfConservationClose
       surface-vs-bulk-sdf-conservation-proved
       (xorMutuallyExclusiveOp bulkInteriorSdfLeaf interfaceShellLeaf)
       surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-proved
    (xorMutuallyExclusiveOp bulkInteriorSdfLeaf interfaceShellLeaf)
    surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-surface-vs-bulk-SDF — nuance **product** closed
------------------------------------------------------------------------

surface-vs-bulk-sdf-admissible-ok :
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap unwiredWitness false ≡
  verdict-surface-vs-bulk-sdf-admissible-ok
surface-vs-bulk-sdf-admissible-ok = refl

surface-vs-bulk-sdf-admissible-verdict-ok :
  surfaceVsBulkSdfConservationVerdictOk
    (evaluateSurfaceVsBulkSdfConservationClose
       surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap unwiredWitness false)
    ≡ true
surface-vs-bulk-sdf-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — surface-vs-bulk-SDF nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  surfaceVsBulkSdfConservationVerdictOk
    (evaluateSurfaceVsBulkSdfConservationClose
       surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-surface-vs-bulk-sdf15-proved :
  surfaceVsBulkSdfConservationVerdictOk
    (evaluateSurfaceVsBulkSdfConservationClose
       surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness false)
    ≡ true
  × surfaceVsBulkSdf15Proved ≡ false
concurrent-product-ok-still-not-surface-vs-bulk-sdf15-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateSurfaceVsBulkSdfConservationClose
    surface-vs-bulk-sdf-conservation-unwired namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  surfaceVsBulkSdfConservationVerdictOk
    (evaluateSurfaceVsBulkSdfConservationClose
       surface-vs-bulk-sdf-conservation-unwired namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

surfaceVsBulkSdfConservationFiberOk : FormalFiber → Bool
surfaceVsBulkSdfConservationFiberOk fiber-quantum-knowing = true
surfaceVsBulkSdfConservationFiberOk fiber-meso-acting = false

surface-vs-bulk-sdf-conservation-knowing-fiber-ok :
  surfaceVsBulkSdfConservationFiberOk fiber-quantum-knowing ≡ true
surface-vs-bulk-sdf-conservation-knowing-fiber-ok = refl

surface-vs-bulk-sdf-conservation-meso-acting-not-ok :
  surfaceVsBulkSdfConservationFiberOk fiber-meso-acting ≡ false
surface-vs-bulk-sdf-conservation-meso-acting-not-ok = refl

surface-vs-bulk-sdf-conservation-routes-knowing-not-meso :
  surfaceVsBulkSdfConservationFiberOk fiber-quantum-knowing ≡ true ×
  surfaceVsBulkSdfConservationFiberOk fiber-meso-acting ≡ false
surface-vs-bulk-sdf-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  surfaceVsBulkSdfConservationFiberOk fiber-quantum-knowing ∧
  not (surfaceVsBulkSdfConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 15 surface_vs_bulk_sdf Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

surface-vs-bulk-sdf-15-not-proved : surfaceVsBulkSdf15Proved ≡ false
surface-vs-bulk-sdf-15-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

surface-vs-bulk-sdf-second-law-conservation-framed : surfaceVsBulkSdfSecondLawConservationFramed ≡ true
surface-vs-bulk-sdf-second-law-conservation-framed = refl

surface-vs-bulk-sdf-not-xor-pin : surfaceVsBulkSdfNotXor ≡ true
surface-vs-bulk-sdf-not-xor-pin = surface-vs-bulk-sdf-not-xor

thin-slab-ne-bulk-interior-pin : thinSlabNeBulkInterior ≡ true
thin-slab-ne-bulk-interior-pin = refl

not-parallel-surface-vs-bulk-sdf-axiom-minted-pin : notParallelSurfaceBulkSdfAxiomMinted ≡ true
not-parallel-surface-vs-bulk-sdf-axiom-minted-pin = refl

tp-graph-function-not-float-pin-pin : tpGraphFunctionNotFloatPin ≡ true
tp-graph-function-not-float-pin-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel surface_vs_bulk_sdf axiom fork)
------------------------------------------------------------------------

surfaceVsBulkSdfConservationAxiom :
  (surfaceVsBulkSdf15Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (surfaceVsBulkSdfSecondLawConservationFramed ≡ true)
  × (surfaceVsBulkSdfNotXor ≡ true)
  × (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-unwired namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessAbsent surfaceVsBulkSdfNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-proved (xorMutuallyExclusiveOp bulkInteriorSdfLeaf interfaceShellLeaf) surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap unwiredWitness false ≡ verdict-surface-vs-bulk-sdf-admissible-ok)
  × (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-proved namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (surfaceVsBulkSdfConservationFiberOk fiber-quantum-knowing ≡ true)
  × (surfaceVsBulkSdfConservationFiberOk fiber-meso-acting ≡ false)
  × (surfaceVsBulkSdfConservationVerdictOk (evaluateSurfaceVsBulkSdfConservationClose surface-vs-bulk-sdf-conservation-unwired namedSurfaceVsBulkSdfNuanceProduct surfaceVsBulkSdfWitnessPresentZeroGap surfaceVsBulkSdfNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp surfaceVsBulkSdfIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a surfaceVsBulkSdfIdentity) ≡ true)
  × (isSurfaceVsBulkSdfAdmissible (xorMutuallyExclusiveOp bulkInteriorSdfLeaf interfaceShellLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (surfaceVsBulkSdfClassIndex ≡ 15)
  × (SurfaceVsBulkSdfBundleWitness.present-count surfaceVsBulkSdfNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
surfaceVsBulkSdfConservationAxiom =
  surface-vs-bulk-sdf-15-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , surface-vs-bulk-sdf-second-law-conservation-framed
  , surface-vs-bulk-sdf-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , surface-vs-bulk-sdf-admissible-ok
  , concurrent-product-ok
  , surface-vs-bulk-sdf-conservation-knowing-fiber-ok
  , surface-vs-bulk-sdf-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , surface-vs-bulk-sdf-class-index-fifteen
  , surface-vs-bulk-sdf-nuance-present-count
  , iron-z-26
  , oganesson-z-118

surfaceVsBulkSdfConservationNamed : String
surfaceVsBulkSdfConservationNamed =
  "surfaceVsBulkSdfConservation: pattern class 15 surface_vs_bulk_sdf conservation concurrent Pi_c identity conserved bulk interior SDF interface shell surface exterior class 15 surface_vs_bulk_sdf concurrent product identity conserved present ge 2 product not XOR thin slab ne bulk interior no parallel surface_vs_bulk_sdf axiom T P graph functions not float pins"

surfaceVsBulkSdfConservationCrossWitnessAuthority : String
surfaceVsBulkSdfConservationCrossWitnessAuthority =
  "umst/umst-chem/src/surface_bulk_sdf.rs"

surfaceVsBulkSdfTableAuthority : String
surfaceVsBulkSdfTableAuthority =
  "umst/umst-chem/src/l0_tables/surface_vs_bulk_sdf.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

surfaceVsBulkSdfConservationCellId : String
surfaceVsBulkSdfConservationCellId = "CHEM-FORMAL-Q-AGDA-SURFACE-VS-BULK-SDF-CONSERVATION"

surfaceVsBulkSdfConservationNonClaim : String
surfaceVsBulkSdfConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-SURFACE-VS-BULK-SDF-CONSERVATION pattern class 15 surface_vs_bulk_sdf conservation concurrent Pi_c identity conserved bulk interior SDF interface shell surface exterior class 15 surface_vs_bulk_sdf product not XOR thin slab ne bulk interior no parallel surface_vs_bulk_sdf axiom T P graph functions not float pins XOR mutually exclusive refuse surface vs bulk SDF nuance witness concurrent surfaceVsBulkSdf15Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite surface_bulk_sdf.rs l0_tables surface_vs_bulk_sdf not fork not physics GREEN not production_wired"

surface-vs-bulk-sdf-conservation-cell-id :
  surfaceVsBulkSdfConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-SURFACE-VS-BULK-SDF-CONSERVATION"
surface-vs-bulk-sdf-conservation-cell-id = refl

surface-vs-bulk-sdf-conservation-cites-surface-vs-bulk-sdf-rs :
  surfaceVsBulkSdfConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/surface_bulk_sdf.rs"
surface-vs-bulk-sdf-conservation-cites-surface-vs-bulk-sdf-rs = refl

surface-vs-bulk-sdf-conservation-cites-l0-table-rs :
  surfaceVsBulkSdfTableAuthority ≡
  "umst/umst-chem/src/l0_tables/surface_vs_bulk_sdf.rs"
surface-vs-bulk-sdf-conservation-cites-l0-table-rs = refl

surface-vs-bulk-sdf-conservation-modality-unwired :
  surfaceVsBulkSdfConservationModalityCurrent ≡ surface-vs-bulk-sdf-conservation-unwired
surface-vs-bulk-sdf-conservation-modality-unwired = refl

surfaceVsBulkSdfConservationPhysicsGreenAuthorized : Set
surfaceVsBulkSdfConservationPhysicsGreenAuthorized = ⊥

surface-vs-bulk-sdf-conservation-physics-green-false : ¬ surfaceVsBulkSdfConservationPhysicsGreenAuthorized
surface-vs-bulk-sdf-conservation-physics-green-false ()

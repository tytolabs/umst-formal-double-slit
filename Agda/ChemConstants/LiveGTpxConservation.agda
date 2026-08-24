-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.LiveGTpxConservation.agda
--
-- CHEM-FORMAL-Q-AGDA-LIVE-G-TPX-CONSERVATION
-- LIVE measured G(T,P,x) **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (T graph function + P graph function +
--     live measured G(T,P,x) type-only; **product** not XOR, no parallel live G axiom)
--   * XOR mutually-exclusive refuse; live G(T,P,x) nuance witness concurrent
--     (T graph function + P graph function + live measured G(T,P,x) type-only)
--   * **live G(T,P,x)** laws Unwired (liveGTpxProved = false; conservationProved = false)
--   * formation-zero ≠ G; type-only until WAVE100 lifts live wire
--
-- INT (read-only cite): umst/umst-chem/src/thermo_g.rs
-- X-row: umst/umst-chem/src/x_rows/live_g_tpx_conservation.rs
-- T graph function: umst/umst-chem/src/temperature_is_graph_function.rs
-- P graph function: umst/umst-chem/src/pressure_is_graph_function.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel live G axiom; formation-zero theater ≠ G. Product not XOR.
-- LIVE G(T,P,x) type-only until WAVE100 — freeze-safe conservation identity.
-- WAVE100: no cabal/lakefile/lib.rs/eos.rs/nano wiring.
------------------------------------------------------------------------
module ChemConstants.LiveGTpxConservation where


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
-- Modality + LIVE G(T,P,x) **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data LiveGTpxConservationModality : Set where
  live-g-tpx-conservation-unwired live-g-tpx-conservation-assumed
    live-g-tpx-conservation-proved live-g-tpx-conservation-surrogate
    : LiveGTpxConservationModality

liveGTpxConservationModalityCurrent : LiveGTpxConservationModality
liveGTpxConservationModalityCurrent = live-g-tpx-conservation-unwired

liveGTpxProved productionWired not118SquaredGreenTable
  liveGTpxSecondLawConservationFramed liveGTpxNotXor
  conservationProved : Bool
liveGTpxProved = false
productionWired = false
not118SquaredGreenTable = true
liveGTpxSecondLawConservationFramed = true
liveGTpxNotXor = true
conservationProved = false

typeOnlyUntilWave100 notParallelLiveGTpxAxiomMinted formationZeroNotG : Bool
typeOnlyUntilWave100 = true
notParallelLiveGTpxAxiomMinted = true
formationZeroNotG = true

------------------------------------------------------------------------
-- Green Book **G** vs formation-zero — live measured G(T,P,x) type-only
------------------------------------------------------------------------

data LiveGTpxGSymbolTag : Set where
  live-measured-g-tpx green-book-g formation-zero : LiveGTpxGSymbolTag

isLiveMeasuredGTpx isGreenBookG isFormationZero : LiveGTpxGSymbolTag → Bool
isLiveMeasuredGTpx live-measured-g-tpx = true
isLiveMeasuredGTpx _ = false

isGreenBookG green-book-g = true
isGreenBookG _ = false

isFormationZero formation-zero = true
isFormationZero _ = false

live-measured-g-tpx-named :
  isLiveMeasuredGTpx live-measured-g-tpx ≡ true × isFormationZero live-measured-g-tpx ≡ false
live-measured-g-tpx-named = refl , refl

formation-zero-not-green-book-g :
  isFormationZero formation-zero ≡ true × isGreenBookG formation-zero ≡ false
formation-zero-not-green-book-g = refl , refl

formation-zero-distinct-from-green-book-g : formation-zero ≢ green-book-g
formation-zero-distinct-from-green-book-g ()

------------------------------------------------------------------------
-- WAVE100 freeze — lib.rs / eos.rs / nano not wired
------------------------------------------------------------------------

wave100LibRsWired wave100EosRsWired wave100NanoWired : Bool
wave100LibRsWired = false
wave100EosRsWired = false
wave100NanoWired = false

wave100-not-wired :
  wave100LibRsWired ≡ false × wave100EosRsWired ≡ false × wave100NanoWired ≡ false
wave100-not-wired = refl , refl , refl

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
-- LIVE G(T,P,x) wire index pin
------------------------------------------------------------------------

liveGTpxClassIndex : ℕ
liveGTpxClassIndex = 20

live-g-tpx-class-index-live-wire : liveGTpxClassIndex ≡ 20
live-g-tpx-class-index-live-wire = refl

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
-- LiveGTpxBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data LiveGTpxBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : LiveGTpxBundleSlot

isSlotPresent : LiveGTpxBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- LiveGTpxBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record LiveGTpxBundle : Set where
  field slot : ℕ → LiveGTpxBundleSlot

liveGTpxBundleUnwired : LiveGTpxBundle
liveGTpxBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : LiveGTpxBundle → ℕ → LiveGTpxBundleSlot → LiveGTpxBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else LiveGTpxBundle.slot b j }

withPresent : LiveGTpxBundle → ℕ → LiveGTpxBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record LiveGTpxBundleWitness : Set where
  constructor mkLiveGTpxBundleWitness
  field
    bundle : LiveGTpxBundle
    present-count : ℕ

liveGTpxBundleIsConcurrentProduct : LiveGTpxBundleWitness → Bool
liveGTpxBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? LiveGTpxBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named live G(T,P,x) channel indices — T graph function (1), P graph function (2), live measured G(T,P,x) type-only (3)
------------------------------------------------------------------------

temperatureGraphFunctionChannelIndex pressureGraphFunctionChannelIndex liveMeasuredGTpxTypeOnlyChannelIndex : ℕ
temperatureGraphFunctionChannelIndex = 1
pressureGraphFunctionChannelIndex = 2
liveMeasuredGTpxTypeOnlyChannelIndex = 3

temperature-graph-function-index-one : temperatureGraphFunctionChannelIndex ≡ 1
temperature-graph-function-index-one = refl

pressure-graph-function-index-two : pressureGraphFunctionChannelIndex ≡ 2
pressure-graph-function-index-two = refl

live-measured-g-tpx-type-only-index-three : liveMeasuredGTpxTypeOnlyChannelIndex ≡ 3
live-measured-g-tpx-type-only-index-three = refl

------------------------------------------------------------------------
-- Live G(T,P,x) nuance witness — T graph function + P graph function + live measured G(T,P,x) type-only concurrent
------------------------------------------------------------------------

liveGTpxNuanceBundle : LiveGTpxBundle
liveGTpxNuanceBundle =
  withPresent
    (withPresent
      (withPresent liveGTpxBundleUnwired temperatureGraphFunctionChannelIndex)
      pressureGraphFunctionChannelIndex)
    liveMeasuredGTpxTypeOnlyChannelIndex

liveGTpxNuanceWitness : LiveGTpxBundleWitness
liveGTpxNuanceWitness =
  mkLiveGTpxBundleWitness liveGTpxNuanceBundle 3

live-g-tpx-nuance-temperature-graph-function-present :
  isSlotPresent (LiveGTpxBundle.slot liveGTpxNuanceBundle temperatureGraphFunctionChannelIndex) ≡ true
live-g-tpx-nuance-temperature-graph-function-present = refl

live-g-tpx-nuance-pressure-graph-function-present :
  isSlotPresent (LiveGTpxBundle.slot liveGTpxNuanceBundle pressureGraphFunctionChannelIndex) ≡ true
live-g-tpx-nuance-pressure-graph-function-present = refl

live-g-tpx-nuance-live-measured-g-tpx-type-only-present :
  isSlotPresent (LiveGTpxBundle.slot liveGTpxNuanceBundle liveMeasuredGTpxTypeOnlyChannelIndex) ≡ true
live-g-tpx-nuance-live-measured-g-tpx-type-only-present = refl

live-g-tpx-nuance-present-count : LiveGTpxBundleWitness.present-count liveGTpxNuanceWitness ≡ 3
live-g-tpx-nuance-present-count = refl

live-g-tpx-nuance-concurrent-product :
  liveGTpxBundleIsConcurrentProduct liveGTpxNuanceWitness ≡ true
live-g-tpx-nuance-concurrent-product = refl

live-g-tpx-nuance-three-factors-concurrent :
  isSlotPresent (LiveGTpxBundle.slot liveGTpxNuanceBundle temperatureGraphFunctionChannelIndex) ≡ true
  × isSlotPresent (LiveGTpxBundle.slot liveGTpxNuanceBundle pressureGraphFunctionChannelIndex) ≡ true
  × isSlotPresent (LiveGTpxBundle.slot liveGTpxNuanceBundle liveMeasuredGTpxTypeOnlyChannelIndex) ≡ true
  × LiveGTpxBundleWitness.present-count liveGTpxNuanceWitness ≡ 3
live-g-tpx-nuance-three-factors-concurrent =
  live-g-tpx-nuance-temperature-graph-function-present
  , live-g-tpx-nuance-pressure-graph-function-present
  , live-g-tpx-nuance-live-measured-g-tpx-type-only-present
  , live-g-tpx-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : LiveGTpxBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if liveGTpxBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = LiveGTpxBundleWitness.bundle w
       in if isSlotPresent (LiveGTpxBundle.slot b i)
          then if isSlotPresent (LiveGTpxBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : LiveGTpxBundleWitness
unwiredWitness = mkLiveGTpxBundleWitness liveGTpxBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

live-g-tpx-nuance-xor-product-ok :
  evaluateXorRefuse liveGTpxNuanceWitness temperatureGraphFunctionChannelIndex pressureGraphFunctionChannelIndex ≡ xor-product-ok
live-g-tpx-nuance-xor-product-ok = refl

live-g-tpx-not-xor : liveGTpxNotXor ≡ true
live-g-tpx-not-xor = refl

------------------------------------------------------------------------
-- ClassifierLiveGTpxStep scaffold — LiveGTpxBundle **conservation**
------------------------------------------------------------------------

data ClassifierLiveGTpxStep : Set where
  live-g-tpx-identity : ClassifierLiveGTpxStep
  slot-leaf : ℕ → ClassifierLiveGTpxStep
  product-concurrent : ClassifierLiveGTpxStep → ClassifierLiveGTpxStep → ClassifierLiveGTpxStep
  xor-mutually-exclusive : ClassifierLiveGTpxStep → ClassifierLiveGTpxStep → ClassifierLiveGTpxStep

liveGTpxIdentity : ClassifierLiveGTpxStep
liveGTpxIdentity = live-g-tpx-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierLiveGTpxStep → ClassifierLiveGTpxStep → ClassifierLiveGTpxStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

temperatureGraphFunctionLeaf pressureGraphFunctionLeaf liveMeasuredGTpxTypeOnlyLeaf : ClassifierLiveGTpxStep
temperatureGraphFunctionLeaf = slot-leaf temperatureGraphFunctionChannelIndex
pressureGraphFunctionLeaf = slot-leaf pressureGraphFunctionChannelIndex
liveMeasuredGTpxTypeOnlyLeaf = slot-leaf liveMeasuredGTpxTypeOnlyChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierLiveGTpxStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isLiveGTpxIdentity : ClassifierLiveGTpxStep → Bool
isLiveGTpxIdentity live-g-tpx-identity = true
isLiveGTpxIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at live-g-tpx-identity
------------------------------------------------------------------------

live-g-tpx-left-identity :
  ∀ (a : ClassifierLiveGTpxStep) →
  isLiveGTpxIdentity liveGTpxIdentity ≡ true
  × isProductConcurrent (productConcurrentOp liveGTpxIdentity a) ≡ true
live-g-tpx-left-identity a = refl , refl

live-g-tpx-right-identity :
  ∀ (a : ClassifierLiveGTpxStep) →
  isProductConcurrent (productConcurrentOp a liveGTpxIdentity) ≡ true
  × isLiveGTpxIdentity liveGTpxIdentity ≡ true
live-g-tpx-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-live-g-tpx :
  (∀ a → isProductConcurrent (productConcurrentOp liveGTpxIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a liveGTpxIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-live-g-tpx =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named live G(T,P,x) nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedLiveGTpxNuanceProduct : ClassifierLiveGTpxStep
namedLiveGTpxNuanceProduct =
  productConcurrentOp
    (productConcurrentOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf)
    liveMeasuredGTpxTypeOnlyLeaf

named-live-g-tpx-nuance-product-concurrent :
  isProductConcurrent namedLiveGTpxNuanceProduct ≡ true
  × liveGTpxBundleIsConcurrentProduct liveGTpxNuanceWitness ≡ true
named-live-g-tpx-nuance-product-concurrent = refl , live-g-tpx-nuance-concurrent-product

------------------------------------------------------------------------
-- LiveGTpxBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data LiveGTpxAdmissibility : Set where
  live-g-tpx-admissible live-g-tpx-xor-refuse : LiveGTpxAdmissibility

isLiveGTpxPreserving : ClassifierLiveGTpxStep → Bool
isLiveGTpxPreserving live-g-tpx-identity = true
isLiveGTpxPreserving (slot-leaf _) = true
isLiveGTpxPreserving (product-concurrent a b) =
  isLiveGTpxPreserving a ∧ isLiveGTpxPreserving b
isLiveGTpxPreserving (xor-mutually-exclusive _ _) = false

isLiveGTpxAdmissible : ClassifierLiveGTpxStep → Bool
isLiveGTpxAdmissible step = isLiveGTpxPreserving step

temperature-graph-function-leaf-admissible : isLiveGTpxAdmissible temperatureGraphFunctionLeaf ≡ true
temperature-graph-function-leaf-admissible = refl

pressure-graph-function-leaf-admissible : isLiveGTpxAdmissible pressureGraphFunctionLeaf ≡ true
pressure-graph-function-leaf-admissible = refl

live-measured-g-tpx-type-only-leaf-admissible : isLiveGTpxAdmissible liveMeasuredGTpxTypeOnlyLeaf ≡ true
live-measured-g-tpx-type-only-leaf-admissible = refl

named-live-g-tpx-nuance-admissible : isLiveGTpxAdmissible namedLiveGTpxNuanceProduct ≡ true
named-live-g-tpx-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isLiveGTpxAdmissible (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-live-measured-g-tpx-refuse :
  isLiveGTpxAdmissible (xorMutuallyExclusiveOp pressureGraphFunctionLeaf liveMeasuredGTpxTypeOnlyLeaf) ≡ false
xor-mutually-exclusive-live-measured-g-tpx-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data LiveGTpxWitnessPresence : Set where
  live-g-tpx-witness-absent live-g-tpx-witness-present : LiveGTpxWitnessPresence

record ClassifierLiveGTpxWitness : Set where
  constructor mkClassifierLiveGTpxWitness
  field
    witness-presence : LiveGTpxWitnessPresence
    live-g-tpx-gap-total : ℕ

liveGTpxWitnessAbsent : ClassifierLiveGTpxWitness
liveGTpxWitnessAbsent = mkClassifierLiveGTpxWitness live-g-tpx-witness-absent zero

liveGTpxWitnessPresentZeroGap : ClassifierLiveGTpxWitness
liveGTpxWitnessPresentZeroGap = mkClassifierLiveGTpxWitness live-g-tpx-witness-present zero

liveGTpxWitnessPresentWithGaps : ℕ → ClassifierLiveGTpxWitness
liveGTpxWitnessPresentWithGaps n = mkClassifierLiveGTpxWitness live-g-tpx-witness-present n

liveGTpxWitnessGapFree : ClassifierLiveGTpxWitness → Bool
liveGTpxWitnessGapFree (mkClassifierLiveGTpxWitness live-g-tpx-witness-absent _) = false
liveGTpxWitnessGapFree (mkClassifierLiveGTpxWitness live-g-tpx-witness-present n) =
  does (n ℕ-Props.≟ zero)

live-g-tpx-witness-present-zero-gap-free :
  liveGTpxWitnessGapFree liveGTpxWitnessPresentZeroGap ≡ true
live-g-tpx-witness-present-zero-gap-free = refl

live-g-tpx-witness-absent-not-gap-free :
  liveGTpxWitnessGapFree liveGTpxWitnessAbsent ≡ false
live-g-tpx-witness-absent-not-gap-free = refl

live-g-tpx-witness-with-gaps-not-gap-free :
  ∀ n → liveGTpxWitnessGapFree (liveGTpxWitnessPresentWithGaps (suc n)) ≡ false
live-g-tpx-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-live-G(T,P,x) **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data LiveGTpxConservationVerdict : Set where
  verdict-unwired-ok verdict-live-g-tpx-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : LiveGTpxConservationVerdict

liveGTpxConservationVerdictOk : LiveGTpxConservationVerdict → Bool
liveGTpxConservationVerdictOk verdict-unwired-ok = true
liveGTpxConservationVerdictOk verdict-live-g-tpx-admissible-ok = true
liveGTpxConservationVerdictOk verdict-concurrent-product-ok = true
liveGTpxConservationVerdictOk _ = false

evaluateLiveGTpxConservationClose :
  LiveGTpxConservationModality → ClassifierLiveGTpxStep → ClassifierLiveGTpxWitness
  → LiveGTpxBundleWitness → Bool → LiveGTpxConservationVerdict
evaluateLiveGTpxConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateLiveGTpxConservationClose live-g-tpx-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateLiveGTpxConservationClose live-g-tpx-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateLiveGTpxConservationClose live-g-tpx-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateLiveGTpxConservationClose live-g-tpx-conservation-proved _ (mkClassifierLiveGTpxWitness live-g-tpx-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateLiveGTpxConservationClose live-g-tpx-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateLiveGTpxConservationClose live-g-tpx-conservation-proved _ (mkClassifierLiveGTpxWitness live-g-tpx-witness-present _) w false
  with liveGTpxBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-live-g-tpx-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without live G(T,P,x) witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-unwired namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-assumed namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-surrogate namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  liveGTpxConservationVerdictOk
    (evaluateLiveGTpxConservationClose live-g-tpx-conservation-unwired namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false)
    ≡ true
  × liveGTpxConservationVerdictOk
      (evaluateLiveGTpxConservationClose live-g-tpx-conservation-assumed namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false)
      ≡ true
  × liveGTpxConservationVerdictOk
      (evaluateLiveGTpxConservationClose live-g-tpx-conservation-surrogate namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without live G(T,P,x) witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  liveGTpxConservationVerdictOk
    (evaluateLiveGTpxConservationClose
       live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false ≡
  verdict-live-g-tpx-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-proved
    (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf)
    liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  liveGTpxConservationVerdictOk
    (evaluateLiveGTpxConservationClose
       live-g-tpx-conservation-proved
       (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf)
       liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-proved
    (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf)
    liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-live-G(T,P,x) — nuance **product** closed
------------------------------------------------------------------------

live-g-tpx-admissible-ok :
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap unwiredWitness false ≡
  verdict-live-g-tpx-admissible-ok
live-g-tpx-admissible-ok = refl

live-g-tpx-admissible-verdict-ok :
  liveGTpxConservationVerdictOk
    (evaluateLiveGTpxConservationClose
       live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap unwiredWitness false)
    ≡ true
live-g-tpx-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — live G(T,P,x) nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  liveGTpxConservationVerdictOk
    (evaluateLiveGTpxConservationClose
       live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-live-g-tpx-proved :
  liveGTpxConservationVerdictOk
    (evaluateLiveGTpxConservationClose
       live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness false)
    ≡ true
  × liveGTpxProved ≡ false
concurrent-product-ok-still-not-live-g-tpx-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateLiveGTpxConservationClose
    live-g-tpx-conservation-unwired namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  liveGTpxConservationVerdictOk
    (evaluateLiveGTpxConservationClose
       live-g-tpx-conservation-unwired namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

liveGTpxConservationFiberOk : FormalFiber → Bool
liveGTpxConservationFiberOk fiber-quantum-knowing = true
liveGTpxConservationFiberOk fiber-meso-acting = false

live-g-tpx-conservation-knowing-fiber-ok :
  liveGTpxConservationFiberOk fiber-quantum-knowing ≡ true
live-g-tpx-conservation-knowing-fiber-ok = refl

live-g-tpx-conservation-meso-acting-not-ok :
  liveGTpxConservationFiberOk fiber-meso-acting ≡ false
live-g-tpx-conservation-meso-acting-not-ok = refl

live-g-tpx-conservation-routes-knowing-not-meso :
  liveGTpxConservationFiberOk fiber-quantum-knowing ≡ true ×
  liveGTpxConservationFiberOk fiber-meso-acting ≡ false
live-g-tpx-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  liveGTpxConservationFiberOk fiber-quantum-knowing ∧
  not (liveGTpxConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not live G(T,P,x) Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

live-g-tpx-not-proved : liveGTpxProved ≡ false
live-g-tpx-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

live-g-tpx-second-law-conservation-framed : liveGTpxSecondLawConservationFramed ≡ true
live-g-tpx-second-law-conservation-framed = refl

live-g-tpx-not-xor-pin : liveGTpxNotXor ≡ true
live-g-tpx-not-xor-pin = live-g-tpx-not-xor

type-only-until-wave100-pin : typeOnlyUntilWave100 ≡ true
type-only-until-wave100-pin = refl

not-parallel-live-g-tpx-axiom-minted-pin : notParallelLiveGTpxAxiomMinted ≡ true
not-parallel-live-g-tpx-axiom-minted-pin = refl

formation-zero-not-g-pin : formationZeroNotG ≡ true
formation-zero-not-g-pin = refl

conservation-not-proved : conservationProved ≡ false
conservation-not-proved = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel live G axiom fork)
------------------------------------------------------------------------

liveGTpxConservationAxiom :
  (liveGTpxProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (liveGTpxSecondLawConservationFramed ≡ true)
  × (liveGTpxNotXor ≡ true)
  × (evaluateLiveGTpxConservationClose live-g-tpx-conservation-unwired namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateLiveGTpxConservationClose live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessAbsent liveGTpxNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateLiveGTpxConservationClose live-g-tpx-conservation-proved (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf) liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateLiveGTpxConservationClose live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap unwiredWitness false ≡ verdict-live-g-tpx-admissible-ok)
  × (evaluateLiveGTpxConservationClose live-g-tpx-conservation-proved namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (liveGTpxConservationFiberOk fiber-quantum-knowing ≡ true)
  × (liveGTpxConservationFiberOk fiber-meso-acting ≡ false)
  × (liveGTpxConservationVerdictOk (evaluateLiveGTpxConservationClose live-g-tpx-conservation-unwired namedLiveGTpxNuanceProduct liveGTpxWitnessPresentZeroGap liveGTpxNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp liveGTpxIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a liveGTpxIdentity) ≡ true)
  × (isLiveGTpxAdmissible (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (liveGTpxClassIndex ≡ 20)
  × (LiveGTpxBundleWitness.present-count liveGTpxNuanceWitness ≡ 3)
  × (elementAtomicZ platinum ≡ 78)
  × (elementAtomicZ oganesson ≡ 118)
  × (conservationProved ≡ false)
  × (isFormationZero formation-zero ≡ true × isGreenBookG formation-zero ≡ false)
  × (wave100LibRsWired ≡ false)
  × (wave100EosRsWired ≡ false)
  × (wave100NanoWired ≡ false)
liveGTpxConservationAxiom =
  live-g-tpx-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , live-g-tpx-second-law-conservation-framed
  , live-g-tpx-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , live-g-tpx-admissible-ok
  , concurrent-product-ok
  , live-g-tpx-conservation-knowing-fiber-ok
  , live-g-tpx-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , live-g-tpx-class-index-live-wire
  , live-g-tpx-nuance-present-count
  , platinum-z-78
  , oganesson-z-118
  , conservation-not-proved
  , formation-zero-not-green-book-g
  , refl
  , refl
  , refl

liveGTpxConservationNamed : String
liveGTpxConservationNamed =
  "liveGTpxConservation: LIVE measured G(T,P,x) type-only until WAVE100 conservation concurrent Pi_c identity conserved T graph function P graph function live measured G(T,P,x) type-only concurrent product identity conserved present ge 2 product not XOR formation-zero not G type-only until WAVE100 conservationProved false liveGTpxProved false"

liveGTpxConservationCrossWitnessAuthority : String
liveGTpxConservationCrossWitnessAuthority =
  "umst/umst-chem/src/thermo_g.rs"

liveGTpxTableAuthority : String
liveGTpxTableAuthority =
  "umst/umst-chem/src/x_rows/live_g_tpx_conservation.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

liveGTpxConservationCellId : String
liveGTpxConservationCellId = "CHEM-FORMAL-Q-AGDA-LIVE-G-TPX-CONSERVATION"

liveGTpxConservationNonClaim : String
liveGTpxConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-LIVE-G-TPX-CONSERVATION LIVE measured G(T,P,x) type-only until WAVE100 conservation concurrent Pi_c identity conserved T graph function P graph function live measured G(T,P,x) type-only product not XOR formation-zero not G type-only until WAVE100 XOR mutually exclusive refuse live G(T,P,x) nuance witness concurrent liveGTpxProved false conservationProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite thermo_g.rs x_rows live_g_tpx_conservation temperature_is_graph_function pressure_is_graph_function not fork not physics GREEN not production_wired WAVE100 no lib.rs eos.rs nano"

live-g-tpx-conservation-cell-id :
  liveGTpxConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-LIVE-G-TPX-CONSERVATION"
live-g-tpx-conservation-cell-id = refl

live-g-tpx-conservation-cites-thermo-g-rs :
  liveGTpxConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/thermo_g.rs"
live-g-tpx-conservation-cites-thermo-g-rs = refl

live-g-tpx-conservation-cites-l0-table-rs :
  liveGTpxTableAuthority ≡
  "umst/umst-chem/src/x_rows/live_g_tpx_conservation.rs"
live-g-tpx-conservation-cites-l0-table-rs = refl

live-g-tpx-conservation-modality-unwired :
  liveGTpxConservationModalityCurrent ≡ live-g-tpx-conservation-unwired
live-g-tpx-conservation-modality-unwired = refl

liveGTpxConservationPhysicsGreenAuthorized : Set
liveGTpxConservationPhysicsGreenAuthorized = ⊥

live-g-tpx-conservation-physics-green-false : ¬ liveGTpxConservationPhysicsGreenAuthorized
live-g-tpx-conservation-physics-green-false ()

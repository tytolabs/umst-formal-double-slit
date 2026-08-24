-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.TpParametricConservation.agda
--
-- Pattern class 19 **tp_parametric** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (T graph function + P graph function + class 19 tp_parametric;
--     **product** not XOR, no parallel tp_parametric axiom)
--   * XOR mutually-exclusive refuse; tp_parametric nuance witness concurrent
--     (T graph function + P graph function + class 19 tp_parametric)
--   * **tp_parametric** laws Unwired (tpParametric19Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/tp_parametric_morphism.rs
-- L0 table: umst/umst-chem/src/l0_tables/tp_parametric.rs
-- T graph function: umst/umst-chem/src/temperature_is_graph_function.rs
-- P graph function: umst/umst-chem/src/pressure_is_graph_function.rs
-- Mirrors sibling `ChemConstants/CatalysisConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel tp_parametric axiom; T/P graph functions not 298 K / 1 atm float pins. Product not XOR.
-- Class 19 tp_parametric: T and P are graph functions on Interact graph, not bare float pins.
------------------------------------------------------------------------
module ChemConstants.TpParametricConservation where


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
-- Modality + pattern class 19 **tp_parametric** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data TpParametricConservationModality : Set where
  tp-parametric-conservation-unwired tp-parametric-conservation-assumed
    tp-parametric-conservation-proved tp-parametric-conservation-surrogate
    : TpParametricConservationModality

tpParametricConservationModalityCurrent : TpParametricConservationModality
tpParametricConservationModalityCurrent = tp-parametric-conservation-unwired

tpParametric19Proved productionWired not118SquaredGreenTable
  tpParametricSecondLawConservationFramed tpParametricNotXor : Bool
tpParametric19Proved = false
productionWired = false
not118SquaredGreenTable = true
tpParametricSecondLawConservationFramed = true
tpParametricNotXor = true

temperatureIsGraphFunction notParallelTpParametricAxiomMinted tpFloatPinNotPhysics : Bool
temperatureIsGraphFunction = true
notParallelTpParametricAxiomMinted = true
tpFloatPinNotPhysics = true

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
-- Pattern class 19 tp_parametric index pin
------------------------------------------------------------------------

tpParametricClassIndex : ℕ
tpParametricClassIndex = 19

tp-parametric-class-index-nineteen : tpParametricClassIndex ≡ 19
tp-parametric-class-index-nineteen = refl

------------------------------------------------------------------------
-- Named element Z pins — C (Z=6), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  carbon oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ carbon = 6
elementAtomicZ oganesson = 118

carbon-z-6 : elementAtomicZ carbon ≡ 6
carbon-z-6 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- TpParametricBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data TpParametricBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : TpParametricBundleSlot

isSlotPresent : TpParametricBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- TpParametricBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record TpParametricBundle : Set where
  field slot : ℕ → TpParametricBundleSlot

tpParametricBundleUnwired : TpParametricBundle
tpParametricBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : TpParametricBundle → ℕ → TpParametricBundleSlot → TpParametricBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else TpParametricBundle.slot b j }

withPresent : TpParametricBundle → ℕ → TpParametricBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record TpParametricBundleWitness : Set where
  constructor mkTpParametricBundleWitness
  field
    bundle : TpParametricBundle
    present-count : ℕ

tpParametricBundleIsConcurrentProduct : TpParametricBundleWitness → Bool
tpParametricBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? TpParametricBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named tp_parametric channel indices — T graph function (1), P graph function (2), class 19 tp_parametric (3)
------------------------------------------------------------------------

temperatureGraphFunctionChannelIndex pressureGraphFunctionChannelIndex class19TpParametricChannelIndex : ℕ
temperatureGraphFunctionChannelIndex = 1
pressureGraphFunctionChannelIndex = 2
class19TpParametricChannelIndex = 3

temperature-graph-function-index-one : temperatureGraphFunctionChannelIndex ≡ 1
temperature-graph-function-index-one = refl

pressure-graph-function-index-two : pressureGraphFunctionChannelIndex ≡ 2
pressure-graph-function-index-two = refl

class19-tp-parametric-index-three : class19TpParametricChannelIndex ≡ 3
class19-tp-parametric-index-three = refl

------------------------------------------------------------------------
-- Tp_parametric nuance witness — T graph function + P graph function + class 19 tp_parametric concurrent
------------------------------------------------------------------------

tpParametricNuanceBundle : TpParametricBundle
tpParametricNuanceBundle =
  withPresent
    (withPresent
      (withPresent tpParametricBundleUnwired temperatureGraphFunctionChannelIndex)
      pressureGraphFunctionChannelIndex)
    class19TpParametricChannelIndex

tpParametricNuanceWitness : TpParametricBundleWitness
tpParametricNuanceWitness =
  mkTpParametricBundleWitness tpParametricNuanceBundle 3

tp-parametric-nuance-temperature-graph-function-present :
  isSlotPresent (TpParametricBundle.slot tpParametricNuanceBundle temperatureGraphFunctionChannelIndex) ≡ true
tp-parametric-nuance-temperature-graph-function-present = refl

tp-parametric-nuance-pressure-graph-function-present :
  isSlotPresent (TpParametricBundle.slot tpParametricNuanceBundle pressureGraphFunctionChannelIndex) ≡ true
tp-parametric-nuance-pressure-graph-function-present = refl

tp-parametric-nuance-class19-tp-parametric-present :
  isSlotPresent (TpParametricBundle.slot tpParametricNuanceBundle class19TpParametricChannelIndex) ≡ true
tp-parametric-nuance-class19-tp-parametric-present = refl

tp-parametric-nuance-present-count : TpParametricBundleWitness.present-count tpParametricNuanceWitness ≡ 3
tp-parametric-nuance-present-count = refl

tp-parametric-nuance-concurrent-product :
  tpParametricBundleIsConcurrentProduct tpParametricNuanceWitness ≡ true
tp-parametric-nuance-concurrent-product = refl

tp-parametric-nuance-three-factors-concurrent :
  isSlotPresent (TpParametricBundle.slot tpParametricNuanceBundle temperatureGraphFunctionChannelIndex) ≡ true
  × isSlotPresent (TpParametricBundle.slot tpParametricNuanceBundle pressureGraphFunctionChannelIndex) ≡ true
  × isSlotPresent (TpParametricBundle.slot tpParametricNuanceBundle class19TpParametricChannelIndex) ≡ true
  × TpParametricBundleWitness.present-count tpParametricNuanceWitness ≡ 3
tp-parametric-nuance-three-factors-concurrent =
  tp-parametric-nuance-temperature-graph-function-present
  , tp-parametric-nuance-pressure-graph-function-present
  , tp-parametric-nuance-class19-tp-parametric-present
  , tp-parametric-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : TpParametricBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if tpParametricBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = TpParametricBundleWitness.bundle w
       in if isSlotPresent (TpParametricBundle.slot b i)
          then if isSlotPresent (TpParametricBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : TpParametricBundleWitness
unwiredWitness = mkTpParametricBundleWitness tpParametricBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

tp-parametric-nuance-xor-product-ok :
  evaluateXorRefuse tpParametricNuanceWitness temperatureGraphFunctionChannelIndex pressureGraphFunctionChannelIndex ≡ xor-product-ok
tp-parametric-nuance-xor-product-ok = refl

tp-parametric-not-xor : tpParametricNotXor ≡ true
tp-parametric-not-xor = refl

------------------------------------------------------------------------
-- ClassifierTpParametricStep scaffold — TpParametricBundle **conservation**
------------------------------------------------------------------------

data ClassifierTpParametricStep : Set where
  tp-parametric-identity : ClassifierTpParametricStep
  slot-leaf : ℕ → ClassifierTpParametricStep
  product-concurrent : ClassifierTpParametricStep → ClassifierTpParametricStep → ClassifierTpParametricStep
  xor-mutually-exclusive : ClassifierTpParametricStep → ClassifierTpParametricStep → ClassifierTpParametricStep

tpParametricIdentity : ClassifierTpParametricStep
tpParametricIdentity = tp-parametric-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierTpParametricStep → ClassifierTpParametricStep → ClassifierTpParametricStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

temperatureGraphFunctionLeaf pressureGraphFunctionLeaf class19TpParametricLeaf : ClassifierTpParametricStep
temperatureGraphFunctionLeaf = slot-leaf temperatureGraphFunctionChannelIndex
pressureGraphFunctionLeaf = slot-leaf pressureGraphFunctionChannelIndex
class19TpParametricLeaf = slot-leaf class19TpParametricChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierTpParametricStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isTpParametricIdentity : ClassifierTpParametricStep → Bool
isTpParametricIdentity tp-parametric-identity = true
isTpParametricIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at tp-parametric-identity
------------------------------------------------------------------------

tp-parametric-left-identity :
  ∀ (a : ClassifierTpParametricStep) →
  isTpParametricIdentity tpParametricIdentity ≡ true
  × isProductConcurrent (productConcurrentOp tpParametricIdentity a) ≡ true
tp-parametric-left-identity a = refl , refl

tp-parametric-right-identity :
  ∀ (a : ClassifierTpParametricStep) →
  isProductConcurrent (productConcurrentOp a tpParametricIdentity) ≡ true
  × isTpParametricIdentity tpParametricIdentity ≡ true
tp-parametric-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-tp-parametric :
  (∀ a → isProductConcurrent (productConcurrentOp tpParametricIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a tpParametricIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-tp-parametric =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named tp_parametric nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedTpParametricNuanceProduct : ClassifierTpParametricStep
namedTpParametricNuanceProduct =
  productConcurrentOp
    (productConcurrentOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf)
    class19TpParametricLeaf

named-tp-parametric-nuance-product-concurrent :
  isProductConcurrent namedTpParametricNuanceProduct ≡ true
  × tpParametricBundleIsConcurrentProduct tpParametricNuanceWitness ≡ true
named-tp-parametric-nuance-product-concurrent = refl , tp-parametric-nuance-concurrent-product

------------------------------------------------------------------------
-- TpParametricBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data TpParametricAdmissibility : Set where
  tp-parametric-admissible tp-parametric-xor-refuse : TpParametricAdmissibility

isTpParametricPreserving : ClassifierTpParametricStep → Bool
isTpParametricPreserving tp-parametric-identity = true
isTpParametricPreserving (slot-leaf _) = true
isTpParametricPreserving (product-concurrent a b) =
  isTpParametricPreserving a ∧ isTpParametricPreserving b
isTpParametricPreserving (xor-mutually-exclusive _ _) = false

isTpParametricAdmissible : ClassifierTpParametricStep → Bool
isTpParametricAdmissible step = isTpParametricPreserving step

temperature-graph-function-leaf-admissible : isTpParametricAdmissible temperatureGraphFunctionLeaf ≡ true
temperature-graph-function-leaf-admissible = refl

pressure-graph-function-leaf-admissible : isTpParametricAdmissible pressureGraphFunctionLeaf ≡ true
pressure-graph-function-leaf-admissible = refl

class19-tp-parametric-leaf-admissible : isTpParametricAdmissible class19TpParametricLeaf ≡ true
class19-tp-parametric-leaf-admissible = refl

named-tp-parametric-nuance-admissible : isTpParametricAdmissible namedTpParametricNuanceProduct ≡ true
named-tp-parametric-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isTpParametricAdmissible (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class19-tp-parametric-refuse :
  isTpParametricAdmissible (xorMutuallyExclusiveOp pressureGraphFunctionLeaf class19TpParametricLeaf) ≡ false
xor-mutually-exclusive-class19-tp-parametric-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data TpParametricWitnessPresence : Set where
  tp-parametric-witness-absent tp-parametric-witness-present : TpParametricWitnessPresence

record ClassifierTpParametricWitness : Set where
  constructor mkClassifierTpParametricWitness
  field
    witness-presence : TpParametricWitnessPresence
    tp-parametric-gap-total : ℕ

tpParametricWitnessAbsent : ClassifierTpParametricWitness
tpParametricWitnessAbsent = mkClassifierTpParametricWitness tp-parametric-witness-absent zero

tpParametricWitnessPresentZeroGap : ClassifierTpParametricWitness
tpParametricWitnessPresentZeroGap = mkClassifierTpParametricWitness tp-parametric-witness-present zero

tpParametricWitnessPresentWithGaps : ℕ → ClassifierTpParametricWitness
tpParametricWitnessPresentWithGaps n = mkClassifierTpParametricWitness tp-parametric-witness-present n

tpParametricWitnessGapFree : ClassifierTpParametricWitness → Bool
tpParametricWitnessGapFree (mkClassifierTpParametricWitness tp-parametric-witness-absent _) = false
tpParametricWitnessGapFree (mkClassifierTpParametricWitness tp-parametric-witness-present n) =
  does (n ℕ-Props.≟ zero)

tp-parametric-witness-present-zero-gap-free :
  tpParametricWitnessGapFree tpParametricWitnessPresentZeroGap ≡ true
tp-parametric-witness-present-zero-gap-free = refl

tp-parametric-witness-absent-not-gap-free :
  tpParametricWitnessGapFree tpParametricWitnessAbsent ≡ false
tp-parametric-witness-absent-not-gap-free = refl

tp-parametric-witness-with-gaps-not-gap-free :
  ∀ n → tpParametricWitnessGapFree (tpParametricWitnessPresentWithGaps (suc n)) ≡ false
tp-parametric-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-tp_parametric **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data TpParametricConservationVerdict : Set where
  verdict-unwired-ok verdict-tp-parametric-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : TpParametricConservationVerdict

tpParametricConservationVerdictOk : TpParametricConservationVerdict → Bool
tpParametricConservationVerdictOk verdict-unwired-ok = true
tpParametricConservationVerdictOk verdict-tp-parametric-admissible-ok = true
tpParametricConservationVerdictOk verdict-concurrent-product-ok = true
tpParametricConservationVerdictOk _ = false

evaluateTpParametricConservationClose :
  TpParametricConservationModality → ClassifierTpParametricStep → ClassifierTpParametricWitness
  → TpParametricBundleWitness → Bool → TpParametricConservationVerdict
evaluateTpParametricConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateTpParametricConservationClose tp-parametric-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateTpParametricConservationClose tp-parametric-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateTpParametricConservationClose tp-parametric-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateTpParametricConservationClose tp-parametric-conservation-proved _ (mkClassifierTpParametricWitness tp-parametric-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateTpParametricConservationClose tp-parametric-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluateTpParametricConservationClose tp-parametric-conservation-proved _ (mkClassifierTpParametricWitness tp-parametric-witness-present _) w false
  with tpParametricBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-tp-parametric-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without tp_parametric witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateTpParametricConservationClose
    tp-parametric-conservation-unwired namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateTpParametricConservationClose
    tp-parametric-conservation-assumed namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateTpParametricConservationClose
    tp-parametric-conservation-surrogate namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  tpParametricConservationVerdictOk
    (evaluateTpParametricConservationClose tp-parametric-conservation-unwired namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false)
    ≡ true
  × tpParametricConservationVerdictOk
      (evaluateTpParametricConservationClose tp-parametric-conservation-assumed namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false)
      ≡ true
  × tpParametricConservationVerdictOk
      (evaluateTpParametricConservationClose tp-parametric-conservation-surrogate namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without tp_parametric witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateTpParametricConservationClose
    tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  tpParametricConservationVerdictOk
    (evaluateTpParametricConservationClose
       tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateTpParametricConservationClose
    tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false ≡
  verdict-tp-parametric-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluateTpParametricConservationClose
    tp-parametric-conservation-proved
    (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf)
    tpParametricWitnessPresentZeroGap tpParametricNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  tpParametricConservationVerdictOk
    (evaluateTpParametricConservationClose
       tp-parametric-conservation-proved
       (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf)
       tpParametricWitnessPresentZeroGap tpParametricNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluateTpParametricConservationClose
    tp-parametric-conservation-proved
    (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf)
    tpParametricWitnessPresentZeroGap tpParametricNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-tp_parametric — nuance **product** closed
------------------------------------------------------------------------

tp-parametric-admissible-ok :
  evaluateTpParametricConservationClose
    tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap unwiredWitness false ≡
  verdict-tp-parametric-admissible-ok
tp-parametric-admissible-ok = refl

tp-parametric-admissible-verdict-ok :
  tpParametricConservationVerdictOk
    (evaluateTpParametricConservationClose
       tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap unwiredWitness false)
    ≡ true
tp-parametric-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — tp_parametric nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluateTpParametricConservationClose
    tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap tpParametricNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  tpParametricConservationVerdictOk
    (evaluateTpParametricConservationClose
       tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap tpParametricNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-tpParametric19-proved :
  tpParametricConservationVerdictOk
    (evaluateTpParametricConservationClose
       tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap tpParametricNuanceWitness false)
    ≡ true
  × tpParametric19Proved ≡ false
concurrent-product-ok-still-not-tpParametric19-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateTpParametricConservationClose
    tp-parametric-conservation-unwired namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap tpParametricNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  tpParametricConservationVerdictOk
    (evaluateTpParametricConservationClose
       tp-parametric-conservation-unwired namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap tpParametricNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

tpParametricConservationFiberOk : FormalFiber → Bool
tpParametricConservationFiberOk fiber-quantum-knowing = true
tpParametricConservationFiberOk fiber-meso-acting = false

tp-parametric-conservation-knowing-fiber-ok :
  tpParametricConservationFiberOk fiber-quantum-knowing ≡ true
tp-parametric-conservation-knowing-fiber-ok = refl

tp-parametric-conservation-meso-acting-not-ok :
  tpParametricConservationFiberOk fiber-meso-acting ≡ false
tp-parametric-conservation-meso-acting-not-ok = refl

tp-parametric-conservation-routes-knowing-not-meso :
  tpParametricConservationFiberOk fiber-quantum-knowing ≡ true ×
  tpParametricConservationFiberOk fiber-meso-acting ≡ false
tp-parametric-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  tpParametricConservationFiberOk fiber-quantum-knowing ∧
  not (tpParametricConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- T/P float-pin refuse — graph functions v14 ≠ bare 298 K / 1 atm float pins
------------------------------------------------------------------------

tpParametricConservationFraming : String
tpParametricConservationFraming =
  "pattern class 19 tp_parametric conservation T P graph functions concurrent Pi_c product not XOR"

tpFloatPinFraming : String
tpFloatPinFraming =
  "bare_298_15_k_1_atm_float_pins_on_tp_parametric_scaffold"

tp-float-pin-refuse-framing : tpParametricConservationFraming ≢ tpFloatPinFraming
tp-float-pin-refuse-framing ()

------------------------------------------------------------------------
-- Honest pins — not class 19 tp_parametric Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

tp-parametric-19-not-proved : tpParametric19Proved ≡ false
tp-parametric-19-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

tp-parametric-second-law-conservation-framed : tpParametricSecondLawConservationFramed ≡ true
tp-parametric-second-law-conservation-framed = refl

tp-parametric-not-xor-pin : tpParametricNotXor ≡ true
tp-parametric-not-xor-pin = tp-parametric-not-xor

temperature-is-graph-function-pin : temperatureIsGraphFunction ≡ true
temperature-is-graph-function-pin = refl

not-parallel-tp-parametric-axiom-minted-pin : notParallelTpParametricAxiomMinted ≡ true
not-parallel-tp-parametric-axiom-minted-pin = refl

tp-float-pin-not-physics-pin : tpFloatPinNotPhysics ≡ true
tp-float-pin-not-physics-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel tp_parametric axiom fork)
------------------------------------------------------------------------

tpParametricConservationAxiom :
  (tpParametric19Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (tpParametricSecondLawConservationFramed ≡ true)
  × (tpParametricNotXor ≡ true)
  × (evaluateTpParametricConservationClose tp-parametric-conservation-unwired namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluateTpParametricConservationClose tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessAbsent tpParametricNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluateTpParametricConservationClose tp-parametric-conservation-proved (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf) tpParametricWitnessPresentZeroGap tpParametricNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluateTpParametricConservationClose tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap unwiredWitness false ≡ verdict-tp-parametric-admissible-ok)
  × (evaluateTpParametricConservationClose tp-parametric-conservation-proved namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap tpParametricNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (tpParametricConservationFiberOk fiber-quantum-knowing ≡ true)
  × (tpParametricConservationFiberOk fiber-meso-acting ≡ false)
  × (tpParametricConservationVerdictOk (evaluateTpParametricConservationClose tp-parametric-conservation-unwired namedTpParametricNuanceProduct tpParametricWitnessPresentZeroGap tpParametricNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp tpParametricIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a tpParametricIdentity) ≡ true)
  × (isTpParametricAdmissible (xorMutuallyExclusiveOp temperatureGraphFunctionLeaf pressureGraphFunctionLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (tpParametricClassIndex ≡ 19)
  × (TpParametricBundleWitness.present-count tpParametricNuanceWitness ≡ 3)
  × (elementAtomicZ carbon ≡ 6)
  × (elementAtomicZ oganesson ≡ 118)
  × (tpParametricConservationFraming ≢ tpFloatPinFraming)
tpParametricConservationAxiom =
  tp-parametric-19-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , tp-parametric-second-law-conservation-framed
  , tp-parametric-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , tp-parametric-admissible-ok
  , concurrent-product-ok
  , tp-parametric-conservation-knowing-fiber-ok
  , tp-parametric-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , tp-parametric-class-index-nineteen
  , tp-parametric-nuance-present-count
  , carbon-z-6
  , oganesson-z-118
  , tp-float-pin-refuse-framing

tpParametricConservationNamed : String
tpParametricConservationNamed =
  "tpParametricConservation: pattern class 19 tp_parametric conservation concurrent Pi_c identity conserved T graph function P graph function class 19 tp_parametric concurrent product identity conserved present ge 2 product not XOR temperature is graph function pressure is graph function no parallel tp_parametric axiom T P not 298 K 1 atm float pins"

tpParametricConservationCrossWitnessAuthority : String
tpParametricConservationCrossWitnessAuthority =
  "umst/umst-chem/src/tp_parametric_morphism.rs"

tpParametricTableAuthority : String
tpParametricTableAuthority =
  "umst/umst-chem/src/l0_tables/tp_parametric.rs"

temperatureGraphFunctionAuthority : String
temperatureGraphFunctionAuthority =
  "umst/umst-chem/src/temperature_is_graph_function.rs"

pressureGraphFunctionAuthority : String
pressureGraphFunctionAuthority =
  "umst/umst-chem/src/pressure_is_graph_function.rs"

temperature-graph-function-authority-pin :
  temperatureGraphFunctionAuthority ≡
  "umst/umst-chem/src/temperature_is_graph_function.rs"
temperature-graph-function-authority-pin = refl

pressure-graph-function-authority-pin :
  pressureGraphFunctionAuthority ≡
  "umst/umst-chem/src/pressure_is_graph_function.rs"
pressure-graph-function-authority-pin = refl

tpParametricConservationCellId : String
tpParametricConservationCellId = "CHEM-FORMAL-Q-AGDA-TP-PARAMETRIC-CONSERVATION"

tpParametricConservationNonClaim : String
tpParametricConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-TP-PARAMETRIC-CONSERVATION pattern class 19 tp_parametric conservation concurrent Pi_c identity conserved T graph function P graph function class 19 tp_parametric product not XOR temperature is graph function pressure is graph function no parallel tp_parametric axiom T P not 298 K 1 atm float pins XOR mutually exclusive refuse tp_parametric nuance witness concurrent tpParametric19Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite tp_parametric_morphism.rs l0_tables tp_parametric temperature_is_graph_function pressure_is_graph_function not fork not physics GREEN not production_wired"

tp-parametric-conservation-cell-id :
  tpParametricConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-TP-PARAMETRIC-CONSERVATION"
tp-parametric-conservation-cell-id = refl

tp-parametric-conservation-cites-tp-parametric-morphism-rs :
  tpParametricConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/tp_parametric_morphism.rs"
tp-parametric-conservation-cites-tp-parametric-morphism-rs = refl

tp-parametric-conservation-cites-l0-table-rs :
  tpParametricTableAuthority ≡
  "umst/umst-chem/src/l0_tables/tp_parametric.rs"
tp-parametric-conservation-cites-l0-table-rs = refl

tp-parametric-conservation-modality-unwired :
  tpParametricConservationModalityCurrent ≡ tp-parametric-conservation-unwired
tp-parametric-conservation-modality-unwired = refl

tpParametricConservationPhysicsGreenAuthorized : Set
tpParametricConservationPhysicsGreenAuthorized = ⊥

tp-parametric-conservation-physics-green-false : ¬ tpParametricConservationPhysicsGreenAuthorized
tp-parametric-conservation-physics-green-false ()

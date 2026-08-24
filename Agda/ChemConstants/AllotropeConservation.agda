-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.AllotropeConservation.agda
--
-- ALLOTROPE-01 **same-Z allotrope** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Three named allotrope forms diamond/graphite/ozone — concurrent Structure⊗Phase⊗Form not XOR
--   * Class structure⊗phase⊗form product factor; atomic Z identity conserved across allotropes
--   * Composed Structure→Phase→Form identity equals Structure→Form direct (typed **conservation**)
--   * Carbon (Z=6) same Z many allotropes; O (Z=8); Sn (Z=50); He (Z=2) closed-shell no-allotrope
--   * folklore / GREEN / trivial / proved-without-bar refuse; total-claim refuse without witness
--   * **allotrope** laws Unwired (allotropeProved = false)
--
-- Mirrors sibling `ChemConstants/GoldschmidtConservation.agda` +
-- `ChemConstants/DensityConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------
module ChemConstants.AllotropeConservation where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + ALLOTROPE-01 Structure⊗Phase⊗Form **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data AllotropeConservationModality : Set where
  allotrope-conservation-unwired allotrope-conservation-assumed
    allotrope-conservation-proved allotrope-conservation-surrogate
    : AllotropeConservationModality

allotropeConservationModalityCurrent : AllotropeConservationModality
allotropeConservationModalityCurrent = allotrope-conservation-unwired

allotropeProved productionWired not118SquaredGreenTable
  allotropeSecondLawConservationFramed allotropeTypedConservation
  allotropeNotXor structurePhaseFormProduct : Bool
allotropeProved = false
productionWired = false
not118SquaredGreenTable = true
allotropeSecondLawConservationFramed = true
allotropeTypedConservation = true
allotropeNotXor = true
structurePhaseFormProduct = true

------------------------------------------------------------------------
-- Class structure⊗phase⊗form pattern indices (structure — not 118²)
------------------------------------------------------------------------

structureClassIndex phaseClassIndex formClassIndex : ℕ
structureClassIndex = 3
phaseClassIndex = 4
formClassIndex = 5

structure-phase-form-product :
  structureClassIndex * phaseClassIndex * formClassIndex ≡ 60
structure-phase-form-product = refl

allotrope-ladder-not-118-squared :
  does (structureClassIndex ℕ-Props.≟ 118) ≡ false
allotrope-ladder-not-118-squared = refl

------------------------------------------------------------------------
-- Named affinity tags — concurrent Structure⊗Phase⊗Form product, not XOR enum
------------------------------------------------------------------------

data AllotropeFormTag : Set where
  diamond graphite ozone : AllotropeFormTag

isDiamond isGraphite isOzone : AllotropeFormTag → Bool
isDiamond diamond = true
isDiamond _ = false

isGraphite graphite = true
isGraphite _ = false

isOzone ozone = true
isOzone _ = false

diamond-named :
  isDiamond diamond ≡ true × isGraphite diamond ≡ false
diamond-named = refl , refl

graphite-named :
  isGraphite graphite ≡ true × isOzone graphite ≡ false
graphite-named = refl , refl

ozone-named :
  isOzone ozone ≡ true × isDiamond ozone ≡ false
ozone-named = refl , refl

diamond-distinct-from-graphite : diamond ≢ graphite
diamond-distinct-from-graphite ()

allotrope-not-xor : allotropeNotXor ≡ true
allotrope-not-xor = refl

------------------------------------------------------------------------
-- Structure⊗Phase⊗Form product factor legs (class 6 ⊗ 7 ⊗ 17)
------------------------------------------------------------------------

data AllotropeLevel : Set where
  allotrope-structure allotrope-phase allotrope-form : AllotropeLevel

data AllotropeProductLeg : Set where
  structure-to-phase phase-to-form structure-to-form-direct : AllotropeProductLeg

allotropeLegSource : AllotropeProductLeg → AllotropeLevel
allotropeLegSource structure-to-phase = allotrope-structure
allotropeLegSource phase-to-form = allotrope-phase
allotropeLegSource structure-to-form-direct = allotrope-structure

allotropeLegTarget : AllotropeProductLeg → AllotropeLevel
allotropeLegTarget structure-to-phase = allotrope-phase
allotropeLegTarget phase-to-form = allotrope-form
allotropeLegTarget structure-to-form-direct = allotrope-form

allotropeLegStructureToPhase allotropeLegPhaseToForm allotropeLegStructureToFormDirect : AllotropeProductLeg
allotropeLegStructureToPhase = structure-to-phase
allotropeLegPhaseToForm = phase-to-form
allotropeLegStructureToFormDirect = structure-to-form-direct

allotrope-leg-first-composes-levels :
  allotropeLegTarget allotropeLegStructureToPhase ≡ allotropeLegSource allotropeLegPhaseToForm
allotrope-leg-first-composes-levels = refl

allotrope-leg-direct-endpoints-match :
  allotropeLegSource allotropeLegStructureToPhase ≡ allotropeLegSource allotropeLegStructureToFormDirect ×
  allotropeLegTarget allotropeLegPhaseToForm ≡ allotropeLegTarget allotropeLegStructureToFormDirect
allotrope-leg-direct-endpoints-match = refl , refl

allotrope-leg-distinct-indirect-vs-direct :
  allotropeLegStructureToPhase ≢ allotropeLegStructureToFormDirect
allotrope-leg-distinct-indirect-vs-direct ()

------------------------------------------------------------------------
-- Named element Z pins — C (Z=6) same Z many allotropes; O (Z=8); Sn (Z=50); He (Z=2) no-allotrope
------------------------------------------------------------------------

data ElementTag : Set where
  carbon oxygen tin helium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ carbon = 6
elementAtomicZ oxygen = 8
elementAtomicZ tin = 50
elementAtomicZ helium = 2

carbon-z-6 : elementAtomicZ carbon ≡ 6
carbon-z-6 = refl

oxygen-z-8 : elementAtomicZ oxygen ≡ 8
oxygen-z-8 = refl

tin-z-50 : elementAtomicZ tin ≡ 50
tin-z-50 = refl

helium-z-2 : elementAtomicZ helium ≡ 2
helium-z-2 = refl

data CarbonAllotropeTag : Set where
  carbon-diamond carbon-graphite carbon-fullerene : CarbonAllotropeTag

carbonAllotropeAtomicZ : CarbonAllotropeTag → ℕ
carbonAllotropeAtomicZ carbon-diamond = 6
carbonAllotropeAtomicZ carbon-graphite = 6
carbonAllotropeAtomicZ carbon-fullerene = 6

carbon-diamond-z-6 : carbonAllotropeAtomicZ carbon-diamond ≡ 6
carbon-diamond-z-6 = refl

carbon-graphite-z-6 : carbonAllotropeAtomicZ carbon-graphite ≡ 6
carbon-graphite-z-6 = refl

carbon-fullerene-z-6 : carbonAllotropeAtomicZ carbon-fullerene ≡ 6
carbon-fullerene-z-6 = refl

carbon-same-z-many-allotropes :
  carbonAllotropeAtomicZ carbon-diamond ≡ carbonAllotropeAtomicZ carbon-graphite ×
  carbonAllotropeAtomicZ carbon-graphite ≡ carbonAllotropeAtomicZ carbon-fullerene ×
  carbonAllotropeAtomicZ carbon-diamond ≡ elementAtomicZ carbon
carbon-same-z-many-allotropes = refl , refl , refl

isClosedShellNoAllotrope : ElementTag → Bool
isClosedShellNoAllotrope helium = true
isClosedShellNoAllotrope _ = false

isAllotropeElement : ElementTag → Bool
isAllotropeElement carbon = true
isAllotropeElement oxygen = true
isAllotropeElement tin = true
isAllotropeElement helium = false

helium-closed-shell-no-allotrope :
  isClosedShellNoAllotrope helium ≡ true × isAllotropeElement helium ≡ false
helium-closed-shell-no-allotrope = refl , refl

oxygen-is-allotrope-element : isAllotropeElement oxygen ≡ true
oxygen-is-allotrope-element = refl

tin-is-allotrope-element : isAllotropeElement tin ≡ true
tin-is-allotrope-element = refl

------------------------------------------------------------------------
-- Typed Structure⊗Phase⊗Form **conservation** — composed indirect equals direct endpoints
------------------------------------------------------------------------

record AllotropeProductWitness : Set where
  constructor mkAllotropeProductWitness
  field
    indirect-source : AllotropeLevel
    indirect-via      : AllotropeLevel
    indirect-target   : AllotropeLevel
    direct-source     : AllotropeLevel
    direct-target     : AllotropeLevel
    form-tag      : AllotropeFormTag

allotropeProductWitnessNamed : AllotropeProductWitness
allotropeProductWitnessNamed = record
  { indirect-source = allotrope-structure
  ; indirect-via    = allotrope-phase
  ; indirect-target = allotrope-form
  ; direct-source   = allotrope-structure
  ; direct-target   = allotrope-form
  ; form-tag    = ozone
  }

composed-indirect-identity-equals-direct-typed :
  AllotropeProductWitness.indirect-source allotropeProductWitnessNamed ≡
  AllotropeProductWitness.direct-source allotropeProductWitnessNamed ×
  AllotropeProductWitness.indirect-target allotropeProductWitnessNamed ≡
  AllotropeProductWitness.direct-target allotropeProductWitnessNamed ×
  allotropeLegTarget allotropeLegStructureToPhase ≡ allotropeLegSource allotropeLegPhaseToForm ×
  allotropeLegSource allotropeLegStructureToPhase ≡ allotropeLegSource allotropeLegStructureToFormDirect ×
  allotropeLegTarget allotropeLegPhaseToForm ≡ allotropeLegTarget allotropeLegStructureToFormDirect ×
  isOzone (AllotropeProductWitness.form-tag allotropeProductWitnessNamed) ≡ true
composed-indirect-identity-equals-direct-typed = refl , refl , refl , refl , refl , refl

allotrope-typed-conservation-pin : allotropeTypedConservation ≡ true
allotrope-typed-conservation-pin = refl

structure-phase-form-product-pin : structurePhaseFormProduct ≡ true
structure-phase-form-product-pin = refl

------------------------------------------------------------------------
-- ClassifierAllotropeStep scaffold — Structure⊗Phase⊗Form **conservation**
------------------------------------------------------------------------

data ClassifierAllotropeStep : Set where
  allotrope-identity : ClassifierAllotropeStep
  allotrope-leg-leaf : AllotropeProductLeg → ClassifierAllotropeStep
  leg-compose : ClassifierAllotropeStep → ClassifierAllotropeStep → ClassifierAllotropeStep
  allotrope-leg-mismatch : ClassifierAllotropeStep → ClassifierAllotropeStep → ClassifierAllotropeStep
  folklore-list-invent : ClassifierAllotropeStep
  xor-enum-smuggle : ClassifierAllotropeStep
  trivial-no-allotrope-step : ElementTag → ClassifierAllotropeStep

allotropeIdentity : ClassifierAllotropeStep
allotropeIdentity = allotrope-identity

legComposeOp allotropeMismatchOp :
  ClassifierAllotropeStep → ClassifierAllotropeStep → ClassifierAllotropeStep
legComposeOp = leg-compose
allotropeMismatchOp = allotrope-leg-mismatch

structureToPhaseLeaf phaseToFormLeaf structureToFormDirectLeaf : ClassifierAllotropeStep
structureToPhaseLeaf = allotrope-leg-leaf structure-to-phase
phaseToFormLeaf = allotrope-leg-leaf phase-to-form
structureToFormDirectLeaf = allotrope-leg-leaf structure-to-form-direct

folkloreListInventStep xorEnumSmuggleStep : ClassifierAllotropeStep
folkloreListInventStep = folklore-list-invent
xorEnumSmuggleStep = xor-enum-smuggle

trivialNoAllotropeStep : ClassifierAllotropeStep
trivialNoAllotropeStep = trivial-no-allotrope-step helium

isLegCompose isAllotropeLeg isAllotropeIdentity : ClassifierAllotropeStep → Bool
isLegCompose (leg-compose _ _) = true
isLegCompose _ = false

isAllotropeLeg (allotrope-leg-leaf _) = true
isAllotropeLeg _ = false

isAllotropeIdentity allotrope-identity = true
isAllotropeIdentity _ = false

isFolkloreListInvent : ClassifierAllotropeStep → Bool
isFolkloreListInvent folklore-list-invent = true
isFolkloreListInvent _ = false

isXorEnumSmuggle : ClassifierAllotropeStep → Bool
isXorEnumSmuggle xor-enum-smuggle = true
isXorEnumSmuggle _ = false

isTrivialNoAllotropeStep : ClassifierAllotropeStep → Bool
isTrivialNoAllotropeStep (trivial-no-allotrope-step e) = isClosedShellNoAllotrope e ∧ not (isAllotropeElement e)
isTrivialNoAllotropeStep _ = false

------------------------------------------------------------------------
-- **Allotrope** identity conserved at allotrope-identity — leg-compose scaffold
------------------------------------------------------------------------

allotrope-left-identity :
  ∀ (a : ClassifierAllotropeStep) →
  isAllotropeIdentity allotropeIdentity ≡ true × isLegCompose (legComposeOp allotropeIdentity a) ≡ true
allotrope-left-identity a = refl , refl

allotrope-right-identity :
  ∀ (a : ClassifierAllotropeStep) →
  isLegCompose (legComposeOp a allotropeIdentity) ≡ true × isAllotropeIdentity allotropeIdentity ≡ true
allotrope-right-identity a = refl , refl

------------------------------------------------------------------------
-- Named three-leg Structure⊗Phase⊗Form closed — indirect composed vs direct product
------------------------------------------------------------------------

namedAllotropeIndirectPath : ClassifierAllotropeStep
namedAllotropeIndirectPath = legComposeOp structureToPhaseLeaf phaseToFormLeaf

namedAllotropeDirectPath : ClassifierAllotropeStep
namedAllotropeDirectPath = structureToFormDirectLeaf

named-allotrope-indirect-is-compose :
  isLegCompose namedAllotropeIndirectPath ≡ true
named-allotrope-indirect-is-compose = refl

named-allotrope-direct-is-leg :
  isAllotropeLeg namedAllotropeDirectPath ≡ true
named-allotrope-direct-is-leg = refl

named-allotrope-ladder-closed :
  isLegCompose namedAllotropeIndirectPath ≡ true
  × isAllotropeLeg namedAllotropeDirectPath ≡ true
  × allotropeLegTarget allotropeLegStructureToPhase ≡ allotropeLegSource allotropeLegPhaseToForm
  × allotropeLegSource allotropeLegStructureToPhase ≡ allotropeLegSource allotropeLegStructureToFormDirect
  × allotropeLegTarget allotropeLegPhaseToForm ≡ allotropeLegTarget allotropeLegStructureToFormDirect
named-allotrope-ladder-closed = refl , refl , refl , refl , refl

allotropeLegMismatchPath : ClassifierAllotropeStep
allotropeLegMismatchPath = allotropeMismatchOp phaseToFormLeaf structureToPhaseLeaf

isAllotropeMismatch : ClassifierAllotropeStep → Bool
isAllotropeMismatch (allotrope-leg-mismatch _ _) = true
isAllotropeMismatch _ = false

allotrope-mismatch-not-compose :
  isLegCompose allotropeLegMismatchPath ≡ false
allotrope-mismatch-not-compose = refl

------------------------------------------------------------------------
-- **Allotrope** admissibility — mismatch / folklore / XOR / He no-allotrope refuse
------------------------------------------------------------------------

isAllotropePreserving : ClassifierAllotropeStep → Bool
isAllotropePreserving allotrope-identity = true
isAllotropePreserving (allotrope-leg-leaf _) = true
isAllotropePreserving (leg-compose a b) =
  isAllotropePreserving a ∧ isAllotropePreserving b
isAllotropePreserving (allotrope-leg-mismatch _ _) = false
isAllotropePreserving folklore-list-invent = false
isAllotropePreserving xor-enum-smuggle = false
isAllotropePreserving (trivial-no-allotrope-step e) =
  not (isClosedShellNoAllotrope e ∧ not (isAllotropeElement e))

isAllotropeAdmissible : ClassifierAllotropeStep → Bool
isAllotropeAdmissible step = isAllotropePreserving step

named-allotrope-indirect-admissible : isAllotropeAdmissible namedAllotropeIndirectPath ≡ true
named-allotrope-indirect-admissible = refl

allotrope-leg-mismatch-not-admissible :
  isAllotropeAdmissible allotropeLegMismatchPath ≡ false
allotrope-leg-mismatch-not-admissible = refl

folklore-list-not-admissible :
  isAllotropeAdmissible folkloreListInventStep ≡ false
folklore-list-not-admissible = refl

xor-enum-not-admissible :
  isAllotropeAdmissible xorEnumSmuggleStep ≡ false
xor-enum-not-admissible = refl

trivial-no-allotrope-not-admissible :
  isAllotropeAdmissible trivialNoAllotropeStep ≡ false
trivial-no-allotrope-not-admissible = refl

------------------------------------------------------------------------
-- **Allotrope** witness — total-claim refuse; proved-without-bar (phase) refuse
------------------------------------------------------------------------

data AllotropeWitnessPresence : Set where
  allotrope-witness-absent allotrope-witness-present : AllotropeWitnessPresence

data PhaseWitnessPresence : Set where
  phase-witness-absent phase-witness-present : PhaseWitnessPresence

record ClassifierAllotropeWitness : Set where
  constructor mkClassifierAllotropeWitness
  field
    witness-presence : AllotropeWitnessPresence
    phase-presence  : PhaseWitnessPresence
    allotrope-gap-total : ℕ

allotropeWitnessAbsent : ClassifierAllotropeWitness
allotropeWitnessAbsent = mkClassifierAllotropeWitness allotrope-witness-absent phase-witness-absent zero

allotropeWitnessPresentZeroGapWithPhase : ClassifierAllotropeWitness
allotropeWitnessPresentZeroGapWithPhase =
  mkClassifierAllotropeWitness allotrope-witness-present phase-witness-present zero

allotropeWitnessPresentWithoutPhase : ClassifierAllotropeWitness
allotropeWitnessPresentWithoutPhase =
  mkClassifierAllotropeWitness allotrope-witness-present phase-witness-absent zero

allotropeWitnessGapFree : ClassifierAllotropeWitness → Bool
allotropeWitnessGapFree (mkClassifierAllotropeWitness allotrope-witness-absent _ _) = false
allotropeWitnessGapFree (mkClassifierAllotropeWitness allotrope-witness-present _ n) =
  does (n ℕ-Props.≟ zero)

allotrope-witness-present-zero-gap-free :
  allotropeWitnessGapFree allotropeWitnessPresentZeroGapWithPhase ≡ true
allotrope-witness-present-zero-gap-free = refl

------------------------------------------------------------------------
-- Classifier-ALLOTROPE-01 close verdict — fail-closed lattice
------------------------------------------------------------------------

data AllotropeConservationVerdict : Set where
  verdict-unwired-ok verdict-allotrope-product-admissible-ok
    verdict-allotrope-leg-mismatch-refuse verdict-total-claim-refuse
    verdict-proved-without-phase-refuse verdict-folklore-list-invent-refuse
    verdict-xor-enum-smuggle-refuse verdict-trivial-no-allotrope-refuse
    verdict-green-invent-refuse
    : AllotropeConservationVerdict

allotropeConservationVerdictOk : AllotropeConservationVerdict → Bool
allotropeConservationVerdictOk verdict-unwired-ok = true
allotropeConservationVerdictOk verdict-allotrope-product-admissible-ok = true
allotropeConservationVerdictOk _ = false

evaluateAllotropeConservationClose :
  AllotropeConservationModality → ClassifierAllotropeStep → ClassifierAllotropeWitness → Bool
  → AllotropeConservationVerdict
evaluateAllotropeConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateAllotropeConservationClose allotrope-conservation-unwired _ _ false = verdict-unwired-ok
evaluateAllotropeConservationClose allotrope-conservation-assumed _ _ false = verdict-unwired-ok
evaluateAllotropeConservationClose allotrope-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateAllotropeConservationClose allotrope-conservation-proved folklore-list-invent _ false =
  verdict-folklore-list-invent-refuse
evaluateAllotropeConservationClose allotrope-conservation-proved xor-enum-smuggle _ false =
  verdict-xor-enum-smuggle-refuse
evaluateAllotropeConservationClose allotrope-conservation-proved (trivial-no-allotrope-step _) _ false =
  verdict-trivial-no-allotrope-refuse
evaluateAllotropeConservationClose allotrope-conservation-proved _ (mkClassifierAllotropeWitness allotrope-witness-absent _ _) false =
  verdict-total-claim-refuse
evaluateAllotropeConservationClose allotrope-conservation-proved _ (mkClassifierAllotropeWitness allotrope-witness-present phase-witness-absent _) false =
  verdict-proved-without-phase-refuse
evaluateAllotropeConservationClose allotrope-conservation-proved (allotrope-leg-mismatch _ _) _ false =
  verdict-allotrope-leg-mismatch-refuse
evaluateAllotropeConservationClose allotrope-conservation-proved step (mkClassifierAllotropeWitness allotrope-witness-present phase-witness-present _) false
  with isAllotropeAdmissible step
... | false = verdict-allotrope-leg-mismatch-refuse
... | true  = verdict-allotrope-product-admissible-ok

unwired-close-without-witness :
  evaluateAllotropeConservationClose
    allotrope-conservation-unwired namedAllotropeIndirectPath allotropeWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

total-claim-refuse-without-witness :
  evaluateAllotropeConservationClose
    allotrope-conservation-proved namedAllotropeIndirectPath allotropeWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

proved-without-phase-refuse-verdict :
  evaluateAllotropeConservationClose
    allotrope-conservation-proved namedAllotropeIndirectPath allotropeWitnessPresentWithoutPhase false ≡
  verdict-proved-without-phase-refuse
proved-without-phase-refuse-verdict = refl

allotrope-leg-mismatch-refuse-verdict :
  evaluateAllotropeConservationClose
    allotrope-conservation-proved allotropeLegMismatchPath allotropeWitnessPresentZeroGapWithPhase false ≡
  verdict-allotrope-leg-mismatch-refuse
allotrope-leg-mismatch-refuse-verdict = refl

folklore-list-invent-refuse-verdict :
  evaluateAllotropeConservationClose
    allotrope-conservation-proved folkloreListInventStep allotropeWitnessPresentZeroGapWithPhase false ≡
  verdict-folklore-list-invent-refuse
folklore-list-invent-refuse-verdict = refl

xor-enum-smuggle-refuse-verdict :
  evaluateAllotropeConservationClose
    allotrope-conservation-proved xorEnumSmuggleStep allotropeWitnessPresentZeroGapWithPhase false ≡
  verdict-xor-enum-smuggle-refuse
xor-enum-smuggle-refuse-verdict = refl

trivial-no-allotrope-refuse-verdict :
  evaluateAllotropeConservationClose
    allotrope-conservation-proved trivialNoAllotropeStep allotropeWitnessPresentZeroGapWithPhase false ≡
  verdict-trivial-no-allotrope-refuse
trivial-no-allotrope-refuse-verdict = refl

allotrope-product-admissible-ok :
  evaluateAllotropeConservationClose
    allotrope-conservation-proved namedAllotropeIndirectPath allotropeWitnessPresentZeroGapWithPhase false ≡
  verdict-allotrope-product-admissible-ok
allotrope-product-admissible-ok = refl

green-invent-always-refuse :
  allotropeConservationVerdictOk
    (evaluateAllotropeConservationClose
       allotrope-conservation-unwired namedAllotropeIndirectPath allotropeWitnessPresentZeroGapWithPhase true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

allotropeConservationFiberOk : FormalFiber → Bool
allotropeConservationFiberOk fiber-quantum-knowing = true
allotropeConservationFiberOk fiber-meso-acting = false

allotrope-conservation-knowing-fiber-ok :
  allotropeConservationFiberOk fiber-quantum-knowing ≡ true
allotrope-conservation-knowing-fiber-ok = refl

allotrope-conservation-meso-acting-not-ok :
  allotropeConservationFiberOk fiber-meso-acting ≡ false
allotrope-conservation-meso-acting-not-ok = refl

------------------------------------------------------------------------
-- Honest pins — not Allotrope Proved, not physics GREEN
------------------------------------------------------------------------

allotrope-not-proved : allotropeProved ≡ false
allotrope-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

allotrope-second-law-conservation-framed : allotropeSecondLawConservationFramed ≡ true
allotrope-second-law-conservation-framed = refl

allotrope-typed-conservation-framed : allotropeTypedConservation ≡ true
allotrope-typed-conservation-framed = allotrope-typed-conservation-pin

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second ALLOTROPE-01 axiom fork)
------------------------------------------------------------------------

allotropeConservationAxiom :
  (allotropeProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (allotropeSecondLawConservationFramed ≡ true)
  × (allotropeTypedConservation ≡ true)
  × (allotropeNotXor ≡ true)
  × (structurePhaseFormProduct ≡ true)
  × (evaluateAllotropeConservationClose allotrope-conservation-unwired namedAllotropeIndirectPath allotropeWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateAllotropeConservationClose allotrope-conservation-proved namedAllotropeIndirectPath allotropeWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateAllotropeConservationClose allotrope-conservation-proved allotropeLegMismatchPath allotropeWitnessPresentZeroGapWithPhase false ≡ verdict-allotrope-leg-mismatch-refuse)
  × (evaluateAllotropeConservationClose allotrope-conservation-proved namedAllotropeIndirectPath allotropeWitnessPresentZeroGapWithPhase false ≡ verdict-allotrope-product-admissible-ok)
  × (evaluateAllotropeConservationClose allotrope-conservation-proved namedAllotropeIndirectPath allotropeWitnessPresentWithoutPhase false ≡ verdict-proved-without-phase-refuse)
  × (evaluateAllotropeConservationClose allotrope-conservation-proved folkloreListInventStep allotropeWitnessPresentZeroGapWithPhase false ≡ verdict-folklore-list-invent-refuse)
  × (evaluateAllotropeConservationClose allotrope-conservation-proved xorEnumSmuggleStep allotropeWitnessPresentZeroGapWithPhase false ≡ verdict-xor-enum-smuggle-refuse)
  × (evaluateAllotropeConservationClose allotrope-conservation-proved trivialNoAllotropeStep allotropeWitnessPresentZeroGapWithPhase false ≡ verdict-trivial-no-allotrope-refuse)
  × (allotropeConservationFiberOk fiber-quantum-knowing ≡ true)
  × (allotropeConservationFiberOk fiber-meso-acting ≡ false)
  × (allotropeConservationVerdictOk (evaluateAllotropeConservationClose allotrope-conservation-unwired namedAllotropeIndirectPath allotropeWitnessPresentZeroGapWithPhase true) ≡ false)
  × (∀ a → isLegCompose (legComposeOp allotropeIdentity a) ≡ true)
  × (isAllotropeAdmissible allotropeLegMismatchPath ≡ false)
  × (allotropeLegTarget allotropeLegStructureToPhase ≡ allotropeLegSource allotropeLegPhaseToForm)
  × (allotropeLegSource allotropeLegStructureToPhase ≡ allotropeLegSource allotropeLegStructureToFormDirect)
  × (allotropeLegTarget allotropeLegPhaseToForm ≡ allotropeLegTarget allotropeLegStructureToFormDirect)
  × (isDiamond diamond ≡ true)
  × (isGraphite graphite ≡ true)
  × (isOzone ozone ≡ true)
  × (elementAtomicZ carbon ≡ 6)
  × (elementAtomicZ oxygen ≡ 8)
  × (elementAtomicZ tin ≡ 50)
  × (elementAtomicZ helium ≡ 2)
  × (isClosedShellNoAllotrope helium ≡ true × isAllotropeElement helium ≡ false)
  × (carbonAllotropeAtomicZ carbon-diamond ≡ carbonAllotropeAtomicZ carbon-graphite)
allotropeConservationAxiom =
  allotrope-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , allotrope-second-law-conservation-framed
  , allotrope-typed-conservation-framed
  , allotrope-not-xor
  , structure-phase-form-product-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , allotrope-leg-mismatch-refuse-verdict
  , allotrope-product-admissible-ok
  , proved-without-phase-refuse-verdict
  , folklore-list-invent-refuse-verdict
  , xor-enum-smuggle-refuse-verdict
  , trivial-no-allotrope-refuse-verdict
  , allotrope-conservation-knowing-fiber-ok
  , allotrope-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , allotrope-leg-mismatch-not-admissible
  , allotrope-leg-first-composes-levels
  , refl
  , refl
  , (proj₁ diamond-named)
  , (proj₁ graphite-named)
  , (proj₁ ozone-named)
  , carbon-z-6
  , oxygen-z-8
  , tin-z-50
  , helium-z-2
  , helium-closed-shell-no-allotrope
  , (proj₁ carbon-same-z-many-allotropes)

allotropeConservationNamed : String
allotropeConservationNamed =
  "allotropeConservation: ALLOTROPE-01 same-Z allotrope Structure⊗Phase⊗Form class 3⊗4⊗5 diamond graphite ozone concurrent product not XOR composed indirect equals direct typed conservation"

allotropeConservationCellId : String
allotropeConservationCellId = "CHEM-FORMAL-Q-AGDA-ALLOTROPE-CONSERVATION"

allotropeConservationNonClaim : String
allotropeConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-ALLOTROPE-CONSERVATION ALLOTROPE-01 same-Z allotrope Structure⊗Phase⊗Form class 3⊗4⊗5 diamond graphite ozone concurrent product not XOR composed indirect equals direct typed conservation folklore list invent refuse XOR enum smuggle refuse trivial He closed shell no allotrope refuse total-claim refuse proved-without-phase refuse C Z 6 same Z many allotropes O Z 8 Sn Z 50 He Z 2 allotropeProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second ALLOTROPE axiom not physics GREEN not production_wired"

allotrope-conservation-modality-unwired :
  allotropeConservationModalityCurrent ≡ allotrope-conservation-unwired
allotrope-conservation-modality-unwired = refl

allotropeConservationPhysicsGreenAuthorized : Set
allotropeConservationPhysicsGreenAuthorized = ⊥

allotrope-conservation-physics-green-false : ¬ allotropeConservationPhysicsGreenAuthorized
allotrope-conservation-physics-green-false ()

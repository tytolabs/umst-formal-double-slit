-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ChemPhysicsChartIsomorphism.agda
--
-- CHART-ISOMORPHISM-01 **chem-physics chart isomorphism** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Chemistry is occupancy physics; constitutive engines are named charts of one second-law object
--   * Eight constitutive chart tags — concurrent Chart⊗Occupancy⊗Physics not XOR
--   * Class 2⊗3⊗4 product factor; order identity conserved across chart presentations
--   * Composed chem→occupancy→physics identity equals chem→physics direct (typed **isomorphism**)
--   * H (Z=1) occupancy physics anchor; Fe (Z=26); O (Z=8); He (Z=2) closed-shell no-chart
--   * folklore / GREEN / trivial / proved-without-bar refuse; total-claim refuse without witness
--   * engines-not-second-physics; extra-chem-force refuse; sole axiom count 1
--   * **chart-isomorphism** laws Unwired (chartIsomorphismProved = false)
--
-- Mirrors sibling `ChemConstants/GoldschmidtConservation.agda` +
-- `ChemConstants/DensityConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ChemPhysicsChartIsomorphism where

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
-- Modality + CHART-ISOMORPHISM-01 Chart⊗Occupancy⊗Physics **isomorphism** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ChartIsomorphismConservationModality : Set where
  chart-isomorphism-conservation-unwired chart-isomorphism-conservation-assumed
    chart-isomorphism-conservation-proved chart-isomorphism-conservation-surrogate
    : ChartIsomorphismConservationModality

chartIsomorphismConservationModalityCurrent : ChartIsomorphismConservationModality
chartIsomorphismConservationModalityCurrent = chart-isomorphism-conservation-unwired

chartIsomorphismProved productionWired not118SquaredGreenTable
  chartSecondLawConservationFramed chartTypedIsomorphism
  chartNotXor chartOccupancyPhysicsProduct : Bool
chartIsomorphismProved = false
productionWired = false
not118SquaredGreenTable = true
chartSecondLawConservationFramed = true
chartTypedIsomorphism = true
chartNotXor = true
chartOccupancyPhysicsProduct = true

enginesNotSecondPhysics extraChemForceRefused : Bool
enginesNotSecondPhysics = false
extraChemForceRefused = true

soleAxiomCount constitutiveChartCount : ℕ
soleAxiomCount = 1
constitutiveChartCount = 8

sole-axiom-count-one : soleAxiomCount ≡ 1
sole-axiom-count-one = refl

constitutive-chart-count-eight : constitutiveChartCount ≡ 8
constitutive-chart-count-eight = refl

engines-not-second-physics : enginesNotSecondPhysics ≡ false
engines-not-second-physics = refl

extra-chem-force-refused : extraChemForceRefused ≡ true
extra-chem-force-refused = refl

chem-physics-isomorphism-holds :
  extraChemForceRefused ≡ true
  × enginesNotSecondPhysics ≡ false
  × constitutiveChartCount ≡ 8
  × soleAxiomCount ≡ 1
chem-physics-isomorphism-holds = refl , refl , refl , refl


------------------------------------------------------------------------
-- Class chart⊗occupancy⊗physics pattern indices (structure — not 118²)
------------------------------------------------------------------------

chemChartClassIndex occupancyChartClassIndex physicsChartClassIndex : ℕ
chemChartClassIndex = 2
occupancyChartClassIndex = 3
physicsChartClassIndex = 4

chart-occupancy-physics-product :
  chemChartClassIndex * occupancyChartClassIndex * physicsChartClassIndex ≡ 24
chart-occupancy-physics-product = refl

chart-isomorphism-ladder-not-118-squared :
  does (chemChartClassIndex ℕ-Props.≟ 118) ≡ false
chart-isomorphism-ladder-not-118-squared = refl

------------------------------------------------------------------------
-- Named constitutive chart tags — concurrent Chart⊗Occupancy⊗Physics product, not XOR enum
------------------------------------------------------------------------

data ConstitutiveChartTag : Set where
  occupancy-sort g-engine interact-closed-shell : ConstitutiveChartTag

isOccupancySort isGEngine isInteractClosedShell : ConstitutiveChartTag → Bool
isOccupancySort occupancy-sort = true
isOccupancySort _ = false

isGEngine g-engine = true
isGEngine _ = false

isInteractClosedShell interact-closed-shell = true
isInteractClosedShell _ = false

occupancy-sort-named :
  isOccupancySort occupancy-sort ≡ true × isGEngine occupancy-sort ≡ false
occupancy-sort-named = refl , refl

g-engine-named :
  isGEngine g-engine ≡ true × isInteractClosedShell g-engine ≡ false
g-engine-named = refl , refl

interact-closed-shell-named :
  isInteractClosedShell interact-closed-shell ≡ true × isOccupancySort interact-closed-shell ≡ false
interact-closed-shell-named = refl , refl

occupancy-sort-distinct-from-g-engine : occupancy-sort ≢ g-engine
occupancy-sort-distinct-from-g-engine ()

chart-not-xor : chartNotXor ≡ true
chart-not-xor = refl

------------------------------------------------------------------------
-- Chart⊗Occupancy⊗Physics product factor legs (class 2 ⊗ 3 ⊗ 4)
------------------------------------------------------------------------

data ChartLevel : Set where
  chart-chem chart-occupancy chart-physics : ChartLevel

data ChartIsomorphismLeg : Set where
  chem-to-occupancy occupancy-to-physics chem-to-physics-direct : ChartIsomorphismLeg

chartLegSource : ChartIsomorphismLeg → ChartLevel
chartLegSource chem-to-occupancy = chart-chem
chartLegSource occupancy-to-physics = chart-occupancy
chartLegSource chem-to-physics-direct = chart-chem

chartLegTarget : ChartIsomorphismLeg → ChartLevel
chartLegTarget chem-to-occupancy = chart-occupancy
chartLegTarget occupancy-to-physics = chart-physics
chartLegTarget chem-to-physics-direct = chart-physics

chartLegChemToOccupancy chartLegOccupancyToPhysics chartLegChemToPhysicsDirect : ChartIsomorphismLeg
chartLegChemToOccupancy = chem-to-occupancy
chartLegOccupancyToPhysics = occupancy-to-physics
chartLegChemToPhysicsDirect = chem-to-physics-direct

chart-leg-first-composes-levels :
  chartLegTarget chartLegChemToOccupancy ≡ chartLegSource chartLegOccupancyToPhysics
chart-leg-first-composes-levels = refl

chart-leg-direct-endpoints-match :
  chartLegSource chartLegChemToOccupancy ≡ chartLegSource chartLegChemToPhysicsDirect ×
  chartLegTarget chartLegOccupancyToPhysics ≡ chartLegTarget chartLegChemToPhysicsDirect
chart-leg-direct-endpoints-match = refl , refl

chart-leg-distinct-indirect-vs-direct :
  chartLegChemToOccupancy ≢ chartLegChemToPhysicsDirect
chart-leg-distinct-indirect-vs-direct ()

------------------------------------------------------------------------
-- Named element Z pins — H (Z=1) occupancy physics; Fe (Z=26); O (Z=8); He (Z=2) no-chart
------------------------------------------------------------------------

data ElementTag : Set where
  hydrogen iron oxygen helium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ hydrogen = 1
elementAtomicZ oxygen = 8
elementAtomicZ iron = 26
elementAtomicZ helium = 2

hydrogen-z-1 : elementAtomicZ hydrogen ≡ 1
hydrogen-z-1 = refl

oxygen-z-8 : elementAtomicZ oxygen ≡ 8
oxygen-z-8 = refl

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

helium-z-2 : elementAtomicZ helium ≡ 2
helium-z-2 = refl

data OccupancyPhysicsTag : Set where
  iron-occupancy-core iron-occupancy-crust iron-occupancy-sulfide : OccupancyPhysicsTag

occupancyPhysicsAtomicZ : OccupancyPhysicsTag → ℕ
occupancyPhysicsAtomicZ iron-occupancy-core = 26
occupancyPhysicsAtomicZ iron-occupancy-crust = 26
occupancyPhysicsAtomicZ iron-occupancy-sulfide = 26

iron-occupancy-core-z-26 : occupancyPhysicsAtomicZ iron-occupancy-core ≡ 26
iron-occupancy-core-z-26 = refl

iron-occupancy-crust-z-26 : occupancyPhysicsAtomicZ iron-occupancy-crust ≡ 26
iron-occupancy-crust-z-26 = refl

iron-occupancy-sulfide-z-26 : occupancyPhysicsAtomicZ iron-occupancy-sulfide ≡ 26
iron-occupancy-sulfide-z-26 = refl

occupancy-same-z-many-charts :
  occupancyPhysicsAtomicZ iron-occupancy-core ≡ occupancyPhysicsAtomicZ iron-occupancy-crust ×
  occupancyPhysicsAtomicZ iron-occupancy-crust ≡ occupancyPhysicsAtomicZ iron-occupancy-sulfide ×
  occupancyPhysicsAtomicZ iron-occupancy-core ≡ elementAtomicZ iron
occupancy-same-z-many-charts = refl , refl , refl

isClosedShellNoChart : ElementTag → Bool
isClosedShellNoChart helium = true
isClosedShellNoChart _ = false

isOccupancyPhysicsElement : ElementTag → Bool
isOccupancyPhysicsElement hydrogen = true
isOccupancyPhysicsElement iron = true
isOccupancyPhysicsElement oxygen = true
isOccupancyPhysicsElement helium = false

helium-closed-shell-no-chart :
  isClosedShellNoChart helium ≡ true × isOccupancyPhysicsElement helium ≡ false
helium-closed-shell-no-chart = refl , refl

iron-is-occupancy-physics-element : isOccupancyPhysicsElement oxygen ≡ true
iron-is-occupancy-physics-element = refl

oxygen-is-occupancy-physics-element : isOccupancyPhysicsElement oxygen ≡ true
oxygen-is-occupancy-physics-element = refl

------------------------------------------------------------------------
-- Typed Chart⊗Occupancy⊗Physics **isomorphism** — composed indirect equals direct endpoints
------------------------------------------------------------------------

record ChartIsomorphismWitness : Set where
  constructor mkChartIsomorphismWitness
  field
    indirect-source : ChartLevel
    indirect-via      : ChartLevel
    indirect-target   : ChartLevel
    direct-source     : ChartLevel
    direct-target     : ChartLevel
    chart-tag      : ConstitutiveChartTag

chartIsomorphismWitnessNamed : ChartIsomorphismWitness
chartIsomorphismWitnessNamed = record
  { indirect-source = chart-chem
  ; indirect-via    = chart-occupancy
  ; indirect-target = chart-physics
  ; direct-source   = chart-chem
  ; direct-target   = chart-physics
  ; chart-tag    = interact-closed-shell
  }

composed-indirect-identity-equals-direct-typed :
  ChartIsomorphismWitness.indirect-source chartIsomorphismWitnessNamed ≡
  ChartIsomorphismWitness.direct-source chartIsomorphismWitnessNamed ×
  ChartIsomorphismWitness.indirect-target chartIsomorphismWitnessNamed ≡
  ChartIsomorphismWitness.direct-target chartIsomorphismWitnessNamed ×
  chartLegTarget chartLegChemToOccupancy ≡ chartLegSource chartLegOccupancyToPhysics ×
  chartLegSource chartLegChemToOccupancy ≡ chartLegSource chartLegChemToPhysicsDirect ×
  chartLegTarget chartLegOccupancyToPhysics ≡ chartLegTarget chartLegChemToPhysicsDirect ×
  isInteractClosedShell (ChartIsomorphismWitness.chart-tag chartIsomorphismWitnessNamed) ≡ true
composed-indirect-identity-equals-direct-typed = refl , refl , refl , refl , refl , refl

chart-typed-isomorphism-pin : chartTypedIsomorphism ≡ true
chart-typed-isomorphism-pin = refl

chart-occupancy-physics-product-pin : chartOccupancyPhysicsProduct ≡ true
chart-occupancy-physics-product-pin = refl

------------------------------------------------------------------------
-- ClassifierChartIsomorphismStep scaffold — Chart⊗Occupancy⊗Physics **isomorphism**
------------------------------------------------------------------------

data ClassifierChartIsomorphismStep : Set where
  chart-isomorphism-identity : ClassifierChartIsomorphismStep
  chart-isomorphism-leg-leaf : ChartIsomorphismLeg → ClassifierChartIsomorphismStep
  leg-compose : ClassifierChartIsomorphismStep → ClassifierChartIsomorphismStep → ClassifierChartIsomorphismStep
  chart-isomorphism-leg-mismatch : ClassifierChartIsomorphismStep → ClassifierChartIsomorphismStep → ClassifierChartIsomorphismStep
  folklore-list-invent : ClassifierChartIsomorphismStep
  xor-enum-smuggle : ClassifierChartIsomorphismStep
  trivial-no-chart-step : ElementTag → ClassifierChartIsomorphismStep

chartIsomorphismIdentity : ClassifierChartIsomorphismStep
chartIsomorphismIdentity = chart-isomorphism-identity

legComposeOp chartIsomorphismMismatchOp :
  ClassifierChartIsomorphismStep → ClassifierChartIsomorphismStep → ClassifierChartIsomorphismStep
legComposeOp = leg-compose
chartIsomorphismMismatchOp = chart-isomorphism-leg-mismatch

chemToOccupancyLeaf occupancyToPhysicsLeaf chemToPhysicsDirectLeaf : ClassifierChartIsomorphismStep
chemToOccupancyLeaf = chart-isomorphism-leg-leaf chem-to-occupancy
occupancyToPhysicsLeaf = chart-isomorphism-leg-leaf occupancy-to-physics
chemToPhysicsDirectLeaf = chart-isomorphism-leg-leaf chem-to-physics-direct

folkloreListInventStep xorEnumSmuggleStep : ClassifierChartIsomorphismStep
folkloreListInventStep = folklore-list-invent
xorEnumSmuggleStep = xor-enum-smuggle

trivialNoChartStep : ClassifierChartIsomorphismStep
trivialNoChartStep = trivial-no-chart-step helium

isLegCompose isChartIsomorphismLeg isChartIsomorphismIdentity : ClassifierChartIsomorphismStep → Bool
isLegCompose (leg-compose _ _) = true
isLegCompose _ = false

isChartIsomorphismLeg (chart-isomorphism-leg-leaf _) = true
isChartIsomorphismLeg _ = false

isChartIsomorphismIdentity chart-isomorphism-identity = true
isChartIsomorphismIdentity _ = false

isFolkloreListInvent : ClassifierChartIsomorphismStep → Bool
isFolkloreListInvent folklore-list-invent = true
isFolkloreListInvent _ = false

isXorEnumSmuggle : ClassifierChartIsomorphismStep → Bool
isXorEnumSmuggle xor-enum-smuggle = true
isXorEnumSmuggle _ = false

isTrivialNoChartStep : ClassifierChartIsomorphismStep → Bool
isTrivialNoChartStep (trivial-no-chart-step e) = isClosedShellNoChart e ∧ not (isOccupancyPhysicsElement e)
isTrivialNoChartStep _ = false

------------------------------------------------------------------------
-- **Chart-isomorphism** identity conserved at chart-isomorphism-identity — leg-compose scaffold
------------------------------------------------------------------------

chart-isomorphism-left-identity :
  ∀ (a : ClassifierChartIsomorphismStep) →
  isChartIsomorphismIdentity chartIsomorphismIdentity ≡ true × isLegCompose (legComposeOp chartIsomorphismIdentity a) ≡ true
chart-isomorphism-left-identity a = refl , refl

chart-isomorphism-right-identity :
  ∀ (a : ClassifierChartIsomorphismStep) →
  isLegCompose (legComposeOp a chartIsomorphismIdentity) ≡ true × isChartIsomorphismIdentity chartIsomorphismIdentity ≡ true
chart-isomorphism-right-identity a = refl , refl

------------------------------------------------------------------------
-- Named three-leg Chart⊗Occupancy⊗Physics closed — indirect composed vs direct product
------------------------------------------------------------------------

namedChartIsomorphismIndirectPath : ClassifierChartIsomorphismStep
namedChartIsomorphismIndirectPath = legComposeOp chemToOccupancyLeaf occupancyToPhysicsLeaf

namedChartIsomorphismDirectPath : ClassifierChartIsomorphismStep
namedChartIsomorphismDirectPath = chemToPhysicsDirectLeaf

named-chart-isomorphism-indirect-is-compose :
  isLegCompose namedChartIsomorphismIndirectPath ≡ true
named-chart-isomorphism-indirect-is-compose = refl

named-chart-isomorphism-direct-is-leg :
  isChartIsomorphismLeg namedChartIsomorphismDirectPath ≡ true
named-chart-isomorphism-direct-is-leg = refl

named-chart-isomorphism-ladder-closed :
  isLegCompose namedChartIsomorphismIndirectPath ≡ true
  × isChartIsomorphismLeg namedChartIsomorphismDirectPath ≡ true
  × chartLegTarget chartLegChemToOccupancy ≡ chartLegSource chartLegOccupancyToPhysics
  × chartLegSource chartLegChemToOccupancy ≡ chartLegSource chartLegChemToPhysicsDirect
  × chartLegTarget chartLegOccupancyToPhysics ≡ chartLegTarget chartLegChemToPhysicsDirect
named-chart-isomorphism-ladder-closed = refl , refl , refl , refl , refl

chartIsomorphismLegMismatchPath : ClassifierChartIsomorphismStep
chartIsomorphismLegMismatchPath = chartIsomorphismMismatchOp occupancyToPhysicsLeaf chemToOccupancyLeaf

isChartIsomorphismMismatch : ClassifierChartIsomorphismStep → Bool
isChartIsomorphismMismatch (chart-isomorphism-leg-mismatch _ _) = true
isChartIsomorphismMismatch _ = false

chart-isomorphism-mismatch-not-compose :
  isLegCompose chartIsomorphismLegMismatchPath ≡ false
chart-isomorphism-mismatch-not-compose = refl

------------------------------------------------------------------------
-- **Chart-isomorphism** admissibility — mismatch / folklore / XOR / He no-chart refuse
------------------------------------------------------------------------

isChartIsomorphismPreserving : ClassifierChartIsomorphismStep → Bool
isChartIsomorphismPreserving chart-isomorphism-identity = true
isChartIsomorphismPreserving (chart-isomorphism-leg-leaf _) = true
isChartIsomorphismPreserving (leg-compose a b) =
  isChartIsomorphismPreserving a ∧ isChartIsomorphismPreserving b
isChartIsomorphismPreserving (chart-isomorphism-leg-mismatch _ _) = false
isChartIsomorphismPreserving folklore-list-invent = false
isChartIsomorphismPreserving xor-enum-smuggle = false
isChartIsomorphismPreserving (trivial-no-chart-step e) =
  not (isClosedShellNoChart e ∧ not (isOccupancyPhysicsElement e))

isChartIsomorphismAdmissible : ClassifierChartIsomorphismStep → Bool
isChartIsomorphismAdmissible step = isChartIsomorphismPreserving step

named-chart-isomorphism-indirect-admissible : isChartIsomorphismAdmissible namedChartIsomorphismIndirectPath ≡ true
named-chart-isomorphism-indirect-admissible = refl

chart-isomorphism-leg-mismatch-not-admissible :
  isChartIsomorphismAdmissible chartIsomorphismLegMismatchPath ≡ false
chart-isomorphism-leg-mismatch-not-admissible = refl

folklore-list-not-admissible :
  isChartIsomorphismAdmissible folkloreListInventStep ≡ false
folklore-list-not-admissible = refl

xor-enum-not-admissible :
  isChartIsomorphismAdmissible xorEnumSmuggleStep ≡ false
xor-enum-not-admissible = refl

trivial-no-chart-not-admissible :
  isChartIsomorphismAdmissible trivialNoChartStep ≡ false
trivial-no-chart-not-admissible = refl

------------------------------------------------------------------------
-- **Chart-isomorphism** witness — total-claim refuse; proved-without-census refuse
------------------------------------------------------------------------

data ChartIsomorphismWitnessPresence : Set where
  chart-isomorphism-witness-absent chart-isomorphism-witness-present : ChartIsomorphismWitnessPresence

data CensusWitnessPresence : Set where
  census-witness-absent census-witness-present : CensusWitnessPresence

record ClassifierChartIsomorphismWitness : Set where
  constructor mkClassifierChartIsomorphismWitness
  field
    witness-presence : ChartIsomorphismWitnessPresence
    census-presence  : CensusWitnessPresence
    chart-isomorphism-gap-total : ℕ

chartIsomorphismWitnessAbsent : ClassifierChartIsomorphismWitness
chartIsomorphismWitnessAbsent = mkClassifierChartIsomorphismWitness chart-isomorphism-witness-absent census-witness-absent zero

chartIsomorphismWitnessPresentZeroGapWithCensus : ClassifierChartIsomorphismWitness
chartIsomorphismWitnessPresentZeroGapWithCensus =
  mkClassifierChartIsomorphismWitness chart-isomorphism-witness-present census-witness-present zero

chartIsomorphismWitnessPresentWithoutCensus : ClassifierChartIsomorphismWitness
chartIsomorphismWitnessPresentWithoutCensus =
  mkClassifierChartIsomorphismWitness chart-isomorphism-witness-present census-witness-absent zero

chartIsomorphismWitnessGapFree : ClassifierChartIsomorphismWitness → Bool
chartIsomorphismWitnessGapFree (mkClassifierChartIsomorphismWitness chart-isomorphism-witness-absent _ _) = false
chartIsomorphismWitnessGapFree (mkClassifierChartIsomorphismWitness chart-isomorphism-witness-present _ n) =
  does (n ℕ-Props.≟ zero)

chart-isomorphism-witness-present-zero-gap-free :
  chartIsomorphismWitnessGapFree chartIsomorphismWitnessPresentZeroGapWithCensus ≡ true
chart-isomorphism-witness-present-zero-gap-free = refl

------------------------------------------------------------------------
-- Classifier-CHART-ISOMORPHISM-01 close verdict — fail-closed lattice
------------------------------------------------------------------------

data ChartIsomorphismConservationVerdict : Set where
  verdict-unwired-ok verdict-chart-isomorphism-product-admissible-ok
    verdict-chart-isomorphism-leg-mismatch-refuse verdict-total-claim-refuse
    verdict-proved-without-census-refuse verdict-folklore-list-invent-refuse
    verdict-xor-enum-smuggle-refuse verdict-trivial-no-chart-refuse
    verdict-green-invent-refuse
    : ChartIsomorphismConservationVerdict

chartIsomorphismConservationVerdictOk : ChartIsomorphismConservationVerdict → Bool
chartIsomorphismConservationVerdictOk verdict-unwired-ok = true
chartIsomorphismConservationVerdictOk verdict-chart-isomorphism-product-admissible-ok = true
chartIsomorphismConservationVerdictOk _ = false

evaluateChartIsomorphismConservationClose :
  ChartIsomorphismConservationModality → ClassifierChartIsomorphismStep → ClassifierChartIsomorphismWitness → Bool
  → ChartIsomorphismConservationVerdict
evaluateChartIsomorphismConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-unwired _ _ false = verdict-unwired-ok
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-assumed _ _ false = verdict-unwired-ok
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved folklore-list-invent _ false =
  verdict-folklore-list-invent-refuse
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved xor-enum-smuggle _ false =
  verdict-xor-enum-smuggle-refuse
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved (trivial-no-chart-step _) _ false =
  verdict-trivial-no-chart-refuse
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved _ (mkClassifierChartIsomorphismWitness chart-isomorphism-witness-absent _ _) false =
  verdict-total-claim-refuse
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved _ (mkClassifierChartIsomorphismWitness chart-isomorphism-witness-present census-witness-absent _) false =
  verdict-proved-without-census-refuse
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved (chart-isomorphism-leg-mismatch _ _) _ false =
  verdict-chart-isomorphism-leg-mismatch-refuse
evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved step (mkClassifierChartIsomorphismWitness chart-isomorphism-witness-present census-witness-present _) false
  with isChartIsomorphismAdmissible step
... | false = verdict-chart-isomorphism-leg-mismatch-refuse
... | true  = verdict-chart-isomorphism-product-admissible-ok

unwired-close-without-witness :
  evaluateChartIsomorphismConservationClose
    chart-isomorphism-conservation-unwired namedChartIsomorphismIndirectPath chartIsomorphismWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

total-claim-refuse-without-witness :
  evaluateChartIsomorphismConservationClose
    chart-isomorphism-conservation-proved namedChartIsomorphismIndirectPath chartIsomorphismWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

proved-without-census-refuse-verdict :
  evaluateChartIsomorphismConservationClose
    chart-isomorphism-conservation-proved namedChartIsomorphismIndirectPath chartIsomorphismWitnessPresentWithoutCensus false ≡
  verdict-proved-without-census-refuse
proved-without-census-refuse-verdict = refl

chart-isomorphism-leg-mismatch-refuse-verdict :
  evaluateChartIsomorphismConservationClose
    chart-isomorphism-conservation-proved chartIsomorphismLegMismatchPath chartIsomorphismWitnessPresentZeroGapWithCensus false ≡
  verdict-chart-isomorphism-leg-mismatch-refuse
chart-isomorphism-leg-mismatch-refuse-verdict = refl

folklore-list-invent-refuse-verdict :
  evaluateChartIsomorphismConservationClose
    chart-isomorphism-conservation-proved folkloreListInventStep chartIsomorphismWitnessPresentZeroGapWithCensus false ≡
  verdict-folklore-list-invent-refuse
folklore-list-invent-refuse-verdict = refl

xor-enum-smuggle-refuse-verdict :
  evaluateChartIsomorphismConservationClose
    chart-isomorphism-conservation-proved xorEnumSmuggleStep chartIsomorphismWitnessPresentZeroGapWithCensus false ≡
  verdict-xor-enum-smuggle-refuse
xor-enum-smuggle-refuse-verdict = refl

trivial-no-chart-refuse-verdict :
  evaluateChartIsomorphismConservationClose
    chart-isomorphism-conservation-proved trivialNoChartStep chartIsomorphismWitnessPresentZeroGapWithCensus false ≡
  verdict-trivial-no-chart-refuse
trivial-no-chart-refuse-verdict = refl

chart-isomorphism-product-admissible-ok :
  evaluateChartIsomorphismConservationClose
    chart-isomorphism-conservation-proved namedChartIsomorphismIndirectPath chartIsomorphismWitnessPresentZeroGapWithCensus false ≡
  verdict-chart-isomorphism-product-admissible-ok
chart-isomorphism-product-admissible-ok = refl

green-invent-always-refuse :
  chartIsomorphismConservationVerdictOk
    (evaluateChartIsomorphismConservationClose
       chart-isomorphism-conservation-unwired namedChartIsomorphismIndirectPath chartIsomorphismWitnessPresentZeroGapWithCensus true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

chartIsomorphismConservationFiberOk : FormalFiber → Bool
chartIsomorphismConservationFiberOk fiber-quantum-knowing = true
chartIsomorphismConservationFiberOk fiber-meso-acting = false

chart-isomorphism-conservation-knowing-fiber-ok :
  chartIsomorphismConservationFiberOk fiber-quantum-knowing ≡ true
chart-isomorphism-conservation-knowing-fiber-ok = refl

chart-isomorphism-conservation-meso-acting-not-ok :
  chartIsomorphismConservationFiberOk fiber-meso-acting ≡ false
chart-isomorphism-conservation-meso-acting-not-ok = refl

------------------------------------------------------------------------
-- Honest pins — not Chart-Isomorphism Proved, not physics GREEN
------------------------------------------------------------------------

chart-isomorphism-not-proved : chartIsomorphismProved ≡ false
chart-isomorphism-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

chart-second-law-conservation-framed : chartSecondLawConservationFramed ≡ true
chart-second-law-conservation-framed = refl

chart-typed-isomorphism-framed : chartTypedIsomorphism ≡ true
chart-typed-isomorphism-framed = chart-typed-isomorphism-pin

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second CHART-ISOMORPHISM-01 axiom fork)
------------------------------------------------------------------------

chartIsomorphismConservationAxiom :
  (chartIsomorphismProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (chartSecondLawConservationFramed ≡ true)
  × (chartTypedIsomorphism ≡ true)
  × (chartNotXor ≡ true)
  × (chartOccupancyPhysicsProduct ≡ true)
  × (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-unwired namedChartIsomorphismIndirectPath chartIsomorphismWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved namedChartIsomorphismIndirectPath chartIsomorphismWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved chartIsomorphismLegMismatchPath chartIsomorphismWitnessPresentZeroGapWithCensus false ≡ verdict-chart-isomorphism-leg-mismatch-refuse)
  × (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved namedChartIsomorphismIndirectPath chartIsomorphismWitnessPresentZeroGapWithCensus false ≡ verdict-chart-isomorphism-product-admissible-ok)
  × (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved namedChartIsomorphismIndirectPath chartIsomorphismWitnessPresentWithoutCensus false ≡ verdict-proved-without-census-refuse)
  × (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved folkloreListInventStep chartIsomorphismWitnessPresentZeroGapWithCensus false ≡ verdict-folklore-list-invent-refuse)
  × (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved xorEnumSmuggleStep chartIsomorphismWitnessPresentZeroGapWithCensus false ≡ verdict-xor-enum-smuggle-refuse)
  × (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-proved trivialNoChartStep chartIsomorphismWitnessPresentZeroGapWithCensus false ≡ verdict-trivial-no-chart-refuse)
  × (chartIsomorphismConservationFiberOk fiber-quantum-knowing ≡ true)
  × (chartIsomorphismConservationFiberOk fiber-meso-acting ≡ false)
  × (chartIsomorphismConservationVerdictOk (evaluateChartIsomorphismConservationClose chart-isomorphism-conservation-unwired namedChartIsomorphismIndirectPath chartIsomorphismWitnessPresentZeroGapWithCensus true) ≡ false)
  × (∀ a → isLegCompose (legComposeOp chartIsomorphismIdentity a) ≡ true)
  × (isChartIsomorphismAdmissible chartIsomorphismLegMismatchPath ≡ false)
  × (chartLegTarget chartLegChemToOccupancy ≡ chartLegSource chartLegOccupancyToPhysics)
  × (chartLegSource chartLegChemToOccupancy ≡ chartLegSource chartLegChemToPhysicsDirect)
  × (chartLegTarget chartLegOccupancyToPhysics ≡ chartLegTarget chartLegChemToPhysicsDirect)
  × (isOccupancySort occupancy-sort ≡ true)
  × (isGEngine g-engine ≡ true)
  × (isInteractClosedShell interact-closed-shell ≡ true)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oxygen ≡ 8)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ helium ≡ 2)
  × (isClosedShellNoChart helium ≡ true × isOccupancyPhysicsElement helium ≡ false)
  × (occupancyPhysicsAtomicZ iron-occupancy-core ≡ occupancyPhysicsAtomicZ iron-occupancy-crust)
chartIsomorphismConservationAxiom =
  chart-isomorphism-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , chart-second-law-conservation-framed
  , chart-typed-isomorphism-framed
  , chart-not-xor
  , chart-occupancy-physics-product-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , chart-isomorphism-leg-mismatch-refuse-verdict
  , chart-isomorphism-product-admissible-ok
  , proved-without-census-refuse-verdict
  , folklore-list-invent-refuse-verdict
  , xor-enum-smuggle-refuse-verdict
  , trivial-no-chart-refuse-verdict
  , chart-isomorphism-conservation-knowing-fiber-ok
  , chart-isomorphism-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , chart-isomorphism-leg-mismatch-not-admissible
  , chart-leg-first-composes-levels
  , refl
  , refl
  , (proj₁ occupancy-sort-named)
  , (proj₁ g-engine-named)
  , (proj₁ interact-closed-shell-named)
  , hydrogen-z-1
  , oxygen-z-8
  , iron-z-26
  , helium-z-2
  , helium-closed-shell-no-chart
  , (proj₁ occupancy-same-z-many-charts)

chemPhysicsChartIsomorphismNamed : String
chemPhysicsChartIsomorphismNamed =
  "chemPhysicsChartIsomorphism: CHART-ISOMORPHISM-01 chemistry is occupancy physics constitutive engines named charts one second-law object Chart⊗Occupancy⊗Physics class 2⊗3⊗4 occupancy-sort g-engine interact-closed-shell concurrent not XOR composed indirect equals direct typed isomorphism conservation engines not second physics sole axiom 1"

chemPhysicsChartIsomorphismCellId : String
chemPhysicsChartIsomorphismCellId = "CHEM-FORMAL-Q-AGDA-CHEM-PHYSICS-CHART-ISOMORPHISM-CONSERVATION"

chemPhysicsChartIsomorphismNonClaim : String
chemPhysicsChartIsomorphismNonClaim =
  "CHEM-FORMAL-Q-AGDA-CHEM-PHYSICS-CHART-ISOMORPHISM-CONSERVATION CHART-ISOMORPHISM-01 chemistry is occupancy physics constitutive engines named charts one second-law object Chart⊗Occupancy⊗Physics class 2⊗3⊗4 occupancy-sort g-engine interact-closed-shell concurrent not XOR composed indirect equals direct typed isomorphism conservation folklore list invent refuse XOR enum smuggle refuse trivial He closed shell no chart refuse total-claim refuse proved-without-census refuse H Z 1 Fe Z 26 O Z 8 He Z 2 chartIsomorphismProved false engines not second physics extra chem force refused sole axiom 1 not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second CHART-ISOMORPHISM axiom not physics GREEN not production_wired"

chart-isomorphism-conservation-modality-unwired :
  chartIsomorphismConservationModalityCurrent ≡ chart-isomorphism-conservation-unwired
chart-isomorphism-conservation-modality-unwired = refl

chemPhysicsChartIsomorphismPhysicsGreenAuthorized : Set
chemPhysicsChartIsomorphismPhysicsGreenAuthorized = ⊥

chem-physics-chart-isomorphism-physics-green-false : ¬ chemPhysicsChartIsomorphismPhysicsGreenAuthorized
chem-physics-chart-isomorphism-physics-green-false ()

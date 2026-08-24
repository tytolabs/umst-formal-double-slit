-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.GoldschmidtConservation.agda
--
-- GOLDSCHMIDT-01 **Goldschmidt** Ore⊗G⊗fO₂ **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Three named affinities lithophile/chalcophile/siderophile — concurrent Ore⊗G⊗fO₂ not XOR
--   * Class 6⊗7⊗17 product factor; order identity conserved
--   * Composed Ore→G→fO₂ identity equals Ore⊗G⊗fO₂ direct (typed **conservation**)
--   * Fe (Z=26) same Z many assemblages; Cu (Z=29); Si (Z=14); He (Z=2) closed-shell no-ore
--   * folklore / GREEN / trivial / proved-without-bar refuse; total-claim refuse without witness
--   * **goldschmidt** laws Unwired (goldschmidtProved = false)
--
-- Mirrors sibling `ChemConstants/ThermoConservation.agda` +
-- `ChemConstants/DensityConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.GoldschmidtConservation where

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
-- Modality + GOLDSCHMIDT-01 Ore⊗G⊗fO₂ **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data GoldschmidtConservationModality : Set where
  goldschmidt-conservation-unwired goldschmidt-conservation-assumed
    goldschmidt-conservation-proved goldschmidt-conservation-surrogate
    : GoldschmidtConservationModality

goldschmidtConservationModalityCurrent : GoldschmidtConservationModality
goldschmidtConservationModalityCurrent = goldschmidt-conservation-unwired

goldschmidtProved productionWired not118SquaredGreenTable
  goldschmidtSecondLawConservationFramed goldschmidtTypedConservation
  affinityNotXor classSixSevenSeventeenProduct : Bool
goldschmidtProved = false
productionWired = false
not118SquaredGreenTable = true
goldschmidtSecondLawConservationFramed = true
goldschmidtTypedConservation = true
affinityNotXor = true
classSixSevenSeventeenProduct = true

------------------------------------------------------------------------
-- Class 6⊗7⊗17 pattern indices (structure — not 118²)
------------------------------------------------------------------------

classSixOrePatternIndex classSevenGStabilityPatternIndex classSeventeenFo2PatternIndex : ℕ
classSixOrePatternIndex = 6
classSevenGStabilityPatternIndex = 7
classSeventeenFo2PatternIndex = 17

class-six-seven-seventeen-product :
  classSixOrePatternIndex * classSevenGStabilityPatternIndex * classSeventeenFo2PatternIndex ≡ 714
class-six-seven-seventeen-product = refl

goldschmidt-ladder-not-118-squared :
  does (classSixOrePatternIndex ℕ-Props.≟ 118) ≡ false
goldschmidt-ladder-not-118-squared = refl

------------------------------------------------------------------------
-- Named affinity tags — concurrent Ore⊗G⊗fO₂ product, not XOR enum
------------------------------------------------------------------------

data GoldschmidtAffinityTag : Set where
  lithophile chalcophile siderophile : GoldschmidtAffinityTag

isLithophile isChalcophile isSiderophile : GoldschmidtAffinityTag → Bool
isLithophile lithophile = true
isLithophile _ = false

isChalcophile chalcophile = true
isChalcophile _ = false

isSiderophile siderophile = true
isSiderophile _ = false

lithophile-named :
  isLithophile lithophile ≡ true × isChalcophile lithophile ≡ false
lithophile-named = refl , refl

chalcophile-named :
  isChalcophile chalcophile ≡ true × isSiderophile chalcophile ≡ false
chalcophile-named = refl , refl

siderophile-named :
  isSiderophile siderophile ≡ true × isLithophile siderophile ≡ false
siderophile-named = refl , refl

lithophile-distinct-from-chalcophile : lithophile ≢ chalcophile
lithophile-distinct-from-chalcophile ()

affinity-not-xor : affinityNotXor ≡ true
affinity-not-xor = refl

------------------------------------------------------------------------
-- Ore⊗G⊗fO₂ product factor legs (class 6 ⊗ 7 ⊗ 17)
------------------------------------------------------------------------

data GoldschmidtLevel : Set where
  goldschmidt-ore goldschmidt-g-stability goldschmidt-fo2-ladder : GoldschmidtLevel

data GoldschmidtProductLeg : Set where
  ore-to-g g-to-fo2 ore-to-product-direct : GoldschmidtProductLeg

goldschmidtLegSource : GoldschmidtProductLeg → GoldschmidtLevel
goldschmidtLegSource ore-to-g = goldschmidt-ore
goldschmidtLegSource g-to-fo2 = goldschmidt-g-stability
goldschmidtLegSource ore-to-product-direct = goldschmidt-ore

goldschmidtLegTarget : GoldschmidtProductLeg → GoldschmidtLevel
goldschmidtLegTarget ore-to-g = goldschmidt-g-stability
goldschmidtLegTarget g-to-fo2 = goldschmidt-fo2-ladder
goldschmidtLegTarget ore-to-product-direct = goldschmidt-fo2-ladder

goldschmidtLegOreToG goldschmidtLegGToFo2 goldschmidtLegOreToProductDirect : GoldschmidtProductLeg
goldschmidtLegOreToG = ore-to-g
goldschmidtLegGToFo2 = g-to-fo2
goldschmidtLegOreToProductDirect = ore-to-product-direct

goldschmidt-leg-first-composes-levels :
  goldschmidtLegTarget goldschmidtLegOreToG ≡ goldschmidtLegSource goldschmidtLegGToFo2
goldschmidt-leg-first-composes-levels = refl

goldschmidt-leg-direct-endpoints-match :
  goldschmidtLegSource goldschmidtLegOreToG ≡ goldschmidtLegSource goldschmidtLegOreToProductDirect ×
  goldschmidtLegTarget goldschmidtLegGToFo2 ≡ goldschmidtLegTarget goldschmidtLegOreToProductDirect
goldschmidt-leg-direct-endpoints-match = refl , refl

goldschmidt-leg-distinct-indirect-vs-direct :
  goldschmidtLegOreToG ≢ goldschmidtLegOreToProductDirect
goldschmidt-leg-distinct-indirect-vs-direct ()

------------------------------------------------------------------------
-- Named element Z pins — Fe (Z=26) many assemblages; Cu (Z=29); Si (Z=14); He (Z=2) no-ore
------------------------------------------------------------------------

data ElementTag : Set where
  iron copper silicon helium : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ iron = 26
elementAtomicZ copper = 29
elementAtomicZ silicon = 14
elementAtomicZ helium = 2

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

copper-z-29 : elementAtomicZ copper ≡ 29
copper-z-29 = refl

silicon-z-14 : elementAtomicZ silicon ≡ 14
silicon-z-14 = refl

helium-z-2 : elementAtomicZ helium ≡ 2
helium-z-2 = refl

data FeAssemblageTag : Set where
  fe-core-siderophile fe-crust-oxide fe-sulfide-trace : FeAssemblageTag

feAssemblageAtomicZ : FeAssemblageTag → ℕ
feAssemblageAtomicZ fe-core-siderophile = 26
feAssemblageAtomicZ fe-crust-oxide = 26
feAssemblageAtomicZ fe-sulfide-trace = 26

fe-core-siderophile-z-26 : feAssemblageAtomicZ fe-core-siderophile ≡ 26
fe-core-siderophile-z-26 = refl

fe-crust-oxide-z-26 : feAssemblageAtomicZ fe-crust-oxide ≡ 26
fe-crust-oxide-z-26 = refl

fe-sulfide-trace-z-26 : feAssemblageAtomicZ fe-sulfide-trace ≡ 26
fe-sulfide-trace-z-26 = refl

fe-same-z-many-assemblages :
  feAssemblageAtomicZ fe-core-siderophile ≡ feAssemblageAtomicZ fe-crust-oxide ×
  feAssemblageAtomicZ fe-crust-oxide ≡ feAssemblageAtomicZ fe-sulfide-trace ×
  feAssemblageAtomicZ fe-core-siderophile ≡ elementAtomicZ iron
fe-same-z-many-assemblages = refl , refl , refl

isClosedShellNoOre : ElementTag → Bool
isClosedShellNoOre helium = true
isClosedShellNoOre _ = false

isOreElement : ElementTag → Bool
isOreElement iron = true
isOreElement copper = true
isOreElement silicon = true
isOreElement helium = false

helium-closed-shell-no-ore :
  isClosedShellNoOre helium ≡ true × isOreElement helium ≡ false
helium-closed-shell-no-ore = refl , refl

copper-is-ore-element : isOreElement copper ≡ true
copper-is-ore-element = refl

silicon-is-ore-element : isOreElement silicon ≡ true
silicon-is-ore-element = refl

------------------------------------------------------------------------
-- Typed Ore⊗G⊗fO₂ **conservation** — composed indirect equals direct endpoints
------------------------------------------------------------------------

record GoldschmidtProductWitness : Set where
  constructor mkGoldschmidtProductWitness
  field
    indirect-source : GoldschmidtLevel
    indirect-via      : GoldschmidtLevel
    indirect-target   : GoldschmidtLevel
    direct-source     : GoldschmidtLevel
    direct-target     : GoldschmidtLevel
    affinity-tag      : GoldschmidtAffinityTag

goldschmidtProductWitnessNamed : GoldschmidtProductWitness
goldschmidtProductWitnessNamed = record
  { indirect-source = goldschmidt-ore
  ; indirect-via    = goldschmidt-g-stability
  ; indirect-target = goldschmidt-fo2-ladder
  ; direct-source   = goldschmidt-ore
  ; direct-target   = goldschmidt-fo2-ladder
  ; affinity-tag    = siderophile
  }

composed-indirect-identity-equals-direct-typed :
  GoldschmidtProductWitness.indirect-source goldschmidtProductWitnessNamed ≡
  GoldschmidtProductWitness.direct-source goldschmidtProductWitnessNamed ×
  GoldschmidtProductWitness.indirect-target goldschmidtProductWitnessNamed ≡
  GoldschmidtProductWitness.direct-target goldschmidtProductWitnessNamed ×
  goldschmidtLegTarget goldschmidtLegOreToG ≡ goldschmidtLegSource goldschmidtLegGToFo2 ×
  goldschmidtLegSource goldschmidtLegOreToG ≡ goldschmidtLegSource goldschmidtLegOreToProductDirect ×
  goldschmidtLegTarget goldschmidtLegGToFo2 ≡ goldschmidtLegTarget goldschmidtLegOreToProductDirect ×
  isSiderophile (GoldschmidtProductWitness.affinity-tag goldschmidtProductWitnessNamed) ≡ true
composed-indirect-identity-equals-direct-typed = refl , refl , refl , refl , refl , refl

goldschmidt-typed-conservation-pin : goldschmidtTypedConservation ≡ true
goldschmidt-typed-conservation-pin = refl

class-six-seven-seventeen-product-pin : classSixSevenSeventeenProduct ≡ true
class-six-seven-seventeen-product-pin = refl

------------------------------------------------------------------------
-- ClassifierGoldschmidtStep scaffold — Ore⊗G⊗fO₂ **conservation**
------------------------------------------------------------------------

data ClassifierGoldschmidtStep : Set where
  goldschmidt-identity : ClassifierGoldschmidtStep
  goldschmidt-leg-leaf : GoldschmidtProductLeg → ClassifierGoldschmidtStep
  leg-compose : ClassifierGoldschmidtStep → ClassifierGoldschmidtStep → ClassifierGoldschmidtStep
  goldschmidt-leg-mismatch : ClassifierGoldschmidtStep → ClassifierGoldschmidtStep → ClassifierGoldschmidtStep
  folklore-list-invent : ClassifierGoldschmidtStep
  xor-enum-smuggle : ClassifierGoldschmidtStep
  trivial-no-ore-step : ElementTag → ClassifierGoldschmidtStep

goldschmidtIdentity : ClassifierGoldschmidtStep
goldschmidtIdentity = goldschmidt-identity

legComposeOp goldschmidtMismatchOp :
  ClassifierGoldschmidtStep → ClassifierGoldschmidtStep → ClassifierGoldschmidtStep
legComposeOp = leg-compose
goldschmidtMismatchOp = goldschmidt-leg-mismatch

oreToGLeaf gToFo2Leaf oreToProductDirectLeaf : ClassifierGoldschmidtStep
oreToGLeaf = goldschmidt-leg-leaf ore-to-g
gToFo2Leaf = goldschmidt-leg-leaf g-to-fo2
oreToProductDirectLeaf = goldschmidt-leg-leaf ore-to-product-direct

folkloreListInventStep xorEnumSmuggleStep : ClassifierGoldschmidtStep
folkloreListInventStep = folklore-list-invent
xorEnumSmuggleStep = xor-enum-smuggle

trivialNoOreStep : ClassifierGoldschmidtStep
trivialNoOreStep = trivial-no-ore-step helium

isLegCompose isGoldschmidtLeg isGoldschmidtIdentity : ClassifierGoldschmidtStep → Bool
isLegCompose (leg-compose _ _) = true
isLegCompose _ = false

isGoldschmidtLeg (goldschmidt-leg-leaf _) = true
isGoldschmidtLeg _ = false

isGoldschmidtIdentity goldschmidt-identity = true
isGoldschmidtIdentity _ = false

isFolkloreListInvent : ClassifierGoldschmidtStep → Bool
isFolkloreListInvent folklore-list-invent = true
isFolkloreListInvent _ = false

isXorEnumSmuggle : ClassifierGoldschmidtStep → Bool
isXorEnumSmuggle xor-enum-smuggle = true
isXorEnumSmuggle _ = false

isTrivialNoOreStep : ClassifierGoldschmidtStep → Bool
isTrivialNoOreStep (trivial-no-ore-step e) = isClosedShellNoOre e ∧ not (isOreElement e)
isTrivialNoOreStep _ = false

------------------------------------------------------------------------
-- **Goldschmidt** identity conserved at goldschmidt-identity — leg-compose scaffold
------------------------------------------------------------------------

goldschmidt-left-identity :
  ∀ (a : ClassifierGoldschmidtStep) →
  isGoldschmidtIdentity goldschmidtIdentity ≡ true × isLegCompose (legComposeOp goldschmidtIdentity a) ≡ true
goldschmidt-left-identity a = refl , refl

goldschmidt-right-identity :
  ∀ (a : ClassifierGoldschmidtStep) →
  isLegCompose (legComposeOp a goldschmidtIdentity) ≡ true × isGoldschmidtIdentity goldschmidtIdentity ≡ true
goldschmidt-right-identity a = refl , refl

------------------------------------------------------------------------
-- Named three-leg Ore⊗G⊗fO₂ closed — indirect composed vs direct product
------------------------------------------------------------------------

namedGoldschmidtIndirectPath : ClassifierGoldschmidtStep
namedGoldschmidtIndirectPath = legComposeOp oreToGLeaf gToFo2Leaf

namedGoldschmidtDirectPath : ClassifierGoldschmidtStep
namedGoldschmidtDirectPath = oreToProductDirectLeaf

named-goldschmidt-indirect-is-compose :
  isLegCompose namedGoldschmidtIndirectPath ≡ true
named-goldschmidt-indirect-is-compose = refl

named-goldschmidt-direct-is-leg :
  isGoldschmidtLeg namedGoldschmidtDirectPath ≡ true
named-goldschmidt-direct-is-leg = refl

named-goldschmidt-ladder-closed :
  isLegCompose namedGoldschmidtIndirectPath ≡ true
  × isGoldschmidtLeg namedGoldschmidtDirectPath ≡ true
  × goldschmidtLegTarget goldschmidtLegOreToG ≡ goldschmidtLegSource goldschmidtLegGToFo2
  × goldschmidtLegSource goldschmidtLegOreToG ≡ goldschmidtLegSource goldschmidtLegOreToProductDirect
  × goldschmidtLegTarget goldschmidtLegGToFo2 ≡ goldschmidtLegTarget goldschmidtLegOreToProductDirect
named-goldschmidt-ladder-closed = refl , refl , refl , refl , refl

goldschmidtLegMismatchPath : ClassifierGoldschmidtStep
goldschmidtLegMismatchPath = goldschmidtMismatchOp gToFo2Leaf oreToGLeaf

isGoldschmidtMismatch : ClassifierGoldschmidtStep → Bool
isGoldschmidtMismatch (goldschmidt-leg-mismatch _ _) = true
isGoldschmidtMismatch _ = false

goldschmidt-mismatch-not-compose :
  isLegCompose goldschmidtLegMismatchPath ≡ false
goldschmidt-mismatch-not-compose = refl

------------------------------------------------------------------------
-- **Goldschmidt** admissibility — mismatch / folklore / XOR / He no-ore refuse
------------------------------------------------------------------------

isGoldschmidtPreserving : ClassifierGoldschmidtStep → Bool
isGoldschmidtPreserving goldschmidt-identity = true
isGoldschmidtPreserving (goldschmidt-leg-leaf _) = true
isGoldschmidtPreserving (leg-compose a b) =
  isGoldschmidtPreserving a ∧ isGoldschmidtPreserving b
isGoldschmidtPreserving (goldschmidt-leg-mismatch _ _) = false
isGoldschmidtPreserving folklore-list-invent = false
isGoldschmidtPreserving xor-enum-smuggle = false
isGoldschmidtPreserving (trivial-no-ore-step e) =
  not (isClosedShellNoOre e ∧ not (isOreElement e))

isGoldschmidtAdmissible : ClassifierGoldschmidtStep → Bool
isGoldschmidtAdmissible step = isGoldschmidtPreserving step

named-goldschmidt-indirect-admissible : isGoldschmidtAdmissible namedGoldschmidtIndirectPath ≡ true
named-goldschmidt-indirect-admissible = refl

goldschmidt-leg-mismatch-not-admissible :
  isGoldschmidtAdmissible goldschmidtLegMismatchPath ≡ false
goldschmidt-leg-mismatch-not-admissible = refl

folklore-list-not-admissible :
  isGoldschmidtAdmissible folkloreListInventStep ≡ false
folklore-list-not-admissible = refl

xor-enum-not-admissible :
  isGoldschmidtAdmissible xorEnumSmuggleStep ≡ false
xor-enum-not-admissible = refl

trivial-no-ore-not-admissible :
  isGoldschmidtAdmissible trivialNoOreStep ≡ false
trivial-no-ore-not-admissible = refl

------------------------------------------------------------------------
-- **Goldschmidt** witness — total-claim refuse; proved-without-bar (census) refuse
------------------------------------------------------------------------

data GoldschmidtWitnessPresence : Set where
  goldschmidt-witness-absent goldschmidt-witness-present : GoldschmidtWitnessPresence

data CensusWitnessPresence : Set where
  census-witness-absent census-witness-present : CensusWitnessPresence

record ClassifierGoldschmidtWitness : Set where
  constructor mkClassifierGoldschmidtWitness
  field
    witness-presence : GoldschmidtWitnessPresence
    census-presence  : CensusWitnessPresence
    goldschmidt-gap-total : ℕ

goldschmidtWitnessAbsent : ClassifierGoldschmidtWitness
goldschmidtWitnessAbsent = mkClassifierGoldschmidtWitness goldschmidt-witness-absent census-witness-absent zero

goldschmidtWitnessPresentZeroGapWithCensus : ClassifierGoldschmidtWitness
goldschmidtWitnessPresentZeroGapWithCensus =
  mkClassifierGoldschmidtWitness goldschmidt-witness-present census-witness-present zero

goldschmidtWitnessPresentWithoutCensus : ClassifierGoldschmidtWitness
goldschmidtWitnessPresentWithoutCensus =
  mkClassifierGoldschmidtWitness goldschmidt-witness-present census-witness-absent zero

goldschmidtWitnessGapFree : ClassifierGoldschmidtWitness → Bool
goldschmidtWitnessGapFree (mkClassifierGoldschmidtWitness goldschmidt-witness-absent _ _) = false
goldschmidtWitnessGapFree (mkClassifierGoldschmidtWitness goldschmidt-witness-present _ n) =
  does (n ℕ-Props.≟ zero)

goldschmidt-witness-present-zero-gap-free :
  goldschmidtWitnessGapFree goldschmidtWitnessPresentZeroGapWithCensus ≡ true
goldschmidt-witness-present-zero-gap-free = refl

------------------------------------------------------------------------
-- Classifier-GOLDSCHMIDT-01 close verdict — fail-closed lattice
------------------------------------------------------------------------

data GoldschmidtConservationVerdict : Set where
  verdict-unwired-ok verdict-goldschmidt-product-admissible-ok
    verdict-goldschmidt-leg-mismatch-refuse verdict-total-claim-refuse
    verdict-proved-without-census-refuse verdict-folklore-list-invent-refuse
    verdict-xor-enum-smuggle-refuse verdict-trivial-no-ore-refuse
    verdict-green-invent-refuse
    : GoldschmidtConservationVerdict

goldschmidtConservationVerdictOk : GoldschmidtConservationVerdict → Bool
goldschmidtConservationVerdictOk verdict-unwired-ok = true
goldschmidtConservationVerdictOk verdict-goldschmidt-product-admissible-ok = true
goldschmidtConservationVerdictOk _ = false

evaluateGoldschmidtConservationClose :
  GoldschmidtConservationModality → ClassifierGoldschmidtStep → ClassifierGoldschmidtWitness → Bool
  → GoldschmidtConservationVerdict
evaluateGoldschmidtConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateGoldschmidtConservationClose goldschmidt-conservation-unwired _ _ false = verdict-unwired-ok
evaluateGoldschmidtConservationClose goldschmidt-conservation-assumed _ _ false = verdict-unwired-ok
evaluateGoldschmidtConservationClose goldschmidt-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateGoldschmidtConservationClose goldschmidt-conservation-proved folklore-list-invent _ false =
  verdict-folklore-list-invent-refuse
evaluateGoldschmidtConservationClose goldschmidt-conservation-proved xor-enum-smuggle _ false =
  verdict-xor-enum-smuggle-refuse
evaluateGoldschmidtConservationClose goldschmidt-conservation-proved (trivial-no-ore-step _) _ false =
  verdict-trivial-no-ore-refuse
evaluateGoldschmidtConservationClose goldschmidt-conservation-proved _ (mkClassifierGoldschmidtWitness goldschmidt-witness-absent _ _) false =
  verdict-total-claim-refuse
evaluateGoldschmidtConservationClose goldschmidt-conservation-proved _ (mkClassifierGoldschmidtWitness goldschmidt-witness-present census-witness-absent _) false =
  verdict-proved-without-census-refuse
evaluateGoldschmidtConservationClose goldschmidt-conservation-proved (goldschmidt-leg-mismatch _ _) _ false =
  verdict-goldschmidt-leg-mismatch-refuse
evaluateGoldschmidtConservationClose goldschmidt-conservation-proved step (mkClassifierGoldschmidtWitness goldschmidt-witness-present census-witness-present _) false
  with isGoldschmidtAdmissible step
... | false = verdict-goldschmidt-leg-mismatch-refuse
... | true  = verdict-goldschmidt-product-admissible-ok

unwired-close-without-witness :
  evaluateGoldschmidtConservationClose
    goldschmidt-conservation-unwired namedGoldschmidtIndirectPath goldschmidtWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

total-claim-refuse-without-witness :
  evaluateGoldschmidtConservationClose
    goldschmidt-conservation-proved namedGoldschmidtIndirectPath goldschmidtWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

proved-without-census-refuse-verdict :
  evaluateGoldschmidtConservationClose
    goldschmidt-conservation-proved namedGoldschmidtIndirectPath goldschmidtWitnessPresentWithoutCensus false ≡
  verdict-proved-without-census-refuse
proved-without-census-refuse-verdict = refl

goldschmidt-leg-mismatch-refuse-verdict :
  evaluateGoldschmidtConservationClose
    goldschmidt-conservation-proved goldschmidtLegMismatchPath goldschmidtWitnessPresentZeroGapWithCensus false ≡
  verdict-goldschmidt-leg-mismatch-refuse
goldschmidt-leg-mismatch-refuse-verdict = refl

folklore-list-invent-refuse-verdict :
  evaluateGoldschmidtConservationClose
    goldschmidt-conservation-proved folkloreListInventStep goldschmidtWitnessPresentZeroGapWithCensus false ≡
  verdict-folklore-list-invent-refuse
folklore-list-invent-refuse-verdict = refl

xor-enum-smuggle-refuse-verdict :
  evaluateGoldschmidtConservationClose
    goldschmidt-conservation-proved xorEnumSmuggleStep goldschmidtWitnessPresentZeroGapWithCensus false ≡
  verdict-xor-enum-smuggle-refuse
xor-enum-smuggle-refuse-verdict = refl

trivial-no-ore-refuse-verdict :
  evaluateGoldschmidtConservationClose
    goldschmidt-conservation-proved trivialNoOreStep goldschmidtWitnessPresentZeroGapWithCensus false ≡
  verdict-trivial-no-ore-refuse
trivial-no-ore-refuse-verdict = refl

goldschmidt-product-admissible-ok :
  evaluateGoldschmidtConservationClose
    goldschmidt-conservation-proved namedGoldschmidtIndirectPath goldschmidtWitnessPresentZeroGapWithCensus false ≡
  verdict-goldschmidt-product-admissible-ok
goldschmidt-product-admissible-ok = refl

green-invent-always-refuse :
  goldschmidtConservationVerdictOk
    (evaluateGoldschmidtConservationClose
       goldschmidt-conservation-unwired namedGoldschmidtIndirectPath goldschmidtWitnessPresentZeroGapWithCensus true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

goldschmidtConservationFiberOk : FormalFiber → Bool
goldschmidtConservationFiberOk fiber-quantum-knowing = true
goldschmidtConservationFiberOk fiber-meso-acting = false

goldschmidt-conservation-knowing-fiber-ok :
  goldschmidtConservationFiberOk fiber-quantum-knowing ≡ true
goldschmidt-conservation-knowing-fiber-ok = refl

goldschmidt-conservation-meso-acting-not-ok :
  goldschmidtConservationFiberOk fiber-meso-acting ≡ false
goldschmidt-conservation-meso-acting-not-ok = refl

------------------------------------------------------------------------
-- Honest pins — not Goldschmidt Proved, not physics GREEN
------------------------------------------------------------------------

goldschmidt-not-proved : goldschmidtProved ≡ false
goldschmidt-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

goldschmidt-second-law-conservation-framed : goldschmidtSecondLawConservationFramed ≡ true
goldschmidt-second-law-conservation-framed = refl

goldschmidt-typed-conservation-framed : goldschmidtTypedConservation ≡ true
goldschmidt-typed-conservation-framed = goldschmidt-typed-conservation-pin

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second GOLDSCHMIDT-01 axiom fork)
------------------------------------------------------------------------

goldschmidtConservationAxiom :
  (goldschmidtProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (goldschmidtSecondLawConservationFramed ≡ true)
  × (goldschmidtTypedConservation ≡ true)
  × (affinityNotXor ≡ true)
  × (classSixSevenSeventeenProduct ≡ true)
  × (evaluateGoldschmidtConservationClose goldschmidt-conservation-unwired namedGoldschmidtIndirectPath goldschmidtWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateGoldschmidtConservationClose goldschmidt-conservation-proved namedGoldschmidtIndirectPath goldschmidtWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateGoldschmidtConservationClose goldschmidt-conservation-proved goldschmidtLegMismatchPath goldschmidtWitnessPresentZeroGapWithCensus false ≡ verdict-goldschmidt-leg-mismatch-refuse)
  × (evaluateGoldschmidtConservationClose goldschmidt-conservation-proved namedGoldschmidtIndirectPath goldschmidtWitnessPresentZeroGapWithCensus false ≡ verdict-goldschmidt-product-admissible-ok)
  × (evaluateGoldschmidtConservationClose goldschmidt-conservation-proved namedGoldschmidtIndirectPath goldschmidtWitnessPresentWithoutCensus false ≡ verdict-proved-without-census-refuse)
  × (evaluateGoldschmidtConservationClose goldschmidt-conservation-proved folkloreListInventStep goldschmidtWitnessPresentZeroGapWithCensus false ≡ verdict-folklore-list-invent-refuse)
  × (evaluateGoldschmidtConservationClose goldschmidt-conservation-proved xorEnumSmuggleStep goldschmidtWitnessPresentZeroGapWithCensus false ≡ verdict-xor-enum-smuggle-refuse)
  × (evaluateGoldschmidtConservationClose goldschmidt-conservation-proved trivialNoOreStep goldschmidtWitnessPresentZeroGapWithCensus false ≡ verdict-trivial-no-ore-refuse)
  × (goldschmidtConservationFiberOk fiber-quantum-knowing ≡ true)
  × (goldschmidtConservationFiberOk fiber-meso-acting ≡ false)
  × (goldschmidtConservationVerdictOk (evaluateGoldschmidtConservationClose goldschmidt-conservation-unwired namedGoldschmidtIndirectPath goldschmidtWitnessPresentZeroGapWithCensus true) ≡ false)
  × (∀ a → isLegCompose (legComposeOp goldschmidtIdentity a) ≡ true)
  × (isGoldschmidtAdmissible goldschmidtLegMismatchPath ≡ false)
  × (goldschmidtLegTarget goldschmidtLegOreToG ≡ goldschmidtLegSource goldschmidtLegGToFo2)
  × (goldschmidtLegSource goldschmidtLegOreToG ≡ goldschmidtLegSource goldschmidtLegOreToProductDirect)
  × (goldschmidtLegTarget goldschmidtLegGToFo2 ≡ goldschmidtLegTarget goldschmidtLegOreToProductDirect)
  × (isLithophile lithophile ≡ true)
  × (isChalcophile chalcophile ≡ true)
  × (isSiderophile siderophile ≡ true)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ copper ≡ 29)
  × (elementAtomicZ silicon ≡ 14)
  × (elementAtomicZ helium ≡ 2)
  × (isClosedShellNoOre helium ≡ true × isOreElement helium ≡ false)
  × (feAssemblageAtomicZ fe-core-siderophile ≡ feAssemblageAtomicZ fe-crust-oxide)
goldschmidtConservationAxiom =
  goldschmidt-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , goldschmidt-second-law-conservation-framed
  , goldschmidt-typed-conservation-framed
  , affinity-not-xor
  , class-six-seven-seventeen-product-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , goldschmidt-leg-mismatch-refuse-verdict
  , goldschmidt-product-admissible-ok
  , proved-without-census-refuse-verdict
  , folklore-list-invent-refuse-verdict
  , xor-enum-smuggle-refuse-verdict
  , trivial-no-ore-refuse-verdict
  , goldschmidt-conservation-knowing-fiber-ok
  , goldschmidt-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , goldschmidt-leg-mismatch-not-admissible
  , goldschmidt-leg-first-composes-levels
  , refl
  , refl
  , (proj₁ lithophile-named)
  , (proj₁ chalcophile-named)
  , (proj₁ siderophile-named)
  , iron-z-26
  , copper-z-29
  , silicon-z-14
  , helium-z-2
  , helium-closed-shell-no-ore
  , (proj₁ fe-same-z-many-assemblages)

goldschmidtConservationNamed : String
goldschmidtConservationNamed =
  "goldschmidtConservation: GOLDSCHMIDT-01 Ore⊗G⊗fO₂ class 6⊗7⊗17 lithophile chalcophile siderophile concurrent product not XOR composed indirect equals direct typed conservation"

goldschmidtConservationCellId : String
goldschmidtConservationCellId = "CHEM-FORMAL-Q-AGDA-GOLDSCHMIDT-CONSERVATION"

goldschmidtConservationNonClaim : String
goldschmidtConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-GOLDSCHMIDT-CONSERVATION GOLDSCHMIDT-01 Ore⊗G⊗fO₂ class 6⊗7⊗17 lithophile chalcophile siderophile concurrent product not XOR composed indirect equals direct typed conservation folklore list invent refuse XOR enum smuggle refuse trivial He closed shell no ore refuse total-claim refuse proved-without-census refuse Fe Z 26 same Z many assemblages Cu Z 29 Si Z 14 He Z 2 goldschmidtProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second GOLDSCHMIDT axiom not physics GREEN not production_wired"

goldschmidt-conservation-modality-unwired :
  goldschmidtConservationModalityCurrent ≡ goldschmidt-conservation-unwired
goldschmidt-conservation-modality-unwired = refl

goldschmidtConservationPhysicsGreenAuthorized : Set
goldschmidtConservationPhysicsGreenAuthorized = ⊥

goldschmidt-conservation-physics-green-false : ¬ goldschmidtConservationPhysicsGreenAuthorized
goldschmidt-conservation-physics-green-false ()

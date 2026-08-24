-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ThermoConservation.agda
--
-- THERMO-01 **Thermo_n** G(T,P,x) **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Four named rungs T → P → x → G hull; order identity conserved
--   * Composed T→P→x→G identity equals T→G direct (typed **conservation**)
--   * CALPHAD hull identity conserved; Green Book **G** named
--   * formation-zero ≠ G; measured-scalar invent refuse
--   * **thermo** leg mismatch / scrambled-order refuse; trivial Z=0 refuse
--   * Total-claim refuse without witness; proved-without-bar refuse
--   * **thermo** laws Unwired (thermoGProved = false)
--
-- Mirrors sibling `ChemConstants/DensityConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- Not Thermo_n Proved. Knowing/quantum fiber — does not mint live Process G.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ThermoConservation where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + THERMO-01 **Thermo_n** G(T,P,x) **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ThermoConservationModality : Set where
  thermo-conservation-unwired thermo-conservation-assumed
    thermo-conservation-proved thermo-conservation-surrogate
    : ThermoConservationModality

thermoConservationModalityCurrent : ThermoConservationModality
thermoConservationModalityCurrent = thermo-conservation-unwired

thermoGProved productionWired not118SquaredGreenTable
  thermoSecondLawConservationFramed thermoTypedConservation : Bool
thermoGProved = false
productionWired = false
not118SquaredGreenTable = true
thermoSecondLawConservationFramed = true
thermoTypedConservation = true

------------------------------------------------------------------------
-- **Thermo** ladder cardinality (structure — not 118²)
------------------------------------------------------------------------

thermoLadderCardinality : ℕ
thermoLadderCardinality = 4

thermo-ladder-cardinality-four : thermoLadderCardinality ≡ 4
thermo-ladder-cardinality-four = refl

thermo-ladder-not-118-squared :
  does (thermoLadderCardinality ℕ-Props.≟ (118 * 118)) ≡ false
thermo-ladder-not-118-squared = refl

------------------------------------------------------------------------
-- Green Book **G** + CALPHAD hull vs formation-zero / measured-scalar pins
------------------------------------------------------------------------

data ThermoGSymbolTag : Set where
  calphad-hull green-book-g formation-zero measured-scalar : ThermoGSymbolTag

isCalphadHull isGreenBookG isFormationZero isMeasuredScalar : ThermoGSymbolTag → Bool
isCalphadHull calphad-hull = true
isCalphadHull _ = false

isGreenBookG green-book-g = true
isGreenBookG _ = false

isFormationZero formation-zero = true
isFormationZero _ = false

isMeasuredScalar measured-scalar = true
isMeasuredScalar _ = false

calphad-hull-named :
  isCalphadHull calphad-hull ≡ true × isGreenBookG calphad-hull ≡ false
calphad-hull-named = refl , refl

green-book-g-named :
  isGreenBookG green-book-g ≡ true × isCalphadHull green-book-g ≡ false
green-book-g-named = refl , refl

formation-zero-not-green-book-g :
  isFormationZero formation-zero ≡ true × isGreenBookG formation-zero ≡ false
formation-zero-not-green-book-g = refl , refl

measured-scalar-not-calphad-hull :
  isMeasuredScalar measured-scalar ≡ true × isCalphadHull measured-scalar ≡ false
measured-scalar-not-calphad-hull = refl , refl

formation-zero-distinct-from-green-book-g : formation-zero ≢ green-book-g
formation-zero-distinct-from-green-book-g ()

measured-scalar-distinct-from-calphad-hull : measured-scalar ≢ calphad-hull
measured-scalar-distinct-from-calphad-hull ()

------------------------------------------------------------------------
-- Named element Z pins — Fe (Z=26), Cu (Z=29), Og (Z=118); trivial Z=0 refuse
------------------------------------------------------------------------

data ElementTag : Set where
  iron copper oganesson vacuum : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ iron = 26
elementAtomicZ copper = 29
elementAtomicZ oganesson = 118
elementAtomicZ vacuum = 0

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

copper-z-29 : elementAtomicZ copper ≡ 29
copper-z-29 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

vacuum-z-0 : elementAtomicZ vacuum ≡ 0
vacuum-z-0 = refl

isTrivialZZero : ElementTag → Bool
isTrivialZZero e = does (elementAtomicZ e ℕ-Props.≟ zero)

trivial-z-zero-refuse-vacuum : isTrivialZZero vacuum ≡ true
trivial-z-zero-refuse-vacuum = refl

trivial-z-zero-not-iron : isTrivialZZero iron ≡ false
trivial-z-zero-not-iron = refl

trivial-z-zero-not-copper : isTrivialZZero copper ≡ false
trivial-z-zero-not-copper = refl

trivial-z-zero-not-oganesson : isTrivialZZero oganesson ≡ false
trivial-z-zero-not-oganesson = refl

------------------------------------------------------------------------
-- **Thermo** level + ladder legs (typed scaffold — Thermo_n G not Proved)
------------------------------------------------------------------------

data ThermoLevel : Set where
  thermo-t thermo-p thermo-x thermo-g-hull : ThermoLevel

data ThermoLadderLeg : Set where
  t-to-p p-to-x x-to-g-hull t-to-g-direct : ThermoLadderLeg

thermoLegSource : ThermoLadderLeg → ThermoLevel
thermoLegSource t-to-p = thermo-t
thermoLegSource p-to-x = thermo-p
thermoLegSource x-to-g-hull = thermo-x
thermoLegSource t-to-g-direct = thermo-t

thermoLegTarget : ThermoLadderLeg → ThermoLevel
thermoLegTarget t-to-p = thermo-p
thermoLegTarget p-to-x = thermo-x
thermoLegTarget x-to-g-hull = thermo-g-hull
thermoLegTarget t-to-g-direct = thermo-g-hull

thermoLegTToP thermoLegPToX thermoLegXToGHull thermoLegTToGDirect : ThermoLadderLeg
thermoLegTToP = t-to-p
thermoLegPToX = p-to-x
thermoLegXToGHull = x-to-g-hull
thermoLegTToGDirect = t-to-g-direct

thermo-leg-t-to-p-named :
  thermoLegTToP ≡ t-to-p
thermo-leg-t-to-p-named = refl

thermo-leg-p-to-x-named :
  thermoLegPToX ≡ p-to-x
thermo-leg-p-to-x-named = refl

thermo-leg-x-to-g-hull-named :
  thermoLegXToGHull ≡ x-to-g-hull
thermo-leg-x-to-g-hull-named = refl

thermo-leg-t-to-g-direct-named :
  thermoLegTToGDirect ≡ t-to-g-direct
thermo-leg-t-to-g-direct-named = refl

thermo-leg-first-composes-levels :
  thermoLegTarget thermoLegTToP ≡ thermoLegSource thermoLegPToX
thermo-leg-first-composes-levels = refl

thermo-leg-second-composes-levels :
  thermoLegTarget thermoLegPToX ≡ thermoLegSource thermoLegXToGHull
thermo-leg-second-composes-levels = refl

thermo-leg-direct-endpoints-match :
  thermoLegSource thermoLegTToP ≡ thermoLegSource thermoLegTToGDirect ×
  thermoLegTarget thermoLegXToGHull ≡ thermoLegTarget thermoLegTToGDirect
thermo-leg-direct-endpoints-match = refl , refl

thermo-leg-t-to-p-source :
  thermoLegSource thermoLegTToP ≡ thermo-t
thermo-leg-t-to-p-source = refl

thermo-leg-x-to-g-hull-target :
  thermoLegTarget thermoLegXToGHull ≡ thermo-g-hull
thermo-leg-x-to-g-hull-target = refl

thermo-leg-distinct-indirect-vs-direct :
  thermoLegTToP ≢ thermoLegTToGDirect
thermo-leg-distinct-indirect-vs-direct ()

------------------------------------------------------------------------
-- Typed **Thermo_n** G(T,P,x) **conservation** — composed indirect equals direct endpoints
------------------------------------------------------------------------

record ThermoGTypedWitness : Set where
  constructor mkThermoGTypedWitness
  field
    indirect-source : ThermoLevel
    indirect-via-a    : ThermoLevel
    indirect-via-b    : ThermoLevel
    indirect-target   : ThermoLevel
    direct-source     : ThermoLevel
    direct-target     : ThermoLevel
    symbol-tag        : ThermoGSymbolTag

thermoGTypedWitnessNamed : ThermoGTypedWitness
thermoGTypedWitnessNamed = record
  { indirect-source = thermo-t
  ; indirect-via-a    = thermo-p
  ; indirect-via-b    = thermo-x
  ; indirect-target   = thermo-g-hull
  ; direct-source     = thermo-t
  ; direct-target     = thermo-g-hull
  ; symbol-tag        = calphad-hull
  }

composed-indirect-identity-equals-direct-typed :
  ThermoGTypedWitness.indirect-source thermoGTypedWitnessNamed ≡
  ThermoGTypedWitness.direct-source thermoGTypedWitnessNamed ×
  ThermoGTypedWitness.indirect-target thermoGTypedWitnessNamed ≡
  ThermoGTypedWitness.direct-target thermoGTypedWitnessNamed ×
  thermoLegTarget thermoLegTToP ≡ thermoLegSource thermoLegPToX ×
  thermoLegTarget thermoLegPToX ≡ thermoLegSource thermoLegXToGHull ×
  thermoLegSource thermoLegTToP ≡ thermoLegSource thermoLegTToGDirect ×
  thermoLegTarget thermoLegXToGHull ≡ thermoLegTarget thermoLegTToGDirect ×
  isCalphadHull (ThermoGTypedWitness.symbol-tag thermoGTypedWitnessNamed) ≡ true
composed-indirect-identity-equals-direct-typed = refl , refl , refl , refl , refl , refl , refl

thermo-typed-conservation-pin : thermoTypedConservation ≡ true
thermo-typed-conservation-pin = refl

------------------------------------------------------------------------
-- ClassifierThermoStep scaffold — **Thermo_n** G(T,P,x) **conservation**
------------------------------------------------------------------------

data ClassifierThermoStep : Set where
  thermo-identity : ClassifierThermoStep
  thermo-leg-leaf : ThermoLadderLeg → ClassifierThermoStep
  leg-compose : ClassifierThermoStep → ClassifierThermoStep → ClassifierThermoStep
  thermo-leg-mismatch : ClassifierThermoStep → ClassifierThermoStep → ClassifierThermoStep
  measured-scalar-invent : ClassifierThermoStep
  formation-zero-as-g : ClassifierThermoStep
  trivial-z-zero-step : ElementTag → ClassifierThermoStep

thermoIdentity : ClassifierThermoStep
thermoIdentity = thermo-identity

legComposeOp thermoMismatchOp :
  ClassifierThermoStep → ClassifierThermoStep → ClassifierThermoStep
legComposeOp = leg-compose
thermoMismatchOp = thermo-leg-mismatch

tToPLeaf pToXLeaf xToGHullLeaf tToGDirectLeaf : ClassifierThermoStep
tToPLeaf = thermo-leg-leaf t-to-p
pToXLeaf = thermo-leg-leaf p-to-x
xToGHullLeaf = thermo-leg-leaf x-to-g-hull
tToGDirectLeaf = thermo-leg-leaf t-to-g-direct

measuredScalarInventStep formationZeroAsGStep : ClassifierThermoStep
measuredScalarInventStep = measured-scalar-invent
formationZeroAsGStep = formation-zero-as-g

trivialZZeroStep : ClassifierThermoStep
trivialZZeroStep = trivial-z-zero-step vacuum

isLegCompose isThermoLeg isThermoIdentity : ClassifierThermoStep → Bool
isLegCompose (leg-compose _ _) = true
isLegCompose _ = false

isThermoLeg (thermo-leg-leaf _) = true
isThermoLeg _ = false

isThermoIdentity thermo-identity = true
isThermoIdentity _ = false

isMeasuredScalarInvent : ClassifierThermoStep → Bool
isMeasuredScalarInvent measured-scalar-invent = true
isMeasuredScalarInvent _ = false

isFormationZeroAsG : ClassifierThermoStep → Bool
isFormationZeroAsG formation-zero-as-g = true
isFormationZeroAsG _ = false

isTrivialZZeroStep : ClassifierThermoStep → Bool
isTrivialZZeroStep (trivial-z-zero-step e) = isTrivialZZero e
isTrivialZZeroStep _ = false

------------------------------------------------------------------------
-- **Thermo** identity conserved at thermo-identity — leg-compose scaffold
------------------------------------------------------------------------

thermo-left-identity :
  ∀ (a : ClassifierThermoStep) →
  isThermoIdentity thermoIdentity ≡ true × isLegCompose (legComposeOp thermoIdentity a) ≡ true
thermo-left-identity a = refl , refl

thermo-right-identity :
  ∀ (a : ClassifierThermoStep) →
  isLegCompose (legComposeOp a thermoIdentity) ≡ true × isThermoIdentity thermoIdentity ≡ true
thermo-right-identity a = refl , refl

thermo-identity-conserved-at-thermo :
  (∀ a → isLegCompose (legComposeOp thermoIdentity a) ≡ true)
  × (∀ a → isLegCompose (legComposeOp a thermoIdentity) ≡ true)
thermo-identity-conserved-at-thermo =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named four-rung **thermo** ladder closed — indirect composed vs direct G
------------------------------------------------------------------------

namedThermoIndirectPath : ClassifierThermoStep
namedThermoIndirectPath =
  legComposeOp (legComposeOp tToPLeaf pToXLeaf) xToGHullLeaf

namedThermoDirectPath : ClassifierThermoStep
namedThermoDirectPath = tToGDirectLeaf

named-thermo-indirect-is-compose :
  isLegCompose namedThermoIndirectPath ≡ true
named-thermo-indirect-is-compose = refl

named-thermo-direct-is-leg :
  isThermoLeg namedThermoDirectPath ≡ true
named-thermo-direct-is-leg = refl

named-thermo-four-rungs-named :
  isThermoLeg tToPLeaf ≡ true
  × isThermoLeg pToXLeaf ≡ true
  × isThermoLeg xToGHullLeaf ≡ true
  × isThermoLeg tToGDirectLeaf ≡ true
named-thermo-four-rungs-named = refl , refl , refl , refl

named-thermo-ladder-closed :
  isLegCompose namedThermoIndirectPath ≡ true
  × isThermoLeg namedThermoDirectPath ≡ true
  × thermoLegTarget thermoLegTToP ≡ thermoLegSource thermoLegPToX
  × thermoLegTarget thermoLegPToX ≡ thermoLegSource thermoLegXToGHull
  × thermoLegSource thermoLegTToP ≡ thermoLegSource thermoLegTToGDirect
  × thermoLegTarget thermoLegXToGHull ≡ thermoLegTarget thermoLegTToGDirect
named-thermo-ladder-closed = refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- **Thermo** leg mismatch / scrambled-order refuse — wrong-order compose fail-closed
------------------------------------------------------------------------

thermoLegMismatchPath : ClassifierThermoStep
thermoLegMismatchPath = thermoMismatchOp pToXLeaf tToPLeaf

isThermoMismatch : ClassifierThermoStep → Bool
isThermoMismatch (thermo-leg-mismatch _ _) = true
isThermoMismatch _ = false

thermo-mismatch-is-mismatch :
  isThermoMismatch thermoLegMismatchPath ≡ true
thermo-mismatch-is-mismatch = refl

thermo-mismatch-not-compose :
  isLegCompose thermoLegMismatchPath ≡ false
thermo-mismatch-not-compose = refl

------------------------------------------------------------------------
-- **Thermo** admissibility — mismatch / measured-scalar / formation-zero / Z=0 refuse
------------------------------------------------------------------------

data ThermoAdmissibility : Set where
  thermo-admissible thermo-leg-mismatch-refuse
    measured-scalar-invent-refuse formation-zero-as-g-refuse
    trivial-z-zero-refuse : ThermoAdmissibility

isThermoPreserving : ClassifierThermoStep → Bool
isThermoPreserving thermo-identity = true
isThermoPreserving (thermo-leg-leaf _) = true
isThermoPreserving (leg-compose a b) =
  isThermoPreserving a ∧ isThermoPreserving b
isThermoPreserving (thermo-leg-mismatch _ _) = false
isThermoPreserving measured-scalar-invent = false
isThermoPreserving formation-zero-as-g = false
isThermoPreserving (trivial-z-zero-step e) =
  not (isTrivialZZero e)

isThermoAdmissible : ClassifierThermoStep → Bool
isThermoAdmissible step = isThermoPreserving step

t-to-p-leaf-admissible : isThermoAdmissible tToPLeaf ≡ true
t-to-p-leaf-admissible = refl

p-to-x-leaf-admissible : isThermoAdmissible pToXLeaf ≡ true
p-to-x-leaf-admissible = refl

x-to-g-hull-leaf-admissible : isThermoAdmissible xToGHullLeaf ≡ true
x-to-g-hull-leaf-admissible = refl

t-to-g-direct-leaf-admissible : isThermoAdmissible tToGDirectLeaf ≡ true
t-to-g-direct-leaf-admissible = refl

named-thermo-indirect-admissible : isThermoAdmissible namedThermoIndirectPath ≡ true
named-thermo-indirect-admissible = refl

named-thermo-direct-admissible : isThermoAdmissible namedThermoDirectPath ≡ true
named-thermo-direct-admissible = refl

thermo-leg-mismatch-not-admissible :
  isThermoAdmissible thermoLegMismatchPath ≡ false
thermo-leg-mismatch-not-admissible = refl

measured-scalar-invent-not-admissible :
  isThermoAdmissible measuredScalarInventStep ≡ false
measured-scalar-invent-not-admissible = refl

formation-zero-as-g-not-admissible :
  isThermoAdmissible formationZeroAsGStep ≡ false
formation-zero-as-g-not-admissible = refl

trivial-z-zero-not-admissible :
  isThermoAdmissible trivialZZeroStep ≡ false
trivial-z-zero-not-admissible = refl

------------------------------------------------------------------------
-- **Thermo** witness — total-claim refuse without witness; proved-without-bar refuse
------------------------------------------------------------------------

data ThermoWitnessPresence : Set where
  thermo-witness-absent thermo-witness-present : ThermoWitnessPresence

data BarWitnessPresence : Set where
  bar-witness-absent bar-witness-present : BarWitnessPresence

record ClassifierThermoWitness : Set where
  constructor mkClassifierThermoWitness
  field
    witness-presence : ThermoWitnessPresence
    bar-presence     : BarWitnessPresence
    thermo-gap-total : ℕ

thermoWitnessAbsent : ClassifierThermoWitness
thermoWitnessAbsent = mkClassifierThermoWitness thermo-witness-absent bar-witness-absent zero

thermoWitnessPresentZeroGapWithBar : ClassifierThermoWitness
thermoWitnessPresentZeroGapWithBar =
  mkClassifierThermoWitness thermo-witness-present bar-witness-present zero

thermoWitnessPresentWithoutBar : ClassifierThermoWitness
thermoWitnessPresentWithoutBar =
  mkClassifierThermoWitness thermo-witness-present bar-witness-absent zero

thermoWitnessPresentWithGaps : ℕ → ClassifierThermoWitness
thermoWitnessPresentWithGaps n =
  mkClassifierThermoWitness thermo-witness-present bar-witness-present n

thermoWitnessGapFree : ClassifierThermoWitness → Bool
thermoWitnessGapFree (mkClassifierThermoWitness thermo-witness-absent _ _) = false
thermoWitnessGapFree (mkClassifierThermoWitness thermo-witness-present _ n) =
  does (n ℕ-Props.≟ zero)

thermo-witness-present-zero-gap-free :
  thermoWitnessGapFree thermoWitnessPresentZeroGapWithBar ≡ true
thermo-witness-present-zero-gap-free = refl

thermo-witness-absent-not-gap-free :
  thermoWitnessGapFree thermoWitnessAbsent ≡ false
thermo-witness-absent-not-gap-free = refl

thermo-witness-with-gaps-not-gap-free :
  ∀ n → thermoWitnessGapFree (thermoWitnessPresentWithGaps (suc n)) ≡ false
thermo-witness-with-gaps-not-gap-free n = refl

thermo-witness-present-without-bar-not-bar :
  ClassifierThermoWitness.bar-presence thermoWitnessPresentWithoutBar ≡ bar-witness-absent
thermo-witness-present-without-bar-not-bar = refl

------------------------------------------------------------------------
-- Classifier-THERMO-01 **thermo** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data ThermoConservationVerdict : Set where
  verdict-unwired-ok verdict-thermo-ladder-admissible-ok
    verdict-thermo-leg-mismatch-refuse verdict-total-claim-refuse
    verdict-proved-without-bar-refuse verdict-measured-scalar-invent-refuse
    verdict-formation-zero-as-g-refuse verdict-trivial-z-zero-refuse
    verdict-green-invent-refuse
    : ThermoConservationVerdict

thermoConservationVerdictOk : ThermoConservationVerdict → Bool
thermoConservationVerdictOk verdict-unwired-ok = true
thermoConservationVerdictOk verdict-thermo-ladder-admissible-ok = true
thermoConservationVerdictOk _ = false

evaluateThermoConservationClose :
  ThermoConservationModality → ClassifierThermoStep → ClassifierThermoWitness → Bool
  → ThermoConservationVerdict
evaluateThermoConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateThermoConservationClose thermo-conservation-unwired _ _ false = verdict-unwired-ok
evaluateThermoConservationClose thermo-conservation-assumed _ _ false = verdict-unwired-ok
evaluateThermoConservationClose thermo-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateThermoConservationClose thermo-conservation-proved measured-scalar-invent _ false =
  verdict-measured-scalar-invent-refuse
evaluateThermoConservationClose thermo-conservation-proved formation-zero-as-g _ false =
  verdict-formation-zero-as-g-refuse
evaluateThermoConservationClose thermo-conservation-proved (trivial-z-zero-step _) _ false =
  verdict-trivial-z-zero-refuse
evaluateThermoConservationClose thermo-conservation-proved _ (mkClassifierThermoWitness thermo-witness-absent _ _) false =
  verdict-total-claim-refuse
evaluateThermoConservationClose thermo-conservation-proved _ (mkClassifierThermoWitness thermo-witness-present bar-witness-absent _) false =
  verdict-proved-without-bar-refuse
evaluateThermoConservationClose thermo-conservation-proved (thermo-leg-mismatch _ _) _ false =
  verdict-thermo-leg-mismatch-refuse
evaluateThermoConservationClose thermo-conservation-proved step (mkClassifierThermoWitness thermo-witness-present bar-witness-present _) false
  with isThermoAdmissible step
... | false = verdict-thermo-leg-mismatch-refuse
... | true  = verdict-thermo-ladder-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without **thermo** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateThermoConservationClose
    thermo-conservation-unwired namedThermoIndirectPath thermoWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateThermoConservationClose
    thermo-conservation-assumed namedThermoIndirectPath thermoWitnessAbsent false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateThermoConservationClose
    thermo-conservation-surrogate namedThermoIndirectPath thermoWitnessAbsent false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose thermo-conservation-unwired namedThermoIndirectPath thermoWitnessAbsent false)
    ≡ true
  × thermoConservationVerdictOk
      (evaluateThermoConservationClose thermo-conservation-assumed namedThermoIndirectPath thermoWitnessAbsent false)
      ≡ true
  × thermoConservationVerdictOk
      (evaluateThermoConservationClose thermo-conservation-surrogate namedThermoIndirectPath thermoWitnessAbsent false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **thermo** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateThermoConservationClose
    thermo-conservation-proved namedThermoIndirectPath thermoWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-proved namedThermoIndirectPath thermoWitnessAbsent false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateThermoConservationClose
    thermo-conservation-proved namedThermoIndirectPath thermoWitnessAbsent false ≡
  verdict-thermo-ladder-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- Proved-without-bar refuse — witness present but bar absent
------------------------------------------------------------------------

proved-without-bar-refuse-verdict :
  evaluateThermoConservationClose
    thermo-conservation-proved namedThermoIndirectPath thermoWitnessPresentWithoutBar false ≡
  verdict-proved-without-bar-refuse
proved-without-bar-refuse-verdict = refl

proved-without-bar-refuse-not-ok :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-proved namedThermoIndirectPath thermoWitnessPresentWithoutBar false)
    ≡ false
proved-without-bar-refuse-not-ok = refl

ProvedWithoutBarWhenIndirectOk : Set
ProvedWithoutBarWhenIndirectOk =
  evaluateThermoConservationClose
    thermo-conservation-proved namedThermoIndirectPath thermoWitnessPresentWithoutBar false ≡
  verdict-thermo-ladder-admissible-ok

proved-without-bar-⊥-when-indirect-ok : ProvedWithoutBarWhenIndirectOk → ⊥
proved-without-bar-⊥-when-indirect-ok ()

------------------------------------------------------------------------
-- **Thermo** leg mismatch refuse — scrambled-order compose fail-closed
------------------------------------------------------------------------

thermo-leg-mismatch-refuse-verdict :
  evaluateThermoConservationClose
    thermo-conservation-proved thermoLegMismatchPath thermoWitnessPresentZeroGapWithBar false ≡
  verdict-thermo-leg-mismatch-refuse
thermo-leg-mismatch-refuse-verdict = refl

thermo-leg-mismatch-refuse-not-ok :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-proved thermoLegMismatchPath thermoWitnessPresentZeroGapWithBar false)
    ≡ false
thermo-leg-mismatch-refuse-not-ok = refl

ThermoMismatchWhenIndirectOk : Set
ThermoMismatchWhenIndirectOk =
  evaluateThermoConservationClose
    thermo-conservation-proved thermoLegMismatchPath thermoWitnessPresentZeroGapWithBar false ≡
  verdict-thermo-ladder-admissible-ok

thermo-mismatch-⊥-when-indirect-ok : ThermoMismatchWhenIndirectOk → ⊥
thermo-mismatch-⊥-when-indirect-ok ()

------------------------------------------------------------------------
-- Measured-scalar invent refuse — not CALPHAD hull G
------------------------------------------------------------------------

measured-scalar-invent-refuse-verdict :
  evaluateThermoConservationClose
    thermo-conservation-proved measuredScalarInventStep thermoWitnessPresentZeroGapWithBar false ≡
  verdict-measured-scalar-invent-refuse
measured-scalar-invent-refuse-verdict = refl

measured-scalar-invent-refuse-not-ok :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-proved measuredScalarInventStep thermoWitnessPresentZeroGapWithBar false)
    ≡ false
measured-scalar-invent-refuse-not-ok = refl

------------------------------------------------------------------------
-- Formation-zero as G refuse — formation-zero ≠ Green Book G
------------------------------------------------------------------------

formation-zero-as-g-refuse-verdict :
  evaluateThermoConservationClose
    thermo-conservation-proved formationZeroAsGStep thermoWitnessPresentZeroGapWithBar false ≡
  verdict-formation-zero-as-g-refuse
formation-zero-as-g-refuse-verdict = refl

formation-zero-as-g-refuse-not-ok :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-proved formationZeroAsGStep thermoWitnessPresentZeroGapWithBar false)
    ≡ false
formation-zero-as-g-refuse-not-ok = refl

------------------------------------------------------------------------
-- Trivial Z=0 refuse — vacuum element not admissible
------------------------------------------------------------------------

trivial-z-zero-refuse-verdict :
  evaluateThermoConservationClose
    thermo-conservation-proved trivialZZeroStep thermoWitnessPresentZeroGapWithBar false ≡
  verdict-trivial-z-zero-refuse
trivial-z-zero-refuse-verdict = refl

trivial-z-zero-refuse-not-ok :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-proved trivialZZeroStep thermoWitnessPresentZeroGapWithBar false)
    ≡ false
trivial-z-zero-refuse-not-ok = refl

------------------------------------------------------------------------
-- Admissible classifier-**thermo** — witness present + bar + typed ladder closed
------------------------------------------------------------------------

thermo-ladder-admissible-ok :
  evaluateThermoConservationClose
    thermo-conservation-proved namedThermoIndirectPath thermoWitnessPresentZeroGapWithBar false ≡
  verdict-thermo-ladder-admissible-ok
thermo-ladder-admissible-ok = refl

thermo-ladder-admissible-verdict-ok :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-proved namedThermoIndirectPath thermoWitnessPresentZeroGapWithBar false)
    ≡ true
thermo-ladder-admissible-verdict-ok = refl

thermo-ladder-admissible-ok-still-not-thermo-g-proved :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-proved namedThermoIndirectPath thermoWitnessPresentZeroGapWithBar false)
    ≡ true
  × thermoGProved ≡ false
thermo-ladder-admissible-ok-still-not-thermo-g-proved =
  thermo-ladder-admissible-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateThermoConservationClose
    thermo-conservation-unwired namedThermoIndirectPath thermoWitnessPresentZeroGapWithBar true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  thermoConservationVerdictOk
    (evaluateThermoConservationClose
       thermo-conservation-unwired namedThermoIndirectPath thermoWitnessPresentZeroGapWithBar true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting; no live Process G
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

thermoConservationFiberOk : FormalFiber → Bool
thermoConservationFiberOk fiber-quantum-knowing = true
thermoConservationFiberOk fiber-meso-acting = false

thermo-conservation-knowing-fiber-ok :
  thermoConservationFiberOk fiber-quantum-knowing ≡ true
thermo-conservation-knowing-fiber-ok = refl

thermo-conservation-meso-acting-not-ok :
  thermoConservationFiberOk fiber-meso-acting ≡ false
thermo-conservation-meso-acting-not-ok = refl

thermo-conservation-routes-knowing-not-meso :
  thermoConservationFiberOk fiber-quantum-knowing ≡ true ×
  thermoConservationFiberOk fiber-meso-acting ≡ false
thermo-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  thermoConservationFiberOk fiber-quantum-knowing ∧
  not (thermoConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not Thermo_n Proved, not physics GREEN, not live Process G
------------------------------------------------------------------------

thermo-g-not-proved : thermoGProved ≡ false
thermo-g-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

thermo-second-law-conservation-framed : thermoSecondLawConservationFramed ≡ true
thermo-second-law-conservation-framed = refl

thermo-typed-conservation-framed : thermoTypedConservation ≡ true
thermo-typed-conservation-framed = thermo-typed-conservation-pin

greenBookGSymbol : String
greenBookGSymbol = "G"

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second THERMO-01 axiom fork)
------------------------------------------------------------------------

thermoConservationAxiom :
  (thermoGProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (thermoSecondLawConservationFramed ≡ true)
  × (thermoTypedConservation ≡ true)
  × (evaluateThermoConservationClose thermo-conservation-unwired namedThermoIndirectPath thermoWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateThermoConservationClose thermo-conservation-proved namedThermoIndirectPath thermoWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateThermoConservationClose thermo-conservation-proved thermoLegMismatchPath thermoWitnessPresentZeroGapWithBar false ≡ verdict-thermo-leg-mismatch-refuse)
  × (evaluateThermoConservationClose thermo-conservation-proved namedThermoIndirectPath thermoWitnessPresentZeroGapWithBar false ≡ verdict-thermo-ladder-admissible-ok)
  × (evaluateThermoConservationClose thermo-conservation-proved namedThermoIndirectPath thermoWitnessPresentWithoutBar false ≡ verdict-proved-without-bar-refuse)
  × (evaluateThermoConservationClose thermo-conservation-proved measuredScalarInventStep thermoWitnessPresentZeroGapWithBar false ≡ verdict-measured-scalar-invent-refuse)
  × (evaluateThermoConservationClose thermo-conservation-proved formationZeroAsGStep thermoWitnessPresentZeroGapWithBar false ≡ verdict-formation-zero-as-g-refuse)
  × (evaluateThermoConservationClose thermo-conservation-proved trivialZZeroStep thermoWitnessPresentZeroGapWithBar false ≡ verdict-trivial-z-zero-refuse)
  × (thermoConservationFiberOk fiber-quantum-knowing ≡ true)
  × (thermoConservationFiberOk fiber-meso-acting ≡ false)
  × (thermoConservationVerdictOk (evaluateThermoConservationClose thermo-conservation-unwired namedThermoIndirectPath thermoWitnessPresentZeroGapWithBar true) ≡ false)
  × (∀ a → isLegCompose (legComposeOp thermoIdentity a) ≡ true)
  × (∀ a → isLegCompose (legComposeOp a thermoIdentity) ≡ true)
  × (isThermoAdmissible thermoLegMismatchPath ≡ false)
  × (thermoLegTarget thermoLegTToP ≡ thermoLegSource thermoLegPToX)
  × (thermoLegTarget thermoLegPToX ≡ thermoLegSource thermoLegXToGHull)
  × (thermoLegSource thermoLegTToP ≡ thermoLegSource thermoLegTToGDirect)
  × (thermoLegTarget thermoLegXToGHull ≡ thermoLegTarget thermoLegTToGDirect)
  × (isCalphadHull calphad-hull ≡ true)
  × (isFormationZero formation-zero ≡ true × isGreenBookG formation-zero ≡ false)
  × (isMeasuredScalar measured-scalar ≡ true × isCalphadHull measured-scalar ≡ false)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ copper ≡ 29)
  × (elementAtomicZ oganesson ≡ 118)
  × (isTrivialZZero vacuum ≡ true)
thermoConservationAxiom =
  thermo-g-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , thermo-second-law-conservation-framed
  , thermo-typed-conservation-framed
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , thermo-leg-mismatch-refuse-verdict
  , thermo-ladder-admissible-ok
  , proved-without-bar-refuse-verdict
  , measured-scalar-invent-refuse-verdict
  , formation-zero-as-g-refuse-verdict
  , trivial-z-zero-refuse-verdict
  , thermo-conservation-knowing-fiber-ok
  , thermo-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , thermo-leg-mismatch-not-admissible
  , thermo-leg-first-composes-levels
  , thermo-leg-second-composes-levels
  , refl
  , refl
  , (proj₁ calphad-hull-named)
  , formation-zero-not-green-book-g
  , measured-scalar-not-calphad-hull
  , iron-z-26
  , copper-z-29
  , oganesson-z-118
  , trivial-z-zero-refuse-vacuum

thermoConservationNamed : String
thermoConservationNamed =
  "thermoConservation: THERMO-01 Thermo_n G(T,P,x) CALPHAD hull four rungs T P x G composed indirect equals direct typed conservation"

thermoConservationCellId : String
thermoConservationCellId = "CHEM-FORMAL-Q-AGDA-THERMO-CONSERVATION"

thermoConservationNonClaim : String
thermoConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-THERMO-CONSERVATION THERMO-01 Thermo_n G(T,P,x) CALPHAD hull conservation four rungs T P x G composed indirect equals direct typed conservation thermo leg mismatch refuse scrambled order refuse total-claim refuse proved-without-bar refuse measured-scalar invent refuse formation-zero not G trivial Z=0 refuse thermoGProved false Green Book G not 118 squared GREEN table geometry knowing quantum fiber not meso acting not live Process G Unwired one axiom second law conservation not second THERMO axiom not physics GREEN not production_wired distinct from occupancy Z identity"

thermo-conservation-modality-unwired :
  thermoConservationModalityCurrent ≡ thermo-conservation-unwired
thermo-conservation-modality-unwired = refl

thermoConservationPhysicsGreenAuthorized : Set
thermoConservationPhysicsGreenAuthorized = ⊥

thermo-conservation-physics-green-false : ¬ thermoConservationPhysicsGreenAuthorized
thermo-conservation-physics-green-false ()

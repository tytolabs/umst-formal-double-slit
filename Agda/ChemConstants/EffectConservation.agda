-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.EffectConservation.agda
--
-- TYPE-04 dissipative effect conservation on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Forward Refine requires positive ChemStamp/Landauer witness
--   * Free purification refuse; reverse contaminate typed
--   * effect laws Unwired (type04EffectProved = false)
--
-- Mirrors sibling `ChemConstants/ModalityConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + conservation framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.EffectConservation where

open import Data.Bool.Base using (Bool; false; true; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + TYPE-04 effect conservation pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data EffectConservationModality : Set where
  effect-conservation-unwired effect-conservation-assumed
    effect-conservation-proved effect-conservation-surrogate
    : EffectConservationModality

effectConservationModalityCurrent : EffectConservationModality
effectConservationModalityCurrent = effect-conservation-unwired

type04EffectProved productionWired not118SquaredGreenTable
  effectSecondLawConservationFramed : Bool
type04EffectProved = false
productionWired = false
not118SquaredGreenTable = true
effectSecondLawConservationFramed = true

------------------------------------------------------------------------
-- Dissipative effect law lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

effectLawLatticeCardinality : ℕ
effectLawLatticeCardinality = 4

effect-law-lattice-cardinality-four : effectLawLatticeCardinality ≡ 4
effect-law-lattice-cardinality-four = refl

effect-law-lattice-not-118-squared :
  does (effectLawLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
effect-law-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- Refine direction — forward refine vs reverse contaminate typed
------------------------------------------------------------------------

data RefineDirection : Set where
  forward-refine reverse-contaminate : RefineDirection

forward-refine-requires-dissipation : RefineDirection → Bool
forward-refine-requires-dissipation forward-refine = true
forward-refine-requires-dissipation reverse-contaminate = false

forward-refine-requires-dissipation-true :
  forward-refine-requires-dissipation forward-refine ≡ true
forward-refine-requires-dissipation-true = refl

reverse-contaminate-no-forward-cost :
  forward-refine-requires-dissipation reverse-contaminate ≡ false
reverse-contaminate-no-forward-cost = refl

------------------------------------------------------------------------
-- ChemStamp / Landauer dissipation witness — forward Refine gate
------------------------------------------------------------------------

record ChemStampLandauerWitness : Set where
  constructor mkChemStampLandauerWitness
  field
    dissipationMicrojoules landauerScaffold : ℕ

chemStampLandauerWitnessZero : ChemStampLandauerWitness
chemStampLandauerWitnessZero = mkChemStampLandauerWitness zero zero

chemStampLandauerWitnessPositive : ChemStampLandauerWitness
chemStampLandauerWitnessPositive = mkChemStampLandauerWitness (suc zero) (suc zero)

witnessDissipationPositive : ℕ → Bool
witnessDissipationPositive zero = false
witnessDissipationPositive (suc _) = true

chemStampLandauerWitnessPositiveOk : ChemStampLandauerWitness → Bool
chemStampLandauerWitnessPositiveOk w =
  witnessDissipationPositive (ChemStampLandauerWitness.dissipationMicrojoules w)
  ∧ witnessDissipationPositive (ChemStampLandauerWitness.landauerScaffold w)

chem-stamp-landauer-zero-not-positive :
  chemStampLandauerWitnessPositiveOk chemStampLandauerWitnessZero ≡ false
chem-stamp-landauer-zero-not-positive = refl

chem-stamp-landauer-positive-witness-ok :
  chemStampLandauerWitnessPositiveOk chemStampLandauerWitnessPositive ≡ true
chem-stamp-landauer-positive-witness-ok = refl

------------------------------------------------------------------------
-- Effect close verdict — fail-closed lattice
------------------------------------------------------------------------

data EffectConservationVerdict : Set where
  verdict-unwired-ok verdict-forward-dissipative-ok
    verdict-free-purification-refuse verdict-reverse-contaminate-ok
    verdict-green-invent-refuse
    : EffectConservationVerdict

effectConservationVerdictOk : EffectConservationVerdict → Bool
effectConservationVerdictOk verdict-unwired-ok = true
effectConservationVerdictOk verdict-forward-dissipative-ok = true
effectConservationVerdictOk verdict-reverse-contaminate-ok = true
effectConservationVerdictOk _ = false

evaluateEffectConservationClose :
  EffectConservationModality → RefineDirection → ChemStampLandauerWitness → Bool
  → EffectConservationVerdict
evaluateEffectConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateEffectConservationClose effect-conservation-unwired _ _ false = verdict-unwired-ok
evaluateEffectConservationClose effect-conservation-assumed _ _ false = verdict-unwired-ok
evaluateEffectConservationClose effect-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateEffectConservationClose effect-conservation-proved forward-refine w false
  with chemStampLandauerWitnessPositiveOk w
... | true = verdict-forward-dissipative-ok
... | false = verdict-free-purification-refuse
evaluateEffectConservationClose effect-conservation-proved reverse-contaminate _ false =
  verdict-reverse-contaminate-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without forward witness census
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateEffectConservationClose
    effect-conservation-unwired forward-refine chemStampLandauerWitnessZero false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateEffectConservationClose
    effect-conservation-assumed forward-refine chemStampLandauerWitnessZero false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateEffectConservationClose
    effect-conservation-surrogate forward-refine chemStampLandauerWitnessZero false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  effectConservationVerdictOk
    (evaluateEffectConservationClose effect-conservation-unwired forward-refine chemStampLandauerWitnessZero false)
    ≡ true
  × effectConservationVerdictOk
      (evaluateEffectConservationClose effect-conservation-assumed forward-refine chemStampLandauerWitnessZero false)
      ≡ true
  × effectConservationVerdictOk
      (evaluateEffectConservationClose effect-conservation-surrogate forward-refine chemStampLandauerWitnessZero false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Forward Refine — positive ChemStamp/Landauer witness required
------------------------------------------------------------------------

forward-refine-positive-witness-ok :
  evaluateEffectConservationClose
    effect-conservation-proved forward-refine chemStampLandauerWitnessPositive false ≡
  verdict-forward-dissipative-ok
forward-refine-positive-witness-ok = refl

forward-refine-positive-witness-verdict-ok :
  effectConservationVerdictOk
    (evaluateEffectConservationClose
       effect-conservation-proved forward-refine chemStampLandauerWitnessPositive false)
    ≡ true
forward-refine-positive-witness-verdict-ok = refl

------------------------------------------------------------------------
-- Free purification refuse — zero witness on forward Refine
------------------------------------------------------------------------

free-purification-refuse-zero-witness :
  evaluateEffectConservationClose
    effect-conservation-proved forward-refine chemStampLandauerWitnessZero false ≡
  verdict-free-purification-refuse
free-purification-refuse-zero-witness = refl

free-purification-refuse-not-ok :
  effectConservationVerdictOk
    (evaluateEffectConservationClose
       effect-conservation-proved forward-refine chemStampLandauerWitnessZero false)
    ≡ false
free-purification-refuse-not-ok = refl

FreePurificationWhenZeroWitness : Set
FreePurificationWhenZeroWitness =
  evaluateEffectConservationClose
    effect-conservation-proved forward-refine chemStampLandauerWitnessZero false ≡
  verdict-forward-dissipative-ok

free-purification-⊥-when-zero-witness : FreePurificationWhenZeroWitness → ⊥
free-purification-⊥-when-zero-witness ()

------------------------------------------------------------------------
-- Reverse contaminate typed — allowed without positive forward cost
------------------------------------------------------------------------

reverse-contaminate-typed-zero-witness :
  evaluateEffectConservationClose
    effect-conservation-proved reverse-contaminate chemStampLandauerWitnessZero false ≡
  verdict-reverse-contaminate-ok
reverse-contaminate-typed-zero-witness = refl

reverse-contaminate-typed-verdict-ok :
  effectConservationVerdictOk
    (evaluateEffectConservationClose
       effect-conservation-proved reverse-contaminate chemStampLandauerWitnessZero false)
    ≡ true
reverse-contaminate-typed-verdict-ok = refl

forward-dissipative-ok-still-not-type04-proved :
  effectConservationVerdictOk
    (evaluateEffectConservationClose
       effect-conservation-proved forward-refine chemStampLandauerWitnessPositive false)
    ≡ true
  × type04EffectProved ≡ false
forward-dissipative-ok-still-not-type04-proved = forward-refine-positive-witness-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateEffectConservationClose
    effect-conservation-unwired forward-refine chemStampLandauerWitnessPositive true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  effectConservationVerdictOk
    (evaluateEffectConservationClose
       effect-conservation-unwired forward-refine chemStampLandauerWitnessPositive true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

effectConservationFiberOk : FormalFiber → Bool
effectConservationFiberOk fiber-quantum-knowing = true
effectConservationFiberOk fiber-meso-acting = false

effect-conservation-knowing-fiber-ok :
  effectConservationFiberOk fiber-quantum-knowing ≡ true
effect-conservation-knowing-fiber-ok = refl

effect-conservation-meso-acting-not-ok :
  effectConservationFiberOk fiber-meso-acting ≡ false
effect-conservation-meso-acting-not-ok = refl

effect-conservation-routes-knowing-not-meso :
  effectConservationFiberOk fiber-quantum-knowing ≡ true ×
  effectConservationFiberOk fiber-meso-acting ≡ false
effect-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  effectConservationFiberOk fiber-quantum-knowing ∧
  not (effectConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not TYPE-04 Proved, not physics GREEN
------------------------------------------------------------------------

type04-effect-not-proved : type04EffectProved ≡ false
type04-effect-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

effect-second-law-conservation-framed : effectSecondLawConservationFramed ≡ true
effect-second-law-conservation-framed = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second effect axiom fork)
------------------------------------------------------------------------

effectConservationAxiom :
  (type04EffectProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (effectSecondLawConservationFramed ≡ true)
  × (evaluateEffectConservationClose effect-conservation-unwired forward-refine chemStampLandauerWitnessZero false ≡ verdict-unwired-ok)
  × (evaluateEffectConservationClose effect-conservation-proved forward-refine chemStampLandauerWitnessZero false ≡ verdict-free-purification-refuse)
  × (evaluateEffectConservationClose effect-conservation-proved forward-refine chemStampLandauerWitnessPositive false ≡ verdict-forward-dissipative-ok)
  × (evaluateEffectConservationClose effect-conservation-proved reverse-contaminate chemStampLandauerWitnessZero false ≡ verdict-reverse-contaminate-ok)
  × (effectConservationFiberOk fiber-quantum-knowing ≡ true)
  × (effectConservationFiberOk fiber-meso-acting ≡ false)
  × (effectConservationVerdictOk (evaluateEffectConservationClose effect-conservation-unwired forward-refine chemStampLandauerWitnessPositive true) ≡ false)
effectConservationAxiom =
  type04-effect-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , effect-second-law-conservation-framed
  , unwired-close-without-witness
  , free-purification-refuse-zero-witness
  , forward-refine-positive-witness-ok
  , reverse-contaminate-typed-zero-witness
  , effect-conservation-knowing-fiber-ok
  , effect-conservation-meso-acting-not-ok
  , green-invent-always-refuse

effectConservationNamed : String
effectConservationNamed =
  "effectConservation: TYPE-04 dissipative effect forward Refine ChemStamp Landauer witness conservation"

effectConservationCellId : String
effectConservationCellId = "CHEM-FORMAL-Q-AGDA-EFFECT-CONSERVATION"

effectConservationNonClaim : String
effectConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-EFFECT-CONSERVATION TYPE-04 dissipative effect conservation forward Refine requires positive ChemStamp Landauer witness free purification refuse reverse contaminate typed type04EffectProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second effect axiom not physics GREEN not production_wired"

effect-conservation-modality-unwired :
  effectConservationModalityCurrent ≡ effect-conservation-unwired
effect-conservation-modality-unwired = refl

effectConservationPhysicsGreenAuthorized : Set
effectConservationPhysicsGreenAuthorized = ⊥

effect-conservation-physics-green-false : ¬ effectConservationPhysicsGreenAuthorized
effect-conservation-physics-green-false ()

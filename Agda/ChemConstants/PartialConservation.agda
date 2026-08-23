-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PartialConservation.agda
--
-- TYPE-05 **partial** Interact **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Interact is **partial**: admissible vs forbidden InteractStep scaffold
--   * Total-claim refuse without **partial** witness; forbidden interact refuse
--   * **partial** laws Unwired (type05PartialProved = false)
--
-- Mirrors sibling `ChemConstants/EffectConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.PartialConservation where

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
-- Modality + TYPE-05 **partial** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PartialConservationModality : Set where
  partial-conservation-unwired partial-conservation-assumed
    partial-conservation-proved partial-conservation-surrogate
    : PartialConservationModality

partialConservationModalityCurrent : PartialConservationModality
partialConservationModalityCurrent = partial-conservation-unwired

type05PartialProved productionWired not118SquaredGreenTable
  partialSecondLawConservationFramed : Bool
type05PartialProved = false
productionWired = false
not118SquaredGreenTable = true
partialSecondLawConservationFramed = true

------------------------------------------------------------------------
-- **Partial** law lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

partialLawLatticeCardinality : ℕ
partialLawLatticeCardinality = 4

partial-law-lattice-cardinality-four : partialLawLatticeCardinality ≡ 4
partial-law-lattice-cardinality-four = refl

partial-law-lattice-not-118-squared :
  does (partialLawLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
partial-law-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- InteractStep scaffold — **partial** admissible vs forbidden
------------------------------------------------------------------------

data InteractTag : Set where
  hematite-dominant bauxite-dominant calcareous-gangue : InteractTag

data InteractStep : Set where
  identity : InteractStep
  atomic : InteractTag → InteractStep
  compose : InteractStep → InteractStep → InteractStep

interactIdentity : InteractStep
interactIdentity = identity

interactCompose : InteractStep → InteractStep → InteractStep
interactCompose = compose

hematiteStep bauxiteStep calcareousStep : InteractStep
hematiteStep = atomic hematite-dominant
bauxiteStep = atomic bauxite-dominant
calcareousStep = atomic calcareous-gangue

isCompose : InteractStep → Bool
isCompose (compose _ _) = true
isCompose _ = false

isIdentity : InteractStep → Bool
isIdentity identity = true
isIdentity _ = false

------------------------------------------------------------------------
-- **Partial** interact admissibility — admissible vs forbidden
------------------------------------------------------------------------

data InteractAdmissibility : Set where
  interact-admissible interact-forbidden : InteractAdmissibility

isInteractAdmissible : InteractStep → Bool
isInteractAdmissible identity = true
isInteractAdmissible (atomic hematite-dominant) = true
isInteractAdmissible (atomic bauxite-dominant) = true
isInteractAdmissible (atomic calcareous-gangue) = false
isInteractAdmissible (compose a b) =
  isInteractAdmissible a ∧ isInteractAdmissible b

hematite-step-admissible : isInteractAdmissible hematiteStep ≡ true
hematite-step-admissible = refl

bauxite-step-admissible : isInteractAdmissible bauxiteStep ≡ true
bauxite-step-admissible = refl

calcareous-step-forbidden : isInteractAdmissible calcareousStep ≡ false
calcareous-step-forbidden = refl

forbidden-compose-refuse :
  isInteractAdmissible (interactCompose hematiteStep calcareousStep) ≡ false
forbidden-compose-refuse = refl

left-identity-scaffold :
  ∀ (a : InteractStep) → isIdentity interactIdentity ≡ true × isCompose (interactCompose interactIdentity a) ≡ true
left-identity-scaffold a = refl , refl

------------------------------------------------------------------------
-- **Partial** witness — total-claim refuse without witness
------------------------------------------------------------------------

data PartialWitnessPresence : Set where
  partial-witness-absent partial-witness-present : PartialWitnessPresence

record PartialInteractWitness : Set where
  constructor mkPartialInteractWitness
  field
    witness-presence : PartialWitnessPresence
    forbidden-gap-total : ℕ

partialWitnessAbsent : PartialInteractWitness
partialWitnessAbsent = mkPartialInteractWitness partial-witness-absent zero

partialWitnessPresentZeroGap : PartialInteractWitness
partialWitnessPresentZeroGap = mkPartialInteractWitness partial-witness-present zero

partialWitnessPresentWithGaps : ℕ → PartialInteractWitness
partialWitnessPresentWithGaps n = mkPartialInteractWitness partial-witness-present n

partialWitnessGapFree : PartialInteractWitness → Bool
partialWitnessGapFree (mkPartialInteractWitness partial-witness-absent _) = false
partialWitnessGapFree (mkPartialInteractWitness partial-witness-present n) =
  does (n ℕ-Props.≟ zero)

partial-witness-present-zero-gap-free :
  partialWitnessGapFree partialWitnessPresentZeroGap ≡ true
partial-witness-present-zero-gap-free = refl

partial-witness-absent-not-gap-free :
  partialWitnessGapFree partialWitnessAbsent ≡ false
partial-witness-absent-not-gap-free = refl

partial-witness-with-gaps-not-gap-free :
  ∀ n → partialWitnessGapFree (partialWitnessPresentWithGaps (suc n)) ≡ false
partial-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- **Partial** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PartialConservationVerdict : Set where
  verdict-unwired-ok verdict-partial-admissible-ok
    verdict-total-claim-refuse verdict-forbidden-interact-refuse
    verdict-green-invent-refuse
    : PartialConservationVerdict

partialConservationVerdictOk : PartialConservationVerdict → Bool
partialConservationVerdictOk verdict-unwired-ok = true
partialConservationVerdictOk verdict-partial-admissible-ok = true
partialConservationVerdictOk _ = false

evaluatePartialConservationClose :
  PartialConservationModality → InteractStep → PartialInteractWitness → Bool
  → PartialConservationVerdict
evaluatePartialConservationClose _ _ _ true = verdict-green-invent-refuse
evaluatePartialConservationClose partial-conservation-unwired _ _ false = verdict-unwired-ok
evaluatePartialConservationClose partial-conservation-assumed _ _ false = verdict-unwired-ok
evaluatePartialConservationClose partial-conservation-surrogate _ _ false = verdict-unwired-ok
evaluatePartialConservationClose partial-conservation-proved step (mkPartialInteractWitness partial-witness-absent _) false =
  verdict-total-claim-refuse
evaluatePartialConservationClose partial-conservation-proved step (mkPartialInteractWitness partial-witness-present _) false
  with isInteractAdmissible step
... | false = verdict-forbidden-interact-refuse
... | true  = verdict-partial-admissible-ok

------------------------------------------------------------------------
-- Sample admissible InteractStep scaffold
------------------------------------------------------------------------

forward-refine-step : InteractStep
forward-refine-step = interactCompose hematiteStep bauxiteStep

forward-refine-step-admissible : isInteractAdmissible forward-refine-step ≡ true
forward-refine-step-admissible = refl

------------------------------------------------------------------------
-- Unwired close — design scaffold without **partial** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePartialConservationClose
    partial-conservation-unwired forward-refine-step partialWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePartialConservationClose
    partial-conservation-assumed forward-refine-step partialWitnessAbsent false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePartialConservationClose
    partial-conservation-surrogate forward-refine-step partialWitnessAbsent false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  partialConservationVerdictOk
    (evaluatePartialConservationClose partial-conservation-unwired forward-refine-step partialWitnessAbsent false)
    ≡ true
  × partialConservationVerdictOk
      (evaluatePartialConservationClose partial-conservation-assumed forward-refine-step partialWitnessAbsent false)
      ≡ true
  × partialConservationVerdictOk
      (evaluatePartialConservationClose partial-conservation-surrogate forward-refine-step partialWitnessAbsent false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **partial** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePartialConservationClose
    partial-conservation-proved forward-refine-step partialWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  partialConservationVerdictOk
    (evaluatePartialConservationClose
       partial-conservation-proved forward-refine-step partialWitnessAbsent false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluatePartialConservationClose
    partial-conservation-proved forward-refine-step partialWitnessAbsent false ≡
  verdict-partial-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- Forbidden interact refuse — **partial** admissible vs forbidden
------------------------------------------------------------------------

forbidden-interact-refuse-calcareous :
  evaluatePartialConservationClose
    partial-conservation-proved calcareousStep partialWitnessPresentZeroGap false ≡
  verdict-forbidden-interact-refuse
forbidden-interact-refuse-calcareous = refl

forbidden-interact-refuse-not-ok :
  partialConservationVerdictOk
    (evaluatePartialConservationClose
       partial-conservation-proved calcareousStep partialWitnessPresentZeroGap false)
    ≡ false
forbidden-interact-refuse-not-ok = refl

ForbiddenInteractWhenCalcareous : Set
ForbiddenInteractWhenCalcareous =
  evaluatePartialConservationClose
    partial-conservation-proved calcareousStep partialWitnessPresentZeroGap false ≡
  verdict-partial-admissible-ok

forbidden-interact-⊥-when-calcareous : ForbiddenInteractWhenCalcareous → ⊥
forbidden-interact-⊥-when-calcareous ()

------------------------------------------------------------------------
-- **Partial** admissible interact — witness present + admissible step
------------------------------------------------------------------------

partial-admissible-interact-ok :
  evaluatePartialConservationClose
    partial-conservation-proved forward-refine-step partialWitnessPresentZeroGap false ≡
  verdict-partial-admissible-ok
partial-admissible-interact-ok = refl

partial-admissible-interact-verdict-ok :
  partialConservationVerdictOk
    (evaluatePartialConservationClose
       partial-conservation-proved forward-refine-step partialWitnessPresentZeroGap false)
    ≡ true
partial-admissible-interact-verdict-ok = refl

partial-admissible-ok-still-not-type05-proved :
  partialConservationVerdictOk
    (evaluatePartialConservationClose
       partial-conservation-proved forward-refine-step partialWitnessPresentZeroGap false)
    ≡ true
  × type05PartialProved ≡ false
partial-admissible-ok-still-not-type05-proved = partial-admissible-interact-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePartialConservationClose
    partial-conservation-unwired forward-refine-step partialWitnessPresentZeroGap true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  partialConservationVerdictOk
    (evaluatePartialConservationClose
       partial-conservation-unwired forward-refine-step partialWitnessPresentZeroGap true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

partialConservationFiberOk : FormalFiber → Bool
partialConservationFiberOk fiber-quantum-knowing = true
partialConservationFiberOk fiber-meso-acting = false

partial-conservation-knowing-fiber-ok :
  partialConservationFiberOk fiber-quantum-knowing ≡ true
partial-conservation-knowing-fiber-ok = refl

partial-conservation-meso-acting-not-ok :
  partialConservationFiberOk fiber-meso-acting ≡ false
partial-conservation-meso-acting-not-ok = refl

partial-conservation-routes-knowing-not-meso :
  partialConservationFiberOk fiber-quantum-knowing ≡ true ×
  partialConservationFiberOk fiber-meso-acting ≡ false
partial-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  partialConservationFiberOk fiber-quantum-knowing ∧
  not (partialConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not TYPE-05 Proved, not physics GREEN
------------------------------------------------------------------------

type05-partial-not-proved : type05PartialProved ≡ false
type05-partial-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

partial-second-law-conservation-framed : partialSecondLawConservationFramed ≡ true
partial-second-law-conservation-framed = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second **partial** axiom fork)
------------------------------------------------------------------------

partialConservationAxiom :
  (type05PartialProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (partialSecondLawConservationFramed ≡ true)
  × (evaluatePartialConservationClose partial-conservation-unwired forward-refine-step partialWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluatePartialConservationClose partial-conservation-proved forward-refine-step partialWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluatePartialConservationClose partial-conservation-proved calcareousStep partialWitnessPresentZeroGap false ≡ verdict-forbidden-interact-refuse)
  × (evaluatePartialConservationClose partial-conservation-proved forward-refine-step partialWitnessPresentZeroGap false ≡ verdict-partial-admissible-ok)
  × (partialConservationFiberOk fiber-quantum-knowing ≡ true)
  × (partialConservationFiberOk fiber-meso-acting ≡ false)
  × (partialConservationVerdictOk (evaluatePartialConservationClose partial-conservation-unwired forward-refine-step partialWitnessPresentZeroGap true) ≡ false)
partialConservationAxiom =
  type05-partial-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , partial-second-law-conservation-framed
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , forbidden-interact-refuse-calcareous
  , partial-admissible-interact-ok
  , partial-conservation-knowing-fiber-ok
  , partial-conservation-meso-acting-not-ok
  , green-invent-always-refuse

partialConservationNamed : String
partialConservationNamed =
  "partialConservation: TYPE-05 partial Interact conservation admissible forbidden total-claim refuse"

partialConservationCellId : String
partialConservationCellId = "CHEM-FORMAL-Q-AGDA-PARTIAL-CONSERVATION"

partialConservationNonClaim : String
partialConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-PARTIAL-CONSERVATION TYPE-05 partial Interact conservation admissible forbidden interact total-claim refuse type05PartialProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second partial axiom not physics GREEN not production_wired"

partial-conservation-modality-unwired :
  partialConservationModalityCurrent ≡ partial-conservation-unwired
partial-conservation-modality-unwired = refl

partialConservationPhysicsGreenAuthorized : Set
partialConservationPhysicsGreenAuthorized = ⊥

partial-conservation-physics-green-false : ¬ partialConservationPhysicsGreenAuthorized
partial-conservation-physics-green-false ()

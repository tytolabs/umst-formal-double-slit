-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.ModalityConservation.agda
--
-- TYPE-03 modality conservation on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Path census: Unwired/Assumed/Surrogate close without census; Proved refuse without
--   * Proved with defects refuse; Proved zero-defect census ok-but-not-GREEN
--   * modality laws Unwired (type03ModalityProved = false)
--
-- Mirrors sibling `ChemConstants/LinearConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + conservation framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.ModalityConservation where

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
-- Modality + TYPE-03 modality conservation pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ModalityConservationModality : Set where
  modality-conservation-unwired modality-conservation-assumed
    modality-conservation-proved modality-conservation-surrogate
    : ModalityConservationModality

modalityConservationModalityCurrent : ModalityConservationModality
modalityConservationModalityCurrent = modality-conservation-unwired

type03ModalityProved productionWired not118SquaredGreenTable
  modalitySecondLawConservationFramed : Bool
type03ModalityProved = false
productionWired = false
not118SquaredGreenTable = true
modalitySecondLawConservationFramed = true

------------------------------------------------------------------------
-- Modality lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

modalityLatticeCardinality : ℕ
modalityLatticeCardinality = 4

modality-lattice-cardinality-four : modalityLatticeCardinality ≡ 4
modality-lattice-cardinality-four = refl

modality-lattice-not-118-squared :
  does (modalityLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
modality-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- Path census presence — Proved refuse-closed without census
------------------------------------------------------------------------

data PathCensusPresence : Set where
  census-absent census-present : PathCensusPresence

record ClaimPathCensus : Set where
  constructor mkClaimPathCensus
  field
    census-presence : PathCensusPresence
    census-defect-total : ℕ

claimPathCensusAbsent : ClaimPathCensus
claimPathCensusAbsent = mkClaimPathCensus census-absent zero

claimPathCensusZeroDefect : ClaimPathCensus
claimPathCensusZeroDefect = mkClaimPathCensus census-present zero

claimPathCensusDefective : ℕ → ClaimPathCensus
claimPathCensusDefective n = mkClaimPathCensus census-present n

claimPathCensusZeroDefectOk : ClaimPathCensus → Bool
claimPathCensusZeroDefectOk (mkClaimPathCensus census-absent _) = false
claimPathCensusZeroDefectOk (mkClaimPathCensus census-present n) =
  does (n ℕ-Props.≟ zero)

claim-path-census-zero-defect-true :
  claimPathCensusZeroDefectOk claimPathCensusZeroDefect ≡ true
claim-path-census-zero-defect-true = refl

claim-path-census-absent-not-zero-defect :
  claimPathCensusZeroDefectOk claimPathCensusAbsent ≡ false
claim-path-census-absent-not-zero-defect = refl

claim-path-census-defective-not-zero-defect :
  ∀ n → claimPathCensusZeroDefectOk (claimPathCensusDefective (suc n)) ≡ false
claim-path-census-defective-not-zero-defect n = refl

------------------------------------------------------------------------
-- Modality close verdict — fail-closed lattice
------------------------------------------------------------------------

data ModalityLatticeVerdict : Set where
  verdict-design-ok verdict-proved-census-ok
    verdict-proved-without-census-refuse verdict-proved-defect-refuse
    verdict-green-invent-refuse
    : ModalityLatticeVerdict

modalityLatticeVerdictOk : ModalityLatticeVerdict → Bool
modalityLatticeVerdictOk verdict-design-ok = true
modalityLatticeVerdictOk verdict-proved-census-ok = true
modalityLatticeVerdictOk _ = false

evaluateModalityConservationClose :
  ModalityConservationModality → ClaimPathCensus → Bool → ModalityLatticeVerdict
evaluateModalityConservationClose _ _ true = verdict-green-invent-refuse
evaluateModalityConservationClose modality-conservation-unwired _ false = verdict-design-ok
evaluateModalityConservationClose modality-conservation-assumed _ false = verdict-design-ok
evaluateModalityConservationClose modality-conservation-surrogate _ false = verdict-design-ok
evaluateModalityConservationClose modality-conservation-proved (mkClaimPathCensus census-absent _) false =
  verdict-proved-without-census-refuse
evaluateModalityConservationClose modality-conservation-proved (mkClaimPathCensus census-present zero) false =
  verdict-proved-census-ok
evaluateModalityConservationClose modality-conservation-proved (mkClaimPathCensus census-present (suc _)) false =
  verdict-proved-defect-refuse

modalityRequiresPathCensus : ModalityConservationModality → Bool
modalityRequiresPathCensus modality-conservation-proved = true
modalityRequiresPathCensus _ = false

modality-unwired-no-census-required :
  modalityRequiresPathCensus modality-conservation-unwired ≡ false
modality-unwired-no-census-required = refl

modality-proved-census-required :
  modalityRequiresPathCensus modality-conservation-proved ≡ true
modality-proved-census-required = refl

------------------------------------------------------------------------
-- Unwired / Assumed / Surrogate close without census
------------------------------------------------------------------------

unwired-close-without-census :
  evaluateModalityConservationClose
    modality-conservation-unwired claimPathCensusAbsent false ≡ verdict-design-ok
unwired-close-without-census = refl

assumed-close-without-census :
  evaluateModalityConservationClose
    modality-conservation-assumed claimPathCensusAbsent false ≡ verdict-design-ok
assumed-close-without-census = refl

surrogate-close-without-census :
  evaluateModalityConservationClose
    modality-conservation-surrogate claimPathCensusAbsent false ≡ verdict-design-ok
surrogate-close-without-census = refl

design-modalities-verdict-ok-without-census :
  modalityLatticeVerdictOk
    (evaluateModalityConservationClose modality-conservation-unwired claimPathCensusAbsent false)
    ≡ true
  × modalityLatticeVerdictOk
      (evaluateModalityConservationClose modality-conservation-assumed claimPathCensusAbsent false)
      ≡ true
  × modalityLatticeVerdictOk
      (evaluateModalityConservationClose modality-conservation-surrogate claimPathCensusAbsent false)
      ≡ true
design-modalities-verdict-ok-without-census = refl , refl , refl

------------------------------------------------------------------------
-- Proved without census refuse
------------------------------------------------------------------------

proved-without-census-refuse :
  evaluateModalityConservationClose
    modality-conservation-proved claimPathCensusAbsent false ≡
  verdict-proved-without-census-refuse
proved-without-census-refuse = refl

proved-without-census-not-ok :
  modalityLatticeVerdictOk
    (evaluateModalityConservationClose modality-conservation-proved claimPathCensusAbsent false)
    ≡ false
proved-without-census-not-ok = refl

------------------------------------------------------------------------
-- Proved with defects refuse
------------------------------------------------------------------------

proved-defective-census-refuse :
  evaluateModalityConservationClose
    modality-conservation-proved (claimPathCensusDefective (suc zero)) false ≡
  verdict-proved-defect-refuse
proved-defective-census-refuse = refl

proved-defective-census-not-ok :
  modalityLatticeVerdictOk
    (evaluateModalityConservationClose
       modality-conservation-proved (claimPathCensusDefective (suc zero)) false)
    ≡ false
proved-defective-census-not-ok = refl

------------------------------------------------------------------------
-- Proved with zero-defect census ok-but-not-GREEN
------------------------------------------------------------------------

proved-zero-defect-census-ok :
  evaluateModalityConservationClose
    modality-conservation-proved claimPathCensusZeroDefect false ≡ verdict-proved-census-ok
proved-zero-defect-census-ok = refl

proved-zero-defect-census-verdict-ok :
  modalityLatticeVerdictOk
    (evaluateModalityConservationClose modality-conservation-proved claimPathCensusZeroDefect false)
    ≡ true
proved-zero-defect-census-verdict-ok = refl

proved-census-ok-still-not-type03-proved :
  modalityLatticeVerdictOk
    (evaluateModalityConservationClose modality-conservation-proved claimPathCensusZeroDefect false)
    ≡ true
  × type03ModalityProved ≡ false
proved-census-ok-still-not-type03-proved = proved-zero-defect-census-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateModalityConservationClose
    modality-conservation-unwired claimPathCensusZeroDefect true ≡ verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  modalityLatticeVerdictOk
    (evaluateModalityConservationClose modality-conservation-unwired claimPathCensusZeroDefect true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

modalityConservationFiberOk : FormalFiber → Bool
modalityConservationFiberOk fiber-quantum-knowing = true
modalityConservationFiberOk fiber-meso-acting = false

modality-conservation-knowing-fiber-ok :
  modalityConservationFiberOk fiber-quantum-knowing ≡ true
modality-conservation-knowing-fiber-ok = refl

modality-conservation-meso-acting-not-ok :
  modalityConservationFiberOk fiber-meso-acting ≡ false
modality-conservation-meso-acting-not-ok = refl

modality-conservation-routes-knowing-not-meso :
  modalityConservationFiberOk fiber-quantum-knowing ≡ true ×
  modalityConservationFiberOk fiber-meso-acting ≡ false
modality-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  modalityConservationFiberOk fiber-quantum-knowing ∧
  not (modalityConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not TYPE-03 Proved, not physics GREEN
------------------------------------------------------------------------

type03-modality-not-proved : type03ModalityProved ≡ false
type03-modality-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

modality-second-law-conservation-framed : modalitySecondLawConservationFramed ≡ true
modality-second-law-conservation-framed = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second modality axiom fork)
------------------------------------------------------------------------

modalityConservationAxiom :
  (type03ModalityProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (modalitySecondLawConservationFramed ≡ true)
  × (evaluateModalityConservationClose modality-conservation-unwired claimPathCensusAbsent false ≡ verdict-design-ok)
  × (evaluateModalityConservationClose modality-conservation-proved claimPathCensusAbsent false ≡ verdict-proved-without-census-refuse)
  × (evaluateModalityConservationClose modality-conservation-proved (claimPathCensusDefective (suc zero)) false ≡ verdict-proved-defect-refuse)
  × (evaluateModalityConservationClose modality-conservation-proved claimPathCensusZeroDefect false ≡ verdict-proved-census-ok)
  × (modalityConservationFiberOk fiber-quantum-knowing ≡ true)
  × (modalityConservationFiberOk fiber-meso-acting ≡ false)
  × (modalityLatticeVerdictOk (evaluateModalityConservationClose modality-conservation-unwired claimPathCensusZeroDefect true) ≡ false)
modalityConservationAxiom =
  type03-modality-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , modality-second-law-conservation-framed
  , unwired-close-without-census
  , proved-without-census-refuse
  , proved-defective-census-refuse
  , proved-zero-defect-census-ok
  , modality-conservation-knowing-fiber-ok
  , modality-conservation-meso-acting-not-ok
  , green-invent-always-refuse

modalityConservationNamed : String
modalityConservationNamed =
  "modalityConservation: claim modality lattice Unwired Assumed Proved Surrogate path census conservation"

modalityConservationCellId : String
modalityConservationCellId = "CHEM-FORMAL-Q-AGDA-MODALITY-CONSERVATION"

modalityConservationNonClaim : String
modalityConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-MODALITY-CONSERVATION TYPE-03 modality conservation claim modality lattice Unwired Assumed Proved Surrogate path census Proved requires census Unwired Assumed Surrogate close without census Proved zero defect census ok but not GREEN not 118 squared GREEN table geometry knowing quantum fiber not meso acting type03ModalityProved false Unwired one axiom second law conservation not second modality axiom not physics GREEN not production_wired"

modality-conservation-modality-unwired :
  modalityConservationModalityCurrent ≡ modality-conservation-unwired
modality-conservation-modality-unwired = refl

modalityConservationPhysicsGreenAuthorized : Set
modalityConservationPhysicsGreenAuthorized = ⊥

modality-conservation-physics-green-false : ¬ modalityConservationPhysicsGreenAuthorized
modality-conservation-physics-green-false ()

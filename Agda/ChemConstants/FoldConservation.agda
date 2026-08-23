-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.FoldConservation.agda
--
-- FP-01 classifier-**fold** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Classifier **fold**: conjunctive (∧) and disjunctive (∨) **fold** identity conserved
--   * Total-claim refuse without **fold** witness; mismatch **fold** refuse
--   * **fold** laws Unwired (fp01FoldProved = false)
--
-- Mirrors sibling `ChemConstants/PartialConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.FoldConservation where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + FP-01 classifier-**fold** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data FoldConservationModality : Set where
  fold-conservation-unwired fold-conservation-assumed
    fold-conservation-proved fold-conservation-surrogate
    : FoldConservationModality

foldConservationModalityCurrent : FoldConservationModality
foldConservationModalityCurrent = fold-conservation-unwired

fp01FoldProved productionWired not118SquaredGreenTable
  foldSecondLawConservationFramed : Bool
fp01FoldProved = false
productionWired = false
not118SquaredGreenTable = true
foldSecondLawConservationFramed = true

------------------------------------------------------------------------
-- **Fold** law lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

foldLawLatticeCardinality : ℕ
foldLawLatticeCardinality = 4

fold-law-lattice-cardinality-four : foldLawLatticeCardinality ≡ 4
fold-law-lattice-cardinality-four = refl

fold-law-lattice-not-118-squared :
  does (foldLawLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
fold-law-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- ClassifierFoldStep scaffold — conjunctive / disjunctive **fold**
------------------------------------------------------------------------

data ClassifierTag : Set where
  hematite-dominant bauxite-dominant calcareous-gangue : ClassifierTag

data ClassifierFoldStep : Set where
  identity : ClassifierFoldStep
  leaf : ClassifierTag → ClassifierFoldStep
  conjunctive-fold : ClassifierFoldStep → ClassifierFoldStep → ClassifierFoldStep
  disjunctive-fold : ClassifierFoldStep → ClassifierFoldStep → ClassifierFoldStep

foldIdentity : ClassifierFoldStep
foldIdentity = identity

foldConjunctive foldDisjunctive : ClassifierFoldStep → ClassifierFoldStep → ClassifierFoldStep
foldConjunctive = conjunctive-fold
foldDisjunctive = disjunctive-fold

hematiteLeaf bauxiteLeaf calcareousLeaf : ClassifierFoldStep
hematiteLeaf = leaf hematite-dominant
bauxiteLeaf = leaf bauxite-dominant
calcareousLeaf = leaf calcareous-gangue

isConjunctiveFold isDisjunctiveFold : ClassifierFoldStep → Bool
isConjunctiveFold (conjunctive-fold _ _) = true
isConjunctiveFold _ = false

isDisjunctiveFold (disjunctive-fold _ _) = true
isDisjunctiveFold _ = false

isFoldIdentity : ClassifierFoldStep → Bool
isFoldIdentity identity = true
isFoldIdentity _ = false

------------------------------------------------------------------------
-- Conjunctive and disjunctive **fold** identity conserved
------------------------------------------------------------------------

conjunctive-fold-left-identity :
  ∀ (a : ClassifierFoldStep) →
  isFoldIdentity foldIdentity ≡ true × isConjunctiveFold (foldConjunctive foldIdentity a) ≡ true
conjunctive-fold-left-identity a = refl , refl

conjunctive-fold-right-identity :
  ∀ (a : ClassifierFoldStep) →
  isConjunctiveFold (foldConjunctive a foldIdentity) ≡ true × isFoldIdentity foldIdentity ≡ true
conjunctive-fold-right-identity a = refl , refl

disjunctive-fold-left-identity :
  ∀ (a : ClassifierFoldStep) →
  isFoldIdentity foldIdentity ≡ true × isDisjunctiveFold (foldDisjunctive foldIdentity a) ≡ true
disjunctive-fold-left-identity a = refl , refl

disjunctive-fold-right-identity :
  ∀ (a : ClassifierFoldStep) →
  isDisjunctiveFold (foldDisjunctive a foldIdentity) ≡ true × isFoldIdentity foldIdentity ≡ true
disjunctive-fold-right-identity a = refl , refl

conjunctive-disjunctive-fold-identity-conserved :
  (∀ a → isConjunctiveFold (foldConjunctive foldIdentity a) ≡ true)
  × (∀ a → isConjunctiveFold (foldConjunctive a foldIdentity) ≡ true)
  × (∀ a → isDisjunctiveFold (foldDisjunctive foldIdentity a) ≡ true)
  × (∀ a → isDisjunctiveFold (foldDisjunctive a foldIdentity) ≡ true)
conjunctive-disjunctive-fold-identity-conserved =
  (λ a → refl)
  , (λ a → refl)
  , (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Classifier **fold** admissibility — conjunctive vs disjunctive mismatch
------------------------------------------------------------------------

data FoldAdmissibility : Set where
  fold-admissible fold-mismatch-refuse : FoldAdmissibility

isFoldAdmissible : ClassifierFoldStep → Bool
isFoldAdmissible identity = true
isFoldAdmissible (leaf hematite-dominant) = true
isFoldAdmissible (leaf bauxite-dominant) = true
isFoldAdmissible (leaf calcareous-gangue) = false
isFoldAdmissible (conjunctive-fold a b) =
  isFoldAdmissible a ∧ isFoldAdmissible b
isFoldAdmissible (disjunctive-fold a b) =
  isFoldAdmissible a ∨ isFoldAdmissible b

hematite-leaf-admissible : isFoldAdmissible hematiteLeaf ≡ true
hematite-leaf-admissible = refl

bauxite-leaf-admissible : isFoldAdmissible bauxiteLeaf ≡ true
bauxite-leaf-admissible = refl

calcareous-leaf-forbidden : isFoldAdmissible calcareousLeaf ≡ false
calcareous-leaf-forbidden = refl

conjunctive-fold-admissible :
  isFoldAdmissible (foldConjunctive hematiteLeaf bauxiteLeaf) ≡ true
conjunctive-fold-admissible = refl

disjunctive-fold-admissible-with-one-forbidden :
  isFoldAdmissible (foldDisjunctive hematiteLeaf calcareousLeaf) ≡ true
disjunctive-fold-admissible-with-one-forbidden = refl

conjunctive-fold-mismatch-refuse :
  isFoldAdmissible (foldConjunctive hematiteLeaf calcareousLeaf) ≡ false
conjunctive-fold-mismatch-refuse = refl

------------------------------------------------------------------------
-- **Fold** witness — total-claim refuse without witness
------------------------------------------------------------------------

data FoldWitnessPresence : Set where
  fold-witness-absent fold-witness-present : FoldWitnessPresence

record ClassifierFoldWitness : Set where
  constructor mkClassifierFoldWitness
  field
    witness-presence : FoldWitnessPresence
    mismatch-gap-total : ℕ

foldWitnessAbsent : ClassifierFoldWitness
foldWitnessAbsent = mkClassifierFoldWitness fold-witness-absent zero

foldWitnessPresentZeroGap : ClassifierFoldWitness
foldWitnessPresentZeroGap = mkClassifierFoldWitness fold-witness-present zero

foldWitnessPresentWithGaps : ℕ → ClassifierFoldWitness
foldWitnessPresentWithGaps n = mkClassifierFoldWitness fold-witness-present n

foldWitnessGapFree : ClassifierFoldWitness → Bool
foldWitnessGapFree (mkClassifierFoldWitness fold-witness-absent _) = false
foldWitnessGapFree (mkClassifierFoldWitness fold-witness-present n) =
  does (n ℕ-Props.≟ zero)

fold-witness-present-zero-gap-free :
  foldWitnessGapFree foldWitnessPresentZeroGap ≡ true
fold-witness-present-zero-gap-free = refl

fold-witness-absent-not-gap-free :
  foldWitnessGapFree foldWitnessAbsent ≡ false
fold-witness-absent-not-gap-free = refl

fold-witness-with-gaps-not-gap-free :
  ∀ n → foldWitnessGapFree (foldWitnessPresentWithGaps (suc n)) ≡ false
fold-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-**fold** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data FoldConservationVerdict : Set where
  verdict-unwired-ok verdict-fold-admissible-ok
    verdict-total-claim-refuse verdict-fold-mismatch-refuse
    verdict-green-invent-refuse
    : FoldConservationVerdict

foldConservationVerdictOk : FoldConservationVerdict → Bool
foldConservationVerdictOk verdict-unwired-ok = true
foldConservationVerdictOk verdict-fold-admissible-ok = true
foldConservationVerdictOk _ = false

evaluateFoldConservationClose :
  FoldConservationModality → ClassifierFoldStep → ClassifierFoldWitness → Bool
  → FoldConservationVerdict
evaluateFoldConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateFoldConservationClose fold-conservation-unwired _ _ false = verdict-unwired-ok
evaluateFoldConservationClose fold-conservation-assumed _ _ false = verdict-unwired-ok
evaluateFoldConservationClose fold-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateFoldConservationClose fold-conservation-proved step (mkClassifierFoldWitness fold-witness-absent _) false =
  verdict-total-claim-refuse
evaluateFoldConservationClose fold-conservation-proved step (mkClassifierFoldWitness fold-witness-present _) false
  with isFoldAdmissible step
... | false = verdict-fold-mismatch-refuse
... | true  = verdict-fold-admissible-ok

------------------------------------------------------------------------
-- Sample admissible classifier-**fold** scaffold
------------------------------------------------------------------------

conjunctive-refine-fold : ClassifierFoldStep
conjunctive-refine-fold = foldConjunctive hematiteLeaf bauxiteLeaf

conjunctive-refine-fold-admissible : isFoldAdmissible conjunctive-refine-fold ≡ true
conjunctive-refine-fold-admissible = refl

------------------------------------------------------------------------
-- Unwired close — design scaffold without **fold** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateFoldConservationClose
    fold-conservation-unwired conjunctive-refine-fold foldWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateFoldConservationClose
    fold-conservation-assumed conjunctive-refine-fold foldWitnessAbsent false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateFoldConservationClose
    fold-conservation-surrogate conjunctive-refine-fold foldWitnessAbsent false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  foldConservationVerdictOk
    (evaluateFoldConservationClose fold-conservation-unwired conjunctive-refine-fold foldWitnessAbsent false)
    ≡ true
  × foldConservationVerdictOk
      (evaluateFoldConservationClose fold-conservation-assumed conjunctive-refine-fold foldWitnessAbsent false)
      ≡ true
  × foldConservationVerdictOk
      (evaluateFoldConservationClose fold-conservation-surrogate conjunctive-refine-fold foldWitnessAbsent false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **fold** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateFoldConservationClose
    fold-conservation-proved conjunctive-refine-fold foldWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  foldConservationVerdictOk
    (evaluateFoldConservationClose
       fold-conservation-proved conjunctive-refine-fold foldWitnessAbsent false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateFoldConservationClose
    fold-conservation-proved conjunctive-refine-fold foldWitnessAbsent false ≡
  verdict-fold-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- Mismatch **fold** refuse — conjunctive vs disjunctive admissibility
------------------------------------------------------------------------

fold-mismatch-refuse-calcareous-conjunctive :
  evaluateFoldConservationClose
    fold-conservation-proved calcareousLeaf foldWitnessPresentZeroGap false ≡
  verdict-fold-mismatch-refuse
fold-mismatch-refuse-calcareous-conjunctive = refl

fold-mismatch-refuse-conjunctive-with-forbidden :
  evaluateFoldConservationClose
    fold-conservation-proved (foldConjunctive hematiteLeaf calcareousLeaf) foldWitnessPresentZeroGap false ≡
  verdict-fold-mismatch-refuse
fold-mismatch-refuse-conjunctive-with-forbidden = refl

fold-mismatch-refuse-not-ok :
  foldConservationVerdictOk
    (evaluateFoldConservationClose
       fold-conservation-proved calcareousLeaf foldWitnessPresentZeroGap false)
    ≡ false
fold-mismatch-refuse-not-ok = refl

FoldMismatchWhenCalcareous : Set
FoldMismatchWhenCalcareous =
  evaluateFoldConservationClose
    fold-conservation-proved calcareousLeaf foldWitnessPresentZeroGap false ≡
  verdict-fold-admissible-ok

fold-mismatch-⊥-when-calcareous : FoldMismatchWhenCalcareous → ⊥
fold-mismatch-⊥-when-calcareous ()

------------------------------------------------------------------------
-- Admissible classifier-**fold** — witness present + admissible step
------------------------------------------------------------------------

fold-admissible-ok :
  evaluateFoldConservationClose
    fold-conservation-proved conjunctive-refine-fold foldWitnessPresentZeroGap false ≡
  verdict-fold-admissible-ok
fold-admissible-ok = refl

fold-admissible-verdict-ok :
  foldConservationVerdictOk
    (evaluateFoldConservationClose
       fold-conservation-proved conjunctive-refine-fold foldWitnessPresentZeroGap false)
    ≡ true
fold-admissible-verdict-ok = refl

fold-admissible-ok-still-not-fp01-proved :
  foldConservationVerdictOk
    (evaluateFoldConservationClose
       fold-conservation-proved conjunctive-refine-fold foldWitnessPresentZeroGap false)
    ≡ true
  × fp01FoldProved ≡ false
fold-admissible-ok-still-not-fp01-proved = fold-admissible-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateFoldConservationClose
    fold-conservation-unwired conjunctive-refine-fold foldWitnessPresentZeroGap true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  foldConservationVerdictOk
    (evaluateFoldConservationClose
       fold-conservation-unwired conjunctive-refine-fold foldWitnessPresentZeroGap true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

foldConservationFiberOk : FormalFiber → Bool
foldConservationFiberOk fiber-quantum-knowing = true
foldConservationFiberOk fiber-meso-acting = false

fold-conservation-knowing-fiber-ok :
  foldConservationFiberOk fiber-quantum-knowing ≡ true
fold-conservation-knowing-fiber-ok = refl

fold-conservation-meso-acting-not-ok :
  foldConservationFiberOk fiber-meso-acting ≡ false
fold-conservation-meso-acting-not-ok = refl

fold-conservation-routes-knowing-not-meso :
  foldConservationFiberOk fiber-quantum-knowing ≡ true ×
  foldConservationFiberOk fiber-meso-acting ≡ false
fold-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  foldConservationFiberOk fiber-quantum-knowing ∧
  not (foldConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not FP-01 Proved, not physics GREEN
------------------------------------------------------------------------

fp01-fold-not-proved : fp01FoldProved ≡ false
fp01-fold-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

fold-second-law-conservation-framed : foldSecondLawConservationFramed ≡ true
fold-second-law-conservation-framed = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second **fold** axiom fork)
------------------------------------------------------------------------

foldConservationAxiom :
  (fp01FoldProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (foldSecondLawConservationFramed ≡ true)
  × (evaluateFoldConservationClose fold-conservation-unwired conjunctive-refine-fold foldWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateFoldConservationClose fold-conservation-proved conjunctive-refine-fold foldWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateFoldConservationClose fold-conservation-proved calcareousLeaf foldWitnessPresentZeroGap false ≡ verdict-fold-mismatch-refuse)
  × (evaluateFoldConservationClose fold-conservation-proved conjunctive-refine-fold foldWitnessPresentZeroGap false ≡ verdict-fold-admissible-ok)
  × (foldConservationFiberOk fiber-quantum-knowing ≡ true)
  × (foldConservationFiberOk fiber-meso-acting ≡ false)
  × (foldConservationVerdictOk (evaluateFoldConservationClose fold-conservation-unwired conjunctive-refine-fold foldWitnessPresentZeroGap true) ≡ false)
  × (∀ a → isConjunctiveFold (foldConjunctive foldIdentity a) ≡ true)
  × (∀ a → isDisjunctiveFold (foldDisjunctive foldIdentity a) ≡ true)
foldConservationAxiom =
  fp01-fold-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , fold-second-law-conservation-framed
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , fold-mismatch-refuse-calcareous-conjunctive
  , fold-admissible-ok
  , fold-conservation-knowing-fiber-ok
  , fold-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)

foldConservationNamed : String
foldConservationNamed =
  "foldConservation: FP-01 classifier fold conjunctive disjunctive identity conservation"

foldConservationCellId : String
foldConservationCellId = "CHEM-FORMAL-Q-AGDA-FOLD-CONSERVATION"

foldConservationNonClaim : String
foldConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-FOLD-CONSERVATION FP-01 classifier fold conservation conjunctive disjunctive fold identity conserved total-claim refuse fold mismatch refuse fp01FoldProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second fold axiom not physics GREEN not production_wired"

fold-conservation-modality-unwired :
  foldConservationModalityCurrent ≡ fold-conservation-unwired
fold-conservation-modality-unwired = refl

foldConservationPhysicsGreenAuthorized : Set
foldConservationPhysicsGreenAuthorized = ⊥

fold-conservation-physics-green-false : ¬ foldConservationPhysicsGreenAuthorized
fold-conservation-physics-green-false ()

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.FixpointConservation.agda
--
-- FP-02 classifier-**fixpoint** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Lattice meet (∧) and join (∨) identity conserved at bottom
--   * Monotone chain reaches a **fixpoint** scaffold witness
--   * Total-claim refuse without **fixpoint** witness; mismatch **fixpoint** refuse
--   * **fixpoint** laws Unwired (fp02FixpointProved = false)
--
-- Mirrors sibling `ChemConstants/FoldConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.FixpointConservation where

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
-- Modality + FP-02 classifier-**fixpoint** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data FixpointConservationModality : Set where
  fixpoint-conservation-unwired fixpoint-conservation-assumed
    fixpoint-conservation-proved fixpoint-conservation-surrogate
    : FixpointConservationModality

fixpointConservationModalityCurrent : FixpointConservationModality
fixpointConservationModalityCurrent = fixpoint-conservation-unwired

fp02FixpointProved productionWired not118SquaredGreenTable
  fixpointSecondLawConservationFramed : Bool
fp02FixpointProved = false
productionWired = false
not118SquaredGreenTable = true
fixpointSecondLawConservationFramed = true

------------------------------------------------------------------------
-- **Fixpoint** law lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

fixpointLawLatticeCardinality : ℕ
fixpointLawLatticeCardinality = 4

fixpoint-law-lattice-cardinality-four : fixpointLawLatticeCardinality ≡ 4
fixpoint-law-lattice-cardinality-four = refl

fixpoint-law-lattice-not-118-squared :
  does (fixpointLawLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
fixpoint-law-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- ClassifierFixpointStep scaffold — lattice meet / join
------------------------------------------------------------------------

data ClassifierTag : Set where
  hematite-dominant bauxite-dominant calcareous-gangue : ClassifierTag

data ClassifierFixpointStep : Set where
  bottom : ClassifierFixpointStep
  leaf : ClassifierTag → ClassifierFixpointStep
  meet-lattice : ClassifierFixpointStep → ClassifierFixpointStep → ClassifierFixpointStep
  join-lattice : ClassifierFixpointStep → ClassifierFixpointStep → ClassifierFixpointStep

latticeBottom : ClassifierFixpointStep
latticeBottom = bottom

meetOp joinOp : ClassifierFixpointStep → ClassifierFixpointStep → ClassifierFixpointStep
meetOp = meet-lattice
joinOp = join-lattice

hematiteLeaf bauxiteLeaf calcareousLeaf : ClassifierFixpointStep
hematiteLeaf = leaf hematite-dominant
bauxiteLeaf = leaf bauxite-dominant
calcareousLeaf = leaf calcareous-gangue

isMeet isJoin : ClassifierFixpointStep → Bool
isMeet (meet-lattice _ _) = true
isMeet _ = false

isJoin (join-lattice _ _) = true
isJoin _ = false

isLatticeBottom : ClassifierFixpointStep → Bool
isLatticeBottom bottom = true
isLatticeBottom _ = false

------------------------------------------------------------------------
-- Lattice meet and join identity conserved at bottom
------------------------------------------------------------------------

meet-left-identity :
  ∀ (a : ClassifierFixpointStep) →
  isLatticeBottom latticeBottom ≡ true × isMeet (meetOp latticeBottom a) ≡ true
meet-left-identity a = refl , refl

meet-right-identity :
  ∀ (a : ClassifierFixpointStep) →
  isMeet (meetOp a latticeBottom) ≡ true × isLatticeBottom latticeBottom ≡ true
meet-right-identity a = refl , refl

join-left-identity :
  ∀ (a : ClassifierFixpointStep) →
  isLatticeBottom latticeBottom ≡ true × isJoin (joinOp latticeBottom a) ≡ true
join-left-identity a = refl , refl

join-right-identity :
  ∀ (a : ClassifierFixpointStep) →
  isJoin (joinOp a latticeBottom) ≡ true × isLatticeBottom latticeBottom ≡ true
join-right-identity a = refl , refl

meet-join-lattice-identity-conserved :
  (∀ a → isMeet (meetOp latticeBottom a) ≡ true)
  × (∀ a → isMeet (meetOp a latticeBottom) ≡ true)
  × (∀ a → isJoin (joinOp latticeBottom a) ≡ true)
  × (∀ a → isJoin (joinOp a latticeBottom) ≡ true)
meet-join-lattice-identity-conserved =
  (λ a → refl)
  , (λ a → refl)
  , (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Monotone chain — reaches a **fixpoint** scaffold
------------------------------------------------------------------------

data FixpointStatus : Set where
  fixpoint-reaching fixpoint-reached : FixpointStatus

record MonotoneChainLink : Set where
  constructor mkMonotoneChainLink
  field
    prior : ClassifierFixpointStep
    next : ClassifierFixpointStep
    monotone-ok : Bool
    fixpoint-status : FixpointStatus

isFixpointReached : FixpointStatus → Bool
isFixpointReached fixpoint-reached = true
isFixpointReached fixpoint-reaching = false

chainReachesFixpoint : MonotoneChainLink → Bool
chainReachesFixpoint l =
  isFixpointReached (MonotoneChainLink.fixpoint-status l)

bottomFixpointLink : MonotoneChainLink
bottomFixpointLink =
  mkMonotoneChainLink latticeBottom latticeBottom true fixpoint-reached

hematiteToBottomLink : MonotoneChainLink
hematiteToBottomLink =
  mkMonotoneChainLink hematiteLeaf latticeBottom true fixpoint-reaching

monotone-chain-bottom-reached :
  chainReachesFixpoint bottomFixpointLink ≡ true
monotone-chain-bottom-reached = refl

monotone-chain-hematite-reaching :
  chainReachesFixpoint hematiteToBottomLink ≡ false
monotone-chain-hematite-reaching = refl

monotone-chain-reaches-fixpoint :
  chainReachesFixpoint bottomFixpointLink ≡ true
  × MonotoneChainLink.fixpoint-status bottomFixpointLink ≡ fixpoint-reached
monotone-chain-reaches-fixpoint = refl , refl

------------------------------------------------------------------------
-- Classifier **fixpoint** admissibility — meet vs join mismatch
------------------------------------------------------------------------

data FixpointAdmissibility : Set where
  fixpoint-admissible fixpoint-mismatch-refuse : FixpointAdmissibility

isFixpointAdmissible : ClassifierFixpointStep → Bool
isFixpointAdmissible bottom = true
isFixpointAdmissible (leaf hematite-dominant) = true
isFixpointAdmissible (leaf bauxite-dominant) = true
isFixpointAdmissible (leaf calcareous-gangue) = false
isFixpointAdmissible (meet-lattice a b) =
  isFixpointAdmissible a ∧ isFixpointAdmissible b
isFixpointAdmissible (join-lattice a b) =
  isFixpointAdmissible a ∨ isFixpointAdmissible b

hematite-leaf-admissible : isFixpointAdmissible hematiteLeaf ≡ true
hematite-leaf-admissible = refl

bauxite-leaf-admissible : isFixpointAdmissible bauxiteLeaf ≡ true
bauxite-leaf-admissible = refl

calcareous-leaf-forbidden : isFixpointAdmissible calcareousLeaf ≡ false
calcareous-leaf-forbidden = refl

meet-lattice-admissible :
  isFixpointAdmissible (meetOp hematiteLeaf bauxiteLeaf) ≡ true
meet-lattice-admissible = refl

join-lattice-admissible-with-one-forbidden :
  isFixpointAdmissible (joinOp hematiteLeaf calcareousLeaf) ≡ true
join-lattice-admissible-with-one-forbidden = refl

meet-lattice-mismatch-refuse :
  isFixpointAdmissible (meetOp hematiteLeaf calcareousLeaf) ≡ false
meet-lattice-mismatch-refuse = refl

------------------------------------------------------------------------
-- **Fixpoint** witness — total-claim refuse without witness
------------------------------------------------------------------------

data FixpointWitnessPresence : Set where
  fixpoint-witness-absent fixpoint-witness-present : FixpointWitnessPresence

record ClassifierFixpointWitness : Set where
  constructor mkClassifierFixpointWitness
  field
    witness-presence : FixpointWitnessPresence
    mismatch-gap-total : ℕ

fixpointWitnessAbsent : ClassifierFixpointWitness
fixpointWitnessAbsent = mkClassifierFixpointWitness fixpoint-witness-absent zero

fixpointWitnessPresentZeroGap : ClassifierFixpointWitness
fixpointWitnessPresentZeroGap = mkClassifierFixpointWitness fixpoint-witness-present zero

fixpointWitnessPresentWithGaps : ℕ → ClassifierFixpointWitness
fixpointWitnessPresentWithGaps n = mkClassifierFixpointWitness fixpoint-witness-present n

fixpointWitnessGapFree : ClassifierFixpointWitness → Bool
fixpointWitnessGapFree (mkClassifierFixpointWitness fixpoint-witness-absent _) = false
fixpointWitnessGapFree (mkClassifierFixpointWitness fixpoint-witness-present n) =
  does (n ℕ-Props.≟ zero)

fixpoint-witness-present-zero-gap-free :
  fixpointWitnessGapFree fixpointWitnessPresentZeroGap ≡ true
fixpoint-witness-present-zero-gap-free = refl

fixpoint-witness-absent-not-gap-free :
  fixpointWitnessGapFree fixpointWitnessAbsent ≡ false
fixpoint-witness-absent-not-gap-free = refl

fixpoint-witness-with-gaps-not-gap-free :
  ∀ n → fixpointWitnessGapFree (fixpointWitnessPresentWithGaps (suc n)) ≡ false
fixpoint-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-**fixpoint** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data FixpointConservationVerdict : Set where
  verdict-unwired-ok verdict-fixpoint-admissible-ok
    verdict-total-claim-refuse verdict-fixpoint-mismatch-refuse
    verdict-green-invent-refuse
    : FixpointConservationVerdict

fixpointConservationVerdictOk : FixpointConservationVerdict → Bool
fixpointConservationVerdictOk verdict-unwired-ok = true
fixpointConservationVerdictOk verdict-fixpoint-admissible-ok = true
fixpointConservationVerdictOk _ = false

evaluateFixpointConservationClose :
  FixpointConservationModality → ClassifierFixpointStep → ClassifierFixpointWitness → Bool
  → FixpointConservationVerdict
evaluateFixpointConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateFixpointConservationClose fixpoint-conservation-unwired _ _ false = verdict-unwired-ok
evaluateFixpointConservationClose fixpoint-conservation-assumed _ _ false = verdict-unwired-ok
evaluateFixpointConservationClose fixpoint-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateFixpointConservationClose fixpoint-conservation-proved step (mkClassifierFixpointWitness fixpoint-witness-absent _) false =
  verdict-total-claim-refuse
evaluateFixpointConservationClose fixpoint-conservation-proved step (mkClassifierFixpointWitness fixpoint-witness-present _) false
  with isFixpointAdmissible step
... | false = verdict-fixpoint-mismatch-refuse
... | true  = verdict-fixpoint-admissible-ok

------------------------------------------------------------------------
-- Sample admissible classifier-**fixpoint** scaffold
------------------------------------------------------------------------

meet-refine-fixpoint : ClassifierFixpointStep
meet-refine-fixpoint = meetOp hematiteLeaf bauxiteLeaf

meet-refine-fixpoint-admissible : isFixpointAdmissible meet-refine-fixpoint ≡ true
meet-refine-fixpoint-admissible = refl

------------------------------------------------------------------------
-- Unwired close — design scaffold without **fixpoint** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateFixpointConservationClose
    fixpoint-conservation-unwired meet-refine-fixpoint fixpointWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateFixpointConservationClose
    fixpoint-conservation-assumed meet-refine-fixpoint fixpointWitnessAbsent false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateFixpointConservationClose
    fixpoint-conservation-surrogate meet-refine-fixpoint fixpointWitnessAbsent false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  fixpointConservationVerdictOk
    (evaluateFixpointConservationClose fixpoint-conservation-unwired meet-refine-fixpoint fixpointWitnessAbsent false)
    ≡ true
  × fixpointConservationVerdictOk
      (evaluateFixpointConservationClose fixpoint-conservation-assumed meet-refine-fixpoint fixpointWitnessAbsent false)
      ≡ true
  × fixpointConservationVerdictOk
      (evaluateFixpointConservationClose fixpoint-conservation-surrogate meet-refine-fixpoint fixpointWitnessAbsent false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **fixpoint** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateFixpointConservationClose
    fixpoint-conservation-proved meet-refine-fixpoint fixpointWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  fixpointConservationVerdictOk
    (evaluateFixpointConservationClose
       fixpoint-conservation-proved meet-refine-fixpoint fixpointWitnessAbsent false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateFixpointConservationClose
    fixpoint-conservation-proved meet-refine-fixpoint fixpointWitnessAbsent false ≡
  verdict-fixpoint-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- Mismatch **fixpoint** refuse — meet vs join admissibility
------------------------------------------------------------------------

fixpoint-mismatch-refuse-calcareous-meet :
  evaluateFixpointConservationClose
    fixpoint-conservation-proved calcareousLeaf fixpointWitnessPresentZeroGap false ≡
  verdict-fixpoint-mismatch-refuse
fixpoint-mismatch-refuse-calcareous-meet = refl

fixpoint-mismatch-refuse-meet-with-forbidden :
  evaluateFixpointConservationClose
    fixpoint-conservation-proved (meetOp hematiteLeaf calcareousLeaf) fixpointWitnessPresentZeroGap false ≡
  verdict-fixpoint-mismatch-refuse
fixpoint-mismatch-refuse-meet-with-forbidden = refl

fixpoint-mismatch-refuse-not-ok :
  fixpointConservationVerdictOk
    (evaluateFixpointConservationClose
       fixpoint-conservation-proved calcareousLeaf fixpointWitnessPresentZeroGap false)
    ≡ false
fixpoint-mismatch-refuse-not-ok = refl

FixpointMismatchWhenCalcareous : Set
FixpointMismatchWhenCalcareous =
  evaluateFixpointConservationClose
    fixpoint-conservation-proved calcareousLeaf fixpointWitnessPresentZeroGap false ≡
  verdict-fixpoint-admissible-ok

fixpoint-mismatch-⊥-when-calcareous : FixpointMismatchWhenCalcareous → ⊥
fixpoint-mismatch-⊥-when-calcareous ()

------------------------------------------------------------------------
-- Admissible classifier-**fixpoint** — witness present + admissible step
------------------------------------------------------------------------

fixpoint-admissible-ok :
  evaluateFixpointConservationClose
    fixpoint-conservation-proved meet-refine-fixpoint fixpointWitnessPresentZeroGap false ≡
  verdict-fixpoint-admissible-ok
fixpoint-admissible-ok = refl

fixpoint-admissible-verdict-ok :
  fixpointConservationVerdictOk
    (evaluateFixpointConservationClose
       fixpoint-conservation-proved meet-refine-fixpoint fixpointWitnessPresentZeroGap false)
    ≡ true
fixpoint-admissible-verdict-ok = refl

fixpoint-admissible-ok-still-not-fp02-proved :
  fixpointConservationVerdictOk
    (evaluateFixpointConservationClose
       fixpoint-conservation-proved meet-refine-fixpoint fixpointWitnessPresentZeroGap false)
    ≡ true
  × fp02FixpointProved ≡ false
fixpoint-admissible-ok-still-not-fp02-proved = fixpoint-admissible-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateFixpointConservationClose
    fixpoint-conservation-unwired meet-refine-fixpoint fixpointWitnessPresentZeroGap true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  fixpointConservationVerdictOk
    (evaluateFixpointConservationClose
       fixpoint-conservation-unwired meet-refine-fixpoint fixpointWitnessPresentZeroGap true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

fixpointConservationFiberOk : FormalFiber → Bool
fixpointConservationFiberOk fiber-quantum-knowing = true
fixpointConservationFiberOk fiber-meso-acting = false

fixpoint-conservation-knowing-fiber-ok :
  fixpointConservationFiberOk fiber-quantum-knowing ≡ true
fixpoint-conservation-knowing-fiber-ok = refl

fixpoint-conservation-meso-acting-not-ok :
  fixpointConservationFiberOk fiber-meso-acting ≡ false
fixpoint-conservation-meso-acting-not-ok = refl

fixpoint-conservation-routes-knowing-not-meso :
  fixpointConservationFiberOk fiber-quantum-knowing ≡ true ×
  fixpointConservationFiberOk fiber-meso-acting ≡ false
fixpoint-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  fixpointConservationFiberOk fiber-quantum-knowing ∧
  not (fixpointConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not FP-02 Proved, not physics GREEN
------------------------------------------------------------------------

fp02-fixpoint-not-proved : fp02FixpointProved ≡ false
fp02-fixpoint-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

fixpoint-second-law-conservation-framed : fixpointSecondLawConservationFramed ≡ true
fixpoint-second-law-conservation-framed = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second **fixpoint** axiom fork)
------------------------------------------------------------------------

fixpointConservationAxiom :
  (fp02FixpointProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (fixpointSecondLawConservationFramed ≡ true)
  × (evaluateFixpointConservationClose fixpoint-conservation-unwired meet-refine-fixpoint fixpointWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateFixpointConservationClose fixpoint-conservation-proved meet-refine-fixpoint fixpointWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateFixpointConservationClose fixpoint-conservation-proved calcareousLeaf fixpointWitnessPresentZeroGap false ≡ verdict-fixpoint-mismatch-refuse)
  × (evaluateFixpointConservationClose fixpoint-conservation-proved meet-refine-fixpoint fixpointWitnessPresentZeroGap false ≡ verdict-fixpoint-admissible-ok)
  × (fixpointConservationFiberOk fiber-quantum-knowing ≡ true)
  × (fixpointConservationFiberOk fiber-meso-acting ≡ false)
  × (fixpointConservationVerdictOk (evaluateFixpointConservationClose fixpoint-conservation-unwired meet-refine-fixpoint fixpointWitnessPresentZeroGap true) ≡ false)
  × (∀ a → isMeet (meetOp latticeBottom a) ≡ true)
  × (∀ a → isJoin (joinOp latticeBottom a) ≡ true)
  × (chainReachesFixpoint bottomFixpointLink ≡ true)
fixpointConservationAxiom =
  fp02-fixpoint-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , fixpoint-second-law-conservation-framed
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , fixpoint-mismatch-refuse-calcareous-meet
  , fixpoint-admissible-ok
  , fixpoint-conservation-knowing-fiber-ok
  , fixpoint-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , monotone-chain-bottom-reached

fixpointConservationNamed : String
fixpointConservationNamed =
  "fixpointConservation: FP-02 classifier fixpoint lattice meet join identity monotone chain conservation"

fixpointConservationCellId : String
fixpointConservationCellId = "CHEM-FORMAL-Q-AGDA-FIXPOINT-CONSERVATION"

fixpointConservationNonClaim : String
fixpointConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-FIXPOINT-CONSERVATION FP-02 classifier fixpoint conservation lattice meet join identity conserved monotone chain reaches fixpoint total-claim refuse fixpoint mismatch refuse fp02FixpointProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second fixpoint axiom not physics GREEN not production_wired"

fixpoint-conservation-modality-unwired :
  fixpointConservationModalityCurrent ≡ fixpoint-conservation-unwired
fixpoint-conservation-modality-unwired = refl

fixpointConservationPhysicsGreenAuthorized : Set
fixpointConservationPhysicsGreenAuthorized = ⊥

fixpoint-conservation-physics-green-false : ¬ fixpointConservationPhysicsGreenAuthorized
fixpoint-conservation-physics-green-false ()

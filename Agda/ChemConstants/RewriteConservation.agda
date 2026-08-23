-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.RewriteConservation.agda
--
-- FP-03 classifier-**rewrite** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Thermo-preserving **fusion** identity conserved at thermo-identity
--   * Non-preserving **rewrite** step fail-closed
--   * Total-claim refuse without **rewrite** witness; non-preserving refuse
--   * **rewrite** laws Unwired (fp03RewriteProved = false)
--
-- Mirrors sibling `ChemConstants/FixpointConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.RewriteConservation where

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
-- Modality + FP-03 classifier-**rewrite** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data RewriteConservationModality : Set where
  rewrite-conservation-unwired rewrite-conservation-assumed
    rewrite-conservation-proved rewrite-conservation-surrogate
    : RewriteConservationModality

rewriteConservationModalityCurrent : RewriteConservationModality
rewriteConservationModalityCurrent = rewrite-conservation-unwired

fp03RewriteProved productionWired not118SquaredGreenTable
  rewriteSecondLawConservationFramed : Bool
fp03RewriteProved = false
productionWired = false
not118SquaredGreenTable = true
rewriteSecondLawConservationFramed = true

------------------------------------------------------------------------
-- **Rewrite** law lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

rewriteLawLatticeCardinality : ℕ
rewriteLawLatticeCardinality = 4

rewrite-law-lattice-cardinality-four : rewriteLawLatticeCardinality ≡ 4
rewrite-law-lattice-cardinality-four = refl

rewrite-law-lattice-not-118-squared :
  does (rewriteLawLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
rewrite-law-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- ClassifierRewriteStep scaffold — thermo-preserving **fusion** / **rewrite**
------------------------------------------------------------------------

data ClassifierTag : Set where
  hematite-dominant bauxite-dominant calcareous-gangue : ClassifierTag

data ClassifierRewriteStep : Set where
  thermo-identity : ClassifierRewriteStep
  leaf : ClassifierTag → ClassifierRewriteStep
  thermo-fusion : ClassifierRewriteStep → ClassifierRewriteStep → ClassifierRewriteStep
  non-preserving-rewrite : ClassifierRewriteStep → ClassifierRewriteStep → ClassifierRewriteStep

thermoIdentity : ClassifierRewriteStep
thermoIdentity = thermo-identity

fusionOp rewriteOp : ClassifierRewriteStep → ClassifierRewriteStep → ClassifierRewriteStep
fusionOp = thermo-fusion
rewriteOp = non-preserving-rewrite

hematiteLeaf bauxiteLeaf calcareousLeaf : ClassifierRewriteStep
hematiteLeaf = leaf hematite-dominant
bauxiteLeaf = leaf bauxite-dominant
calcareousLeaf = leaf calcareous-gangue

isThermoFusion isNonPreservingRewrite : ClassifierRewriteStep → Bool
isThermoFusion (thermo-fusion _ _) = true
isThermoFusion _ = false

isNonPreservingRewrite (non-preserving-rewrite _ _) = true
isNonPreservingRewrite _ = false

isThermoIdentity : ClassifierRewriteStep → Bool
isThermoIdentity thermo-identity = true
isThermoIdentity _ = false

------------------------------------------------------------------------
-- Thermo-preserving **fusion** identity conserved at thermo-identity
------------------------------------------------------------------------

fusion-left-identity :
  ∀ (a : ClassifierRewriteStep) →
  isThermoIdentity thermoIdentity ≡ true × isThermoFusion (fusionOp thermoIdentity a) ≡ true
fusion-left-identity a = refl , refl

fusion-right-identity :
  ∀ (a : ClassifierRewriteStep) →
  isThermoFusion (fusionOp a thermoIdentity) ≡ true × isThermoIdentity thermoIdentity ≡ true
fusion-right-identity a = refl , refl

thermo-preserving-fusion-identity-conserved :
  (∀ a → isThermoFusion (fusionOp thermoIdentity a) ≡ true)
  × (∀ a → isThermoFusion (fusionOp a thermoIdentity) ≡ true)
thermo-preserving-fusion-identity-conserved =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Thermo-preserving admissibility — non-preserving **rewrite** fail-closed
------------------------------------------------------------------------

data RewriteAdmissibility : Set where
  rewrite-admissible rewrite-non-preserving-refuse : RewriteAdmissibility

isThermoPreserving : ClassifierRewriteStep → Bool
isThermoPreserving thermo-identity = true
isThermoPreserving (leaf hematite-dominant) = true
isThermoPreserving (leaf bauxite-dominant) = true
isThermoPreserving (leaf calcareous-gangue) = false
isThermoPreserving (thermo-fusion a b) =
  isThermoPreserving a ∧ isThermoPreserving b
isThermoPreserving (non-preserving-rewrite _ _) = false

isRewriteAdmissible : ClassifierRewriteStep → Bool
isRewriteAdmissible step = isThermoPreserving step

hematite-leaf-admissible : isRewriteAdmissible hematiteLeaf ≡ true
hematite-leaf-admissible = refl

bauxite-leaf-admissible : isRewriteAdmissible bauxiteLeaf ≡ true
bauxite-leaf-admissible = refl

calcareous-leaf-non-preserving : isRewriteAdmissible calcareousLeaf ≡ false
calcareous-leaf-non-preserving = refl

thermo-fusion-admissible :
  isRewriteAdmissible (fusionOp hematiteLeaf bauxiteLeaf) ≡ true
thermo-fusion-admissible = refl

non-preserving-rewrite-refuse :
  isRewriteAdmissible (rewriteOp hematiteLeaf bauxiteLeaf) ≡ false
non-preserving-rewrite-refuse = refl

thermo-fusion-with-forbidden-non-preserving :
  isRewriteAdmissible (fusionOp hematiteLeaf calcareousLeaf) ≡ false
thermo-fusion-with-forbidden-non-preserving = refl

------------------------------------------------------------------------
-- **Rewrite** witness — total-claim refuse without witness
------------------------------------------------------------------------

data RewriteWitnessPresence : Set where
  rewrite-witness-absent rewrite-witness-present : RewriteWitnessPresence

record ClassifierRewriteWitness : Set where
  constructor mkClassifierRewriteWitness
  field
    witness-presence : RewriteWitnessPresence
    thermo-gap-total : ℕ

rewriteWitnessAbsent : ClassifierRewriteWitness
rewriteWitnessAbsent = mkClassifierRewriteWitness rewrite-witness-absent zero

rewriteWitnessPresentZeroGap : ClassifierRewriteWitness
rewriteWitnessPresentZeroGap = mkClassifierRewriteWitness rewrite-witness-present zero

rewriteWitnessPresentWithGaps : ℕ → ClassifierRewriteWitness
rewriteWitnessPresentWithGaps n = mkClassifierRewriteWitness rewrite-witness-present n

rewriteWitnessGapFree : ClassifierRewriteWitness → Bool
rewriteWitnessGapFree (mkClassifierRewriteWitness rewrite-witness-absent _) = false
rewriteWitnessGapFree (mkClassifierRewriteWitness rewrite-witness-present n) =
  does (n ℕ-Props.≟ zero)

rewrite-witness-present-zero-gap-free :
  rewriteWitnessGapFree rewriteWitnessPresentZeroGap ≡ true
rewrite-witness-present-zero-gap-free = refl

rewrite-witness-absent-not-gap-free :
  rewriteWitnessGapFree rewriteWitnessAbsent ≡ false
rewrite-witness-absent-not-gap-free = refl

rewrite-witness-with-gaps-not-gap-free :
  ∀ n → rewriteWitnessGapFree (rewriteWitnessPresentWithGaps (suc n)) ≡ false
rewrite-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-**rewrite** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data RewriteConservationVerdict : Set where
  verdict-unwired-ok verdict-rewrite-admissible-ok
    verdict-total-claim-refuse verdict-non-preserving-refuse
    verdict-green-invent-refuse
    : RewriteConservationVerdict

rewriteConservationVerdictOk : RewriteConservationVerdict → Bool
rewriteConservationVerdictOk verdict-unwired-ok = true
rewriteConservationVerdictOk verdict-rewrite-admissible-ok = true
rewriteConservationVerdictOk _ = false

evaluateRewriteConservationClose :
  RewriteConservationModality → ClassifierRewriteStep → ClassifierRewriteWitness → Bool
  → RewriteConservationVerdict
evaluateRewriteConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateRewriteConservationClose rewrite-conservation-unwired _ _ false = verdict-unwired-ok
evaluateRewriteConservationClose rewrite-conservation-assumed _ _ false = verdict-unwired-ok
evaluateRewriteConservationClose rewrite-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateRewriteConservationClose rewrite-conservation-proved step (mkClassifierRewriteWitness rewrite-witness-absent _) false =
  verdict-total-claim-refuse
evaluateRewriteConservationClose rewrite-conservation-proved step (mkClassifierRewriteWitness rewrite-witness-present _) false
  with isRewriteAdmissible step
... | false = verdict-non-preserving-refuse
... | true  = verdict-rewrite-admissible-ok

------------------------------------------------------------------------
-- Sample admissible classifier-**rewrite** scaffold
------------------------------------------------------------------------

thermo-fusion-refine-rewrite : ClassifierRewriteStep
thermo-fusion-refine-rewrite = fusionOp hematiteLeaf bauxiteLeaf

thermo-fusion-refine-rewrite-admissible : isRewriteAdmissible thermo-fusion-refine-rewrite ≡ true
thermo-fusion-refine-rewrite-admissible = refl

------------------------------------------------------------------------
-- Unwired close — design scaffold without **rewrite** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateRewriteConservationClose
    rewrite-conservation-unwired thermo-fusion-refine-rewrite rewriteWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateRewriteConservationClose
    rewrite-conservation-assumed thermo-fusion-refine-rewrite rewriteWitnessAbsent false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateRewriteConservationClose
    rewrite-conservation-surrogate thermo-fusion-refine-rewrite rewriteWitnessAbsent false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  rewriteConservationVerdictOk
    (evaluateRewriteConservationClose rewrite-conservation-unwired thermo-fusion-refine-rewrite rewriteWitnessAbsent false)
    ≡ true
  × rewriteConservationVerdictOk
      (evaluateRewriteConservationClose rewrite-conservation-assumed thermo-fusion-refine-rewrite rewriteWitnessAbsent false)
      ≡ true
  × rewriteConservationVerdictOk
      (evaluateRewriteConservationClose rewrite-conservation-surrogate thermo-fusion-refine-rewrite rewriteWitnessAbsent false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **rewrite** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateRewriteConservationClose
    rewrite-conservation-proved thermo-fusion-refine-rewrite rewriteWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  rewriteConservationVerdictOk
    (evaluateRewriteConservationClose
       rewrite-conservation-proved thermo-fusion-refine-rewrite rewriteWitnessAbsent false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateRewriteConservationClose
    rewrite-conservation-proved thermo-fusion-refine-rewrite rewriteWitnessAbsent false ≡
  verdict-rewrite-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- Non-preserving **rewrite** refuse — thermo-violating step fail-closed
------------------------------------------------------------------------

non-preserving-refuse-calcareous-leaf :
  evaluateRewriteConservationClose
    rewrite-conservation-proved calcareousLeaf rewriteWitnessPresentZeroGap false ≡
  verdict-non-preserving-refuse
non-preserving-refuse-calcareous-leaf = refl

non-preserving-refuse-rewrite-op :
  evaluateRewriteConservationClose
    rewrite-conservation-proved (rewriteOp hematiteLeaf bauxiteLeaf) rewriteWitnessPresentZeroGap false ≡
  verdict-non-preserving-refuse
non-preserving-refuse-rewrite-op = refl

non-preserving-refuse-fusion-with-forbidden :
  evaluateRewriteConservationClose
    rewrite-conservation-proved (fusionOp hematiteLeaf calcareousLeaf) rewriteWitnessPresentZeroGap false ≡
  verdict-non-preserving-refuse
non-preserving-refuse-fusion-with-forbidden = refl

non-preserving-refuse-not-ok :
  rewriteConservationVerdictOk
    (evaluateRewriteConservationClose
       rewrite-conservation-proved calcareousLeaf rewriteWitnessPresentZeroGap false)
    ≡ false
non-preserving-refuse-not-ok = refl

NonPreservingWhenCalcareous : Set
NonPreservingWhenCalcareous =
  evaluateRewriteConservationClose
    rewrite-conservation-proved calcareousLeaf rewriteWitnessPresentZeroGap false ≡
  verdict-rewrite-admissible-ok

non-preserving-⊥-when-calcareous : NonPreservingWhenCalcareous → ⊥
non-preserving-⊥-when-calcareous ()

------------------------------------------------------------------------
-- Admissible classifier-**rewrite** — witness present + thermo-preserving step
------------------------------------------------------------------------

rewrite-admissible-ok :
  evaluateRewriteConservationClose
    rewrite-conservation-proved thermo-fusion-refine-rewrite rewriteWitnessPresentZeroGap false ≡
  verdict-rewrite-admissible-ok
rewrite-admissible-ok = refl

rewrite-admissible-verdict-ok :
  rewriteConservationVerdictOk
    (evaluateRewriteConservationClose
       rewrite-conservation-proved thermo-fusion-refine-rewrite rewriteWitnessPresentZeroGap false)
    ≡ true
rewrite-admissible-verdict-ok = refl

rewrite-admissible-ok-still-not-fp03-proved :
  rewriteConservationVerdictOk
    (evaluateRewriteConservationClose
       rewrite-conservation-proved thermo-fusion-refine-rewrite rewriteWitnessPresentZeroGap false)
    ≡ true
  × fp03RewriteProved ≡ false
rewrite-admissible-ok-still-not-fp03-proved = rewrite-admissible-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateRewriteConservationClose
    rewrite-conservation-unwired thermo-fusion-refine-rewrite rewriteWitnessPresentZeroGap true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  rewriteConservationVerdictOk
    (evaluateRewriteConservationClose
       rewrite-conservation-unwired thermo-fusion-refine-rewrite rewriteWitnessPresentZeroGap true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

rewriteConservationFiberOk : FormalFiber → Bool
rewriteConservationFiberOk fiber-quantum-knowing = true
rewriteConservationFiberOk fiber-meso-acting = false

rewrite-conservation-knowing-fiber-ok :
  rewriteConservationFiberOk fiber-quantum-knowing ≡ true
rewrite-conservation-knowing-fiber-ok = refl

rewrite-conservation-meso-acting-not-ok :
  rewriteConservationFiberOk fiber-meso-acting ≡ false
rewrite-conservation-meso-acting-not-ok = refl

rewrite-conservation-routes-knowing-not-meso :
  rewriteConservationFiberOk fiber-quantum-knowing ≡ true ×
  rewriteConservationFiberOk fiber-meso-acting ≡ false
rewrite-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  rewriteConservationFiberOk fiber-quantum-knowing ∧
  not (rewriteConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not FP-03 Proved, not physics GREEN
------------------------------------------------------------------------

fp03-rewrite-not-proved : fp03RewriteProved ≡ false
fp03-rewrite-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

rewrite-second-law-conservation-framed : rewriteSecondLawConservationFramed ≡ true
rewrite-second-law-conservation-framed = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second **rewrite** axiom fork)
------------------------------------------------------------------------

rewriteConservationAxiom :
  (fp03RewriteProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (rewriteSecondLawConservationFramed ≡ true)
  × (evaluateRewriteConservationClose rewrite-conservation-unwired thermo-fusion-refine-rewrite rewriteWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateRewriteConservationClose rewrite-conservation-proved thermo-fusion-refine-rewrite rewriteWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateRewriteConservationClose rewrite-conservation-proved calcareousLeaf rewriteWitnessPresentZeroGap false ≡ verdict-non-preserving-refuse)
  × (evaluateRewriteConservationClose rewrite-conservation-proved thermo-fusion-refine-rewrite rewriteWitnessPresentZeroGap false ≡ verdict-rewrite-admissible-ok)
  × (rewriteConservationFiberOk fiber-quantum-knowing ≡ true)
  × (rewriteConservationFiberOk fiber-meso-acting ≡ false)
  × (rewriteConservationVerdictOk (evaluateRewriteConservationClose rewrite-conservation-unwired thermo-fusion-refine-rewrite rewriteWitnessPresentZeroGap true) ≡ false)
  × (∀ a → isThermoFusion (fusionOp thermoIdentity a) ≡ true)
  × (∀ a → isThermoFusion (fusionOp a thermoIdentity) ≡ true)
  × (isRewriteAdmissible (rewriteOp hematiteLeaf bauxiteLeaf) ≡ false)
rewriteConservationAxiom =
  fp03-rewrite-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , rewrite-second-law-conservation-framed
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , non-preserving-refuse-calcareous-leaf
  , rewrite-admissible-ok
  , rewrite-conservation-knowing-fiber-ok
  , rewrite-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , non-preserving-rewrite-refuse

rewriteConservationNamed : String
rewriteConservationNamed =
  "rewriteConservation: FP-03 classifier rewrite thermo-preserving fusion identity conservation"

rewriteConservationCellId : String
rewriteConservationCellId = "CHEM-FORMAL-Q-AGDA-REWRITE-CONSERVATION"

rewriteConservationNonClaim : String
rewriteConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-REWRITE-CONSERVATION FP-03 classifier rewrite conservation thermo-preserving fusion identity conserved non-preserving rewrite step fail-closed total-claim refuse fp03RewriteProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second rewrite axiom not physics GREEN not production_wired"

rewrite-conservation-modality-unwired :
  rewriteConservationModalityCurrent ≡ rewrite-conservation-unwired
rewrite-conservation-modality-unwired = refl

rewriteConservationPhysicsGreenAuthorized : Set
rewriteConservationPhysicsGreenAuthorized = ⊥

rewrite-conservation-physics-green-false : ¬ rewriteConservationPhysicsGreenAuthorized
rewrite-conservation-physics-green-false ()

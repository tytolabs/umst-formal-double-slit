-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.PhaseEutecticSolidSolutionConservation.agda
--
-- Pattern class 13 **phase_eutectic_solid_solution** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Concurrent Π_c identity conserved (phase edge scaffold + CALPHAD Gmin + class 13 phase_eutectic_solid_solution;
--     **product** not XOR, no parallel phase_eutectic_solid_solution axiom)
--   * XOR mutually-exclusive refuse; phase-eutectic-solid-solution nuance witness concurrent
--     (phase edge scaffold + CALPHAD Gmin + class 13 phase_eutectic_solid_solution)
--   * **phase_eutectic_solid_solution** laws Unwired (phaseEutecticSolidSolution13Proved = false)
--
-- INT (read-only cite): umst/umst-chem/src/phase_eutectic_nonstoich.rs
-- L0 table: umst/umst-chem/src/l0_tables/phase_eutectic_solid_solution.rs
-- Mirrors sibling `ChemConstants/PatternProductConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
-- No parallel phase_eutectic_solid_solution axiom; line compound not all solids. Product not XOR.
------------------------------------------------------------------------
module ChemConstants.PhaseEutecticSolidSolutionConservation where


open import Data.Bool.Base using (Bool; false; true; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties as ℕ-Props using (_≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + pattern class 13 **phase_eutectic_solid_solution** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PhaseEutecticSolidSolutionConservationModality : Set where
  phase-eutectic-solid-solution-conservation-unwired phase-eutectic-solid-solution-conservation-assumed
    phase-eutectic-solid-solution-conservation-proved phase-eutectic-solid-solution-conservation-surrogate
    : PhaseEutecticSolidSolutionConservationModality

phaseEutecticSolidSolutionConservationModalityCurrent : PhaseEutecticSolidSolutionConservationModality
phaseEutecticSolidSolutionConservationModalityCurrent = phase-eutectic-solid-solution-conservation-unwired

phaseEutecticSolidSolution13Proved productionWired not118SquaredGreenTable
  phaseEutecticSolidSolutionSecondLawConservationFramed phaseEutecticSolidSolutionNotXor : Bool
phaseEutecticSolidSolution13Proved = false
productionWired = false
not118SquaredGreenTable = true
phaseEutecticSolidSolutionSecondLawConservationFramed = true
phaseEutecticSolidSolutionNotXor = true

phaseEdgeIsScaffold notParallelPhaseEutecticSolidSolutionAxiomMinted lineCompoundNotAllSolids : Bool
phaseEdgeIsScaffold = true
notParallelPhaseEutecticSolidSolutionAxiomMinted = true
lineCompoundNotAllSolids = true

------------------------------------------------------------------------
-- Pattern class cardinality 25 — Π_c structure, not 118²
------------------------------------------------------------------------

patternClassCardinality : ℕ
patternClassCardinality = 25

pattern-class-cardinality-twenty-five : patternClassCardinality ≡ 25
pattern-class-cardinality-twenty-five = refl

pattern-class-not-118-squared :
  does (patternClassCardinality ℕ-Props.≟ (118 * 118)) ≡ false
pattern-class-not-118-squared = refl

------------------------------------------------------------------------
-- Pattern class 13 Phase-eutectic-solid-solution index pin
------------------------------------------------------------------------

phaseEutecticSolidSolutionClassIndex : ℕ
phaseEutecticSolidSolutionClassIndex = 13

phase-eutectic-solid-solution-class-index-thirteen : phaseEutecticSolidSolutionClassIndex ≡ 13
phase-eutectic-solid-solution-class-index-thirteen = refl

------------------------------------------------------------------------
-- Named element Z pins — Fe (Z=26), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  iron oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ iron = 26
elementAtomicZ oganesson = 118

iron-z-26 : elementAtomicZ iron ≡ 26
iron-z-26 = refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- PhaseEutecticSolidSolutionBundle slot modality — concurrent **product** factor, not XOR bucket
------------------------------------------------------------------------

data PhaseEutecticSolidSolutionBundleSlot : Set where
  bundle-unwired bundle-absent bundle-present : PhaseEutecticSolidSolutionBundleSlot

isSlotPresent : PhaseEutecticSolidSolutionBundleSlot → Bool
isSlotPresent bundle-present = true
isSlotPresent _ = false

------------------------------------------------------------------------
-- PhaseEutecticSolidSolutionBundle_25 — many channels may hold at once (Π_c **product**)
------------------------------------------------------------------------

record PhaseEutecticSolidSolutionBundle : Set where
  field slot : ℕ → PhaseEutecticSolidSolutionBundleSlot

phaseEutecticSolidSolutionBundleUnwired : PhaseEutecticSolidSolutionBundle
phaseEutecticSolidSolutionBundleUnwired = record { slot = λ _ → bundle-unwired }

slotEq : ℕ → ℕ → Bool
slotEq zero zero = true
slotEq (suc m) (suc n) = slotEq m n
slotEq _ _ = false

withSlot : PhaseEutecticSolidSolutionBundle → ℕ → PhaseEutecticSolidSolutionBundleSlot → PhaseEutecticSolidSolutionBundle
withSlot b i s = record
  { slot = λ j → if slotEq j i then s else PhaseEutecticSolidSolutionBundle.slot b j }

withPresent : PhaseEutecticSolidSolutionBundle → ℕ → PhaseEutecticSolidSolutionBundle
withPresent b i = withSlot b i bundle-present

------------------------------------------------------------------------
-- Present count witness — concurrent **product** (≥2 Present, not XOR)
------------------------------------------------------------------------

record PhaseEutecticSolidSolutionBundleWitness : Set where
  constructor mkPhaseEutecticSolidSolutionBundleWitness
  field
    bundle : PhaseEutecticSolidSolutionBundle
    present-count : ℕ

phaseEutecticSolidSolutionBundleIsConcurrentProduct : PhaseEutecticSolidSolutionBundleWitness → Bool
phaseEutecticSolidSolutionBundleIsConcurrentProduct w =
  does ((suc (suc zero)) ℕ-Props.≤? PhaseEutecticSolidSolutionBundleWitness.present-count w)

------------------------------------------------------------------------
-- Named phase-eutectic-solid-solution channel indices — phase edge scaffold (1), CALPHAD Gmin (2), class 13 phase_eutectic_solid_solution (3)
------------------------------------------------------------------------

phaseEdgeScaffoldChannelIndex calphadGminChannelIndex class9PhaseEutecticSolidSolutionChannelIndex : ℕ
phaseEdgeScaffoldChannelIndex = 1
calphadGminChannelIndex = 2
class9PhaseEutecticSolidSolutionChannelIndex = 3

phase-edge-scaffold-index-one : phaseEdgeScaffoldChannelIndex ≡ 1
phase-edge-scaffold-index-one = refl

calphad-gmin-index-two : calphadGminChannelIndex ≡ 2
calphad-gmin-index-two = refl

class9-phase-eutectic-solid-solution-index-three : class9PhaseEutecticSolidSolutionChannelIndex ≡ 3
class9-phase-eutectic-solid-solution-index-three = refl

------------------------------------------------------------------------
-- Phase-eutectic-solid-solution nuance witness — phase edge scaffold + CALPHAD Gmin + class 13 phase_eutectic_solid_solution concurrent
------------------------------------------------------------------------

phaseEutecticSolidSolutionNuanceBundle : PhaseEutecticSolidSolutionBundle
phaseEutecticSolidSolutionNuanceBundle =
  withPresent
    (withPresent
      (withPresent phaseEutecticSolidSolutionBundleUnwired phaseEdgeScaffoldChannelIndex)
      calphadGminChannelIndex)
    class9PhaseEutecticSolidSolutionChannelIndex

phaseEutecticSolidSolutionNuanceWitness : PhaseEutecticSolidSolutionBundleWitness
phaseEutecticSolidSolutionNuanceWitness =
  mkPhaseEutecticSolidSolutionBundleWitness phaseEutecticSolidSolutionNuanceBundle 3

phase-eutectic-solid-solution-nuance-phase-edge-scaffold-present :
  isSlotPresent (PhaseEutecticSolidSolutionBundle.slot phaseEutecticSolidSolutionNuanceBundle phaseEdgeScaffoldChannelIndex) ≡ true
phase-eutectic-solid-solution-nuance-phase-edge-scaffold-present = refl

phase-eutectic-solid-solution-nuance-calphad-gmin-present :
  isSlotPresent (PhaseEutecticSolidSolutionBundle.slot phaseEutecticSolidSolutionNuanceBundle calphadGminChannelIndex) ≡ true
phase-eutectic-solid-solution-nuance-calphad-gmin-present = refl

phase-eutectic-solid-solution-nuance-class9-phase-eutectic-solid-solution-present :
  isSlotPresent (PhaseEutecticSolidSolutionBundle.slot phaseEutecticSolidSolutionNuanceBundle class9PhaseEutecticSolidSolutionChannelIndex) ≡ true
phase-eutectic-solid-solution-nuance-class9-phase-eutectic-solid-solution-present = refl

phase-eutectic-solid-solution-nuance-present-count : PhaseEutecticSolidSolutionBundleWitness.present-count phaseEutecticSolidSolutionNuanceWitness ≡ 3
phase-eutectic-solid-solution-nuance-present-count = refl

phase-eutectic-solid-solution-nuance-concurrent-product :
  phaseEutecticSolidSolutionBundleIsConcurrentProduct phaseEutecticSolidSolutionNuanceWitness ≡ true
phase-eutectic-solid-solution-nuance-concurrent-product = refl

phase-eutectic-solid-solution-nuance-three-factors-concurrent :
  isSlotPresent (PhaseEutecticSolidSolutionBundle.slot phaseEutecticSolidSolutionNuanceBundle phaseEdgeScaffoldChannelIndex) ≡ true
  × isSlotPresent (PhaseEutecticSolidSolutionBundle.slot phaseEutecticSolidSolutionNuanceBundle calphadGminChannelIndex) ≡ true
  × isSlotPresent (PhaseEutecticSolidSolutionBundle.slot phaseEutecticSolidSolutionNuanceBundle class9PhaseEutecticSolidSolutionChannelIndex) ≡ true
  × PhaseEutecticSolidSolutionBundleWitness.present-count phaseEutecticSolidSolutionNuanceWitness ≡ 3
phase-eutectic-solid-solution-nuance-three-factors-concurrent =
  phase-eutectic-solid-solution-nuance-phase-edge-scaffold-present
  , phase-eutectic-solid-solution-nuance-calphad-gmin-present
  , phase-eutectic-solid-solution-nuance-class9-phase-eutectic-solid-solution-present
  , phase-eutectic-solid-solution-nuance-present-count

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect, not desired **product**
------------------------------------------------------------------------

data XorRefuseVerdict : Set where
  xor-refuse xor-product-ok : XorRefuseVerdict

evaluateXorRefuse : PhaseEutecticSolidSolutionBundleWitness → ℕ → ℕ → XorRefuseVerdict
evaluateXorRefuse w i j =
  if phaseEutecticSolidSolutionBundleIsConcurrentProduct w
  then xor-product-ok
  else let b = PhaseEutecticSolidSolutionBundleWitness.bundle w
       in if isSlotPresent (PhaseEutecticSolidSolutionBundle.slot b i)
          then if isSlotPresent (PhaseEutecticSolidSolutionBundle.slot b j)
               then xor-refuse
               else xor-product-ok
          else xor-product-ok

unwiredWitness : PhaseEutecticSolidSolutionBundleWitness
unwiredWitness = mkPhaseEutecticSolidSolutionBundleWitness phaseEutecticSolidSolutionBundleUnwired zero

xor-refuse-not-product-ok : evaluateXorRefuse unwiredWitness 0 1 ≡ xor-product-ok
xor-refuse-not-product-ok = refl

phase-eutectic-solid-solution-nuance-xor-product-ok :
  evaluateXorRefuse phaseEutecticSolidSolutionNuanceWitness phaseEdgeScaffoldChannelIndex calphadGminChannelIndex ≡ xor-product-ok
phase-eutectic-solid-solution-nuance-xor-product-ok = refl

phase-eutectic-solid-solution-not-xor : phaseEutecticSolidSolutionNotXor ≡ true
phase-eutectic-solid-solution-not-xor = refl

------------------------------------------------------------------------
-- ClassifierPhaseEutecticSolidSolutionStep scaffold — PhaseEutecticSolidSolutionBundle **conservation**
------------------------------------------------------------------------

data ClassifierPhaseEutecticSolidSolutionStep : Set where
  phase-eutectic-solid-solution-identity : ClassifierPhaseEutecticSolidSolutionStep
  slot-leaf : ℕ → ClassifierPhaseEutecticSolidSolutionStep
  product-concurrent : ClassifierPhaseEutecticSolidSolutionStep → ClassifierPhaseEutecticSolidSolutionStep → ClassifierPhaseEutecticSolidSolutionStep
  xor-mutually-exclusive : ClassifierPhaseEutecticSolidSolutionStep → ClassifierPhaseEutecticSolidSolutionStep → ClassifierPhaseEutecticSolidSolutionStep

phaseEutecticSolidSolutionIdentity : ClassifierPhaseEutecticSolidSolutionStep
phaseEutecticSolidSolutionIdentity = phase-eutectic-solid-solution-identity

productConcurrentOp xorMutuallyExclusiveOp :
  ClassifierPhaseEutecticSolidSolutionStep → ClassifierPhaseEutecticSolidSolutionStep → ClassifierPhaseEutecticSolidSolutionStep
productConcurrentOp = product-concurrent
xorMutuallyExclusiveOp = xor-mutually-exclusive

phaseEdgeScaffoldLeaf calphadGminLeaf class9PhaseEutecticSolidSolutionLeaf : ClassifierPhaseEutecticSolidSolutionStep
phaseEdgeScaffoldLeaf = slot-leaf phaseEdgeScaffoldChannelIndex
calphadGminLeaf = slot-leaf calphadGminChannelIndex
class9PhaseEutecticSolidSolutionLeaf = slot-leaf class9PhaseEutecticSolidSolutionChannelIndex

isProductConcurrent isXorMutuallyExclusive : ClassifierPhaseEutecticSolidSolutionStep → Bool
isProductConcurrent (product-concurrent _ _) = true
isProductConcurrent _ = false

isXorMutuallyExclusive (xor-mutually-exclusive _ _) = true
isXorMutuallyExclusive _ = false

isPhaseEutecticSolidSolutionIdentity : ClassifierPhaseEutecticSolidSolutionStep → Bool
isPhaseEutecticSolidSolutionIdentity phase-eutectic-solid-solution-identity = true
isPhaseEutecticSolidSolutionIdentity _ = false

------------------------------------------------------------------------
-- Concurrent Π_c identity conserved at phase-eutectic-solid-solution-identity
------------------------------------------------------------------------

phase-eutectic-solid-solution-left-identity :
  ∀ (a : ClassifierPhaseEutecticSolidSolutionStep) →
  isPhaseEutecticSolidSolutionIdentity phaseEutecticSolidSolutionIdentity ≡ true
  × isProductConcurrent (productConcurrentOp phaseEutecticSolidSolutionIdentity a) ≡ true
phase-eutectic-solid-solution-left-identity a = refl , refl

phase-eutectic-solid-solution-right-identity :
  ∀ (a : ClassifierPhaseEutecticSolidSolutionStep) →
  isProductConcurrent (productConcurrentOp a phaseEutecticSolidSolutionIdentity) ≡ true
  × isPhaseEutecticSolidSolutionIdentity phaseEutecticSolidSolutionIdentity ≡ true
phase-eutectic-solid-solution-right-identity a = refl , refl

concurrent-pi-c-identity-conserved-at-phase-eutectic-solid-solution :
  (∀ a → isProductConcurrent (productConcurrentOp phaseEutecticSolidSolutionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a phaseEutecticSolidSolutionIdentity) ≡ true)
concurrent-pi-c-identity-conserved-at-phase-eutectic-solid-solution =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named phase-eutectic-solid-solution nuance **product** closed — concurrent classifiers
------------------------------------------------------------------------

namedPhaseEutecticSolidSolutionNuanceProduct : ClassifierPhaseEutecticSolidSolutionStep
namedPhaseEutecticSolidSolutionNuanceProduct =
  productConcurrentOp
    (productConcurrentOp phaseEdgeScaffoldLeaf calphadGminLeaf)
    class9PhaseEutecticSolidSolutionLeaf

named-phase-eutectic-solid-solution-nuance-product-concurrent :
  isProductConcurrent namedPhaseEutecticSolidSolutionNuanceProduct ≡ true
  × phaseEutecticSolidSolutionBundleIsConcurrentProduct phaseEutecticSolidSolutionNuanceWitness ≡ true
named-phase-eutectic-solid-solution-nuance-product-concurrent = refl , phase-eutectic-solid-solution-nuance-concurrent-product

------------------------------------------------------------------------
-- PhaseEutecticSolidSolutionBundle admissibility — XOR refuse fail-closed
------------------------------------------------------------------------

data PhaseEutecticSolidSolutionAdmissibility : Set where
  phase-eutectic-solid-solution-admissible phase-eutectic-solid-solution-xor-refuse : PhaseEutecticSolidSolutionAdmissibility

isPhaseEutecticSolidSolutionPreserving : ClassifierPhaseEutecticSolidSolutionStep → Bool
isPhaseEutecticSolidSolutionPreserving phase-eutectic-solid-solution-identity = true
isPhaseEutecticSolidSolutionPreserving (slot-leaf _) = true
isPhaseEutecticSolidSolutionPreserving (product-concurrent a b) =
  isPhaseEutecticSolidSolutionPreserving a ∧ isPhaseEutecticSolidSolutionPreserving b
isPhaseEutecticSolidSolutionPreserving (xor-mutually-exclusive _ _) = false

isPhaseEutecticSolidSolutionAdmissible : ClassifierPhaseEutecticSolidSolutionStep → Bool
isPhaseEutecticSolidSolutionAdmissible step = isPhaseEutecticSolidSolutionPreserving step

phase-edge-scaffold-leaf-admissible : isPhaseEutecticSolidSolutionAdmissible phaseEdgeScaffoldLeaf ≡ true
phase-edge-scaffold-leaf-admissible = refl

calphad-gmin-leaf-admissible : isPhaseEutecticSolidSolutionAdmissible calphadGminLeaf ≡ true
calphad-gmin-leaf-admissible = refl

class9-phase-eutectic-solid-solution-leaf-admissible : isPhaseEutecticSolidSolutionAdmissible class9PhaseEutecticSolidSolutionLeaf ≡ true
class9-phase-eutectic-solid-solution-leaf-admissible = refl

named-phase-eutectic-solid-solution-nuance-admissible : isPhaseEutecticSolidSolutionAdmissible namedPhaseEutecticSolidSolutionNuanceProduct ≡ true
named-phase-eutectic-solid-solution-nuance-admissible = refl

xor-mutually-exclusive-refuse :
  isPhaseEutecticSolidSolutionAdmissible (xorMutuallyExclusiveOp phaseEdgeScaffoldLeaf calphadGminLeaf) ≡ false
xor-mutually-exclusive-refuse = refl

xor-mutually-exclusive-class9-phase-eutectic-solid-solution-refuse :
  isPhaseEutecticSolidSolutionAdmissible (xorMutuallyExclusiveOp calphadGminLeaf class9PhaseEutecticSolidSolutionLeaf) ≡ false
xor-mutually-exclusive-class9-phase-eutectic-solid-solution-refuse = refl

------------------------------------------------------------------------
-- Assemblage-stability-why witness — total-claim refuse without witness
------------------------------------------------------------------------

data PhaseEutecticSolidSolutionWitnessPresence : Set where
  phase-eutectic-solid-solution-witness-absent phase-eutectic-solid-solution-witness-present : PhaseEutecticSolidSolutionWitnessPresence

record ClassifierPhaseEutecticSolidSolutionWitness : Set where
  constructor mkClassifierPhaseEutecticSolidSolutionWitness
  field
    witness-presence : PhaseEutecticSolidSolutionWitnessPresence
    phase-eutectic-solid-solution-gap-total : ℕ

phaseEutecticSolidSolutionWitnessAbsent : ClassifierPhaseEutecticSolidSolutionWitness
phaseEutecticSolidSolutionWitnessAbsent = mkClassifierPhaseEutecticSolidSolutionWitness phase-eutectic-solid-solution-witness-absent zero

phaseEutecticSolidSolutionWitnessPresentZeroGap : ClassifierPhaseEutecticSolidSolutionWitness
phaseEutecticSolidSolutionWitnessPresentZeroGap = mkClassifierPhaseEutecticSolidSolutionWitness phase-eutectic-solid-solution-witness-present zero

phaseEutecticSolidSolutionWitnessPresentWithGaps : ℕ → ClassifierPhaseEutecticSolidSolutionWitness
phaseEutecticSolidSolutionWitnessPresentWithGaps n = mkClassifierPhaseEutecticSolidSolutionWitness phase-eutectic-solid-solution-witness-present n

phaseEutecticSolidSolutionWitnessGapFree : ClassifierPhaseEutecticSolidSolutionWitness → Bool
phaseEutecticSolidSolutionWitnessGapFree (mkClassifierPhaseEutecticSolidSolutionWitness phase-eutectic-solid-solution-witness-absent _) = false
phaseEutecticSolidSolutionWitnessGapFree (mkClassifierPhaseEutecticSolidSolutionWitness phase-eutectic-solid-solution-witness-present n) =
  does (n ℕ-Props.≟ zero)

phase-eutectic-solid-solution-witness-present-zero-gap-free :
  phaseEutecticSolidSolutionWitnessGapFree phaseEutecticSolidSolutionWitnessPresentZeroGap ≡ true
phase-eutectic-solid-solution-witness-present-zero-gap-free = refl

phase-eutectic-solid-solution-witness-absent-not-gap-free :
  phaseEutecticSolidSolutionWitnessGapFree phaseEutecticSolidSolutionWitnessAbsent ≡ false
phase-eutectic-solid-solution-witness-absent-not-gap-free = refl

phase-eutectic-solid-solution-witness-with-gaps-not-gap-free :
  ∀ n → phaseEutecticSolidSolutionWitnessGapFree (phaseEutecticSolidSolutionWitnessPresentWithGaps (suc n)) ≡ false
phase-eutectic-solid-solution-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-Phase-eutectic-solid-solution **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data PhaseEutecticSolidSolutionConservationVerdict : Set where
  verdict-unwired-ok verdict-phase-eutectic-solid-solution-admissible-ok
    verdict-concurrent-product-ok verdict-xor-mutually-exclusive-refuse
    verdict-total-claim-refuse verdict-green-invent-refuse
    : PhaseEutecticSolidSolutionConservationVerdict

phaseEutecticSolidSolutionConservationVerdictOk : PhaseEutecticSolidSolutionConservationVerdict → Bool
phaseEutecticSolidSolutionConservationVerdictOk verdict-unwired-ok = true
phaseEutecticSolidSolutionConservationVerdictOk verdict-phase-eutectic-solid-solution-admissible-ok = true
phaseEutecticSolidSolutionConservationVerdictOk verdict-concurrent-product-ok = true
phaseEutecticSolidSolutionConservationVerdictOk _ = false

evaluatePhaseEutecticSolidSolutionConservationClose :
  PhaseEutecticSolidSolutionConservationModality → ClassifierPhaseEutecticSolidSolutionStep → ClassifierPhaseEutecticSolidSolutionWitness
  → PhaseEutecticSolidSolutionBundleWitness → Bool → PhaseEutecticSolidSolutionConservationVerdict
evaluatePhaseEutecticSolidSolutionConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-proved _ (mkClassifierPhaseEutecticSolidSolutionWitness phase-eutectic-solid-solution-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-proved (xor-mutually-exclusive _ _) _ _ false =
  verdict-xor-mutually-exclusive-refuse
evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-proved _ (mkClassifierPhaseEutecticSolidSolutionWitness phase-eutectic-solid-solution-witness-present _) w false
  with phaseEutecticSolidSolutionBundleIsConcurrentProduct w
... | true  = verdict-concurrent-product-ok
... | false = verdict-phase-eutectic-solid-solution-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without phase-eutectic-solid-solution witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-unwired namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-assumed namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-surrogate namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  phaseEutecticSolidSolutionConservationVerdictOk
    (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-unwired namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false)
    ≡ true
  × phaseEutecticSolidSolutionConservationVerdictOk
      (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-assumed namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false)
      ≡ true
  × phaseEutecticSolidSolutionConservationVerdictOk
      (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-surrogate namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without phase-eutectic-solid-solution witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  phaseEutecticSolidSolutionConservationVerdictOk
    (evaluatePhaseEutecticSolidSolutionConservationClose
       phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false ≡
  verdict-phase-eutectic-solid-solution-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- XOR mutually-exclusive refuse — scaffold defect fail-closed
------------------------------------------------------------------------

xor-mutually-exclusive-refuse-verdict :
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-proved
    (xorMutuallyExclusiveOp phaseEdgeScaffoldLeaf calphadGminLeaf)
    phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness false ≡
  verdict-xor-mutually-exclusive-refuse
xor-mutually-exclusive-refuse-verdict = refl

xor-mutually-exclusive-refuse-not-ok :
  phaseEutecticSolidSolutionConservationVerdictOk
    (evaluatePhaseEutecticSolidSolutionConservationClose
       phase-eutectic-solid-solution-conservation-proved
       (xorMutuallyExclusiveOp phaseEdgeScaffoldLeaf calphadGminLeaf)
       phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness false)
    ≡ false
xor-mutually-exclusive-refuse-not-ok = refl

XorMutuallyExclusiveWhenConcurrent : Set
XorMutuallyExclusiveWhenConcurrent =
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-proved
    (xorMutuallyExclusiveOp phaseEdgeScaffoldLeaf calphadGminLeaf)
    phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness false ≡
  verdict-concurrent-product-ok

xor-mutually-exclusive-⊥-when-concurrent : XorMutuallyExclusiveWhenConcurrent → ⊥
xor-mutually-exclusive-⊥-when-concurrent ()

------------------------------------------------------------------------
-- Admissible classifier-phase-eutectic-solid-solution — nuance **product** closed
------------------------------------------------------------------------

phase-eutectic-solid-solution-admissible-ok :
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap unwiredWitness false ≡
  verdict-phase-eutectic-solid-solution-admissible-ok
phase-eutectic-solid-solution-admissible-ok = refl

phase-eutectic-solid-solution-admissible-verdict-ok :
  phaseEutecticSolidSolutionConservationVerdictOk
    (evaluatePhaseEutecticSolidSolutionConservationClose
       phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap unwiredWitness false)
    ≡ true
phase-eutectic-solid-solution-admissible-verdict-ok = refl

------------------------------------------------------------------------
-- Concurrent **product** ok — phase-eutectic-solid-solution nuance witness ≥2 Present
------------------------------------------------------------------------

concurrent-product-ok :
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness false ≡
  verdict-concurrent-product-ok
concurrent-product-ok = refl

concurrent-product-verdict-ok :
  phaseEutecticSolidSolutionConservationVerdictOk
    (evaluatePhaseEutecticSolidSolutionConservationClose
       phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness false)
    ≡ true
concurrent-product-verdict-ok = refl

concurrent-product-ok-still-not-phase-eutectic-solid-solution09-proved :
  phaseEutecticSolidSolutionConservationVerdictOk
    (evaluatePhaseEutecticSolidSolutionConservationClose
       phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness false)
    ≡ true
  × phaseEutecticSolidSolution13Proved ≡ false
concurrent-product-ok-still-not-phase-eutectic-solid-solution09-proved = concurrent-product-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluatePhaseEutecticSolidSolutionConservationClose
    phase-eutectic-solid-solution-conservation-unwired namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  phaseEutecticSolidSolutionConservationVerdictOk
    (evaluatePhaseEutecticSolidSolutionConservationClose
       phase-eutectic-solid-solution-conservation-unwired namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

phaseEutecticSolidSolutionConservationFiberOk : FormalFiber → Bool
phaseEutecticSolidSolutionConservationFiberOk fiber-quantum-knowing = true
phaseEutecticSolidSolutionConservationFiberOk fiber-meso-acting = false

phase-eutectic-solid-solution-conservation-knowing-fiber-ok :
  phaseEutecticSolidSolutionConservationFiberOk fiber-quantum-knowing ≡ true
phase-eutectic-solid-solution-conservation-knowing-fiber-ok = refl

phase-eutectic-solid-solution-conservation-meso-acting-not-ok :
  phaseEutecticSolidSolutionConservationFiberOk fiber-meso-acting ≡ false
phase-eutectic-solid-solution-conservation-meso-acting-not-ok = refl

phase-eutectic-solid-solution-conservation-routes-knowing-not-meso :
  phaseEutecticSolidSolutionConservationFiberOk fiber-quantum-knowing ≡ true ×
  phaseEutecticSolidSolutionConservationFiberOk fiber-meso-acting ≡ false
phase-eutectic-solid-solution-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  phaseEutecticSolidSolutionConservationFiberOk fiber-quantum-knowing ∧
  not (phaseEutecticSolidSolutionConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not class 13 phase_eutectic_solid_solution Proved, not physics GREEN, **product** not XOR
------------------------------------------------------------------------

phase-eutectic-solid-solution-13-not-proved : phaseEutecticSolidSolution13Proved ≡ false
phase-eutectic-solid-solution-13-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

phase-eutectic-solid-solution-second-law-conservation-framed : phaseEutecticSolidSolutionSecondLawConservationFramed ≡ true
phase-eutectic-solid-solution-second-law-conservation-framed = refl

phase-eutectic-solid-solution-not-xor-pin : phaseEutecticSolidSolutionNotXor ≡ true
phase-eutectic-solid-solution-not-xor-pin = phase-eutectic-solid-solution-not-xor

phase-edge-is-scaffold-pin : phaseEdgeIsScaffold ≡ true
phase-edge-is-scaffold-pin = refl

not-parallel-phase-eutectic-solid-solution-axiom-minted-pin : notParallelPhaseEutecticSolidSolutionAxiomMinted ≡ true
not-parallel-phase-eutectic-solid-solution-axiom-minted-pin = refl

line-compound-not-all-solids-pin : lineCompoundNotAllSolids ≡ true
line-compound-not-all-solids-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (no parallel phase_eutectic_solid_solution axiom fork)
------------------------------------------------------------------------

phaseEutecticSolidSolutionConservationAxiom :
  (phaseEutecticSolidSolution13Proved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (phaseEutecticSolidSolutionSecondLawConservationFramed ≡ true)
  × (phaseEutecticSolidSolutionNotXor ≡ true)
  × (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-unwired namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false ≡ verdict-unwired-ok)
  × (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessAbsent phaseEutecticSolidSolutionNuanceWitness false ≡ verdict-total-claim-refuse)
  × (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-proved (xorMutuallyExclusiveOp phaseEdgeScaffoldLeaf calphadGminLeaf) phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness false ≡ verdict-xor-mutually-exclusive-refuse)
  × (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap unwiredWitness false ≡ verdict-phase-eutectic-solid-solution-admissible-ok)
  × (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-proved namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness false ≡ verdict-concurrent-product-ok)
  × (phaseEutecticSolidSolutionConservationFiberOk fiber-quantum-knowing ≡ true)
  × (phaseEutecticSolidSolutionConservationFiberOk fiber-meso-acting ≡ false)
  × (phaseEutecticSolidSolutionConservationVerdictOk (evaluatePhaseEutecticSolidSolutionConservationClose phase-eutectic-solid-solution-conservation-unwired namedPhaseEutecticSolidSolutionNuanceProduct phaseEutecticSolidSolutionWitnessPresentZeroGap phaseEutecticSolidSolutionNuanceWitness true) ≡ false)
  × (∀ a → isProductConcurrent (productConcurrentOp phaseEutecticSolidSolutionIdentity a) ≡ true)
  × (∀ a → isProductConcurrent (productConcurrentOp a phaseEutecticSolidSolutionIdentity) ≡ true)
  × (isPhaseEutecticSolidSolutionAdmissible (xorMutuallyExclusiveOp phaseEdgeScaffoldLeaf calphadGminLeaf) ≡ false)
  × (patternClassCardinality ≡ 25)
  × (phaseEutecticSolidSolutionClassIndex ≡ 13)
  × (PhaseEutecticSolidSolutionBundleWitness.present-count phaseEutecticSolidSolutionNuanceWitness ≡ 3)
  × (elementAtomicZ iron ≡ 26)
  × (elementAtomicZ oganesson ≡ 118)
phaseEutecticSolidSolutionConservationAxiom =
  phase-eutectic-solid-solution-13-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , phase-eutectic-solid-solution-second-law-conservation-framed
  , phase-eutectic-solid-solution-not-xor-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , xor-mutually-exclusive-refuse-verdict
  , phase-eutectic-solid-solution-admissible-ok
  , concurrent-product-ok
  , phase-eutectic-solid-solution-conservation-knowing-fiber-ok
  , phase-eutectic-solid-solution-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , xor-mutually-exclusive-refuse
  , pattern-class-cardinality-twenty-five
  , phase-eutectic-solid-solution-class-index-thirteen
  , phase-eutectic-solid-solution-nuance-present-count
  , iron-z-26
  , oganesson-z-118

phaseEutecticSolidSolutionConservationNamed : String
phaseEutecticSolidSolutionConservationNamed =
  "phaseEutecticSolidSolutionConservation: pattern class 13 phase_eutectic_solid_solution conservation concurrent Pi_c identity conserved phase edge scaffold CALPHAD Gmin class 13 phase_eutectic_solid_solution concurrent product identity conserved present ge 2 product not XOR phase edge is scaffold no parallel phase_eutectic_solid_solution axiom line compound not all solids"

phaseEutecticSolidSolutionConservationCrossWitnessAuthority : String
phaseEutecticSolidSolutionConservationCrossWitnessAuthority =
  "umst/umst-chem/src/phase_eutectic_nonstoich.rs"

phaseEutecticSolidSolutionTableAuthority : String
phaseEutecticSolidSolutionTableAuthority =
  "umst/umst-chem/src/l0_tables/phase_eutectic_solid_solution.rs"

thermoGTypeAuthority : String
thermoGTypeAuthority =
  "umst/umst-chem/src/thermo_g.rs"

calphadKineticsAuthority : String
calphadKineticsAuthority =
  "umst/umst-chem/src/cross_classifier/calphad_equilibrium_is_not_kinetics.rs"

phaseEutecticSolidSolutionConservationCellId : String
phaseEutecticSolidSolutionConservationCellId = "CHEM-FORMAL-Q-AGDA-PHASE-EUTECTIC-SOLID-SOLUTION-CONSERVATION"

phaseEutecticSolidSolutionConservationNonClaim : String
phaseEutecticSolidSolutionConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-PHASE-EUTECTIC-SOLID-SOLUTION-CONSERVATION pattern class 13 phase_eutectic_solid_solution conservation concurrent Pi_c identity conserved phase edge scaffold CALPHAD Gmin class 13 phase_eutectic_solid_solution product not XOR phase edge is scaffold no parallel phase_eutectic_solid_solution axiom line compound not all solids XOR mutually exclusive refuse phase eutectic solid solution nuance witness concurrent phaseEutecticSolidSolution13Proved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation cite phase_eutectic_nonstoich.rs l0_tables phase_eutectic_solid_solution not fork not physics GREEN not production_wired"

phase-eutectic-solid-solution-conservation-cell-id :
  phaseEutecticSolidSolutionConservationCellId ≡ "CHEM-FORMAL-Q-AGDA-PHASE-EUTECTIC-SOLID-SOLUTION-CONSERVATION"
phase-eutectic-solid-solution-conservation-cell-id = refl

phase-eutectic-solid-solution-conservation-cites-phase-eutectic-nonstoich-rs :
  phaseEutecticSolidSolutionConservationCrossWitnessAuthority ≡
  "umst/umst-chem/src/phase_eutectic_nonstoich.rs"
phase-eutectic-solid-solution-conservation-cites-phase-eutectic-nonstoich-rs = refl

phase-eutectic-solid-solution-conservation-cites-l0-table-rs :
  phaseEutecticSolidSolutionTableAuthority ≡
  "umst/umst-chem/src/l0_tables/phase_eutectic_solid_solution.rs"
phase-eutectic-solid-solution-conservation-cites-l0-table-rs = refl

phase-eutectic-solid-solution-conservation-modality-unwired :
  phaseEutecticSolidSolutionConservationModalityCurrent ≡ phase-eutectic-solid-solution-conservation-unwired
phase-eutectic-solid-solution-conservation-modality-unwired = refl

phaseEutecticSolidSolutionConservationPhysicsGreenAuthorized : Set
phaseEutecticSolidSolutionConservationPhysicsGreenAuthorized = ⊥

phase-eutectic-solid-solution-conservation-physics-green-false : ¬ phaseEutecticSolidSolutionConservationPhysicsGreenAuthorized
phase-eutectic-solid-solution-conservation-physics-green-false ()

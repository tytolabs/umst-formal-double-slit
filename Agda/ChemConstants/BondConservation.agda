-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.BondConservation.agda
--
-- GRAPH-01 classifier-**bond** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Named **bond** / reaction edge identity conserved at thermo-identity
--   * Self-loop **bond** step fail-closed
--   * Total-claim refuse without **bond** witness; self-loop refuse
--   * **bond** laws Unwired (graph01BondProved = false)
--
-- Mirrors sibling `ChemConstants/RewriteConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.BondConservation where

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
-- Modality + GRAPH-01 classifier-**bond** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data BondConservationModality : Set where
  bond-conservation-unwired bond-conservation-assumed
    bond-conservation-proved bond-conservation-surrogate
    : BondConservationModality

bondConservationModalityCurrent : BondConservationModality
bondConservationModalityCurrent = bond-conservation-unwired

graph01BondProved productionWired not118SquaredGreenTable
  bondSecondLawConservationFramed : Bool
graph01BondProved = false
productionWired = false
not118SquaredGreenTable = true
bondSecondLawConservationFramed = true

------------------------------------------------------------------------
-- **Bond** law lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

bondLawLatticeCardinality : ℕ
bondLawLatticeCardinality = 4

bond-law-lattice-cardinality-four : bondLawLatticeCardinality ≡ 4
bond-law-lattice-cardinality-four = refl

bond-law-lattice-not-118-squared :
  does (bondLawLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
bond-law-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- Named element Z pins — H–O (Z=1/8), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  hydrogen oxygen oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ hydrogen = 1
elementAtomicZ oxygen = 8
elementAtomicZ oganesson = 118

ho-bond-z-pins : elementAtomicZ hydrogen ≡ 1 × elementAtomicZ oxygen ≡ 8
ho-bond-z-pins = refl , refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- Named reaction edge — forward hydration + H–O **bond** identity
------------------------------------------------------------------------

data ReactionEdgeName : Set where
  forward-hydration named-ho-bond : ReactionEdgeName

record NamedBondEdge : Set where
  constructor mkNamedBondEdge
  field
    edge-name : ReactionEdgeName
    lhs rhs : ElementTag

forwardHydrationEdge : NamedBondEdge
forwardHydrationEdge = mkNamedBondEdge forward-hydration hydrogen oxygen

namedHoBondEdge : NamedBondEdge
namedHoBondEdge = mkNamedBondEdge named-ho-bond hydrogen oxygen

forward-hydration-named :
  NamedBondEdge.edge-name forwardHydrationEdge ≡ forward-hydration
forward-hydration-named = refl

named-ho-bond-edge-z-pins :
  elementAtomicZ (NamedBondEdge.lhs namedHoBondEdge) ≡ 1
  × elementAtomicZ (NamedBondEdge.rhs namedHoBondEdge) ≡ 8
named-ho-bond-edge-z-pins = refl , refl

------------------------------------------------------------------------
-- ClassifierBondStep scaffold — thermo-preserving **bond** / reaction edge
------------------------------------------------------------------------

data ClassifierBondStep : Set where
  thermo-identity : ClassifierBondStep
  leaf : ElementTag → ClassifierBondStep
  thermo-bond : ClassifierBondStep → ClassifierBondStep → ClassifierBondStep
  self-loop-bond : ClassifierBondStep → ClassifierBondStep → ClassifierBondStep

thermoIdentity : ClassifierBondStep
thermoIdentity = thermo-identity

bondOp selfLoopOp : ClassifierBondStep → ClassifierBondStep → ClassifierBondStep
bondOp = thermo-bond
selfLoopOp = self-loop-bond

hydrogenLeaf oxygenLeaf oganessonLeaf : ClassifierBondStep
hydrogenLeaf = leaf hydrogen
oxygenLeaf = leaf oxygen
oganessonLeaf = leaf oganesson

isThermoBond isSelfLoopBond : ClassifierBondStep → Bool
isThermoBond (thermo-bond _ _) = true
isThermoBond _ = false

isSelfLoopBond (self-loop-bond _ _) = true
isSelfLoopBond _ = false

isThermoIdentity : ClassifierBondStep → Bool
isThermoIdentity thermo-identity = true
isThermoIdentity _ = false

------------------------------------------------------------------------
-- Thermo-preserving **bond** identity conserved at thermo-identity
------------------------------------------------------------------------

bond-left-identity :
  ∀ (a : ClassifierBondStep) →
  isThermoIdentity thermoIdentity ≡ true × isThermoBond (bondOp thermoIdentity a) ≡ true
bond-left-identity a = refl , refl

bond-right-identity :
  ∀ (a : ClassifierBondStep) →
  isThermoBond (bondOp a thermoIdentity) ≡ true × isThermoIdentity thermoIdentity ≡ true
bond-right-identity a = refl , refl

thermo-preserving-bond-identity-conserved :
  (∀ a → isThermoBond (bondOp thermoIdentity a) ≡ true)
  × (∀ a → isThermoBond (bondOp a thermoIdentity) ≡ true)
thermo-preserving-bond-identity-conserved =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named **bond** edge identity conserved — forward hydration H–O
------------------------------------------------------------------------

forwardHydrationBond : ClassifierBondStep
forwardHydrationBond = bondOp hydrogenLeaf oxygenLeaf

forward-hydration-bond-named :
  NamedBondEdge.edge-name forwardHydrationEdge ≡ forward-hydration
  × isThermoBond forwardHydrationBond ≡ true
forward-hydration-bond-named = forward-hydration-named , refl

named-bond-edge-identity-conserved :
  elementAtomicZ hydrogen ≡ 1
  × elementAtomicZ oxygen ≡ 8
  × isThermoBond (bondOp hydrogenLeaf oxygenLeaf) ≡ true
named-bond-edge-identity-conserved = refl , refl , refl

------------------------------------------------------------------------
-- Thermo-preserving admissibility — self-loop **bond** fail-closed
------------------------------------------------------------------------

data BondAdmissibility : Set where
  bond-admissible bond-self-loop-refuse : BondAdmissibility

isBondPreserving : ClassifierBondStep → Bool
isBondPreserving thermo-identity = true
isBondPreserving (leaf hydrogen) = true
isBondPreserving (leaf oxygen) = true
isBondPreserving (leaf oganesson) = true
isBondPreserving (thermo-bond a b) =
  isBondPreserving a ∧ isBondPreserving b
isBondPreserving (self-loop-bond _ _) = false

isBondAdmissible : ClassifierBondStep → Bool
isBondAdmissible step = isBondPreserving step

hydrogen-leaf-admissible : isBondAdmissible hydrogenLeaf ≡ true
hydrogen-leaf-admissible = refl

oxygen-leaf-admissible : isBondAdmissible oxygenLeaf ≡ true
oxygen-leaf-admissible = refl

oganesson-leaf-admissible : isBondAdmissible oganessonLeaf ≡ true
oganesson-leaf-admissible = refl

forward-hydration-bond-admissible : isBondAdmissible forwardHydrationBond ≡ true
forward-hydration-bond-admissible = refl

self-loop-bond-refuse :
  isBondAdmissible (selfLoopOp hydrogenLeaf hydrogenLeaf) ≡ false
self-loop-bond-refuse = refl

self-loop-oxygen-refuse :
  isBondAdmissible (selfLoopOp oxygenLeaf oxygenLeaf) ≡ false
self-loop-oxygen-refuse = refl

------------------------------------------------------------------------
-- **Bond** witness — total-claim refuse without witness
------------------------------------------------------------------------

data BondWitnessPresence : Set where
  bond-witness-absent bond-witness-present : BondWitnessPresence

record ClassifierBondWitness : Set where
  constructor mkClassifierBondWitness
  field
    witness-presence : BondWitnessPresence
    thermo-gap-total : ℕ

bondWitnessAbsent : ClassifierBondWitness
bondWitnessAbsent = mkClassifierBondWitness bond-witness-absent zero

bondWitnessPresentZeroGap : ClassifierBondWitness
bondWitnessPresentZeroGap = mkClassifierBondWitness bond-witness-present zero

bondWitnessPresentWithGaps : ℕ → ClassifierBondWitness
bondWitnessPresentWithGaps n = mkClassifierBondWitness bond-witness-present n

bondWitnessGapFree : ClassifierBondWitness → Bool
bondWitnessGapFree (mkClassifierBondWitness bond-witness-absent _) = false
bondWitnessGapFree (mkClassifierBondWitness bond-witness-present n) =
  does (n ℕ-Props.≟ zero)

bond-witness-present-zero-gap-free :
  bondWitnessGapFree bondWitnessPresentZeroGap ≡ true
bond-witness-present-zero-gap-free = refl

bond-witness-absent-not-gap-free :
  bondWitnessGapFree bondWitnessAbsent ≡ false
bond-witness-absent-not-gap-free = refl

bond-witness-with-gaps-not-gap-free :
  ∀ n → bondWitnessGapFree (bondWitnessPresentWithGaps (suc n)) ≡ false
bond-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-**bond** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data BondConservationVerdict : Set where
  verdict-unwired-ok verdict-bond-admissible-ok
    verdict-total-claim-refuse verdict-self-loop-refuse
    verdict-green-invent-refuse
    : BondConservationVerdict

bondConservationVerdictOk : BondConservationVerdict → Bool
bondConservationVerdictOk verdict-unwired-ok = true
bondConservationVerdictOk verdict-bond-admissible-ok = true
bondConservationVerdictOk _ = false

evaluateBondConservationClose :
  BondConservationModality → ClassifierBondStep → ClassifierBondWitness → Bool
  → BondConservationVerdict
evaluateBondConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateBondConservationClose bond-conservation-unwired _ _ false = verdict-unwired-ok
evaluateBondConservationClose bond-conservation-assumed _ _ false = verdict-unwired-ok
evaluateBondConservationClose bond-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateBondConservationClose bond-conservation-proved step (mkClassifierBondWitness bond-witness-absent _) false =
  verdict-total-claim-refuse
evaluateBondConservationClose bond-conservation-proved step (mkClassifierBondWitness bond-witness-present _) false
  with isBondAdmissible step
... | false = verdict-self-loop-refuse
... | true  = verdict-bond-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without **bond** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateBondConservationClose
    bond-conservation-unwired forwardHydrationBond bondWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateBondConservationClose
    bond-conservation-assumed forwardHydrationBond bondWitnessAbsent false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateBondConservationClose
    bond-conservation-surrogate forwardHydrationBond bondWitnessAbsent false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  bondConservationVerdictOk
    (evaluateBondConservationClose bond-conservation-unwired forwardHydrationBond bondWitnessAbsent false)
    ≡ true
  × bondConservationVerdictOk
      (evaluateBondConservationClose bond-conservation-assumed forwardHydrationBond bondWitnessAbsent false)
      ≡ true
  × bondConservationVerdictOk
      (evaluateBondConservationClose bond-conservation-surrogate forwardHydrationBond bondWitnessAbsent false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **bond** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateBondConservationClose
    bond-conservation-proved forwardHydrationBond bondWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  bondConservationVerdictOk
    (evaluateBondConservationClose
       bond-conservation-proved forwardHydrationBond bondWitnessAbsent false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateBondConservationClose
    bond-conservation-proved forwardHydrationBond bondWitnessAbsent false ≡
  verdict-bond-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- Self-loop **bond** refuse — thermo-violating step fail-closed
------------------------------------------------------------------------

self-loop-refuse-hydrogen :
  evaluateBondConservationClose
    bond-conservation-proved (selfLoopOp hydrogenLeaf hydrogenLeaf) bondWitnessPresentZeroGap false ≡
  verdict-self-loop-refuse
self-loop-refuse-hydrogen = refl

self-loop-refuse-oxygen :
  evaluateBondConservationClose
    bond-conservation-proved (selfLoopOp oxygenLeaf oxygenLeaf) bondWitnessPresentZeroGap false ≡
  verdict-self-loop-refuse
self-loop-refuse-oxygen = refl

self-loop-refuse-not-ok :
  bondConservationVerdictOk
    (evaluateBondConservationClose
       bond-conservation-proved (selfLoopOp hydrogenLeaf hydrogenLeaf) bondWitnessPresentZeroGap false)
    ≡ false
self-loop-refuse-not-ok = refl

SelfLoopWhenHydrogen : Set
SelfLoopWhenHydrogen =
  evaluateBondConservationClose
    bond-conservation-proved (selfLoopOp hydrogenLeaf hydrogenLeaf) bondWitnessPresentZeroGap false ≡
  verdict-bond-admissible-ok

self-loop-⊥-when-hydrogen : SelfLoopWhenHydrogen → ⊥
self-loop-⊥-when-hydrogen ()

------------------------------------------------------------------------
-- Admissible classifier-**bond** — witness present + thermo-preserving step
------------------------------------------------------------------------

bond-admissible-ok :
  evaluateBondConservationClose
    bond-conservation-proved forwardHydrationBond bondWitnessPresentZeroGap false ≡
  verdict-bond-admissible-ok
bond-admissible-ok = refl

bond-admissible-verdict-ok :
  bondConservationVerdictOk
    (evaluateBondConservationClose
       bond-conservation-proved forwardHydrationBond bondWitnessPresentZeroGap false)
    ≡ true
bond-admissible-verdict-ok = refl

bond-admissible-ok-still-not-graph01-proved :
  bondConservationVerdictOk
    (evaluateBondConservationClose
       bond-conservation-proved forwardHydrationBond bondWitnessPresentZeroGap false)
    ≡ true
  × graph01BondProved ≡ false
bond-admissible-ok-still-not-graph01-proved = bond-admissible-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateBondConservationClose
    bond-conservation-unwired forwardHydrationBond bondWitnessPresentZeroGap true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  bondConservationVerdictOk
    (evaluateBondConservationClose
       bond-conservation-unwired forwardHydrationBond bondWitnessPresentZeroGap true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

bondConservationFiberOk : FormalFiber → Bool
bondConservationFiberOk fiber-quantum-knowing = true
bondConservationFiberOk fiber-meso-acting = false

bond-conservation-knowing-fiber-ok :
  bondConservationFiberOk fiber-quantum-knowing ≡ true
bond-conservation-knowing-fiber-ok = refl

bond-conservation-meso-acting-not-ok :
  bondConservationFiberOk fiber-meso-acting ≡ false
bond-conservation-meso-acting-not-ok = refl

bond-conservation-routes-knowing-not-meso :
  bondConservationFiberOk fiber-quantum-knowing ≡ true ×
  bondConservationFiberOk fiber-meso-acting ≡ false
bond-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  bondConservationFiberOk fiber-quantum-knowing ∧
  not (bondConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not GRAPH-01 Proved, not physics GREEN
------------------------------------------------------------------------

graph01-bond-not-proved : graph01BondProved ≡ false
graph01-bond-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

bond-second-law-conservation-framed : bondSecondLawConservationFramed ≡ true
bond-second-law-conservation-framed = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second **bond** axiom fork)
------------------------------------------------------------------------

bondConservationAxiom :
  (graph01BondProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (bondSecondLawConservationFramed ≡ true)
  × (evaluateBondConservationClose bond-conservation-unwired forwardHydrationBond bondWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateBondConservationClose bond-conservation-proved forwardHydrationBond bondWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateBondConservationClose bond-conservation-proved (selfLoopOp hydrogenLeaf hydrogenLeaf) bondWitnessPresentZeroGap false ≡ verdict-self-loop-refuse)
  × (evaluateBondConservationClose bond-conservation-proved forwardHydrationBond bondWitnessPresentZeroGap false ≡ verdict-bond-admissible-ok)
  × (bondConservationFiberOk fiber-quantum-knowing ≡ true)
  × (bondConservationFiberOk fiber-meso-acting ≡ false)
  × (bondConservationVerdictOk (evaluateBondConservationClose bond-conservation-unwired forwardHydrationBond bondWitnessPresentZeroGap true) ≡ false)
  × (∀ a → isThermoBond (bondOp thermoIdentity a) ≡ true)
  × (∀ a → isThermoBond (bondOp a thermoIdentity) ≡ true)
  × (isBondAdmissible (selfLoopOp hydrogenLeaf hydrogenLeaf) ≡ false)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oxygen ≡ 8)
  × (elementAtomicZ oganesson ≡ 118)
bondConservationAxiom =
  graph01-bond-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , bond-second-law-conservation-framed
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , self-loop-refuse-hydrogen
  , bond-admissible-ok
  , bond-conservation-knowing-fiber-ok
  , bond-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , self-loop-bond-refuse
  , refl
  , refl
  , oganesson-z-118

bondConservationNamed : String
bondConservationNamed =
  "bondConservation: GRAPH-01 classifier bond thermo-preserving bond identity conservation"

bondConservationCellId : String
bondConservationCellId = "CHEM-FORMAL-Q-AGDA-BOND-CONSERVATION"

bondConservationNonClaim : String
bondConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-BOND-CONSERVATION GRAPH-01 classifier bond conservation thermo-preserving bond identity conserved named H-O Z=1/8 Og Z=118 forward hydration named self-loop bond fail-closed total-claim refuse graph01BondProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second bond axiom not physics GREEN not production_wired"

bond-conservation-modality-unwired :
  bondConservationModalityCurrent ≡ bond-conservation-unwired
bond-conservation-modality-unwired = refl

bondConservationPhysicsGreenAuthorized : Set
bondConservationPhysicsGreenAuthorized = ⊥

bond-conservation-physics-green-false : ¬ bondConservationPhysicsGreenAuthorized
bond-conservation-physics-green-false ()

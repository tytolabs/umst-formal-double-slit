-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.DissipConservation.agda
--
-- GRAPH-04 classifier-**dissip** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Cyclic vs **dissip**ative path identity conserved at thermo-identity
--   * Named reaction-cycle closed — **dissip** identity not **bond** identity
--   * Trivial **dissip** step fail-closed
--   * Total-claim refuse without **dissip** witness; trivial **dissip** refuse
--   * Bond-path **dissip**ative typed (positive witness required)
--   * **dissip** laws Unwired (graph04DissipProved = false)
--
-- Mirrors sibling `ChemConstants/HyperConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.DissipConservation where

open import Data.Bool.Base using (Bool; false; true; not; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties as ℕ-Props using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does)

------------------------------------------------------------------------
-- Modality + GRAPH-04 classifier-**dissip** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data DissipConservationModality : Set where
  dissip-conservation-unwired dissip-conservation-assumed
    dissip-conservation-proved dissip-conservation-surrogate
    : DissipConservationModality

dissipConservationModalityCurrent : DissipConservationModality
dissipConservationModalityCurrent = dissip-conservation-unwired

graph04DissipProved productionWired not118SquaredGreenTable
  dissipSecondLawConservationFramed dissipNotBond : Bool
graph04DissipProved = false
productionWired = false
not118SquaredGreenTable = true
dissipSecondLawConservationFramed = true
dissipNotBond = true

------------------------------------------------------------------------
-- **Dissip** law lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

dissipLawLatticeCardinality : ℕ
dissipLawLatticeCardinality = 4

dissip-law-lattice-cardinality-four : dissipLawLatticeCardinality ≡ 4
dissip-law-lattice-cardinality-four = refl

dissip-law-lattice-not-118-squared :
  does (dissipLawLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
dissip-law-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- Named element Z pins — H–O (Z=1/8), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  hydrogen oxygen oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ hydrogen = 1
elementAtomicZ oxygen = 8
elementAtomicZ oganesson = 118

ho-dissip-z-pins : elementAtomicZ hydrogen ≡ 1 × elementAtomicZ oxygen ≡ 8
ho-dissip-z-pins = refl , refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- Cyclic vs **dissip**ative path identity — **conservation** scaffold
------------------------------------------------------------------------

data PathTag : Set where
  cyclic-part dissipative-part : PathTag

isCyclicPath isDissipativePath : PathTag → Bool
isCyclicPath cyclic-part = true
isCyclicPath dissipative-part = false

isDissipativePath dissipative-part = true
isDissipativePath cyclic-part = false

cyclic-path-identity :
  isCyclicPath cyclic-part ≡ true × isDissipativePath cyclic-part ≡ false
cyclic-path-identity = refl , refl

dissipative-path-identity :
  isDissipativePath dissipative-part ≡ true × isCyclicPath dissipative-part ≡ false
dissipative-path-identity = refl , refl

cyclic-not-dissipative : cyclic-part ≢ dissipative-part
cyclic-not-dissipative ()

dissipative-not-cyclic : dissipative-part ≢ cyclic-part
dissipative-not-cyclic ()

cyclic-dissipative-path-identity-conserved :
  isCyclicPath cyclic-part ≡ not (isDissipativePath cyclic-part)
  × isDissipativePath dissipative-part ≡ not (isCyclicPath dissipative-part)
cyclic-dissipative-path-identity-conserved = refl , refl

------------------------------------------------------------------------
-- Named reaction-cycle closed — **dissip** identity (dissip ≠ **bond**)
------------------------------------------------------------------------

data ReactionCycleName : Set where
  named-reaction-cycle : ReactionCycleName

record NamedReactionCycle : Set where
  constructor mkNamedReactionCycle
  field
    cycle-name : ReactionCycleName
    cyclic-side dissipative-side : PathTag

namedReactionCycle : NamedReactionCycle
namedReactionCycle =
  mkNamedReactionCycle named-reaction-cycle cyclic-part dissipative-part

named-reaction-cycle-named :
  NamedReactionCycle.cycle-name namedReactionCycle ≡ named-reaction-cycle
named-reaction-cycle-named = refl

named-reaction-cycle-path-tags :
  NamedReactionCycle.cyclic-side namedReactionCycle ≡ cyclic-part
  × NamedReactionCycle.dissipative-side namedReactionCycle ≡ dissipative-part
named-reaction-cycle-path-tags = refl , refl

dissip-not-bond : dissipNotBond ≡ true
dissip-not-bond = refl

------------------------------------------------------------------------
-- Bond-path **dissip**ative witness — positive dissipation required
------------------------------------------------------------------------

record BondPathDissipativeWitness : Set where
  constructor mkBondPathDissipativeWitness
  field
    dissipationMicrojoules : ℕ

bondPathWitnessZero : BondPathDissipativeWitness
bondPathWitnessZero = mkBondPathDissipativeWitness zero

bondPathWitnessPositive : BondPathDissipativeWitness
bondPathWitnessPositive = mkBondPathDissipativeWitness (suc zero)

witnessDissipationPositive : ℕ → Bool
witnessDissipationPositive zero = false
witnessDissipationPositive (suc _) = true

bondPathDissipativeTyped : BondPathDissipativeWitness → Bool
bondPathDissipativeTyped w =
  witnessDissipationPositive (BondPathDissipativeWitness.dissipationMicrojoules w)

bond-path-zero-not-dissipative-typed :
  bondPathDissipativeTyped bondPathWitnessZero ≡ false
bond-path-zero-not-dissipative-typed = refl

bond-path-positive-dissipative-typed :
  bondPathDissipativeTyped bondPathWitnessPositive ≡ true
bond-path-positive-dissipative-typed = refl

------------------------------------------------------------------------
-- ClassifierDissipStep scaffold — reaction-cycle / bond-path **dissip**ative
------------------------------------------------------------------------

data ClassifierDissipStep : Set where
  thermo-identity : ClassifierDissipStep
  leaf : PathTag → ClassifierDissipStep
  reaction-cycle-closed : ClassifierDissipStep → ClassifierDissipStep → ClassifierDissipStep
  bond-dissip-path : ClassifierDissipStep → ClassifierDissipStep → ClassifierDissipStep
  trivial-dissip : ClassifierDissipStep → ClassifierDissipStep → ClassifierDissipStep

thermoIdentity : ClassifierDissipStep
thermoIdentity = thermo-identity

reactionCycleOp bondDissipPathOp trivialDissipOp :
  ClassifierDissipStep → ClassifierDissipStep → ClassifierDissipStep
reactionCycleOp = reaction-cycle-closed
bondDissipPathOp = bond-dissip-path
trivialDissipOp = trivial-dissip

cyclicLeaf dissipativeLeaf : ClassifierDissipStep
cyclicLeaf = leaf cyclic-part
dissipativeLeaf = leaf dissipative-part

hydrogenLeaf oxygenLeaf : ClassifierDissipStep
hydrogenLeaf = leaf cyclic-part
oxygenLeaf = leaf dissipative-part

isReactionCycleClosed isBondDissipPath isTrivialDissip : ClassifierDissipStep → Bool
isReactionCycleClosed (reaction-cycle-closed _ _) = true
isReactionCycleClosed _ = false

isBondDissipPath (bond-dissip-path _ _) = true
isBondDissipPath _ = false

isTrivialDissip (trivial-dissip _ _) = true
isTrivialDissip _ = false

isThermoIdentity : ClassifierDissipStep → Bool
isThermoIdentity thermo-identity = true
isThermoIdentity _ = false

------------------------------------------------------------------------
-- Cyclic vs **dissip**ative path identity conserved at thermo-identity
------------------------------------------------------------------------

dissip-left-identity :
  ∀ (a : ClassifierDissipStep) →
  isThermoIdentity thermoIdentity ≡ true
  × isReactionCycleClosed (reactionCycleOp thermoIdentity a) ≡ true
dissip-left-identity a = refl , refl

dissip-right-identity :
  ∀ (a : ClassifierDissipStep) →
  isReactionCycleClosed (reactionCycleOp a thermoIdentity) ≡ true
  × isThermoIdentity thermoIdentity ≡ true
dissip-right-identity a = refl , refl

cyclic-dissipative-path-identity-conserved-at-thermo :
  (∀ a → isReactionCycleClosed (reactionCycleOp thermoIdentity a) ≡ true)
  × (∀ a → isReactionCycleClosed (reactionCycleOp a thermoIdentity) ≡ true)
cyclic-dissipative-path-identity-conserved-at-thermo =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named reaction-cycle closed — cyclic/dissipative path **conservation**
------------------------------------------------------------------------

namedReactionCycleClosed : ClassifierDissipStep
namedReactionCycleClosed = reactionCycleOp cyclicLeaf dissipativeLeaf

named-reaction-cycle-closed-named :
  NamedReactionCycle.cycle-name namedReactionCycle ≡ named-reaction-cycle
  × isReactionCycleClosed namedReactionCycleClosed ≡ true
named-reaction-cycle-closed-named = named-reaction-cycle-named , refl

named-cycle-path-identity-conserved :
  isCyclicPath cyclic-part ≡ true
  × isDissipativePath dissipative-part ≡ true
  × isReactionCycleClosed (reactionCycleOp cyclicLeaf dissipativeLeaf) ≡ true
named-cycle-path-identity-conserved = refl , refl , refl

------------------------------------------------------------------------
-- Named bond-path **dissip**ative typed — H–O forward hydration scaffold
------------------------------------------------------------------------

namedBondDissipPath : ClassifierDissipStep
namedBondDissipPath = bondDissipPathOp hydrogenLeaf oxygenLeaf

named-bond-dissip-path-typed :
  elementAtomicZ hydrogen ≡ 1
  × elementAtomicZ oxygen ≡ 8
  × isBondDissipPath namedBondDissipPath ≡ true
named-bond-dissip-path-typed = refl , refl , refl

bond-path-dissipative-typed-positive :
  bondPathDissipativeTyped bondPathWitnessPositive ≡ true
  × isBondDissipPath namedBondDissipPath ≡ true
bond-path-dissipative-typed-positive = bond-path-positive-dissipative-typed , refl

------------------------------------------------------------------------
-- Thermo-preserving admissibility — trivial **dissip** fail-closed
------------------------------------------------------------------------

data DissipAdmissibility : Set where
  dissip-admissible dissip-trivial-refuse : DissipAdmissibility

isDissipPreserving : ClassifierDissipStep → Bool
isDissipPreserving thermo-identity = true
isDissipPreserving (leaf cyclic-part) = true
isDissipPreserving (leaf dissipative-part) = true
isDissipPreserving (reaction-cycle-closed a b) =
  isDissipPreserving a ∧ isDissipPreserving b
isDissipPreserving (bond-dissip-path a b) =
  isDissipPreserving a ∧ isDissipPreserving b
isDissipPreserving (trivial-dissip _ _) = false

isDissipAdmissible : ClassifierDissipStep → Bool
isDissipAdmissible step = isDissipPreserving step

cyclic-leaf-admissible : isDissipAdmissible cyclicLeaf ≡ true
cyclic-leaf-admissible = refl

dissipative-leaf-admissible : isDissipAdmissible dissipativeLeaf ≡ true
dissipative-leaf-admissible = refl

named-reaction-cycle-admissible : isDissipAdmissible namedReactionCycleClosed ≡ true
named-reaction-cycle-admissible = refl

named-bond-dissip-path-admissible : isDissipAdmissible namedBondDissipPath ≡ true
named-bond-dissip-path-admissible = refl

trivial-dissip-refuse :
  isDissipAdmissible (trivialDissipOp cyclicLeaf cyclicLeaf) ≡ false
trivial-dissip-refuse = refl

trivial-dissip-dissipative-refuse :
  isDissipAdmissible (trivialDissipOp dissipativeLeaf dissipativeLeaf) ≡ false
trivial-dissip-dissipative-refuse = refl

------------------------------------------------------------------------
-- **Dissip** witness — total-claim refuse without witness
------------------------------------------------------------------------

data DissipWitnessPresence : Set where
  dissip-witness-absent dissip-witness-present : DissipWitnessPresence

record ClassifierDissipWitness : Set where
  constructor mkClassifierDissipWitness
  field
    witness-presence : DissipWitnessPresence
    thermo-gap-total : ℕ

dissipWitnessAbsent : ClassifierDissipWitness
dissipWitnessAbsent = mkClassifierDissipWitness dissip-witness-absent zero

dissipWitnessPresentZeroGap : ClassifierDissipWitness
dissipWitnessPresentZeroGap = mkClassifierDissipWitness dissip-witness-present zero

dissipWitnessPresentWithGaps : ℕ → ClassifierDissipWitness
dissipWitnessPresentWithGaps n = mkClassifierDissipWitness dissip-witness-present n

dissipWitnessGapFree : ClassifierDissipWitness → Bool
dissipWitnessGapFree (mkClassifierDissipWitness dissip-witness-absent _) = false
dissipWitnessGapFree (mkClassifierDissipWitness dissip-witness-present n) =
  does (n ℕ-Props.≟ zero)

dissip-witness-present-zero-gap-free :
  dissipWitnessGapFree dissipWitnessPresentZeroGap ≡ true
dissip-witness-present-zero-gap-free = refl

dissip-witness-absent-not-gap-free :
  dissipWitnessGapFree dissipWitnessAbsent ≡ false
dissip-witness-absent-not-gap-free = refl

dissip-witness-with-gaps-not-gap-free :
  ∀ n → dissipWitnessGapFree (dissipWitnessPresentWithGaps (suc n)) ≡ false
dissip-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-**dissip** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data DissipConservationVerdict : Set where
  verdict-unwired-ok verdict-dissip-admissible-ok
    verdict-bond-dissip-path-ok verdict-bond-path-not-dissipative-refuse
    verdict-total-claim-refuse verdict-trivial-dissip-refuse
    verdict-green-invent-refuse
    : DissipConservationVerdict

dissipConservationVerdictOk : DissipConservationVerdict → Bool
dissipConservationVerdictOk verdict-unwired-ok = true
dissipConservationVerdictOk verdict-dissip-admissible-ok = true
dissipConservationVerdictOk verdict-bond-dissip-path-ok = true
dissipConservationVerdictOk _ = false

evaluateDissipConservationClose :
  DissipConservationModality → ClassifierDissipStep → ClassifierDissipWitness
  → BondPathDissipativeWitness → Bool → DissipConservationVerdict
evaluateDissipConservationClose _ _ _ _ true = verdict-green-invent-refuse
evaluateDissipConservationClose dissip-conservation-unwired _ _ _ false = verdict-unwired-ok
evaluateDissipConservationClose dissip-conservation-assumed _ _ _ false = verdict-unwired-ok
evaluateDissipConservationClose dissip-conservation-surrogate _ _ _ false = verdict-unwired-ok
evaluateDissipConservationClose dissip-conservation-proved _ (mkClassifierDissipWitness dissip-witness-absent _) _ false =
  verdict-total-claim-refuse
evaluateDissipConservationClose dissip-conservation-proved (bond-dissip-path _ _) (mkClassifierDissipWitness dissip-witness-present _) bondW false
  with bondPathDissipativeTyped bondW
... | true  = verdict-bond-dissip-path-ok
... | false = verdict-bond-path-not-dissipative-refuse
evaluateDissipConservationClose dissip-conservation-proved (trivial-dissip _ _) (mkClassifierDissipWitness dissip-witness-present _) _ false =
  verdict-trivial-dissip-refuse
evaluateDissipConservationClose dissip-conservation-proved _ (mkClassifierDissipWitness dissip-witness-present _) _ false =
  verdict-dissip-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without **dissip** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateDissipConservationClose
    dissip-conservation-unwired namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateDissipConservationClose
    dissip-conservation-assumed namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateDissipConservationClose
    dissip-conservation-surrogate namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose dissip-conservation-unwired namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false)
    ≡ true
  × dissipConservationVerdictOk
      (evaluateDissipConservationClose dissip-conservation-assumed namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false)
      ≡ true
  × dissipConservationVerdictOk
      (evaluateDissipConservationClose dissip-conservation-surrogate namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **dissip** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateDissipConservationClose
    dissip-conservation-proved namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose
       dissip-conservation-proved namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateDissipConservationClose
    dissip-conservation-proved namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false ≡
  verdict-dissip-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- Trivial **dissip** refuse — thermo-violating step fail-closed
------------------------------------------------------------------------

trivial-dissip-refuse-cyclic :
  evaluateDissipConservationClose
    dissip-conservation-proved (trivialDissipOp cyclicLeaf cyclicLeaf) dissipWitnessPresentZeroGap bondPathWitnessPositive false ≡
  verdict-trivial-dissip-refuse
trivial-dissip-refuse-cyclic = refl

trivial-dissip-refuse-dissipative :
  evaluateDissipConservationClose
    dissip-conservation-proved (trivialDissipOp dissipativeLeaf dissipativeLeaf) dissipWitnessPresentZeroGap bondPathWitnessPositive false ≡
  verdict-trivial-dissip-refuse
trivial-dissip-refuse-dissipative = refl

trivial-dissip-refuse-not-ok :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose
       dissip-conservation-proved (trivialDissipOp cyclicLeaf cyclicLeaf) dissipWitnessPresentZeroGap bondPathWitnessPositive false)
    ≡ false
trivial-dissip-refuse-not-ok = refl

TrivialDissipWhenCyclic : Set
TrivialDissipWhenCyclic =
  evaluateDissipConservationClose
    dissip-conservation-proved (trivialDissipOp cyclicLeaf cyclicLeaf) dissipWitnessPresentZeroGap bondPathWitnessPositive false ≡
  verdict-dissip-admissible-ok

trivial-dissip-⊥-when-cyclic : TrivialDissipWhenCyclic → ⊥
trivial-dissip-⊥-when-cyclic ()

------------------------------------------------------------------------
-- Bond-path not **dissip**ative refuse — zero witness fail-closed
------------------------------------------------------------------------

bond-path-not-dissipative-refuse :
  evaluateDissipConservationClose
    dissip-conservation-proved namedBondDissipPath dissipWitnessPresentZeroGap bondPathWitnessZero false ≡
  verdict-bond-path-not-dissipative-refuse
bond-path-not-dissipative-refuse = refl

bond-path-not-dissipative-refuse-not-ok :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose
       dissip-conservation-proved namedBondDissipPath dissipWitnessPresentZeroGap bondPathWitnessZero false)
    ≡ false
bond-path-not-dissipative-refuse-not-ok = refl

BondPathNotDissipativeWhenZero : Set
BondPathNotDissipativeWhenZero =
  evaluateDissipConservationClose
    dissip-conservation-proved namedBondDissipPath dissipWitnessPresentZeroGap bondPathWitnessZero false ≡
  verdict-bond-dissip-path-ok

bond-path-not-dissipative-⊥-when-zero : BondPathNotDissipativeWhenZero → ⊥
bond-path-not-dissipative-⊥-when-zero ()

------------------------------------------------------------------------
-- Admissible classifier-**dissip** — reaction-cycle closed
------------------------------------------------------------------------

dissip-admissible-ok :
  evaluateDissipConservationClose
    dissip-conservation-proved namedReactionCycleClosed dissipWitnessPresentZeroGap bondPathWitnessZero false ≡
  verdict-dissip-admissible-ok
dissip-admissible-ok = refl

dissip-admissible-verdict-ok :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose
       dissip-conservation-proved namedReactionCycleClosed dissipWitnessPresentZeroGap bondPathWitnessZero false)
    ≡ true
dissip-admissible-verdict-ok = refl

dissip-admissible-ok-still-not-graph04-proved :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose
       dissip-conservation-proved namedReactionCycleClosed dissipWitnessPresentZeroGap bondPathWitnessZero false)
    ≡ true
  × graph04DissipProved ≡ false
dissip-admissible-ok-still-not-graph04-proved = dissip-admissible-verdict-ok , refl

------------------------------------------------------------------------
-- Bond-path **dissip**ative typed — positive witness ok
------------------------------------------------------------------------

bond-dissip-path-ok :
  evaluateDissipConservationClose
    dissip-conservation-proved namedBondDissipPath dissipWitnessPresentZeroGap bondPathWitnessPositive false ≡
  verdict-bond-dissip-path-ok
bond-dissip-path-ok = refl

bond-dissip-path-verdict-ok :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose
       dissip-conservation-proved namedBondDissipPath dissipWitnessPresentZeroGap bondPathWitnessPositive false)
    ≡ true
bond-dissip-path-verdict-ok = refl

bond-dissip-path-ok-still-not-graph04-proved :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose
       dissip-conservation-proved namedBondDissipPath dissipWitnessPresentZeroGap bondPathWitnessPositive false)
    ≡ true
  × graph04DissipProved ≡ false
bond-dissip-path-ok-still-not-graph04-proved = bond-dissip-path-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateDissipConservationClose
    dissip-conservation-unwired namedReactionCycleClosed dissipWitnessPresentZeroGap bondPathWitnessPositive true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  dissipConservationVerdictOk
    (evaluateDissipConservationClose
       dissip-conservation-unwired namedReactionCycleClosed dissipWitnessPresentZeroGap bondPathWitnessPositive true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

dissipConservationFiberOk : FormalFiber → Bool
dissipConservationFiberOk fiber-quantum-knowing = true
dissipConservationFiberOk fiber-meso-acting = false

dissip-conservation-knowing-fiber-ok :
  dissipConservationFiberOk fiber-quantum-knowing ≡ true
dissip-conservation-knowing-fiber-ok = refl

dissip-conservation-meso-acting-not-ok :
  dissipConservationFiberOk fiber-meso-acting ≡ false
dissip-conservation-meso-acting-not-ok = refl

dissip-conservation-routes-knowing-not-meso :
  dissipConservationFiberOk fiber-quantum-knowing ≡ true ×
  dissipConservationFiberOk fiber-meso-acting ≡ false
dissip-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  dissipConservationFiberOk fiber-quantum-knowing ∧
  not (dissipConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not GRAPH-04 Proved, not physics GREEN, dissip ≠ bond
------------------------------------------------------------------------

graph04-dissip-not-proved : graph04DissipProved ≡ false
graph04-dissip-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

dissip-second-law-conservation-framed : dissipSecondLawConservationFramed ≡ true
dissip-second-law-conservation-framed = refl

dissip-not-bond-pin : dissipNotBond ≡ true
dissip-not-bond-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second **dissip** axiom fork)
------------------------------------------------------------------------

dissipConservationAxiom :
  (graph04DissipProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (dissipSecondLawConservationFramed ≡ true)
  × (dissipNotBond ≡ true)
  × (evaluateDissipConservationClose dissip-conservation-unwired namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false ≡ verdict-unwired-ok)
  × (evaluateDissipConservationClose dissip-conservation-proved namedReactionCycleClosed dissipWitnessAbsent bondPathWitnessZero false ≡ verdict-total-claim-refuse)
  × (evaluateDissipConservationClose dissip-conservation-proved (trivialDissipOp cyclicLeaf cyclicLeaf) dissipWitnessPresentZeroGap bondPathWitnessPositive false ≡ verdict-trivial-dissip-refuse)
  × (evaluateDissipConservationClose dissip-conservation-proved namedReactionCycleClosed dissipWitnessPresentZeroGap bondPathWitnessZero false ≡ verdict-dissip-admissible-ok)
  × (evaluateDissipConservationClose dissip-conservation-proved namedBondDissipPath dissipWitnessPresentZeroGap bondPathWitnessPositive false ≡ verdict-bond-dissip-path-ok)
  × (evaluateDissipConservationClose dissip-conservation-proved namedBondDissipPath dissipWitnessPresentZeroGap bondPathWitnessZero false ≡ verdict-bond-path-not-dissipative-refuse)
  × (dissipConservationFiberOk fiber-quantum-knowing ≡ true)
  × (dissipConservationFiberOk fiber-meso-acting ≡ false)
  × (dissipConservationVerdictOk (evaluateDissipConservationClose dissip-conservation-unwired namedReactionCycleClosed dissipWitnessPresentZeroGap bondPathWitnessPositive true) ≡ false)
  × (∀ a → isReactionCycleClosed (reactionCycleOp thermoIdentity a) ≡ true)
  × (∀ a → isReactionCycleClosed (reactionCycleOp a thermoIdentity) ≡ true)
  × (isDissipAdmissible (trivialDissipOp cyclicLeaf cyclicLeaf) ≡ false)
  × (isCyclicPath cyclic-part ≡ true)
  × (isDissipativePath dissipative-part ≡ true)
  × (cyclic-part ≢ dissipative-part)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oxygen ≡ 8)
  × (elementAtomicZ oganesson ≡ 118)
dissipConservationAxiom =
  graph04-dissip-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , dissip-second-law-conservation-framed
  , dissip-not-bond-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , trivial-dissip-refuse-cyclic
  , dissip-admissible-ok
  , bond-dissip-path-ok
  , bond-path-not-dissipative-refuse
  , dissip-conservation-knowing-fiber-ok
  , dissip-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , trivial-dissip-refuse
  , refl
  , refl
  , cyclic-not-dissipative
  , refl
  , refl
  , oganesson-z-118

dissipConservationNamed : String
dissipConservationNamed =
  "dissipConservation: GRAPH-04 classifier dissip cyclic dissipative path identity reaction cycle closed bond path dissipative typed conservation"

dissipConservationCellId : String
dissipConservationCellId = "CHEM-FORMAL-Q-AGDA-DISSIP-CONSERVATION"

dissipConservationNonClaim : String
dissipConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-DISSIP-CONSERVATION GRAPH-04 classifier dissip conservation cyclic vs dissipative path identity conserved reaction cycle closed bond path dissipative typed trivial dissip fail-closed total-claim refuse graph04DissipProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second dissip axiom not physics GREEN not production_wired dissip not bond Og Z=118"

dissip-conservation-modality-unwired :
  dissipConservationModalityCurrent ≡ dissip-conservation-unwired
dissip-conservation-modality-unwired = refl

dissipConservationPhysicsGreenAuthorized : Set
dissipConservationPhysicsGreenAuthorized = ⊥

dissip-conservation-physics-green-false : ¬ dissipConservationPhysicsGreenAuthorized
dissip-conservation-physics-green-false ()

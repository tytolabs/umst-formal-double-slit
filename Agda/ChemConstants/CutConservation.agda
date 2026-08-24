-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.CutConservation.agda
--
-- GRAPH-02 classifier-**cut** **conservation** on the knowing fiber (Q lattice):
--   * Modality lattice Unwired/Assumed/Proved/Surrogate — structure not 118² GREEN
--   * Ore/waste partition complement conserved at thermo-identity
--   * Named recycle loop — **cut** identity not **bond** identity
--   * Trivial **cut** step fail-closed
--   * Total-claim refuse without **cut** witness; trivial **cut** refuse
--   * **cut** laws Unwired (graph02CutProved = false)
--
-- Mirrors sibling `ChemConstants/BondConservation.agda` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
-- Not 118² GREEN table. Second-law + **conservation** framing (not wired).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.CutConservation where

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
-- Modality + GRAPH-02 classifier-**cut** **conservation** pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data CutConservationModality : Set where
  cut-conservation-unwired cut-conservation-assumed
    cut-conservation-proved cut-conservation-surrogate
    : CutConservationModality

cutConservationModalityCurrent : CutConservationModality
cutConservationModalityCurrent = cut-conservation-unwired

graph02CutProved productionWired not118SquaredGreenTable
  cutSecondLawConservationFramed cutNotBond : Bool
graph02CutProved = false
productionWired = false
not118SquaredGreenTable = true
cutSecondLawConservationFramed = true
cutNotBond = true

------------------------------------------------------------------------
-- **Cut** law lattice cardinality (structure — not 118²)
------------------------------------------------------------------------

cutLawLatticeCardinality : ℕ
cutLawLatticeCardinality = 4

cut-law-lattice-cardinality-four : cutLawLatticeCardinality ≡ 4
cut-law-lattice-cardinality-four = refl

cut-law-lattice-not-118-squared :
  does (cutLawLatticeCardinality ℕ-Props.≟ (118 * 118)) ≡ false
cut-law-lattice-not-118-squared = refl

------------------------------------------------------------------------
-- Named element Z pins — H–O (Z=1/8), Og (Z=118)
------------------------------------------------------------------------

data ElementTag : Set where
  hydrogen oxygen oganesson : ElementTag

elementAtomicZ : ElementTag → ℕ
elementAtomicZ hydrogen = 1
elementAtomicZ oxygen = 8
elementAtomicZ oganesson = 118

ho-cut-z-pins : elementAtomicZ hydrogen ≡ 1 × elementAtomicZ oxygen ≡ 8
ho-cut-z-pins = refl , refl

oganesson-z-118 : elementAtomicZ oganesson ≡ 118
oganesson-z-118 = refl

------------------------------------------------------------------------
-- Ore/waste partition complement — **conservation** scaffold
------------------------------------------------------------------------

data PartitionTag : Set where
  ore-part waste-part : PartitionTag

isOrePart isWastePart : PartitionTag → Bool
isOrePart ore-part = true
isOrePart waste-part = false

isWastePart waste-part = true
isWastePart ore-part = false

partitionComplement : PartitionTag → PartitionTag
partitionComplement ore-part = waste-part
partitionComplement waste-part = ore-part

partition-complement-ore :
  isOrePart ore-part ≡ true × isWastePart ore-part ≡ false
partition-complement-ore = refl , refl

partition-complement-waste :
  isWastePart waste-part ≡ true × isOrePart waste-part ≡ false
partition-complement-waste = refl , refl

partition-complement-conserved :
  isOrePart ore-part ≡ not (isWastePart ore-part)
  × isWastePart waste-part ≡ not (isOrePart waste-part)
partition-complement-conserved = refl , refl

partition-complement-flip :
  partitionComplement (partitionComplement ore-part) ≡ ore-part
  × partitionComplement (partitionComplement waste-part) ≡ waste-part
partition-complement-flip = refl , refl

------------------------------------------------------------------------
-- Named recycle loop — **cut** identity (cut ≠ **bond**)
------------------------------------------------------------------------

data CutLoopName : Set where
  named-recycle-loop : CutLoopName

record NamedRecycleLoop : Set where
  constructor mkNamedRecycleLoop
  field
    loop-name : CutLoopName
    ore-side waste-side : PartitionTag

namedRecycleLoop : NamedRecycleLoop
namedRecycleLoop = mkNamedRecycleLoop named-recycle-loop ore-part waste-part

named-recycle-loop-named :
  NamedRecycleLoop.loop-name namedRecycleLoop ≡ named-recycle-loop
named-recycle-loop-named = refl

named-recycle-loop-partition-complement :
  partitionComplement (NamedRecycleLoop.ore-side namedRecycleLoop) ≡
    NamedRecycleLoop.waste-side namedRecycleLoop
  × partitionComplement (NamedRecycleLoop.waste-side namedRecycleLoop) ≡
    NamedRecycleLoop.ore-side namedRecycleLoop
named-recycle-loop-partition-complement = refl , refl

cut-not-bond : cutNotBond ≡ true
cut-not-bond = refl

------------------------------------------------------------------------
-- ClassifierCutStep scaffold — partition **cut** / trivial **cut**
------------------------------------------------------------------------

data ClassifierCutStep : Set where
  thermo-identity : ClassifierCutStep
  leaf : PartitionTag → ClassifierCutStep
  partition-cut : ClassifierCutStep → ClassifierCutStep → ClassifierCutStep
  trivial-cut : ClassifierCutStep → ClassifierCutStep → ClassifierCutStep

thermoIdentity : ClassifierCutStep
thermoIdentity = thermo-identity

cutOp trivialCutOp : ClassifierCutStep → ClassifierCutStep → ClassifierCutStep
cutOp = partition-cut
trivialCutOp = trivial-cut

oreLeaf wasteLeaf : ClassifierCutStep
oreLeaf = leaf ore-part
wasteLeaf = leaf waste-part

isPartitionCut isTrivialCut : ClassifierCutStep → Bool
isPartitionCut (partition-cut _ _) = true
isPartitionCut _ = false

isTrivialCut (trivial-cut _ _) = true
isTrivialCut _ = false

isThermoIdentity : ClassifierCutStep → Bool
isThermoIdentity thermo-identity = true
isThermoIdentity _ = false

------------------------------------------------------------------------
-- Partition complement conserved at thermo-identity — **cut** **conservation**
------------------------------------------------------------------------

cut-left-identity :
  ∀ (a : ClassifierCutStep) →
  isThermoIdentity thermoIdentity ≡ true × isPartitionCut (cutOp thermoIdentity a) ≡ true
cut-left-identity a = refl , refl

cut-right-identity :
  ∀ (a : ClassifierCutStep) →
  isPartitionCut (cutOp a thermoIdentity) ≡ true × isThermoIdentity thermoIdentity ≡ true
cut-right-identity a = refl , refl

partition-complement-cut-identity-conserved :
  (∀ a → isPartitionCut (cutOp thermoIdentity a) ≡ true)
  × (∀ a → isPartitionCut (cutOp a thermoIdentity) ≡ true)
partition-complement-cut-identity-conserved =
  (λ a → refl)
  , (λ a → refl)

------------------------------------------------------------------------
-- Named recycle loop **cut** — ore/waste partition complement
------------------------------------------------------------------------

namedRecycleCut : ClassifierCutStep
namedRecycleCut = cutOp oreLeaf wasteLeaf

named-recycle-cut-loop-named :
  NamedRecycleLoop.loop-name namedRecycleLoop ≡ named-recycle-loop
  × isPartitionCut namedRecycleCut ≡ true
named-recycle-cut-loop-named = named-recycle-loop-named , refl

named-cut-partition-complement-conserved :
  partitionComplement ore-part ≡ waste-part
  × partitionComplement waste-part ≡ ore-part
  × isPartitionCut (cutOp oreLeaf wasteLeaf) ≡ true
named-cut-partition-complement-conserved = refl , refl , refl

------------------------------------------------------------------------
-- Thermo-preserving admissibility — trivial **cut** fail-closed
------------------------------------------------------------------------

data CutAdmissibility : Set where
  cut-admissible cut-trivial-refuse : CutAdmissibility

isCutPreserving : ClassifierCutStep → Bool
isCutPreserving thermo-identity = true
isCutPreserving (leaf ore-part) = true
isCutPreserving (leaf waste-part) = true
isCutPreserving (partition-cut a b) =
  isCutPreserving a ∧ isCutPreserving b
isCutPreserving (trivial-cut _ _) = false

isCutAdmissible : ClassifierCutStep → Bool
isCutAdmissible step = isCutPreserving step

ore-leaf-admissible : isCutAdmissible oreLeaf ≡ true
ore-leaf-admissible = refl

waste-leaf-admissible : isCutAdmissible wasteLeaf ≡ true
waste-leaf-admissible = refl

named-recycle-cut-admissible : isCutAdmissible namedRecycleCut ≡ true
named-recycle-cut-admissible = refl

trivial-cut-refuse :
  isCutAdmissible (trivialCutOp oreLeaf oreLeaf) ≡ false
trivial-cut-refuse = refl

trivial-cut-waste-refuse :
  isCutAdmissible (trivialCutOp wasteLeaf wasteLeaf) ≡ false
trivial-cut-waste-refuse = refl

------------------------------------------------------------------------
-- **Cut** witness — total-claim refuse without witness
------------------------------------------------------------------------

data CutWitnessPresence : Set where
  cut-witness-absent cut-witness-present : CutWitnessPresence

record ClassifierCutWitness : Set where
  constructor mkClassifierCutWitness
  field
    witness-presence : CutWitnessPresence
    thermo-gap-total : ℕ

cutWitnessAbsent : ClassifierCutWitness
cutWitnessAbsent = mkClassifierCutWitness cut-witness-absent zero

cutWitnessPresentZeroGap : ClassifierCutWitness
cutWitnessPresentZeroGap = mkClassifierCutWitness cut-witness-present zero

cutWitnessPresentWithGaps : ℕ → ClassifierCutWitness
cutWitnessPresentWithGaps n = mkClassifierCutWitness cut-witness-present n

cutWitnessGapFree : ClassifierCutWitness → Bool
cutWitnessGapFree (mkClassifierCutWitness cut-witness-absent _) = false
cutWitnessGapFree (mkClassifierCutWitness cut-witness-present n) =
  does (n ℕ-Props.≟ zero)

cut-witness-present-zero-gap-free :
  cutWitnessGapFree cutWitnessPresentZeroGap ≡ true
cut-witness-present-zero-gap-free = refl

cut-witness-absent-not-gap-free :
  cutWitnessGapFree cutWitnessAbsent ≡ false
cut-witness-absent-not-gap-free = refl

cut-witness-with-gaps-not-gap-free :
  ∀ n → cutWitnessGapFree (cutWitnessPresentWithGaps (suc n)) ≡ false
cut-witness-with-gaps-not-gap-free n = refl

------------------------------------------------------------------------
-- Classifier-**cut** **conservation** close verdict — fail-closed lattice
------------------------------------------------------------------------

data CutConservationVerdict : Set where
  verdict-unwired-ok verdict-cut-admissible-ok
    verdict-total-claim-refuse verdict-trivial-cut-refuse
    verdict-green-invent-refuse
    : CutConservationVerdict

cutConservationVerdictOk : CutConservationVerdict → Bool
cutConservationVerdictOk verdict-unwired-ok = true
cutConservationVerdictOk verdict-cut-admissible-ok = true
cutConservationVerdictOk _ = false

evaluateCutConservationClose :
  CutConservationModality → ClassifierCutStep → ClassifierCutWitness → Bool
  → CutConservationVerdict
evaluateCutConservationClose _ _ _ true = verdict-green-invent-refuse
evaluateCutConservationClose cut-conservation-unwired _ _ false = verdict-unwired-ok
evaluateCutConservationClose cut-conservation-assumed _ _ false = verdict-unwired-ok
evaluateCutConservationClose cut-conservation-surrogate _ _ false = verdict-unwired-ok
evaluateCutConservationClose cut-conservation-proved step (mkClassifierCutWitness cut-witness-absent _) false =
  verdict-total-claim-refuse
evaluateCutConservationClose cut-conservation-proved step (mkClassifierCutWitness cut-witness-present _) false
  with isCutAdmissible step
... | false = verdict-trivial-cut-refuse
... | true  = verdict-cut-admissible-ok

------------------------------------------------------------------------
-- Unwired close — design scaffold without **cut** witness
------------------------------------------------------------------------

unwired-close-without-witness :
  evaluateCutConservationClose
    cut-conservation-unwired namedRecycleCut cutWitnessAbsent false ≡
  verdict-unwired-ok
unwired-close-without-witness = refl

assumed-close-without-witness :
  evaluateCutConservationClose
    cut-conservation-assumed namedRecycleCut cutWitnessAbsent false ≡
  verdict-unwired-ok
assumed-close-without-witness = refl

surrogate-close-without-witness :
  evaluateCutConservationClose
    cut-conservation-surrogate namedRecycleCut cutWitnessAbsent false ≡
  verdict-unwired-ok
surrogate-close-without-witness = refl

design-modalities-verdict-ok-without-witness :
  cutConservationVerdictOk
    (evaluateCutConservationClose cut-conservation-unwired namedRecycleCut cutWitnessAbsent false)
    ≡ true
  × cutConservationVerdictOk
      (evaluateCutConservationClose cut-conservation-assumed namedRecycleCut cutWitnessAbsent false)
      ≡ true
  × cutConservationVerdictOk
      (evaluateCutConservationClose cut-conservation-surrogate namedRecycleCut cutWitnessAbsent false)
      ≡ true
design-modalities-verdict-ok-without-witness = refl , refl , refl

------------------------------------------------------------------------
-- Total-claim refuse — proved modality without **cut** witness
------------------------------------------------------------------------

total-claim-refuse-without-witness :
  evaluateCutConservationClose
    cut-conservation-proved namedRecycleCut cutWitnessAbsent false ≡
  verdict-total-claim-refuse
total-claim-refuse-without-witness = refl

total-claim-refuse-not-ok :
  cutConservationVerdictOk
    (evaluateCutConservationClose
       cut-conservation-proved namedRecycleCut cutWitnessAbsent false)
    ≡ false
total-claim-refuse-not-ok = refl

TotalClaimWhenWitnessAbsent : Set
TotalClaimWhenWitnessAbsent =
  evaluateCutConservationClose
    cut-conservation-proved namedRecycleCut cutWitnessAbsent false ≡
  verdict-cut-admissible-ok

total-claim-⊥-when-witness-absent : TotalClaimWhenWitnessAbsent → ⊥
total-claim-⊥-when-witness-absent ()

------------------------------------------------------------------------
-- Trivial **cut** refuse — thermo-violating step fail-closed
------------------------------------------------------------------------

trivial-cut-refuse-ore :
  evaluateCutConservationClose
    cut-conservation-proved (trivialCutOp oreLeaf oreLeaf) cutWitnessPresentZeroGap false ≡
  verdict-trivial-cut-refuse
trivial-cut-refuse-ore = refl

trivial-cut-refuse-waste :
  evaluateCutConservationClose
    cut-conservation-proved (trivialCutOp wasteLeaf wasteLeaf) cutWitnessPresentZeroGap false ≡
  verdict-trivial-cut-refuse
trivial-cut-refuse-waste = refl

trivial-cut-refuse-not-ok :
  cutConservationVerdictOk
    (evaluateCutConservationClose
       cut-conservation-proved (trivialCutOp oreLeaf oreLeaf) cutWitnessPresentZeroGap false)
    ≡ false
trivial-cut-refuse-not-ok = refl

TrivialCutWhenOre : Set
TrivialCutWhenOre =
  evaluateCutConservationClose
    cut-conservation-proved (trivialCutOp oreLeaf oreLeaf) cutWitnessPresentZeroGap false ≡
  verdict-cut-admissible-ok

trivial-cut-⊥-when-ore : TrivialCutWhenOre → ⊥
trivial-cut-⊥-when-ore ()

------------------------------------------------------------------------
-- Admissible classifier-**cut** — witness present + partition-preserving step
------------------------------------------------------------------------

cut-admissible-ok :
  evaluateCutConservationClose
    cut-conservation-proved namedRecycleCut cutWitnessPresentZeroGap false ≡
  verdict-cut-admissible-ok
cut-admissible-ok = refl

cut-admissible-verdict-ok :
  cutConservationVerdictOk
    (evaluateCutConservationClose
       cut-conservation-proved namedRecycleCut cutWitnessPresentZeroGap false)
    ≡ true
cut-admissible-verdict-ok = refl

cut-admissible-ok-still-not-graph02-proved :
  cutConservationVerdictOk
    (evaluateCutConservationClose
       cut-conservation-proved namedRecycleCut cutWitnessPresentZeroGap false)
    ≡ true
  × graph02CutProved ≡ false
cut-admissible-ok-still-not-graph02-proved = cut-admissible-verdict-ok , refl

------------------------------------------------------------------------
-- Green invent refuse — physics GREEN never authorized
------------------------------------------------------------------------

green-invent-refuse-unwired :
  evaluateCutConservationClose
    cut-conservation-unwired namedRecycleCut cutWitnessPresentZeroGap true ≡
  verdict-green-invent-refuse
green-invent-refuse-unwired = refl

green-invent-always-refuse :
  cutConservationVerdictOk
    (evaluateCutConservationClose
       cut-conservation-unwired namedRecycleCut cutWitnessPresentZeroGap true)
    ≡ false
green-invent-always-refuse = refl

------------------------------------------------------------------------
-- Knowing / quantum fiber routing — geometry not meso acting
------------------------------------------------------------------------

data FormalFiber : Set where
  fiber-quantum-knowing fiber-meso-acting : FormalFiber

cutConservationFiberOk : FormalFiber → Bool
cutConservationFiberOk fiber-quantum-knowing = true
cutConservationFiberOk fiber-meso-acting = false

cut-conservation-knowing-fiber-ok :
  cutConservationFiberOk fiber-quantum-knowing ≡ true
cut-conservation-knowing-fiber-ok = refl

cut-conservation-meso-acting-not-ok :
  cutConservationFiberOk fiber-meso-acting ≡ false
cut-conservation-meso-acting-not-ok = refl

cut-conservation-routes-knowing-not-meso :
  cutConservationFiberOk fiber-quantum-knowing ≡ true ×
  cutConservationFiberOk fiber-meso-acting ≡ false
cut-conservation-routes-knowing-not-meso = refl , refl

fiberNotMesoActing : Bool
fiberNotMesoActing =
  cutConservationFiberOk fiber-quantum-knowing ∧
  not (cutConservationFiberOk fiber-meso-acting)

fiber-not-meso-acting-true : fiberNotMesoActing ≡ true
fiber-not-meso-acting-true = refl

------------------------------------------------------------------------
-- Honest pins — not GRAPH-02 Proved, not physics GREEN, cut ≠ bond
------------------------------------------------------------------------

graph02-cut-not-proved : graph02CutProved ≡ false
graph02-cut-not-proved = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

not-118-squared-green-table : not118SquaredGreenTable ≡ true
not-118-squared-green-table = refl

cut-second-law-conservation-framed : cutSecondLawConservationFramed ≡ true
cut-second-law-conservation-framed = refl

cut-not-bond-pin : cutNotBond ≡ true
cut-not-bond-pin = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second **cut** axiom fork)
------------------------------------------------------------------------

cutConservationAxiom :
  (graph02CutProved ≡ false)
  × (productionWired ≡ false)
  × (not118SquaredGreenTable ≡ true)
  × (cutSecondLawConservationFramed ≡ true)
  × (cutNotBond ≡ true)
  × (evaluateCutConservationClose cut-conservation-unwired namedRecycleCut cutWitnessAbsent false ≡ verdict-unwired-ok)
  × (evaluateCutConservationClose cut-conservation-proved namedRecycleCut cutWitnessAbsent false ≡ verdict-total-claim-refuse)
  × (evaluateCutConservationClose cut-conservation-proved (trivialCutOp oreLeaf oreLeaf) cutWitnessPresentZeroGap false ≡ verdict-trivial-cut-refuse)
  × (evaluateCutConservationClose cut-conservation-proved namedRecycleCut cutWitnessPresentZeroGap false ≡ verdict-cut-admissible-ok)
  × (cutConservationFiberOk fiber-quantum-knowing ≡ true)
  × (cutConservationFiberOk fiber-meso-acting ≡ false)
  × (cutConservationVerdictOk (evaluateCutConservationClose cut-conservation-unwired namedRecycleCut cutWitnessPresentZeroGap true) ≡ false)
  × (∀ a → isPartitionCut (cutOp thermoIdentity a) ≡ true)
  × (∀ a → isPartitionCut (cutOp a thermoIdentity) ≡ true)
  × (isCutAdmissible (trivialCutOp oreLeaf oreLeaf) ≡ false)
  × (partitionComplement ore-part ≡ waste-part)
  × (partitionComplement waste-part ≡ ore-part)
  × (elementAtomicZ hydrogen ≡ 1)
  × (elementAtomicZ oxygen ≡ 8)
  × (elementAtomicZ oganesson ≡ 118)
cutConservationAxiom =
  graph02-cut-not-proved
  , production-not-wired
  , not-118-squared-green-table
  , cut-second-law-conservation-framed
  , cut-not-bond-pin
  , unwired-close-without-witness
  , total-claim-refuse-without-witness
  , trivial-cut-refuse-ore
  , cut-admissible-ok
  , cut-conservation-knowing-fiber-ok
  , cut-conservation-meso-acting-not-ok
  , green-invent-always-refuse
  , (λ a → refl)
  , (λ a → refl)
  , trivial-cut-refuse
  , refl
  , refl
  , refl
  , refl
  , oganesson-z-118

cutConservationNamed : String
cutConservationNamed =
  "cutConservation: GRAPH-02 classifier cut ore waste partition complement conservation"

cutConservationCellId : String
cutConservationCellId = "CHEM-FORMAL-Q-AGDA-CUT-CONSERVATION"

cutConservationNonClaim : String
cutConservationNonClaim =
  "CHEM-FORMAL-Q-AGDA-CUT-CONSERVATION GRAPH-02 classifier cut conservation ore waste partition complement conserved named recycle loop cut not bond trivial cut fail-closed total-claim refuse graph02CutProved false not 118 squared GREEN table geometry knowing quantum fiber not meso acting Unwired one axiom second law conservation not second cut axiom not physics GREEN not production_wired Og Z=118"

cut-conservation-modality-unwired :
  cutConservationModalityCurrent ≡ cut-conservation-unwired
cut-conservation-modality-unwired = refl

cutConservationPhysicsGreenAuthorized : Set
cutConservationPhysicsGreenAuthorized = ⊥

cut-conservation-physics-green-false : ¬ cutConservationPhysicsGreenAuthorized
cut-conservation-physics-green-false ()

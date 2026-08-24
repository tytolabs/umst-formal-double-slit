-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.CompactionMiCost.agda
--
-- Knowing fiber (§17.5 / §22.4): compaction pays MI vs epistemicMI_null.
--   * EpistemicMI scaffold on PathProbe (null / whichPath)
--   * compaction must pay positive probe-indexed MI above null baseline
--   * derivation witness retains chain; compose imported Excitement select
--   * sole postulate `physicalSecondLaw` (Landauer axiom — no extra postulate)
--
-- Mirrors Lean `EpistemicMI.epistemicMI_null` / `URGE-INT-COMPACTION-MI-COST`.
-- Not ChemConstants. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.CompactionMiCost where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + compaction MI pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data CompactionMiCostModality : Set where
  compaction-mi-cost-unwired compaction-mi-cost-assumed
    compaction-mi-cost-proved compaction-mi-cost-surrogate
    : CompactionMiCostModality

compactionMiCostModalityCurrent : CompactionMiCostModality
compactionMiCostModalityCurrent = compaction-mi-cost-unwired

productionWired compactionProductionWired : Bool
productionWired = false
compactionProductionWired = false

------------------------------------------------------------------------
-- Excitement compose pin — import select; refuse second argmin
------------------------------------------------------------------------

data ExcitementComposePin : Set where
  import-select-excitement second-argmin-refused : ExcitementComposePin

data SecondArgminRefusal : Set where
  second-argmin-inadmissible : SecondArgminRefusal

data ImportSelectExcitementOk : Set where
  import-select-excitement-ok-marker : ImportSelectExcitementOk

refuse-second-argmin : ExcitementComposePin → Set
refuse-second-argmin import-select-excitement = ImportSelectExcitementOk
refuse-second-argmin second-argmin-refused = SecondArgminRefusal

second-argmin-refused-inadmissible :
  refuse-second-argmin second-argmin-refused
second-argmin-refused-inadmissible = second-argmin-inadmissible

import-select-excitement-ok :
  refuse-second-argmin import-select-excitement
import-select-excitement-ok = import-select-excitement-ok-marker

------------------------------------------------------------------------
-- EpistemicMI scaffold — probe-indexed MI bits (qubit cap = 1)
------------------------------------------------------------------------

data PathProbe : Set where
  null whichPath : PathProbe

epistemicMIBits : PathProbe → ℕ
epistemicMIBits null = zero
epistemicMIBits whichPath = suc zero

epistemic-mi-null-zero : epistemicMIBits null ≡ zero
epistemic-mi-null-zero = refl

epistemic-mi-bits-nonneg : ∀ (p : PathProbe) → zero ≤ epistemicMIBits p
epistemic-mi-bits-nonneg null = z≤n
epistemic-mi-bits-nonneg whichPath = z≤n

epistemic-mi-bits-le-one : ∀ (p : PathProbe) → epistemicMIBits p ≤ suc zero
epistemic-mi-bits-le-one null = z≤n
epistemic-mi-bits-le-one whichPath = s≤s z≤n

------------------------------------------------------------------------
-- Compaction MI cost — pay MI above epistemicMI_null baseline
------------------------------------------------------------------------

compactionMIBits : PathProbe → ℕ
compactionMIBits p = epistemicMIBits p

compactionMiCost : PathProbe → ℕ
compactionMiCost p = compactionMIBits p

compactionLandauerCost : PathProbe → ℕ
compactionLandauerCost p = compactionMiCost p

compaction-mi-null-zero :
  compactionMIBits null ≡ zero
compaction-mi-null-zero = epistemic-mi-null-zero

compaction-pays-mi-vs-null : PathProbe → Set
compaction-pays-mi-vs-null null = ⊥
compaction-pays-mi-vs-null whichPath = suc zero ≤ compactionMIBits whichPath

compaction-pays-mi-vs-null-whichPath :
  compaction-pays-mi-vs-null whichPath
compaction-pays-mi-vs-null-whichPath = s≤s z≤n

compaction-cost-nonneg :
  ∀ (p : PathProbe) → zero ≤ compactionLandauerCost p
compaction-cost-nonneg p = epistemic-mi-bits-nonneg p

compaction-cost-le-one :
  ∀ (p : PathProbe) → compactionLandauerCost p ≤ suc zero
compaction-cost-le-one p = epistemic-mi-bits-le-one p

compaction-landauer-null-zero :
  ∀ (p : PathProbe) → compactionLandauerCost null ≡ zero
compaction-landauer-null-zero p = refl

------------------------------------------------------------------------
-- Derivation witness — semantic compaction retains chain
------------------------------------------------------------------------

record CompactionDerivationWitness : Set where
  field
    chainLength : ℕ

retains-chain : CompactionDerivationWitness → Set
retains-chain w = suc zero ≤ CompactionDerivationWitness.chainLength w

record CompactionMiAttempt : Set where
  field
    probe : PathProbe
    witness : CompactionDerivationWitness

------------------------------------------------------------------------
-- Typed refusal — positive refuse null-probe compaction theater
------------------------------------------------------------------------

data CompactionMiCostRefusal : Set where
  epistemic-mi-null-compaction null-probe-compaction-theater
    derivation-witness-absent second-argmin : CompactionMiCostRefusal

refuse-epistemic-mi-null-compaction : CompactionMiCostRefusal
refuse-epistemic-mi-null-compaction = epistemic-mi-null-compaction

refuse-null-probe-compaction-theater : CompactionMiCostRefusal
refuse-null-probe-compaction-theater = null-probe-compaction-theater

refuse-second-argmin-selector : CompactionMiCostRefusal
refuse-second-argmin-selector = second-argmin

data CompactionMiCostOutcome : Set where
  admitted : ℕ → CompactionMiCostOutcome
  refused : CompactionMiCostRefusal → CompactionMiCostOutcome

evaluate-compaction-mi-cost :
  CompactionMiAttempt → CompactionMiCostOutcome
evaluate-compaction-mi-cost (record { probe = null ; witness = _ }) =
  refused epistemic-mi-null-compaction
evaluate-compaction-mi-cost
  (record { probe = whichPath ; witness = record { chainLength = zero } }) =
  refused derivation-witness-absent
evaluate-compaction-mi-cost
  (record { probe = whichPath ; witness = record { chainLength = suc n } }) =
  admitted (compactionMIBits whichPath)

fixture-accept-mi-bits-paid :
  evaluate-compaction-mi-cost
    (record { probe = whichPath
            ; witness = record { chainLength = suc (suc zero) } })
  ≡ admitted (suc zero)
fixture-accept-mi-bits-paid = refl

fixture-refuse-epistemic-mi-null :
  evaluate-compaction-mi-cost
    (record { probe = null
            ; witness = record { chainLength = suc zero } })
  ≡ refused epistemic-mi-null-compaction
fixture-refuse-epistemic-mi-null = refl

fixture-refuse-derivation-witness-absent :
  evaluate-compaction-mi-cost
    (record { probe = whichPath
            ; witness = record { chainLength = zero } })
  ≡ refused derivation-witness-absent
fixture-refuse-derivation-witness-absent = refl

------------------------------------------------------------------------
-- Sole Landauer postulate — mirrors LandauerLaw.physicalSecondLaw
------------------------------------------------------------------------

record HeatBath : Set where
  field
    temperature : ℕ

record ErasureProcess : Set where
  field
    bath : HeatBath
    dissipatedEntropy : ℕ

PhysicalSecondLaw : ErasureProcess → ℕ → Set
PhysicalSecondLaw proc entropyDecrease =
  entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc

postulate
  physicalSecondLaw : ∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
    PhysicalSecondLaw proc entropyDecrease

landauerBound :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
  PhysicalSecondLaw proc entropyDecrease →
  entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc
landauerBound proc ΔS h = h

compactionLandauerBound :
  ∀ (proc : ErasureProcess) (p : PathProbe) (entropyDrop : ℕ) →
  entropyDrop ≤ compactionLandauerCost p →
  PhysicalSecondLaw proc entropyDrop →
  entropyDrop ≤ ErasureProcess.dissipatedEntropy proc
compactionLandauerBound proc p ΔS _ hSL = hSL

physicalSecondLawUniformBinary :
  ∀ (proc : ErasureProcess) (uniformBinaryDrop : ℕ) →
  PhysicalSecondLaw proc uniformBinaryDrop →
  uniformBinaryDrop ≤ ErasureProcess.dissipatedEntropy proc
physicalSecondLawUniformBinary proc ΔS h = h

production-not-wired : productionWired ≡ false
production-not-wired = refl

compaction-not-production-wired : compactionProductionWired ≡ false
compaction-not-production-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

compactionMiCostAxiom :
  (epistemicMIBits null ≡ zero)
  × (∀ (p : PathProbe) → zero ≤ epistemicMIBits p)
  × (compaction-pays-mi-vs-null whichPath)
  × (productionWired ≡ false)
  × (compactionProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
  × (refuse-second-argmin import-select-excitement)
  × (evaluate-compaction-mi-cost
      (record { probe = null
              ; witness = record { chainLength = suc zero } })
      ≡ refused epistemic-mi-null-compaction)
compactionMiCostAxiom =
  epistemic-mi-null-zero
  , epistemic-mi-bits-nonneg
  , compaction-pays-mi-vs-null-whichPath
  , production-not-wired
  , compaction-not-production-wired
  , landauerBound
  , import-select-excitement-ok
  , fixture-refuse-epistemic-mi-null

compactionMiCostNamed : String
compactionMiCostNamed =
  "compactionMiCost: §17.5 §22.4 compaction pays MI vs epistemicMI_null compose Excitement select"

compactionMiCostCellId : String
compactionMiCostCellId = "URGE-FORMAL-Q-AGDA-COMPACTION-MI-COST"

compactionMiCostNonClaim : String
compactionMiCostNonClaim =
  "URGE-FORMAL-Q-AGDA-COMPACTION-MI-COST §17.5 §22.4 compaction pays MI vs epistemicMI_null epistemicMIBits null probe compaction theater refused compose Excitement select no second argmin sole postulate physicalSecondLaw no extra postulate modality Unwired not physics GREEN not production_wired"

compaction-mi-cost-modality-unwired :
  compactionMiCostModalityCurrent ≡ compaction-mi-cost-unwired
compaction-mi-cost-modality-unwired = refl

CompactionMiCostPhysicsGreenAuthorized : Set
CompactionMiCostPhysicsGreenAuthorized = ⊥

compaction-mi-cost-physics-green-false :
  ¬ CompactionMiCostPhysicsGreenAuthorized
compaction-mi-cost-physics-green-false ()

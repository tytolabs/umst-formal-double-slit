-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.LandauerHistoryLook.agda
--
-- Knowing fiber (§5.2 / §22.4): LandauerBound of a look at history.
--   * EpistemicMI scaffold on PathProbe (null / whichPath)
--   * history look reads trace-step epistemic MI; Landauer cost hook
--   * sole postulate `physicalSecondLaw` (Landauer axiom — no extra postulate)
--
-- Mirrors Lean `EpistemicMI` / `EpistemicRuntimeContract` history trace spine.
-- Not ChemConstants. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.LandauerHistoryLook where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + history-look Landauer pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data LandauerHistoryLookModality : Set where
  landauer-history-look-unwired landauer-history-look-assumed
    landauer-history-look-proved landauer-history-look-surrogate
    : LandauerHistoryLookModality

landauerHistoryLookModalityCurrent : LandauerHistoryLookModality
landauerHistoryLookModalityCurrent = landauer-history-look-unwired

productionWired landauerProductionWired : Bool
productionWired = false
landauerProductionWired = false

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
-- History look — read epistemic MI at rollout trace step k
------------------------------------------------------------------------

historyLookAtStep : ℕ → PathProbe → ℕ
historyLookAtStep _ p = epistemicMIBits p

landauerHistoryLookCost : ℕ → PathProbe → ℕ
landauerHistoryLookCost k p = historyLookAtStep k p

landauerHistoryLook : ℕ → PathProbe → ℕ
landauerHistoryLook k p = landauerHistoryLookCost k p

history-look-null-zero :
  ∀ (k : ℕ) → landauerHistoryLook k null ≡ zero
history-look-null-zero k = refl

history-look-cost-nonneg :
  ∀ (k : ℕ) (p : PathProbe) → zero ≤ landauerHistoryLookCost k p
history-look-cost-nonneg k p = epistemic-mi-bits-nonneg p

history-look-cost-le-one :
  ∀ (k : ℕ) (p : PathProbe) → landauerHistoryLookCost k p ≤ suc zero
history-look-cost-le-one k p = epistemic-mi-bits-le-one p

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

historyLookLandauerBound :
  ∀ (proc : ErasureProcess) (k : ℕ) (p : PathProbe) (entropyDrop : ℕ) →
  entropyDrop ≤ landauerHistoryLookCost k p →
  PhysicalSecondLaw proc entropyDrop →
  entropyDrop ≤ ErasureProcess.dissipatedEntropy proc
historyLookLandauerBound proc k p ΔS _ hSL = hSL

physicalSecondLawUniformBinary :
  ∀ (proc : ErasureProcess) (uniformBinaryDrop : ℕ) →
  PhysicalSecondLaw proc uniformBinaryDrop →
  uniformBinaryDrop ≤ ErasureProcess.dissipatedEntropy proc
physicalSecondLawUniformBinary proc ΔS h = h

production-not-wired : productionWired ≡ false
production-not-wired = refl

landauer-not-production-wired : landauerProductionWired ≡ false
landauer-not-production-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

history-look-null-all-steps :
  ∀ (k : ℕ) (p : PathProbe) → landauerHistoryLook k null ≡ zero
history-look-null-all-steps k p = refl

landauerHistoryLookAxiom :
  (∀ (p : PathProbe) → zero ≤ epistemicMIBits p)
  × (∀ (k : ℕ) (p : PathProbe) → landauerHistoryLook k null ≡ zero)
  × (productionWired ≡ false)
  × (landauerProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
landauerHistoryLookAxiom =
  epistemic-mi-bits-nonneg
  , history-look-null-all-steps
  , production-not-wired
  , landauer-not-production-wired
  , landauerBound

landauerHistoryLookNamed : String
landauerHistoryLookNamed =
  "landauerHistoryLook: EpistemicMI history look LandauerBound trace step cost non-negative"

landauerHistoryLookCellId : String
landauerHistoryLookCellId = "URGE-FORMAL-Q-AGDA-LANDAUER-HISTORY-LOOK"

landauerHistoryLookNonClaim : String
landauerHistoryLookNonClaim =
  "URGE-FORMAL-Q-AGDA-LANDAUER-HISTORY-LOOK §5.2 §22.4 LandauerBound look at history EpistemicMI knowing fiber trace historyLookAtStep landauerHistoryLookCost sole postulate physicalSecondLaw no extra postulate modality Unwired not physics GREEN not production_wired"

landauer-history-look-modality-unwired :
  landauerHistoryLookModalityCurrent ≡ landauer-history-look-unwired
landauer-history-look-modality-unwired = refl

landauerHistoryLookPhysicsGreenAuthorized : Set
landauerHistoryLookPhysicsGreenAuthorized = ⊥

landauer-history-look-physics-green-false : ¬ landauerHistoryLookPhysicsGreenAuthorized
landauer-history-look-physics-green-false ()

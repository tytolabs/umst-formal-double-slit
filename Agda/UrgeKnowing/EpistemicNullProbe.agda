-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.EpistemicNullProbe.agda
--
-- Knowing fiber (§22.4): EpistemicMI null probe I=0.
--   * epistemicMIBits null = 0 (definitional)
--   * epistemicLandauerCost null = 0
--   * sole postulate `physicalSecondLaw` (imported — no extra postulate)
--
-- Mirrors Lean `EpistemicMI.epistemicMI_null` / `epistemicMIBits_null` /
-- `epistemicLandauerCost_null` and Haskell `UrgeKnowing.EpistemicNullProbe`.
-- Not ChemConstants. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.EpistemicNullProbe where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import UrgeKnowing.LandauerHistoryLook
  using (PathProbe; null; whichPath; epistemicMIBits
       ; epistemic-mi-null-zero; epistemic-mi-bits-nonneg; epistemic-mi-bits-le-one
       ; HeatBath; ErasureProcess; PhysicalSecondLaw; physicalSecondLaw; landauerBound
       ; productionWired; landauerProductionWired
       ; production-not-wired; landauer-not-production-wired)

------------------------------------------------------------------------
-- Modality + null-probe pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data EpistemicNullProbeModality : Set where
  epistemic-null-probe-unwired epistemic-null-probe-assumed
    epistemic-null-probe-proved epistemic-null-probe-surrogate
    : EpistemicNullProbeModality

epistemicNullProbeModalityCurrent : EpistemicNullProbeModality
epistemicNullProbeModalityCurrent = epistemic-null-probe-unwired

------------------------------------------------------------------------
-- EpistemicMI null probe — I=0 on knowing fiber (qubit cap = 1)
------------------------------------------------------------------------

epistemicMI : PathProbe → ℕ
epistemicMI p = epistemicMIBits p

epistemicMINull : epistemicMI null ≡ zero
epistemicMINull = epistemic-mi-null-zero

epistemic-mi-nonneg : ∀ (p : PathProbe) → zero ≤ epistemicMI p
epistemic-mi-nonneg p = epistemic-mi-bits-nonneg p

epistemic-mi-le-one : ∀ (p : PathProbe) → epistemicMI p ≤ suc zero
epistemic-mi-le-one p = epistemic-mi-bits-le-one p

epistemicMIBitsNull : PathProbe → ℕ
epistemicMIBitsNull p = epistemicMIBits p

epistemicMIBitsNullZero : epistemicMIBitsNull null ≡ zero
epistemicMIBitsNullZero = epistemic-mi-null-zero

------------------------------------------------------------------------
-- Landauer hook — vanishes under null readout
------------------------------------------------------------------------

epistemicLandauerCost : PathProbe → ℕ
epistemicLandauerCost p = epistemicMIBits p

epistemicLandauerCostNull : epistemicLandauerCost null ≡ zero
epistemicLandauerCostNull = epistemic-mi-null-zero

epistemic-landauer-cost-nonneg :
  ∀ (p : PathProbe) → zero ≤ epistemicLandauerCost p
epistemic-landauer-cost-nonneg p = epistemic-mi-bits-nonneg p

epistemic-landauer-cost-le-one :
  ∀ (p : PathProbe) → epistemicLandauerCost p ≤ suc zero
epistemic-landauer-cost-le-one p = epistemic-mi-bits-le-one p

------------------------------------------------------------------------
-- Null-probe policy — all representative null claims hold
------------------------------------------------------------------------

epistemicNullProbePolicy :
  (epistemicMI null ≡ zero)
  × (epistemicMIBitsNull null ≡ zero)
  × (epistemicLandauerCost null ≡ zero)
epistemicNullProbePolicy =
  epistemicMINull
  , epistemicMIBitsNullZero
  , epistemicLandauerCostNull

epistemicMINullAllSteps :
  ∀ (p : PathProbe) → epistemicMI null ≡ zero
epistemicMINullAllSteps p = refl

epistemicMIBitsNullAllSteps :
  ∀ (p : PathProbe) → epistemicMIBitsNull null ≡ zero
epistemicMIBitsNullAllSteps p = refl

epistemicLandauerCostNullAllTemps :
  ∀ (p : PathProbe) → epistemicLandauerCost null ≡ zero
epistemicLandauerCostNullAllTemps p = refl

------------------------------------------------------------------------
-- Landauer framing — sole postulate imported from LandauerHistoryLook
------------------------------------------------------------------------

landauerNotSecondAxiom :
  ∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
  PhysicalSecondLaw proc entropyDecrease →
  entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc
landauerNotSecondAxiom proc ΔS h = landauerBound proc ΔS h

epistemicNullLandauerBound :
  ∀ (proc : ErasureProcess) (p : PathProbe) (entropyDrop : ℕ) →
  entropyDrop ≤ epistemicLandauerCost p →
  PhysicalSecondLaw proc entropyDrop →
  entropyDrop ≤ ErasureProcess.dissipatedEntropy proc
epistemicNullLandauerBound proc p ΔS _ hSL = hSL

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

epistemicNullProbeAxiom :
  (epistemicMI null ≡ zero)
  × (epistemicMIBitsNull null ≡ zero)
  × (epistemicLandauerCost null ≡ zero)
  × (productionWired ≡ false)
  × (landauerProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
epistemicNullProbeAxiom =
  epistemicMINull
  , epistemicMIBitsNullZero
  , epistemicLandauerCostNull
  , production-not-wired
  , landauer-not-production-wired
  , landauerBound

epistemicNullProbeNamed : String
epistemicNullProbeNamed =
  "epistemic_null_probe: EpistemicMI null probe I=0 on knowing fiber; Landauer hook zero; physicalSecondLaw sole axiom framing"

epistemicNullProbeCellId : String
epistemicNullProbeCellId = "URGE-FORMAL-Q-AGDA-EPISTEMIC-NULL-PROBE"

epistemicNullProbeNonClaim : String
epistemicNullProbeNonClaim =
  "URGE-FORMAL-Q-AGDA-EPISTEMIC-NULL-PROBE §22.4 epistemic_null_probe EpistemicMI null probe I=0 epistemicMIBitsNull epistemicLandauerCost null zero sole postulate physicalSecondLaw no extra postulate modality Unwired not physics GREEN not production_wired knowing fiber not meso thermo"

epistemic-null-probe-modality-unwired :
  epistemicNullProbeModalityCurrent ≡ epistemic-null-probe-unwired
epistemic-null-probe-modality-unwired = refl

epistemicNullProbePhysicsGreenAuthorized : Set
epistemicNullProbePhysicsGreenAuthorized = ⊥

epistemic-null-probe-physics-green-false : ¬ epistemicNullProbePhysicsGreenAuthorized
epistemic-null-probe-physics-green-false ()

epistemicNullProbeKnowingFiberOk :
  (epistemicNullProbeModalityCurrent ≡ epistemic-null-probe-unwired)
  × (¬ epistemicNullProbePhysicsGreenAuthorized)
epistemicNullProbeKnowingFiberOk =
  epistemic-null-probe-modality-unwired
  , epistemic-null-probe-physics-green-false

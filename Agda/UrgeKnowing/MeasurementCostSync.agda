-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.MeasurementCostSync.agda
--
-- Knowing fiber (§16): measurement cost of a sync look at inbound state.
--   * EpistemicMI scaffold on PathProbe (null / whichPath)
--   * sync look reads probe-indexed epistemic MI; Landauer cost hook
--   * sole postulate `physicalSecondLaw` (Landauer axiom — no extra postulate)
--   * compose imported Excitement select — no second local argmin
--
-- Distinct from rollout history look (LandauerHistoryLook). Not meso thermo.
-- Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.MeasurementCostSync where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Unit using (tt; ⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (no)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + sync-look measurement pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data MeasurementCostSyncModality : Set where
  measurement-cost-sync-unwired measurement-cost-sync-assumed
    measurement-cost-sync-proved measurement-cost-sync-surrogate
    : MeasurementCostSyncModality

measurementCostSyncModalityCurrent : MeasurementCostSyncModality
measurementCostSyncModalityCurrent = measurement-cost-sync-unwired

productionWired syncProductionWired : Bool
productionWired = false
syncProductionWired = false

------------------------------------------------------------------------
-- Excitement compose pin — import select; refuse second argmin
------------------------------------------------------------------------

data ExcitementComposePin : Set where
  import-select-excitement second-argmin-refused : ExcitementComposePin

data SecondArgminRefusal : Set where
  second-argmin-inadmissible : SecondArgminRefusal

refuse-second-argmin : ExcitementComposePin → Set
refuse-second-argmin import-select-excitement = ⊤
refuse-second-argmin second-argmin-refused = SecondArgminRefusal

second-argmin-refused-inadmissible :
  refuse-second-argmin second-argmin-refused
second-argmin-refused-inadmissible = second-argmin-inadmissible

import-select-excitement-ok :
  refuse-second-argmin import-select-excitement
import-select-excitement-ok = tt

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
-- Sync look — inbound Kleisli sync inspects probe-indexed epistemic MI
------------------------------------------------------------------------

syncLookMIBits : PathProbe → ℕ
syncLookMIBits p = epistemicMIBits p

syncLookMeasurementCost : PathProbe → ℕ
syncLookMeasurementCost p = syncLookMIBits p

syncLookLandauerCost : PathProbe → ℕ
syncLookLandauerCost p = syncLookMeasurementCost p

sync-look-null-zero :
  ∀ (p : PathProbe) → syncLookLandauerCost null ≡ zero
sync-look-null-zero p = refl

sync-look-cost-nonneg :
  ∀ (p : PathProbe) → zero ≤ syncLookLandauerCost p
sync-look-cost-nonneg p = epistemic-mi-bits-nonneg p

sync-look-cost-le-one :
  ∀ (p : PathProbe) → syncLookLandauerCost p ≤ suc zero
sync-look-cost-le-one p = epistemic-mi-bits-le-one p

sync-look-mi-equals-epistemic :
  ∀ (p : PathProbe) → syncLookMIBits p ≡ epistemicMIBits p
sync-look-mi-equals-epistemic p = refl

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

syncLookLandauerBound :
  ∀ (proc : ErasureProcess) (p : PathProbe) (entropyDrop : ℕ) →
  entropyDrop ≤ syncLookLandauerCost p →
  PhysicalSecondLaw proc entropyDrop →
  entropyDrop ≤ ErasureProcess.dissipatedEntropy proc
syncLookLandauerBound proc p ΔS _ hSL = hSL

physicalSecondLawUniformBinary :
  ∀ (proc : ErasureProcess) (uniformBinaryDrop : ℕ) →
  PhysicalSecondLaw proc uniformBinaryDrop →
  uniformBinaryDrop ≤ ErasureProcess.dissipatedEntropy proc
physicalSecondLawUniformBinary proc ΔS h = h

production-not-wired : productionWired ≡ false
production-not-wired = refl

sync-not-production-wired : syncProductionWired ≡ false
sync-not-production-wired = refl

------------------------------------------------------------------------
-- Authority cites + meso thermo restate fence
------------------------------------------------------------------------

measurementCostSyncNamed : String
measurementCostSyncNamed =
  "measurementCostSync: EpistemicMI sync look LandauerBound inbound Kleisli cost non-negative"

measurementCostSyncCellId : String
measurementCostSyncCellId = "URGE-FORMAL-Q-AGDA-MEASUREMENT-COST-SYNC"

measurementCostSyncNonClaim : String
measurementCostSyncNonClaim =
  "URGE-FORMAL-Q-AGDA-MEASUREMENT-COST-SYNC §16 measurement cost of sync look knowing fiber syncLookLandauerCost epistemicMIBits sole postulate physicalSecondLaw no extra postulate compose Excitement select no second argmin not meso thermo not physics GREEN not production_wired"

mesoThermoGRestated : String
mesoThermoGRestated = "meso_thermo_G_T_P_x_restate"

formalFiberQuantumKnowing : String
formalFiberQuantumKnowing = "umst-formal-double-slit/quantum_knowing"

formalFiberMesoActing : String
formalFiberMesoActing = "umst-formal"

measurement-cost-sync-not-meso-thermo-restate :
  measurementCostSyncNonClaim ≢ mesoThermoGRestated
measurement-cost-sync-not-meso-thermo-restate ()

knowing-fiber-ok :
  formalFiberQuantumKnowing ≢ formalFiberMesoActing
knowing-fiber-ok ()

------------------------------------------------------------------------
-- One design axiom bundle (not a second optimizer fork)
------------------------------------------------------------------------

measurementCostSyncAxiom :
  (∀ (p : PathProbe) → zero ≤ epistemicMIBits p)
  × (∀ (p : PathProbe) → syncLookLandauerCost null ≡ zero)
  × (productionWired ≡ false)
  × (syncProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
  × (refuse-second-argmin import-select-excitement)
measurementCostSyncAxiom =
  epistemic-mi-bits-nonneg
  , sync-look-null-zero
  , production-not-wired
  , sync-not-production-wired
  , landauerBound
  , import-select-excitement-ok

measurement-cost-sync-modality-unwired :
  measurementCostSyncModalityCurrent ≡ measurement-cost-sync-unwired
measurement-cost-sync-modality-unwired = refl

MeasurementCostSyncPhysicsGreenAuthorized : Set
MeasurementCostSyncPhysicsGreenAuthorized = ⊥

measurement-cost-sync-physics-green-false :
  ¬ MeasurementCostSyncPhysicsGreenAuthorized
measurement-cost-sync-physics-green-false ()

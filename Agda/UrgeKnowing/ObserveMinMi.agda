-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.ObserveMinMi.agda
--
-- Knowing fiber (§5.2 step-1): observe local+mesh at minimal MI (Landauer accounted).
--   * paired LocalMeshState carrier; pairwise MI bits H(local)+H(mesh)−H(joint)
--   * observeMinMiLandauerCost hook; sole postulate `physicalSecondLaw` (imported)
--   * zero extra postulate beyond LandauerHistoryLook spine
--
-- Mirrors Lean `UrgeKnowing.ObserveMinMi` / Haskell `UrgeKnowing.ObserveMinMi`.
-- Not ChemConstants. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.ObserveMinMi where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Base using (z≤n)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import UrgeKnowing.LandauerHistoryLook
  using (HeatBath; ErasureProcess; PhysicalSecondLaw; physicalSecondLaw; landauerBound
       ; productionWired; landauerProductionWired
       ; production-not-wired; landauer-not-production-wired)

------------------------------------------------------------------------
-- Modality + observe-min-MI pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data ObserveMinMiModality : Set where
  observe-min-mi-unwired observe-min-mi-assumed
    observe-min-mi-proved observe-min-mi-surrogate
    : ObserveMinMiModality

observeMinMiModalityCurrent : ObserveMinMiModality
observeMinMiModalityCurrent = observe-min-mi-unwired

------------------------------------------------------------------------
-- Local+mesh carriers — paired observation scaffold (knowing fiber)
------------------------------------------------------------------------

record LocalState : Set where
  field
    entropyBits : ℕ

record MeshState : Set where
  field
    entropyBits : ℕ

record LocalMeshState : Set where
  field
    local : LocalState
    mesh  : MeshState

data LocalMeshCoalgebra : Set where
  local-only  : LocalState → LocalMeshCoalgebra
  mesh-only   : MeshState → LocalMeshCoalgebra
  paired      : LocalMeshState → LocalMeshCoalgebra

local-mesh-paired : LocalState → MeshState → LocalMeshState
local-mesh-paired l m = record { local = l ; mesh = m }

local-mesh-deconstruct : LocalMeshState → LocalMeshCoalgebra
local-mesh-deconstruct s = paired s

------------------------------------------------------------------------
-- Minimal MI bits — I(local;mesh) = H(local) + H(mesh) − H(joint)
------------------------------------------------------------------------

pairwise-mi-bits : ℕ → ℕ → ℕ → ℕ
pairwise-mi-bits hLocal hMesh jointEntropy = (hLocal + hMesh) ∸ jointEntropy

pairwise-mi-bits-nonneg :
  ∀ (hLocal hMesh jointEntropy : ℕ) →
  zero ≤ pairwise-mi-bits hLocal hMesh jointEntropy
pairwise-mi-bits-nonneg hLocal hMesh jointEntropy = z≤n

observe-min-mi-bits :
  (s : LocalMeshState) (jointEntropy : ℕ) → ℕ
observe-min-mi-bits s jointEntropy =
  pairwise-mi-bits
    (LocalState.entropyBits (LocalMeshState.local s))
    (MeshState.entropyBits (LocalMeshState.mesh s))
    jointEntropy

observe-min-mi-bits-nonneg :
  ∀ (s : LocalMeshState) (jointEntropy : ℕ) →
  zero ≤ observe-min-mi-bits s jointEntropy
observe-min-mi-bits-nonneg s jointEntropy = z≤n

independent-local-mesh : LocalMeshState
independent-local-mesh = local-mesh-paired
  (record { entropyBits = suc zero })
  (record { entropyBits = suc zero })

observe-min-mi-independent-zero :
  observe-min-mi-bits independent-local-mesh (suc (suc zero)) ≡ zero
observe-min-mi-independent-zero = refl

correlated-local-mesh : LocalMeshState
correlated-local-mesh = local-mesh-paired
  (record { entropyBits = suc zero })
  (record { entropyBits = suc zero })

observe-min-mi-correlated-one :
  observe-min-mi-bits correlated-local-mesh (suc zero) ≡ suc zero
observe-min-mi-correlated-one = refl

------------------------------------------------------------------------
-- Landauer hook — observe local+mesh at minimal MI (accounted)
------------------------------------------------------------------------

observeMinMiLandauerCost : LocalMeshState → ℕ → ℕ
observeMinMiLandauerCost s jointEntropy = observe-min-mi-bits s jointEntropy

observe-min-mi-landauer-cost-nonneg :
  ∀ (s : LocalMeshState) (jointEntropy : ℕ) →
  zero ≤ observeMinMiLandauerCost s jointEntropy
observe-min-mi-landauer-cost-nonneg s jointEntropy =
  observe-min-mi-bits-nonneg s jointEntropy

observeMinMiLandauerBound :
  ∀ (proc : ErasureProcess) (s : LocalMeshState) (jointEntropy entropyDrop : ℕ) →
  entropyDrop ≤ observeMinMiLandauerCost s jointEntropy →
  PhysicalSecondLaw proc entropyDrop →
  entropyDrop ≤ ErasureProcess.dissipatedEntropy proc
observeMinMiLandauerBound proc s jointEntropy ΔS _ hSL = hSL

------------------------------------------------------------------------
-- Observation outcome — paired local+mesh vs positive refuse tags
------------------------------------------------------------------------

data ObserveMinMiRefusal : Set where
  mesh-absent-when-paired-required mutual-information-zero : ObserveMinMiRefusal

data ObserveMinMiOutcome : Set where
  observed : ℕ → ObserveMinMiOutcome
  refused  : ObserveMinMiRefusal → ObserveMinMiOutcome

requires-paired : LocalMeshCoalgebra → Set
requires-paired (paired _) = ⊤
requires-paired _ = ⊥

observe-min-mi-from-coalgebra :
  LocalMeshCoalgebra → ℕ → ObserveMinMiOutcome
observe-min-mi-from-coalgebra (paired s) jointEntropy =
  observed (observe-min-mi-bits s jointEntropy)
observe-min-mi-from-coalgebra (local-only _) _ =
  refused mesh-absent-when-paired-required
observe-min-mi-from-coalgebra (mesh-only _) _ =
  refused mesh-absent-when-paired-required

refuse-mi-zero-occupancy :
  ∀ (s : LocalMeshState) (jointEntropy : ℕ) →
  observe-min-mi-bits s jointEntropy ≡ zero →
  ObserveMinMiOutcome
refuse-mi-zero-occupancy s jointEntropy h0 =
  refused mutual-information-zero

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

observeMinMiPolicy :
  (∀ (s : LocalMeshState) (jointEntropy : ℕ) →
    zero ≤ observe-min-mi-bits s jointEntropy)
  × (∀ (s : LocalMeshState) (jointEntropy : ℕ) →
    zero ≤ observeMinMiLandauerCost s jointEntropy)
  × (productionWired ≡ false)
  × (landauerProductionWired ≡ false)
observeMinMiPolicy =
  observe-min-mi-bits-nonneg
  , observe-min-mi-landauer-cost-nonneg
  , production-not-wired
  , landauer-not-production-wired

observeMinMiAxiom :
  (∀ (s : LocalMeshState) (jointEntropy : ℕ) →
    zero ≤ observe-min-mi-bits s jointEntropy)
  × (∀ (s : LocalMeshState) (jointEntropy : ℕ) →
    zero ≤ observeMinMiLandauerCost s jointEntropy)
  × (productionWired ≡ false)
  × (landauerProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
observeMinMiAxiom =
  observe-min-mi-bits-nonneg
  , observe-min-mi-landauer-cost-nonneg
  , production-not-wired
  , landauer-not-production-wired
  , landauerBound

observeMinMiNamed : String
observeMinMiNamed =
  "observeMinMi: paired local+mesh minimal MI observation Landauer accounted knowing fiber physicalSecondLaw sole axiom framing"

observeMinMiCellId : String
observeMinMiCellId = "URGE-FORMAL-Q-AGDA-OBSERVE-MIN-MI"

observeMinMiNonClaim : String
observeMinMiNonClaim =
  "URGE-FORMAL-Q-AGDA-OBSERVE-MIN-MI §5.2 step-1 observe local+mesh at minimal MI Landauer accounted pairwiseMIBits observeMinMiLandauerCost sole postulate physicalSecondLaw no extra postulate modality Unwired not physics GREEN not production_wired knowing fiber not meso acting coalgebra"

observe-min-mi-modality-unwired :
  observeMinMiModalityCurrent ≡ observe-min-mi-unwired
observe-min-mi-modality-unwired = refl

observeMinMiPhysicsGreenAuthorized : Set
observeMinMiPhysicsGreenAuthorized = ⊥

observe-min-mi-physics-green-false : ¬ observeMinMiPhysicsGreenAuthorized
observe-min-mi-physics-green-false ()

observeMinMiKnowingFiberOk :
  (observeMinMiModalityCurrent ≡ observe-min-mi-unwired)
  × (¬ observeMinMiPhysicsGreenAuthorized)
observeMinMiKnowingFiberOk =
  observe-min-mi-modality-unwired
  , observe-min-mi-physics-green-false

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.PersistVsOccupancy.agda
--
-- Knowing fiber (§12.7): persist Hilbert ≠ occupancy Hilbert; homolog ≠ copy.
--   * Persist Hilbert (acting): egoff hilbert_index(ucrs_seq, grid_hash) via xy2d
--   * Occupancy Hilbert (knowing): ADK cell_locality_hash FNV antichain sort
--   * Homolog relates fibers geometrically — homolog ≠ copy; fuse positively refused
--   * compose imported Excitement select — no second local argmin
--   * sole postulate `physicalSecondLaw` (Landauer axiom — no extra postulate)
--
-- Mirrors URGE-INT-PERSIST-VS-OCCUPANCY Rust witness. Not meso thermo.
-- Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.PersistVsOccupancy where

open import Agda.Builtin.Unit using (tt; ⊤)
open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Base using (z≤n)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + persist-vs-occupancy pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data PersistVsOccupancyModality : Set where
  persist-vs-occupancy-unwired persist-vs-occupancy-assumed
    persist-vs-occupancy-proved persist-vs-occupancy-surrogate
    : PersistVsOccupancyModality

persistVsOccupancyModalityCurrent : PersistVsOccupancyModality
persistVsOccupancyModalityCurrent = persist-vs-occupancy-unwired

productionWired persistProductionWired : Bool
productionWired = false
persistProductionWired = false

------------------------------------------------------------------------
-- Hilbert roles — persist (acting) vs occupancy (knowing) are distinct
------------------------------------------------------------------------

data HilbertRole : Set where
  persistActing occupancyKnowing : HilbertRole

persist-ne-occupancy-role : persistActing ≢ occupancyKnowing
persist-ne-occupancy-role ()

record PersistHilbert : Set where
  constructor mk-persist
  field
    raw : ℕ

record OccupancyHilbert : Set where
  constructor mk-occupancy
  field
    raw : ℕ

persist-hilbert-role : HilbertRole
persist-hilbert-role = persistActing

occupancy-hilbert-role : HilbertRole
occupancy-hilbert-role = occupancyKnowing

persist-role-ne-occupancy-role :
  persist-hilbert-role ≢ occupancy-hilbert-role
persist-role-ne-occupancy-role = persist-ne-occupancy-role

------------------------------------------------------------------------
-- Positive fuse refusal — distinct from bare `!physics_green`
------------------------------------------------------------------------

data HilbertFuseRefused : Set where
  persistIntoOccupancy occupancyIntoPersist homologIsNotCopy secondArgmin
    : HilbertFuseRefused

refuse-fuse-persist-into-occupancy :
  PersistHilbert → HilbertFuseRefused
refuse-fuse-persist-into-occupancy _ = persistIntoOccupancy

refuse-fuse-occupancy-into-persist :
  OccupancyHilbert → HilbertFuseRefused
refuse-fuse-occupancy-into-persist _ = occupancyIntoPersist

refuse-second-argmin : HilbertFuseRefused
refuse-second-argmin = secondArgmin

fuse-persist-into-occupancy-refused :
  ∀ (p : PersistHilbert) →
  refuse-fuse-persist-into-occupancy p ≡ persistIntoOccupancy
fuse-persist-into-occupancy-refused _ = refl

fuse-occupancy-into-persist-refused :
  ∀ (o : OccupancyHilbert) →
  refuse-fuse-occupancy-into-persist o ≡ occupancyIntoPersist
fuse-occupancy-into-persist-refused _ = refl

------------------------------------------------------------------------
-- Homolog witness — homolog relates fibers; homolog ≠ copy
------------------------------------------------------------------------

record HilbertHomologWitness : Set where
  field
    persist : PersistHilbert
    occupancy : OccupancyHilbert
    claimsIdentityCopy : Bool

homolog-not-copy :
  ∀ (w : HilbertHomologWitness) →
  HilbertHomologWitness.claimsIdentityCopy w ≡ false →
  persist-hilbert-role ≢ occupancy-hilbert-role
homolog-not-copy w noCopy = persist-role-ne-occupancy-role

homolog-claims-identity-copy :
  ∀ (w : HilbertHomologWitness) →
  HilbertHomologWitness.claimsIdentityCopy w ≡ true →
  HilbertFuseRefused
homolog-claims-identity-copy w copy = homologIsNotCopy

------------------------------------------------------------------------
-- Excitement compose pin — import select; refuse second argmin
------------------------------------------------------------------------

data ExcitementComposePin : Set where
  importSelectExcitement secondArgminRefused : ExcitementComposePin

import-select-excitement-ok :
  ExcitementComposePin → Set
import-select-excitement-ok importSelectExcitement = ⊤
import-select-excitement-ok secondArgminRefused = HilbertFuseRefused

compose-import-select-excitement :
  import-select-excitement-ok importSelectExcitement
compose-import-select-excitement = tt

compose-second-argmin-refused :
  import-select-excitement-ok secondArgminRefused
compose-second-argmin-refused = secondArgmin

------------------------------------------------------------------------
-- Authority cites (read-only — no Cargo / ADK import)
------------------------------------------------------------------------

persistHilbertAuthority : String
persistHilbertAuthority = "umst/egoff/egoff/src/memory/hilbert_layout.rs"

occupancyHilbertAuthority : String
occupancyHilbertAuthority =
  "umst/umst-meta/crates/umst-adk/src/hilbert_allocate.rs"

metaExcitementModule : String
metaExcitementModule = "umst-meta/crates/umst-meta/src/excitement.rs"

composeSurrogateFor : String
composeSurrogateFor = "UMST.Excitement.select"

persistNotOccupancyCopyCollision : String
persistNotOccupancyCopyCollision =
  "persist Hilbert xy2d(ucrs_seq, grid_hash) ≠ occupancy Hilbert FNV(cell_id, write_set) — homolog ≠ copy"

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

physicalSecondLawUniformBinary :
  ∀ (proc : ErasureProcess) (uniformBinaryDrop : ℕ) →
  PhysicalSecondLaw proc uniformBinaryDrop →
  uniformBinaryDrop ≤ ErasureProcess.dissipatedEntropy proc
physicalSecondLawUniformBinary proc ΔS h = h

production-not-wired : productionWired ≡ false
production-not-wired = refl

persist-not-production-wired : persistProductionWired ≡ false
persist-not-production-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

persistVsOccupancyAxiom :
  (persistActing ≢ occupancyKnowing)
  × (∀ (p : PersistHilbert) →
      refuse-fuse-persist-into-occupancy p ≡ persistIntoOccupancy)
  × (∀ (o : OccupancyHilbert) →
      refuse-fuse-occupancy-into-persist o ≡ occupancyIntoPersist)
  × (productionWired ≡ false)
  × (persistProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
  × (import-select-excitement-ok importSelectExcitement)
persistVsOccupancyAxiom =
  persist-ne-occupancy-role
  , fuse-persist-into-occupancy-refused
  , fuse-occupancy-into-persist-refused
  , production-not-wired
  , persist-not-production-wired
  , landauerBound
  , compose-import-select-excitement

persistVsOccupancyNamed : String
persistVsOccupancyNamed =
  "persistVsOccupancy: §12.7 persist Hilbert acting distinct from occupancy Hilbert knowing homolog not copy fuse refused"

persistVsOccupancyCellId : String
persistVsOccupancyCellId = "URGE-FORMAL-Q-AGDA-PERSIST-VS-OCCUPANCY"

persistVsOccupancyNonClaim : String
persistVsOccupancyNonClaim =
  "URGE-FORMAL-Q-AGDA-PERSIST-VS-OCCUPANCY §12.7 persist Hilbert acting egoff hilbert_index ucrs_seq grid_hash xy2d distinct from occupancy Hilbert knowing ADK cell_locality_hash FNV antichain sort homolog not copy fuse refused positive compose Excitement select no second argmin sole postulate physicalSecondLaw no extra postulate modality Unwired not physics GREEN not production_wired"

persist-vs-occupancy-modality-unwired :
  persistVsOccupancyModalityCurrent ≡ persist-vs-occupancy-unwired
persist-vs-occupancy-modality-unwired = refl

PersistVsOccupancyPhysicsGreenAuthorized : Set
PersistVsOccupancyPhysicsGreenAuthorized = ⊥

persist-vs-occupancy-physics-green-false :
  ¬ PersistVsOccupancyPhysicsGreenAuthorized
persist-vs-occupancy-physics-green-false ()

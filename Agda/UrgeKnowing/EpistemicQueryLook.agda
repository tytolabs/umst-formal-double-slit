-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: UrgeKnowing.EpistemicQueryLook.agda
--
-- Knowing fiber (§18): query is verification cost (information-up), not coordination.
--   * QueryLookClass — verification-cost bits vs coordination-theater refuse
--   * Epistemic query look on quantum knowing fiber; meso-acting misroute refused
--   * sole postulate `physicalSecondLaw` imported from LandauerHistoryLook
--     (Landauer axiom — zero extra postulate in this module)
--
-- Mirrors Rust `epistemic_query_look` / Lean `EpistemicQueryLook` spine.
-- Not ChemConstants. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module UrgeKnowing.EpistemicQueryLook where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import UrgeKnowing.LandauerHistoryLook
  using (PathProbe; epistemicMIBits
  ; ErasureProcess; PhysicalSecondLaw; landauerBound
  ; productionWired; landauerProductionWired)

------------------------------------------------------------------------
-- Modality + epistemic query look pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data EpistemicQueryLookModality : Set where
  epistemic-query-look-unwired epistemic-query-look-assumed
    epistemic-query-look-proved epistemic-query-look-surrogate
    : EpistemicQueryLookModality

epistemicQueryLookModalityCurrent : EpistemicQueryLookModality
epistemicQueryLookModalityCurrent = epistemic-query-look-unwired

queryLookProductionWired : Bool
queryLookProductionWired = false

------------------------------------------------------------------------
-- §18 query class — verification cost (information-up) vs coordination
------------------------------------------------------------------------

data QueryLookClass : Set where
  verification-cost : ℕ → QueryLookClass
  coordination-theater : QueryLookClass

data FormalFiber : Set where
  meso-acting quantum-knowing : FormalFiber

record EpistemicQueryLook : Set where
  field
    class : QueryLookClass
    fiber : FormalFiber

verification-cost-look : ℕ → EpistemicQueryLook
verification-cost-look bits = record
  { class = verification-cost bits
  ; fiber = quantum-knowing
  }

coordination-theater-look : EpistemicQueryLook
coordination-theater-look = record
  { class = coordination-theater
  ; fiber = quantum-knowing
  }

data EpistemicQueryLookRefusal : Set where
  coordination-theater-refused meso-fiber-misroute
    non-positive-verification-bits second-argmin-refused
    : EpistemicQueryLookRefusal

data EpistemicQueryLookOutcome : Set where
  admitted refused
    : EpistemicQueryLookOutcome

admit-epistemic-query-look : EpistemicQueryLook → EpistemicQueryLookOutcome
admit-epistemic-query-look q with EpistemicQueryLook.fiber q
                           | EpistemicQueryLook.class q
admit-epistemic-query-look q | meso-acting | _ = refused
admit-epistemic-query-look q | quantum-knowing | coordination-theater = refused
admit-epistemic-query-look q | quantum-knowing | verification-cost zero = refused
admit-epistemic-query-look q | quantum-knowing | verification-cost (suc _) = admitted

query-look-is-verification-cost : QueryLookClass → Set
query-look-is-verification-cost (verification-cost _) = ⊤
query-look-is-verification-cost coordination-theater = ⊥

query-look-is-coordination-theater : QueryLookClass → Set
query-look-is-coordination-theater coordination-theater = ⊤
query-look-is-coordination-theater (verification-cost _) = ⊥

------------------------------------------------------------------------
-- Verification cost bits — information-up, not coordination theater
------------------------------------------------------------------------

queryLookVerificationBits : EpistemicQueryLook → ℕ
queryLookVerificationBits q with EpistemicQueryLook.class q
... | verification-cost bits = bits
... | coordination-theater = zero

queryLookLandauerCost : EpistemicQueryLook → ℕ
queryLookLandauerCost q = queryLookVerificationBits q

query-look-verification-cost-nonneg :
  ∀ (q : EpistemicQueryLook) → zero ≤ queryLookLandauerCost q
query-look-verification-cost-nonneg q with EpistemicQueryLook.class q
... | verification-cost bits = z≤n
... | coordination-theater = z≤n

query-look-admitted-positive :
  ∀ (bits : ℕ) →
  admit-epistemic-query-look (verification-cost-look (suc bits)) ≡ admitted
query-look-admitted-positive bits = refl

query-look-coordination-theater-refused :
  admit-epistemic-query-look coordination-theater-look ≡ refused
query-look-coordination-theater-refused = refl

query-look-meso-misroute-refused :
  ∀ (bits : ℕ) →
  admit-epistemic-query-look (record
    { class = verification-cost bits
    ; fiber = meso-acting
    }) ≡ refused
query-look-meso-misroute-refused bits = refl

query-look-zero-bits-refused :
  admit-epistemic-query-look (verification-cost-look zero) ≡ refused
query-look-zero-bits-refused = refl

------------------------------------------------------------------------
-- Landauer bound for admitted verification-cost query looks
-- (sole postulate imported — no extra postulate here)
------------------------------------------------------------------------

queryLookLandauerBound :
  ∀ (proc : ErasureProcess) (q : EpistemicQueryLook) (entropyDrop : ℕ) →
  entropyDrop ≤ queryLookLandauerCost q →
  PhysicalSecondLaw proc entropyDrop →
  entropyDrop ≤ ErasureProcess.dissipatedEntropy proc
queryLookLandauerBound proc q ΔS _ hSL = hSL

query-look-which-path-one-bit :
  queryLookVerificationBits (verification-cost-look (suc zero)) ≡ suc zero
query-look-which-path-one-bit = refl

query-look-probe-bits-align :
  ∀ (p : PathProbe) →
  queryLookVerificationBits (verification-cost-look (epistemicMIBits p)) ≡ epistemicMIBits p
query-look-probe-bits-align PathProbe.null = refl
query-look-probe-bits-align PathProbe.whichPath = refl

query-look-not-coordination :
  ¬ query-look-is-coordination-theater (verification-cost (suc zero))
query-look-not-coordination ()

refuse-second-argmin : EpistemicQueryLookRefusal
refuse-second-argmin = second-argmin-refused

refuse-coordination-theater : EpistemicQueryLookRefusal
refuse-coordination-theater = coordination-theater-refused

query-look-production-not-wired : queryLookProductionWired ≡ false
query-look-production-not-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

epistemicQueryLookAxiom :
  (∀ (bits : ℕ) →
    admit-epistemic-query-look (verification-cost-look (suc bits)) ≡ admitted)
  × (admit-epistemic-query-look coordination-theater-look ≡ refused)
  × (queryLookProductionWired ≡ false)
  × (productionWired ≡ false)
  × (landauerProductionWired ≡ false)
  × (∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease →
      entropyDecrease ≤ ErasureProcess.dissipatedEntropy proc)
epistemicQueryLookAxiom =
  query-look-admitted-positive
  , query-look-coordination-theater-refused
  , query-look-production-not-wired
  , refl
  , refl
  , landauerBound

epistemicQueryLookNamed : String
epistemicQueryLookNamed =
  "epistemicQueryLook: §18 query verification cost information-up not coordination theater knowing fiber LandauerBound sole postulate physicalSecondLaw"

epistemicQueryLookCellId : String
epistemicQueryLookCellId = "URGE-FORMAL-Q-AGDA-EPISTEMIC-QUERY-LOOK"

epistemicQueryLookNonClaim : String
epistemicQueryLookNonClaim =
  "URGE-FORMAL-Q-AGDA-EPISTEMIC-QUERY-LOOK §18 query is verification cost information-up not coordination EpistemicQueryLook QueryLookClass verification-cost coordination-theater refused sole postulate physicalSecondLaw zero extra postulate modality Unwired not physics GREEN not production_wired knowing fiber only"

epistemic-query-look-modality-unwired :
  epistemicQueryLookModalityCurrent ≡ epistemic-query-look-unwired
epistemic-query-look-modality-unwired = refl

epistemicQueryLookPhysicsGreenAuthorized : Set
epistemicQueryLookPhysicsGreenAuthorized = ⊥

epistemic-query-look-physics-green-false : ¬ epistemicQueryLookPhysicsGreenAuthorized
epistemic-query-look-physics-green-false ()

epistemicQueryLookKnowingFiberOk : Set
epistemicQueryLookKnowingFiberOk =
  EpistemicQueryLook.fiber (verification-cost-look (suc zero)) ≡ quantum-knowing

epistemic-query-look-knowing-fiber-ok : epistemicQueryLookKnowingFiberOk
epistemic-query-look-knowing-fiber-ok = refl

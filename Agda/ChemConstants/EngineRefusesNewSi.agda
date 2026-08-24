-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.EngineRefusesNewSi.agda
--
-- Knowing-fiber Agda: constitutive engines sort using the existing SI/occupancy/
-- derived-morphism sheaf; they do not mint k, R, or ε₀.
--   * engineMayMintSi false; engineUsesExistingSheaf true
--   * forbiddenSiMints k R epsilon_0 (three named refuses)
--   * engineRefusesNewSiProved false; modality Unwired; physics GREEN false
--   * One design axiom: second law + conservation (not 26th axiom)
--
-- Mirrors sibling `ChemConstants/CartridgeConstitutiveCompose.agda` scaffold +
-- INT `umst-chem/src/x_rows/engine_refuses_new_si.rs`.
-- No meso / acting theorems. WAVE100: remainder deferred composition on same
-- second law, not impossibility; not wired in lib.rs / eos.rs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.EngineRefusesNewSi where

open import Data.Bool using (Bool; false; not; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + engine-refuses-new-SI pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data EngineRefusesNewSiModality : Set where
  engine-refuses-new-si-unwired engine-refuses-new-si-assumed
    engine-refuses-new-si-proved engine-refuses-new-si-surrogate
    : EngineRefusesNewSiModality

engineRefusesNewSiModalityCurrent : EngineRefusesNewSiModality
engineRefusesNewSiModalityCurrent = engine-refuses-new-si-unwired

engineRefusesNewSiProved productionWired engineMayMintSi engineUsesExistingSheaf
  soleAxiomSecondLawConservation : Bool
engineRefusesNewSiProved = false
productionWired = false
engineMayMintSi = false
engineUsesExistingSheaf = true
soleAxiomSecondLawConservation = true

soleAxiomCount : ℕ
soleAxiomCount = 1

sole-axiom-count-one : soleAxiomCount ≡ 1
sole-axiom-count-one = refl

------------------------------------------------------------------------
-- Forbidden SI mint names — engines consult sheaf, never mint k/R/ε₀
------------------------------------------------------------------------

data ForbiddenSiMint : Set where
  forbidden-mint-k forbidden-mint-R forbidden-mint-epsilon-0 : ForbiddenSiMint

forbiddenMintKTag forbiddenMintRTag forbiddenMintEpsilon0Tag : String
forbiddenMintKTag = "k"
forbiddenMintRTag = "R"
forbiddenMintEpsilon0Tag = "epsilon_0"

forbidden-mint-k-named : forbiddenMintKTag ≡ "k"
forbidden-mint-k-named = refl

forbidden-mint-R-named : forbiddenMintRTag ≡ "R"
forbidden-mint-R-named = refl

forbidden-mint-epsilon-0-named : forbiddenMintEpsilon0Tag ≡ "epsilon_0"
forbidden-mint-epsilon-0-named = refl

forbiddenMintCount : ℕ
forbiddenMintCount = 3

forbidden-mint-count-three : forbiddenMintCount ≡ 3
forbidden-mint-count-three = refl

forbidden-mint-k-not-R : forbidden-mint-k ≢ forbidden-mint-R
forbidden-mint-k-not-R ()

forbidden-mint-k-not-epsilon-0 : forbidden-mint-k ≢ forbidden-mint-epsilon-0
forbidden-mint-k-not-epsilon-0 ()

forbidden-mint-R-not-epsilon-0 : forbidden-mint-R ≢ forbidden-mint-epsilon-0
forbidden-mint-R-not-epsilon-0 ()

engine-may-not-mint-si : engineMayMintSi ≡ false
engine-may-not-mint-si = refl

not-engine-may-mint-si : engineMayMintSi ≡ true → ⊥
not-engine-may-mint-si ()

engine-uses-existing-sheaf : engineUsesExistingSheaf ≡ true
engine-uses-existing-sheaf = refl

sheaf-consult-not-mint :
  (engineMayMintSi ≡ false)
  × (forbiddenMintCount ≡ 3)
  × (engineUsesExistingSheaf ≡ true)
sheaf-consult-not-mint = engine-may-not-mint-si , forbidden-mint-count-three , engine-uses-existing-sheaf

row-not-proved : engineRefusesNewSiProved ≡ false
row-not-proved = refl

sole-axiom-second-law : soleAxiomSecondLawConservation ≡ true
sole-axiom-second-law = refl

production-not-wired : productionWired ≡ false
production-not-wired = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

engineRefusesNewSiAxiom :
  (engineRefusesNewSiProved ≡ false)
  × (productionWired ≡ false)
  × (engineMayMintSi ≡ false)
  × (engineUsesExistingSheaf ≡ true)
  × (soleAxiomSecondLawConservation ≡ true)
  × (soleAxiomCount ≡ 1)
  × (forbiddenMintCount ≡ 3)
  × ¬ (engineMayMintSi ≡ true)
  × (forbidden-mint-k ≢ forbidden-mint-R)
  × (forbidden-mint-k ≢ forbidden-mint-epsilon-0)
  × (forbidden-mint-R ≢ forbidden-mint-epsilon-0)
engineRefusesNewSiAxiom =
  row-not-proved
  , production-not-wired
  , engine-may-not-mint-si
  , engine-uses-existing-sheaf
  , sole-axiom-second-law
  , sole-axiom-count-one
  , forbidden-mint-count-three
  , not-engine-may-mint-si
  , forbidden-mint-k-not-R
  , forbidden-mint-k-not-epsilon-0
  , forbidden-mint-R-not-epsilon-0

engineRefusesNewSiNamed : String
engineRefusesNewSiNamed =
  "engineRefusesNewSi: engines sort existing SI sheaf; engineMayMintSi false; forbidden k R epsilon_0"

engineRefusesNewSiCellId : String
engineRefusesNewSiCellId =
  "CHEM-FORMAL-Q-AGDA-ENGINE-REFUSES-NEW-SI-CONSERVATION"

engineRefusesNewSiIntCellId : String
engineRefusesNewSiIntCellId =
  "CHEM-INT-CROSS-ENGINE-REFUSES-NEW-SI-CONSERVATION"

engineRefusesNewSiMarker : String
engineRefusesNewSiMarker = "chem_int_cross_engine_refuses_new_si_v1"

engineRefusesNewSiNonClaim : String
engineRefusesNewSiNonClaim =
  "CHEM-FORMAL-Q-AGDA-ENGINE-REFUSES-NEW-SI-CONSERVATION Unwired — constitutive engines sort using the existing SI occupancy derived-morphism sheaf; they do not mint k R epsilon_0 not a 26th axiom; not physics GREEN; not production_wired WAVE100 remainder deferred composition on same second law not impossibility"

engine-refuses-new-si-modality-unwired :
  engineRefusesNewSiModalityCurrent ≡ engine-refuses-new-si-unwired
engine-refuses-new-si-modality-unwired = refl

engineRefusesNewSiPhysicsGreenAuthorized : Set
engineRefusesNewSiPhysicsGreenAuthorized = ⊥

engine-refuses-new-si-physics-green-false :
  ¬ engineRefusesNewSiPhysicsGreenAuthorized
engine-refuses-new-si-physics-green-false ()

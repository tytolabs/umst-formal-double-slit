-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: ChemConstants.Eco02ConsumeNotFork.agda
--
-- ECO-02 consume-not-fork on the knowing fiber (Q lattice):
--   * chem consumes the liquid_ppo / Burn learner spine — does not fork it
--   * BIND antichain until measured; no second optimizer kernel in chem
--   * chemForksLiquidPpoKernel = false; burnKernelCopiedToChem = false
--
-- Mirrors sibling `ChemConstants/ScaleOccupancyZCommute.agda` +
-- Coq `ChemConstants/Eco02ConsumeNotFork.v` style.
-- No meso / acting theorems. Modality Unwired; physics GREEN false.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ChemConstants.Eco02ConsumeNotFork where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Modality + consume-not-fork pins (knowing fiber — Unwired)
------------------------------------------------------------------------

data Eco02ConsumeNotForkModality : Set where
  eco-02-consume-not-fork-unwired eco-02-consume-not-fork-assumed eco-02-consume-not-fork-proved eco-02-consume-not-fork-surrogate
    : Eco02ConsumeNotForkModality

eco02ConsumeNotForkModalityCurrent : Eco02ConsumeNotForkModality
eco02ConsumeNotForkModalityCurrent = eco-02-consume-not-fork-unwired

chemForksLiquidPpoKernel burnKernelCopiedToChem liquidPpoProductionWired bindAntichainUntilMeasured : Bool
chemForksLiquidPpoKernel = false
burnKernelCopiedToChem = false
liquidPpoProductionWired = false
bindAntichainUntilMeasured = true

oneLearnerSpine : chemForksLiquidPpoKernel ≡ false
oneLearnerSpine = refl

notChemForksLiquidPpo : chemForksLiquidPpoKernel ≡ true → ⊥
notChemForksLiquidPpo ()

burn-not-copied : burnKernelCopiedToChem ≡ false
burn-not-copied = refl

liquid-ppo-not-wired : liquidPpoProductionWired ≡ false
liquid-ppo-not-wired = refl

bind-antichain : bindAntichainUntilMeasured ≡ true
bind-antichain = refl

------------------------------------------------------------------------
-- One design axiom + authority cites (not a second optimizer fork)
------------------------------------------------------------------------

eco02ConsumeNotForkAxiom :
  (chemForksLiquidPpoKernel ≡ false)
  × (burnKernelCopiedToChem ≡ false)
  × (liquidPpoProductionWired ≡ false)
  × (bindAntichainUntilMeasured ≡ true)
  × ¬ (chemForksLiquidPpoKernel ≡ true)
eco02ConsumeNotForkAxiom =
  oneLearnerSpine , burn-not-copied , liquid-ppo-not-wired , bind-antichain , notChemForksLiquidPpo

eco02ConsumeNotForkNamed : String
eco02ConsumeNotForkNamed =
  "eco02ConsumeNotFork: chem consumes liquid_ppo learner spine; chemForksLiquidPpoKernel false"

eco02ConsumeNotForkCellId : String
eco02ConsumeNotForkCellId = "CHEM-FORMAL-Q-AGDA-ECO-02-CONSUME-NOT-FORK"

eco02ConsumeNotForkNonClaim : String
eco02ConsumeNotForkNonClaim =
  "CHEM-FORMAL-Q-AGDA-ECO-02-CONSUME-NOT-FORK ECO-02 consume-not-fork chem does not fork Burn liquid_ppo kernel; one learner spine BIND antichain until measured; chemForksLiquidPpoKernel false burnKernelCopiedToChem false liquidPpoProductionWired false; one design axiom second law conservation not second optimizer axiom; modality Unwired; not physics GREEN; not production_wired"

eco-02-consume-not-fork-modality-unwired :
  eco02ConsumeNotForkModalityCurrent ≡ eco-02-consume-not-fork-unwired
eco-02-consume-not-fork-modality-unwired = refl

eco02ConsumeNotForkPhysicsGreenAuthorized : Set
eco02ConsumeNotForkPhysicsGreenAuthorized = ⊥

eco-02-consume-not-fork-physics-green-false : ¬ eco02ConsumeNotForkPhysicsGreenAuthorized
eco-02-consume-not-fork-physics-green-false ()

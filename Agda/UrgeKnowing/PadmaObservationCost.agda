-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UrgeKnowing.PadmaObservationCost — knowing-fiber observation-cost pin.
-- Zero extra postulate. physics_green false. Modality Unwired.
-- Cell: PADMA-FORMAL-KNOW-AGDA-OBS-COST
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module UrgeKnowing.PadmaObservationCost where

open import Data.Bool using (Bool; false; true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

data ObsCostModality : Set where
  obs-cost-unwired obs-cost-assumed obs-cost-proved obs-cost-surrogate : ObsCostModality

obsCostModalityCurrent : ObsCostModality
obsCostModalityCurrent = obs-cost-unwired

physicsGreenFormal : Bool
physicsGreenFormal = false

productionWiredFormal : Bool
productionWiredFormal = false

observationCostProvedFormal : Bool
observationCostProvedFormal = false

physicsGreenStaysFalse : physicsGreenFormal ≡ false
physicsGreenStaysFalse = refl

productionWiredStaysFalse : productionWiredFormal ≡ false
productionWiredStaysFalse = refl

observationCostNotProved : observationCostProvedFormal ≡ false
observationCostNotProved = refl

modalityUnwired : obsCostModalityCurrent ≡ obs-cost-unwired
modalityUnwired = refl

fourArmRunFormal : Bool
fourArmRunFormal = false

fourArmRunStaysFalse : fourArmRunFormal ≡ false
fourArmRunStaysFalse = refl

inventPhysicsGreenRefused : ¬ (physicsGreenFormal ≡ true)
inventPhysicsGreenRefused ()

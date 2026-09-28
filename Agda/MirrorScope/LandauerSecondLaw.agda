-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
{-# OPTIONS --without-K --safe #-}

-- P0-13b: Landauer second law as record field (no postulate).

module MirrorScope.LandauerSecondLaw where

open import Data.Nat using (ℕ; _≤_)

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

record LandauerPhysics : Set where
  field
    physicalSecondLaw :
      ∀ (proc : ErasureProcess) (entropyDecrease : ℕ) →
      PhysicalSecondLaw proc entropyDecrease

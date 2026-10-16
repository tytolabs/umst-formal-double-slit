-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
------------------------------------------------------------------------
-- UMST-Formal-Double-Slit: Learning/EvidenceCost.agda
--
-- Twin of Lean/Learning/EvidenceCost.lean and Coq/Learning/EvidenceCost.v. The logarithm is the PathLog carriage of
-- KnowingFibreLaw.agda; energies are k_B T times nats, and bounds with a division are stated with cleared
-- denominators. A record of b evidence bits holds b · ln 2 nats; its reset under the erase case costs at least
-- b · k_B T ln 2 (evidenceBits-cost-ge), which is the bound of at most 1 / (k_B T ln 2) bits per joule
-- (evidenceBitsPerJoule-le); on the path qubit the reset pays for the path entropy at the same rate and at least the
-- Englert bound k_B T V² / 2 (pathEvidence-cost-ge-both).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Learning.EvidenceCost where

open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _*_; _≤_; nonNegative)
open import Data.Rational.Properties using (≤-trans; ≤-reflexive; *-monoˡ-≤-nonNeg; *-assoc; *-comm; *-identityˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)

open import DensityStateSpec
open import ComplementaritySpec
open import KnowingFibreLaw

open ErasureProcess

-- The erase case on a record of `bits` evidence bits: the bits · ln 2 nats it holds.
bitsEraseCase : PathLog → ErasureProcess → ℚ → Set
bitsEraseCase L e bits = eraseCase e (bits * PathLog.ln L two)

private
  rearrange : ∀ bits kT l → bits * (kT * l) ≡ kT * (bits * l)
  rearrange bits kT l =
    trans (sym (*-assoc bits kT l)) (trans (cong (_* l) (*-comm bits kT)) (*-assoc kT bits l))

-- Each evidence bit costs at least k_B T ln 2.
evidenceBits-cost-ge : ∀ L e kT bits → 0ℚ ≤ kT → bitsEraseCase L e bits →
  bits * landauerBitEnergy L kT ≤ kT * dissipatedEntropy e
evidenceBits-cost-ge L e kT bits hk h =
  ≤-trans (≤-reflexive (rearrange bits kT (PathLog.ln L two))) (*-monoˡ-≤-nonNeg kT {{nonNegative hk}} h)

-- Evidence per joule is bounded: bits / E ≤ 1 / L, cleared of its positive denominators E and L.
evidenceBitsPerJoule-le : ∀ L e kT bits → 0ℚ ≤ kT → bitsEraseCase L e bits →
  bits * landauerBitEnergy L kT ≤ 1ℚ * (kT * dissipatedEntropy e)
evidenceBitsPerJoule-le L e kT bits hk h =
  ≤-trans (evidenceBits-cost-ge L e kT bits hk h) (≤-reflexive (sym (*-identityˡ (kT * dissipatedEntropy e))))

-- On the path qubit, Landauer and Englert together: the reset pays the diagonal Landauer cost of the path entropy
-- and at least k_B T V² / 2.
pathEvidence-cost-ge-both : ∀ L e ρ kT → 0ℚ ≤ kT → eraseCase e (entropyDrop L ρ) →
  landauerCostDiagonal L kT ρ ≤ kT * dissipatedEntropy e × ½ * (kT * visibility² ρ) ≤ kT * dissipatedEntropy e
pathEvidence-cost-ge-both L e ρ kT hk h =
  erase-pathRecord-cost-ge-bits L e ρ kT hk h , erase-pathRecord-cost-ge-visibility-sq L e ρ kT hk h

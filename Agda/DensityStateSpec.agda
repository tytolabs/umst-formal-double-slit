-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal-Double-Slit: DensityStateSpec.agda
--
-- A qubit density matrix by its diagonal (the Born weights) and the magnitude of its coherence, carrying the
-- constraints of a density matrix: nonnegative weights summing to one, and |ρ₀₁|² ≤ ρ₀₀ ρ₁₁ (positive
-- semidefiniteness). Twin of Coq/DensityStateSpec.v; over ℚ, as the standard library has no reals.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module DensityStateSpec where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record DensityMatrix2 : Set where
  constructor mkDensityMatrix2
  field
    p₀                : ℚ
    p₁                : ℚ
    c₀₁               : ℚ
    p₀-nonneg         : 0ℚ ≤ p₀
    p₁-nonneg         : 0ℚ ≤ p₁
    trace-one         : p₀ + p₁ ≡ 1ℚ
    coherence-nonneg  : 0ℚ ≤ c₀₁
    coherence-bounded : c₀₁ * c₀₁ ≤ p₀ * p₁

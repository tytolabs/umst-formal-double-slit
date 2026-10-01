-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal-Double-Slit: ComplementaritySpec.agda
--
-- Englert's complementarity V² + D² ≤ 1 for every qubit density matrix: with V = 2|ρ₀₁| and D = |ρ₀₀ − ρ₁₁|,
-- V² + D² = 4|ρ₀₁|² + (ρ₀₀ − ρ₁₁)² ≤ 4ρ₀₀ρ₁₁ + (ρ₀₀ − ρ₁₁)² = (ρ₀₀ + ρ₁₁)² = 1.
-- Twin of Coq/ComplementaritySpec.v and Lean QuantumClassicalBridge.complementarity_fringe_path.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module ComplementaritySpec where

open import Data.Rational using (ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
open import Data.Rational.Properties using (*-monoˡ-≤-nonNeg; +-monoˡ-≤; ≤-trans; ≤-reflexive)
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import DensityStateSpec

open DensityMatrix2

four : ℚ
four = (1ℚ + 1ℚ) * (1ℚ + 1ℚ)

-- V² = 4|ρ₀₁|² and D² = (ρ₀₀ − ρ₁₁)².
visibility² distinguishability² : DensityMatrix2 → ℚ
visibility² ρ = four * (c₀₁ ρ * c₀₁ ρ)
distinguishability² ρ = (p₀ ρ - p₁ ρ) * (p₀ ρ - p₁ ρ)

open +-*-Solver

square-identity : ∀ a b → four * (a * b) + (a - b) * (a - b) ≡ (a + b) * (a + b)
square-identity = solve 2 (λ a b → ((con 1ℚ :+ con 1ℚ) :* (con 1ℚ :+ con 1ℚ)) :* (a :* b) :+ (a :- b) :* (a :- b)
                                   := (a :+ b) :* (a :+ b)) refl

englert : ∀ ρ → visibility² ρ + distinguishability² ρ ≤ 1ℚ
englert ρ = ≤-trans (+-monoˡ-≤ (distinguishability² ρ) (*-monoˡ-≤-nonNeg four (coherence-bounded ρ)))
  (≤-reflexive (trans (square-identity (p₀ ρ) (p₁ ρ))
                      (trans (cong (λ s → s * s) (trace-one ρ)) refl)))

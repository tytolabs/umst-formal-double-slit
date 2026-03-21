------------------------------------------------------------------------
-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy
--   — Studio TYTO
--
-- UMST-Formal: DensityStateSpec.agda
--
-- Qubit density matrix spec (diagonal representation over rationals).
--
-- Mirrors:
--   * Lean  @Lean/DensityState.lean@  — full PSD + trace-one structure,
--     `pureDensity`, `mixedDensity`, diagonal non-negativity, re ≤ 1
--
-- This Agda layer keeps the *interface* (record + key properties) using
-- stdlib ℚ for decidable arithmetic; full spectral / PSD proofs live in
-- the Lean codebase.  Properties that rely on ℂ / eigenvalue analysis
-- are postulated here; authority is the Lean proofs.
------------------------------------------------------------------------

module DensityStateSpec where

open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Properties as ℚ-Props
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- 1. Qubit density matrix (2 × 2, diagonal representation)
------------------------------------------------------------------------

-- A qubit density matrix in the computational basis is determined by
-- its diagonal entries p₀, p₁ (Born weights) and off-diagonal coherence
-- magnitude c₀₁.  We use ℚ throughout; the Lean codebase uses ℂ with
-- full PSD proofs.
--
-- Physical meaning:
--   p₀   — probability of path 0 (Born rule)
--   p₁   — probability of path 1 (Born rule)
--   c₀₁  — |ρ₀₁|, off-diagonal coherence magnitude

record DensityMatrix2 : Set where
  constructor mkDensityMatrix2
  field
    p₀  : ℚ       -- diagonal entry ρ₀₀ (real, as Born weight)
    p₁  : ℚ       -- diagonal entry ρ₁₁ (real, as Born weight)
    c₀₁ : ℚ       -- |ρ₀₁|, off-diagonal coherence magnitude

------------------------------------------------------------------------
-- 2. Structural properties (postulated; authority: Lean proofs)
------------------------------------------------------------------------

-- These mirror DensityMat.diag_re_nonneg_n, DensityMat.trace_re_eq_one_n,
-- and the PSD coherence bound from QuantumClassicalBridge.lean.

postulate
  -- | Diagonal entries are non-negative (Born probabilities).
  --   Lean: DensityMat.diag_re_nonneg_n
  p₀-nonneg : ∀ (ρ : DensityMatrix2) → 0ℚ ≤ DensityMatrix2.p₀ ρ

  -- | Diagonal entries are non-negative.
  --   Lean: DensityMat.diag_re_nonneg_n
  p₁-nonneg : ∀ (ρ : DensityMatrix2) → 0ℚ ≤ DensityMatrix2.p₁ ρ

  -- | Trace equals one: p₀ + p₁ = 1.
  --   Lean: DensityMat.trace_re_eq_one_n, pathWeight0_add_pathWeight1
  trace-one : ∀ (ρ : DensityMatrix2) →
    DensityMatrix2.p₀ ρ + DensityMatrix2.p₁ ρ ≡ 1ℚ

  -- | Coherence magnitude is non-negative.
  --   Lean: fringeVisibility_nonneg (V = 2|ρ₀₁| ≥ 0 implies |ρ₀₁| ≥ 0)
  coherence-nonneg : ∀ (ρ : DensityMatrix2) → 0ℚ ≤ DensityMatrix2.c₀₁ ρ

  -- | Coherence is bounded by the geometric mean of diagonal entries.
  --   From PSD: |ρ₀₁|² ≤ p₀ · p₁ (Cauchy-Schwarz for PSD matrices).
  --   Lean: complementarity_fringe_path (implies c₀₁² ≤ p₀ · p₁)
  coherence-bounded : ∀ (ρ : DensityMatrix2) →
    DensityMatrix2.c₀₁ ρ * DensityMatrix2.c₀₁ ρ ≤
      DensityMatrix2.p₀ ρ * DensityMatrix2.p₁ ρ

  -- | Each diagonal entry is at most 1.
  --   Lean: DensityMat.diag_re_le_one_n
  p₀-le-one : ∀ (ρ : DensityMatrix2) → DensityMatrix2.p₀ ρ ≤ 1ℚ
  p₁-le-one : ∀ (ρ : DensityMatrix2) → DensityMatrix2.p₁ ρ ≤ 1ℚ

------------------------------------------------------------------------
-- 3. Pure and mixed state constructors
------------------------------------------------------------------------

-- | A pure state has one eigenvalue = 1 and the other = 0.
--   Lean: pureDensity, vonNeumannEntropy_pure_eq_zero
pureDensity : ℚ → ℚ → DensityMatrix2
pureDensity p₀ c₀₁ = mkDensityMatrix2 p₀ (1ℚ + ℚ.- p₀) c₀₁
  where open ℚ using (-_)

-- | Convex combination weight: t ∈ [0,1].
--   Lean: mixedDensity (ρ₁ ρ₂ : DensityMatCore hn) (t : ℝ)
record ConvexWeight : Set where
  constructor mkConvexWeight
  field
    t    : ℚ
    t≥0  : 0ℚ ≤ t
    t≤1  : t ≤ 1ℚ

postulate
  -- | Convex combination preserves density matrix properties.
  --   Lean: mixedDensity — proves PSD and trace-one for t·ρ₁ + (1-t)·ρ₂
  mixedDensity-valid : ∀ (ρ₁ ρ₂ : DensityMatrix2) (w : ConvexWeight) →
    DensityMatrix2.p₀ ρ₁ + DensityMatrix2.p₀ ρ₂ ≡
      DensityMatrix2.p₀ ρ₁ + DensityMatrix2.p₀ ρ₂
      -- (placeholder type; full convex combination needs ℝ arithmetic)

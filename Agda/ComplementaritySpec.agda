-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

------------------------------------------------------------------------
-- UMST-Formal: ComplementaritySpec.agda
--
-- Englert complementarity relation for qubit density matrices.
--
-- Mirrors:
--   * Lean  @Lean/Complementarity.lean@        — discoverability shim
--   * Lean  @Lean/QuantumClassicalBridge.lean@  — full proof of V² + I² ≤ 1
--   * Lean  @Lean/DoubleSlitCore.lean@          — Complementary record
--
-- The Englert duality inequality states that for any qubit density
-- matrix ρ, the fringe visibility V and which-path distinguishability
-- I satisfy:
--
--   V² + I² ≤ 1
--
-- where:
--   V = 2|ρ₀₁|              (off-diagonal coherence)
--   I = |p₀ - p₁|           (which-path information)
--
-- This Agda module postulates the key properties; authority is the
-- Lean proof `complementarity_fringe_path` in QuantumClassicalBridge.lean.
------------------------------------------------------------------------

module ComplementaritySpec where

open import DensityStateSpec
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- 1. Visibility and distinguishability (definitions over ℚ)
------------------------------------------------------------------------

-- | Fringe visibility: V = 2 · |ρ₀₁|.
--   Lean: fringeVisibility ρ = 2 * Complex.abs (ρ.carrier 0 1)
--   We approximate with 2 · c₀₁ where c₀₁ = |ρ₀₁| from DensityMatrix2.
fringeVisibility : DensityMatrix2 → ℚ
fringeVisibility ρ = (1ℚ + 1ℚ) * DensityMatrix2.c₀₁ ρ

-- | Which-path distinguishability: I = |p₀ - p₁|.
--   Lean: whichPathDistinguishability ρ = |pathWeight ρ 0 - pathWeight ρ 1|
--   Since we lack absolute value on ℚ in a convenient form, we store
--   the squared quantity I² = (p₀ - p₁)² directly.
distinguishability² : DensityMatrix2 → ℚ
distinguishability² ρ = let d = DensityMatrix2.p₀ ρ - DensityMatrix2.p₁ ρ
                         in d * d

-- | Visibility squared: V² = 4 · c₀₁².
visibility² : DensityMatrix2 → ℚ
visibility² ρ = let c = DensityMatrix2.c₀₁ ρ
                    two = 1ℚ + 1ℚ
                    four = two * two
                in four * (c * c)

------------------------------------------------------------------------
-- 2. Complementarity record (mirrors DoubleSlitCore.Complementary)
------------------------------------------------------------------------

-- | A pair (I, V) is complementary if V² + I² ≤ 1.
--   Lean: structure Complementary (obs : ObservationState) where
--           hComp : obs.V ^ 2 + obs.I ^ 2 ≤ 1
record Complementary : Set where
  constructor mkComplementary
  field
    I  : ℚ       -- which-path distinguishability
    V  : ℚ       -- fringe visibility
    I∈ : 0ℚ ≤ I  -- I ∈ [0, 1]
    V∈ : 0ℚ ≤ V  -- V ∈ [0, 1]
    hComp : V * V + I * I ≤ 1ℚ   -- Englert: V² + I² ≤ 1

------------------------------------------------------------------------
-- 3. Englert complementarity (postulated; authority: Lean proofs)
------------------------------------------------------------------------

postulate
  -- | The Englert inequality: V² + I² ≤ 1 for any qubit density matrix.
  --   Lean: complementarity_fringe_path (ρ : DensityMatrix hnQubit) :
  --         fringeVisibility ρ ^ 2 + whichPathDistinguishability ρ ^ 2 ≤ 1
  englert-complementarity : ∀ (ρ : DensityMatrix2) →
    visibility² ρ + distinguishability² ρ ≤ 1ℚ

  -- | Fringe visibility is non-negative.
  --   Lean: fringeVisibility_nonneg
  fringeVisibility-nonneg : ∀ (ρ : DensityMatrix2) →
    0ℚ ≤ fringeVisibility ρ

  -- | Fringe visibility is at most 1.
  --   Lean: fringeVisibility_le_one
  fringeVisibility-le-one : ∀ (ρ : DensityMatrix2) →
    fringeVisibility ρ ≤ 1ℚ

  -- | Which-path distinguishability is non-negative (as squared quantity).
  --   Lean: whichPathDistinguishability_nonneg
  distinguishability²-nonneg : ∀ (ρ : DensityMatrix2) →
    0ℚ ≤ distinguishability² ρ

  -- | Measurement destroys coherence: V drops to 0 after which-path
  --   measurement.
  --   Lean: fringeVisibility_whichPath_apply
  fringeVisibility-after-measurement-zero : ∀ (ρ : DensityMatrix2) →
    -- After dephasing, c₀₁ = 0 so V = 0.
    -- Type witnesses the qualitative property; exact channel
    -- formalization lives in Lean (KrausChannel.whichPathChannel).
    fringeVisibility (mkDensityMatrix2
      (DensityMatrix2.p₀ ρ) (DensityMatrix2.p₁ ρ) 0ℚ) ≡ 0ℚ

  -- | Distinguishability is invariant under which-path measurement.
  --   Lean: whichPathDistinguishability_whichPath_apply
  distinguishability²-measurement-invariant : ∀ (ρ : DensityMatrix2) →
    distinguishability² (mkDensityMatrix2
      (DensityMatrix2.p₀ ρ) (DensityMatrix2.p₁ ρ) 0ℚ) ≡
    distinguishability² ρ

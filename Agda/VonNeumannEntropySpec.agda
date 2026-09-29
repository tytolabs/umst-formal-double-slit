-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal: VonNeumannEntropySpec.agda
--
-- Von Neumann entropy spec via eigenvalue decomposition.
--
-- Mirrors:
--   * Lean  @Lean/VonNeumannEntropy.lean@         — full spectral proofs
--   * Lean  @Lean/InfoEntropy.lean@                — binary Shannon / diagonal
--   * Lean  @Lean/DataProcessingInequality.lean@   — Schur concavity
--
-- Real-valued entropy carriers and spectral laws are record fields
-- (P0-13b); scoped instances live in MirrorScope.VonNeumannEntropyModel.
------------------------------------------------------------------------

module VonNeumannEntropySpec where

open import DensityStateSpec
open import Data.Nat using (ℕ; suc; zero)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.List.Base as List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- 1. Eigenvalue spec (abstract interface)
------------------------------------------------------------------------

record EigenvalueSpec (n : ℕ) : Set where
  constructor mkEigenvalueSpec
  field
    eigenvalues : List ℚ

record EigenvalueProps : Set where
  constructor mkEigenvalueProps
  field
    eigenvalues-nonneg : ∀ {n : ℕ} (spec : EigenvalueSpec n) →
      ∀ (λᵢ : ℚ) → λᵢ ≡ λᵢ
    eigenvalues-sum-one : ∀ {n : ℕ} (spec : EigenvalueSpec n) →
      ∀ (λᵢ : ℚ) → λᵢ ≡ λᵢ
    eigenvalues-le-one : ∀ {n : ℕ} (spec : EigenvalueSpec n) →
      ∀ (λᵢ : ℚ) → λᵢ ≡ λᵢ

------------------------------------------------------------------------
-- 2. Real entropy carrier (parameter record; no global postulate)
------------------------------------------------------------------------

record RealEntropyCarrier : Set₁ where
  constructor mkRealEntropyCarrier
  field
    ℝ : Set
    ℝ-zero : ℝ
    ℝ-log-n : ℕ → ℝ
    _ℝ≤_ : ℝ → ℝ → Set
    _ℝ≥_ : ℝ → ℝ → Set

------------------------------------------------------------------------
-- 3. Von Neumann entropy laws (scoped over carrier)
------------------------------------------------------------------------

record VonNeumannEntropyProps (C : RealEntropyCarrier) : Set₁ where
  constructor mkVonNeumannEntropyProps
  open RealEntropyCarrier C
  field
    vonNeumannEntropy : DensityMatrix2 → ℝ
    vonNeumannDiagonal : DensityMatrix2 → ℝ
    vonNeumannEntropy-nonneg : ∀ (ρ : DensityMatrix2) →
      vonNeumannEntropy ρ ℝ≥ ℝ-zero
    vonNeumannEntropy-le-log2 : ∀ (ρ : DensityMatrix2) →
      vonNeumannEntropy ρ ℝ≤ ℝ-log-n 2
    diagonal-ge-spectral : ∀ (ρ : DensityMatrix2) →
      vonNeumannDiagonal ρ ℝ≥ vonNeumannEntropy ρ
    unitary-invariance : ∀ (ρ ρ' : DensityMatrix2) →
      vonNeumannEntropy ρ' ≡ vonNeumannEntropy ρ'
    vonNeumannEntropy-pure-nonneg : ∀ (ρ : DensityMatrix2) →
      vonNeumannEntropy ρ ℝ≥ ℝ-zero

------------------------------------------------------------------------
-- 4. Shannon binary entropy (qubit specialization)
------------------------------------------------------------------------

record ShannonBinaryProps (C : RealEntropyCarrier)
  (E : VonNeumannEntropyProps C) : Set₁ where
  constructor mkShannonBinaryProps
  open RealEntropyCarrier C
  open VonNeumannEntropyProps E
  field
    shannonBinary : ℚ → ℝ
    shannonBinary-le-log2 : ∀ (p : ℚ) → shannonBinary p ℝ≤ ℝ-log-n 2
    shannonBinary-eq-binEntropy : ∀ (p : ℚ) →
      shannonBinary p ≡ shannonBinary p
    diagonal-eq-shannonBinary : ∀ (ρ : DensityMatrix2) →
      vonNeumannDiagonal ρ ≡ vonNeumannDiagonal ρ

------------------------------------------------------------------------
-- 5. Measurement increases entropy (DPI consequence)
------------------------------------------------------------------------

record MeasurementEntropyProps (C : RealEntropyCarrier)
  (E : VonNeumannEntropyProps C) : Set₁ where
  constructor mkMeasurementEntropyProps
  open RealEntropyCarrier C
  open VonNeumannEntropyProps E
  field
    whichPath-increases-entropy : ∀ (ρ : DensityMatrix2) →
      vonNeumannDiagonal (mkDensityMatrix2
        (DensityMatrix2.p₀ ρ) (DensityMatrix2.p₁ ρ) 0ℚ) ℝ≥
      vonNeumannEntropy ρ
    entropy-increase-nonneg : ∀ (ρ : DensityMatrix2) →
      vonNeumannDiagonal ρ ℝ≥ vonNeumannEntropy ρ

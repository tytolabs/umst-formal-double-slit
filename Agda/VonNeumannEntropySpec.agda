-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

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
-- The von Neumann entropy of a density matrix ρ is:
--
--   S(ρ) = -Tr(ρ log ρ) = ∑ᵢ negMulLog(λᵢ)
--
-- where λᵢ are the eigenvalues of ρ.  Since ρ is PSD with trace 1,
-- all λᵢ ∈ [0, 1] and ∑ λᵢ = 1.
--
-- Key results (all proved in Lean, postulated here):
--   vonNeumannEntropy-nonneg    : S(ρ) ≥ 0
--   vonNeumannEntropy-le-log-n  : S(ρ) ≤ log n
--   diagonal-ge-spectral        : diagonal entropy ≥ spectral entropy
--   unitary-invariance           : S(UρU†) = S(ρ)
--   pure-state-zero              : S(|ψ⟩⟨ψ|) ≥ 0  (= 0 for rank-1)
--
-- This Agda layer uses ℚ for the diagonal (Born weight) representation
-- and postulates real-valued entropy properties.  The full negMulLog /
-- eigenvalue analysis is in the Lean codebase.
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

-- | Eigenvalue list for an n-dimensional density matrix.
--   Each λᵢ ∈ [0,1] and ∑ λᵢ = 1.
--   Lean: IsHermitian.eigenvalues, density_eigenvalues_nonneg,
--         density_eigenvalues_le_one, density_eigenvalues_sum_eq_one_real
record EigenvalueSpec (n : ℕ) : Set where
  constructor mkEigenvalueSpec
  field
    eigenvalues : List ℚ    -- length n list of eigenvalues (ℚ proxy)

postulate
  -- | Eigenvalues are non-negative.
  --   Lean: density_eigenvalues_nonneg
  eigenvalues-nonneg : ∀ {n : ℕ} (spec : EigenvalueSpec n) →
    ∀ (λᵢ : ℚ) → λᵢ ≡ λᵢ  -- placeholder type; full proof uses List membership

  -- | Eigenvalues sum to 1.
  --   Lean: density_eigenvalues_sum_eq_one_real
  eigenvalues-sum-one : ∀ {n : ℕ} (spec : EigenvalueSpec n) →
    ∀ (λᵢ : ℚ) → λᵢ ≡ λᵢ  -- placeholder; real proof uses ∑ eigenvalues = 1

  -- | Each eigenvalue is at most 1.
  --   Lean: density_eigenvalues_le_one
  eigenvalues-le-one : ∀ {n : ℕ} (spec : EigenvalueSpec n) →
    ∀ (λᵢ : ℚ) → λᵢ ≡ λᵢ  -- placeholder

------------------------------------------------------------------------
-- 2. Von Neumann entropy (postulated real-valued properties)
------------------------------------------------------------------------

-- We postulate a real-valued entropy function.  The ℚ-representable
-- fragment uses negMulLog which requires ℝ (log); full definitions
-- live in Lean via Mathlib's Real.negMulLog.

-- | Abstract entropy value carrier (postulated real number).
--   Agda stdlib lacks a convenient ℝ; we use a postulated type.
postulate
  ℝ : Set
  ℝ-zero : ℝ
  ℝ-log-n : ℕ → ℝ     -- log(n) in nats
  _ℝ≤_ : ℝ → ℝ → Set
  _ℝ≥_ : ℝ → ℝ → Set

------------------------------------------------------------------------
-- 3. Von Neumann entropy: key theorems (postulated)
------------------------------------------------------------------------

postulate
  -- | Von Neumann entropy function.
  --   Lean: vonNeumannEntropy (ρ : DensityMatrix hn) : ℝ :=
  --         ∑ i, negMulLog (ρ.isHermitian.eigenvalues i)
  vonNeumannEntropy : DensityMatrix2 → ℝ

  -- | Diagonal (Born-weight Shannon) entropy.
  --   Lean: vonNeumannDiagonal / shannonBinary
  vonNeumannDiagonal : DensityMatrix2 → ℝ

  -- | S(ρ) ≥ 0.  Each λᵢ ∈ [0,1] and negMulLog is non-negative on [0,1].
  --   Lean: vonNeumannEntropy_nonneg
  vonNeumannEntropy-nonneg : ∀ (ρ : DensityMatrix2) →
    vonNeumannEntropy ρ ℝ≥ ℝ-zero

  -- | S(ρ) ≤ log 2 (qubit bound; general: S(ρ) ≤ log n).
  --   Lean: vonNeumannEntropy_le_log_n
  --   For qubits (n = 2): S(ρ) ≤ log 2 ≈ 0.693 nats.
  vonNeumannEntropy-le-log2 : ∀ (ρ : DensityMatrix2) →
    vonNeumannEntropy ρ ℝ≤ ℝ-log-n 2

  -- | Diagonal entropy ≥ spectral entropy (Schur concavity).
  --   The Born-weight (diagonal) Shannon entropy of a qubit density
  --   matrix is at least its von Neumann (spectral) entropy:
  --
  --     vonNeumannDiagonal ρ ≥ vonNeumannEntropy ρ
  --
  --   Equivalently: measurement cannot decrease entropy.
  --   Lean: vonNeumannDiagonal_ge_vonNeumannEntropy
  diagonal-ge-spectral : ∀ (ρ : DensityMatrix2) →
    vonNeumannDiagonal ρ ℝ≥ vonNeumannEntropy ρ

  -- | Unitary invariance: S(UρU†) = S(ρ).
  --   The von Neumann entropy depends only on the spectrum, which is
  --   preserved under unitary conjugation.
  --   Lean: vonNeumannEntropy_unitarily_invariant
  unitary-invariance : ∀ (ρ ρ' : DensityMatrix2) →
    -- ρ' = UρU† for some unitary U (stated abstractly)
    vonNeumannEntropy ρ' ≡ vonNeumannEntropy ρ'
    -- placeholder: full statement needs unitary group representation

  -- | Pure state entropy is zero.
  --   A pure state |ψ⟩⟨ψ| has eigenvalues (1, 0), so
  --   negMulLog(1) + negMulLog(0) = 0.
  --   Lean: vonNeumannEntropy_pure_eq_zero (proves ≥ 0; = 0 for rank-1)
  vonNeumannEntropy-pure-nonneg : ∀ (ρ : DensityMatrix2) →
    vonNeumannEntropy ρ ℝ≥ ℝ-zero

------------------------------------------------------------------------
-- 4. Shannon binary entropy (qubit specialization)
------------------------------------------------------------------------

-- | Binary Shannon entropy H₂(p) = -p log p - (1-p) log(1-p).
--   Lean: shannonBinary p = negMulLog p + negMulLog (1 - p)
postulate
  shannonBinary : ℚ → ℝ

  -- | H₂(p) ≤ log 2.
  --   Lean: shannonBinary_le_log_two
  shannonBinary-le-log2 : ∀ (p : ℚ) → shannonBinary p ℝ≤ ℝ-log-n 2

  -- | H₂(p) = binEntropy(p) (Mathlib agreement).
  --   Lean: shannonBinary_eq_binEntropy
  shannonBinary-eq-binEntropy : ∀ (p : ℚ) →
    shannonBinary p ≡ shannonBinary p  -- identity placeholder

  -- | Qubit diagonal entropy equals shannonBinary of p₀.
  --   Lean: vonNeumannDiagonal = shannonBinary (pathWeight ρ 0)
  diagonal-eq-shannonBinary : ∀ (ρ : DensityMatrix2) →
    vonNeumannDiagonal ρ ≡ vonNeumannDiagonal ρ  -- identity placeholder

------------------------------------------------------------------------
-- 5. Measurement increases entropy (DPI consequence)
------------------------------------------------------------------------

postulate
  -- | Which-path measurement increases entropy:
  --   S(dephased ρ) ≥ S(ρ).
  --   Lean: whichPath_increases_entropy
  whichPath-increases-entropy : ∀ (ρ : DensityMatrix2) →
    vonNeumannDiagonal (mkDensityMatrix2
      (DensityMatrix2.p₀ ρ) (DensityMatrix2.p₁ ρ) 0ℚ) ℝ≥
    vonNeumannEntropy ρ

  -- | Entropy increase from measurement is non-negative:
  --   vonNeumannDiagonal ρ - vonNeumannEntropy ρ ≥ 0.
  --   Lean: entropy_increase_from_measurement_nonneg
  entropy-increase-nonneg : ∀ (ρ : DensityMatrix2) →
    vonNeumannDiagonal ρ ℝ≥ vonNeumannEntropy ρ

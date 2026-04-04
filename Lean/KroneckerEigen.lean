/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Complex.Order
import TensorPartialTrace
import VonNeumannEntropy

/-!
# KroneckerEigen — spectrum of `ρ_A ⊗ ρ_B` and tensor von Neumann entropy

`ρ_A ⊗ ρ_B` is unitarily similar to the diagonal matrix of pairwise products `λ_i μ_j` of factor
eigenvalues, hence `S(ρ_A ⊗ ρ_B) = S(ρ_A) + S(ρ_B)` via `negMulLog_mul` on the flattened product
indexing.
-/

namespace UMST.Quantum

open Matrix Complex Real
open scoped Kronecker BigOperators ComplexOrder

variable {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)

private noncomputable abbrev ΛA (ρA : DensityMatrix ha) : Matrix (Fin na) (Fin na) ℂ :=
  diagonal (RCLike.ofReal ∘ ρA.isHermitian.eigenvalues)

private noncomputable abbrev ΛB (ρB : DensityMatrix hb) : Matrix (Fin nb) (Fin nb) ℂ :=
  diagonal (RCLike.ofReal ∘ ρB.isHermitian.eigenvalues)

theorem mul_kronecker_mul' (A₁ A₂ : Matrix (Fin na) (Fin na) ℂ) (B₁ B₂ : Matrix (Fin nb) (Fin nb) ℂ) :
    (A₁ * A₂) ⊗ₖ (B₁ * B₂) = A₁ ⊗ₖ B₁ * A₂ ⊗ₖ B₂ :=
  Matrix.mul_kronecker_mul (fintype := inferInstance) (fintype := inferInstance) A₁ A₂ B₁ B₂

/-- Kronecker product of unitary matrices (on `Fin na × Fin nb`) is unitary. -/
theorem unitary_kronecker_prod (U : Matrix.unitaryGroup (Fin na) ℂ)
    (V : Matrix.unitaryGroup (Fin nb) ℂ) :
    (U.val ⊗ₖ V.val) ∈ Matrix.unitaryGroup (Fin na × Fin nb) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [TensorPartialTrace.conjTranspose_kronecker (na := na) (nb := nb), mul_kronecker_mul']
  have hU := Matrix.mem_unitaryGroup_iff.mp U.2
  have hV := Matrix.mem_unitaryGroup_iff.mp V.2
  simp [hU, hV, Matrix.one_kronecker_one]

theorem carrier_kronecker_spectral (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    ρA.carrier ⊗ₖ ρB.carrier =
      (ρA.isHermitian.eigenvectorUnitary : Matrix (Fin na) (Fin na) ℂ) * ΛA ρA *
          star (ρA.isHermitian.eigenvectorUnitary : Matrix (Fin na) (Fin na) ℂ) ⊗ₖ
        (ρB.isHermitian.eigenvectorUnitary : Matrix (Fin nb) (Fin nb) ℂ) * ΛB ρB *
          star (ρB.isHermitian.eigenvectorUnitary : Matrix (Fin nb) (Fin nb) ℂ) := by
  conv_lhs =>
    rw [ρA.isHermitian.spectral_theorem, ρB.isHermitian.spectral_theorem]
  simp_rw [mul_kronecker_mul']

theorem charpoly_kronecker_carrier (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (ρA.carrier ⊗ₖ ρB.carrier).charpoly = (ΛA ρA ⊗ₖ ΛB ρB).charpoly := by
  let UA := (ρA.isHermitian.eigenvectorUnitary : Matrix.unitaryGroup (Fin na) ℂ)
  let UB := (ρB.isHermitian.eigenvectorUnitary : Matrix.unitaryGroup (Fin nb) ℂ)
  let W : Matrix.unitaryGroup (Fin na × Fin nb) ℂ :=
    ⟨(UA.val ⊗ₖ UB.val), unitary_kronecker_prod UA UB⟩
  have hspl : ρA.carrier ⊗ₖ ρB.carrier =
      (W.val : Matrix _ _ ℂ) * (ΛA ρA ⊗ₖ ΛB ρB) * star (W.val : Matrix _ _ ℂ) := by
    simpa [W, UA, UB] using carrier_kronecker_spectral ha hb ρA ρB
  rw [hspl]
  exact (charpoly_unitary_conj W (ΛA ρA ⊗ₖ ΛB ρB)).symm

/-- Flattened diagonal of pairwise eigenvalue products (`finProdFinEquiv` layout). -/
noncomputable def tensorEigenDiag (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    Matrix (Fin (na * nb)) (Fin (na * nb)) ℂ :=
  diagonal fun k =>
    (ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 : ℂ) *
      (ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2 : ℂ)

theorem charpoly_tensorDensity_carrier (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (tensorDensity ha hb ρA ρB).carrier.charpoly = (tensorEigenDiag ha hb ρA ρB).charpoly := by
  unfold tensorDensity tensorEigenDiag Matrix.reindex
  rw [Matrix.charpoly_reindex]
  have hΛ : ΛA ρA ⊗ₖ ΛB ρB =
      diagonal fun p : Fin na × Fin nb =>
        (ρA.isHermitian.eigenvalues p.1 : ℂ) * (ρB.isHermitian.eigenvalues p.2 : ℂ) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.diagonal_apply, ΛA, ΛB, Function.comp_apply,
      RCLike.ofReal_mul]
    split_ifs with hdiag <;> try simp
    rcases Prod.mk.inj hdiag with ⟨rfl, rfl⟩
    simp
  rw [← hΛ, charpoly_kronecker_carrier ha hb ρA ρB]

theorem vonNeumannEntropy_eq_of_carrier_charpoly_eq {n : ℕ} {hn : 0 < n} (ρ σ : DensityMatrix hn)
    (h : ρ.carrier.charpoly = σ.carrier.charpoly) :
    vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  have hms := IsHermitian.eigenvalue_multiset_eq_of_charpoly_eq ρ.isHermitian σ.isHermitian h
  have hms_real : Finset.univ.val.map (fun i => ρ.isHermitian.eigenvalues i) =
                  Finset.univ.val.map (fun i => σ.isHermitian.eigenvalues i) :=
    Multiset.map_injective Complex.ofReal_injective hms
  unfold vonNeumannEntropy
  have : (Finset.univ.val.map (fun i => negMulLog (ρ.isHermitian.eigenvalues i))).sum =
         (Finset.univ.val.map (fun i => negMulLog (σ.isHermitian.eigenvalues i))).sum := by
    congr 1
    exact Multiset.map_congr hms_real fun a _ => rfl
  simpa [Finset.sum] using this

private noncomputable def tensorRefDensity (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    DensityMatrix (Nat.mul_pos ha hb) where
  carrier := tensorEigenDiag ha hb ρA ρB
  psd := by
    constructor
    · ext i j
      simp only [tensorEigenDiag, Matrix.conjTranspose_apply, Matrix.diagonal_apply, star_mul',
        star_ofReal]
      split_ifs with h <;> simp [h]
    · intro x
      dsimp [tensorEigenDiag, dotProduct, Matrix.mulVec, Matrix.diagonal_mulVec, Pi.smul_apply,
        smul_eq_mul]
      refine Fintype.sum_nonneg fun i => ?_
      set dR :=
        ρA.isHermitian.eigenvalues (finProdFinEquiv.symm i).1 *
          ρB.isHermitian.eigenvalues (finProdFinEquiv.symm i).2
      have hdR : 0 ≤ dR :=
        mul_nonneg (density_eigenvalues_nonneg ρA _) (density_eigenvalues_nonneg ρB _)
      have hstar : star (x i) * x i = (Complex.normSq (x i) : ℂ) := by
        rw [Complex.star_def]
        rw [show conj (x i) * x i = conj (x i * conj (x i)) by ring]
        rw [Complex.mul_conj]
        simp
      have hterm :
          star (x i) * ((dR : ℂ)) * x i = (dR * Complex.normSq (x i) : ℂ) := by
        calc
          star (x i) * ((dR : ℂ)) * x i = (dR : ℂ) * (star (x i) * x i) := by ring_nf
          _ = (dR : ℂ) * (Complex.normSq (x i) : ℂ) := by rw [hstar]
          _ = (dR * Complex.normSq (x i) : ℂ) := by simp
      rw [hterm]
      have hr : 0 ≤ dR * Complex.normSq (x i) :=
        mul_nonneg hdR (Complex.normSq_nonneg _)
      exact Complex.zero_le_real.mpr hr
  trace_one := by
    simp only [tensorEigenDiag, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply, map_sum,
      Complex.ofReal_mul, ← Fintype.sum_equiv (finProdFinEquiv (m := na) (n := nb)).symm _ _
        fun _ => rfl]
    rw [← trace_eq_sum_eigenvalues_hermitian ρA.isHermitian, ρA.trace_one, ←
      trace_eq_sum_eigenvalues_hermitian ρB.isHermitian, ρB.trace_one, mul_one]

theorem sum_negMulLog_tensor_eigenvalues (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (∑ k : Fin (na * nb),
        negMulLog
          (ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 *
            ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2)) =
      vonNeumannEntropy ρA + vonNeumannEntropy ρB := by
  classical
  rw [Fintype.sum_equiv (finProdFinEquiv (m := na) (n := nb)).symm _ _ fun _ => rfl]
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  conv_lhs =>
    apply_congr
    ext i j
    rw [negMulLog_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul, ← Finset.mul_sum, density_eigenvalues_sum_eq_one_real,
    one_mul, mul_one]
  simp [vonNeumannEntropy, Finset.sum_add_distrib, mul_comm]

theorem vonNeumannEntropy_tensorDensity_eq (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    vonNeumannEntropy (tensorDensity ha hb ρA ρB) =
      vonNeumannEntropy ρA + vonNeumannEntropy ρB := by
  have hcp := charpoly_tensorDensity_carrier ha hb ρA ρB
  have hS :=
    vonNeumannEntropy_eq_of_carrier_charpoly_eq (tensorDensity ha hb ρA ρB)
      (tensorRefDensity ha hb ρA ρB) hcp
  have hdiag :=
    vonNeumannEntropy_eq_sum_negMulLog_of_diagonal_carrier (tensorRefDensity ha hb ρA ρB)
      (fun k =>
        ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 *
          ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2) rfl
  rw [hS, hdiag, sum_negMulLog_tensor_eigenvalues ha hb ρA ρB]

end UMST.Quantum

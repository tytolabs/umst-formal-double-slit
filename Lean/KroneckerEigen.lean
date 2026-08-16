SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
/-
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

set_option maxHeartbeats 800000

/-!
# KroneckerEigen — spectrum of `ρ_A ⊗ ρ_B` and tensor von Neumann entropy

`ρ_A ⊗ ρ_B` is unitarily similar to the diagonal matrix of pairwise products `λ_i μ_j` of factor
eigenvalues, hence `S(ρ_A ⊗ ρ_B) = S(ρ_A) + S(ρ_B)` via `negMulLog_mul` on the flattened product
indexing.
-/

namespace UMST.Quantum

open Matrix Complex Real
open scoped Kronecker BigOperators ComplexOrder

variable {na nb : ℕ}

private noncomputable def rhoDiagA {na : ℕ} (ha : 0 < na) (ρA : DensityMatrix ha) :
    Matrix (Fin na) (Fin na) ℂ :=
  diagonal (RCLike.ofReal ∘ ρA.isHermitian.eigenvalues)

private noncomputable def rhoDiagB {nb : ℕ} (hb : 0 < nb) (ρB : DensityMatrix hb) :
    Matrix (Fin nb) (Fin nb) ℂ :=
  diagonal (RCLike.ofReal ∘ ρB.isHermitian.eigenvalues)

private noncomputable def kroneckerSpectralUnitary {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ :=
  Matrix.kroneckerMap (fun x y => x * y)
    (ρA.isHermitian.eigenvectorUnitary : Matrix (Fin na) (Fin na) ℂ)
    (ρB.isHermitian.eigenvectorUnitary : Matrix (Fin nb) (Fin nb) ℂ)

private noncomputable def kroneckerSpectralInner {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ :=
  diagonal fun p : Fin na × Fin nb =>
    (ρA.isHermitian.eigenvalues p.1 : ℂ) * (ρB.isHermitian.eigenvalues p.2 : ℂ)

private noncomputable def kroneckerSpectralForm {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ :=
  let U := kroneckerSpectralUnitary ha hb ρA ρB
  let D := kroneckerSpectralInner ha hb ρA ρB
  U * D * star U

theorem mul_kronecker_mul' {na nb : ℕ} (A₁ A₂ : Matrix (Fin na) (Fin na) ℂ)
    (B₁ B₂ : Matrix (Fin nb) (Fin nb) ℂ) :
    (A₁ * A₂) ⊗ₖ (B₁ * B₂) = A₁ ⊗ₖ B₁ * A₂ ⊗ₖ B₂ :=
  Matrix.mul_kronecker_mul A₁ A₂ B₁ B₂

/-- Kronecker product of unitary matrices (on `Fin na × Fin nb`) is unitary. -/
theorem unitary_kronecker_prod {na nb : ℕ} (U : Matrix.unitaryGroup (Fin na) ℂ)
    (V : Matrix.unitaryGroup (Fin nb) ℂ) :
    (U.val ⊗ₖ V.val) ∈ Matrix.unitaryGroup (Fin na × Fin nb) ℂ := by
  have hstar : star (U.val ⊗ₖ V.val) = star U.val ⊗ₖ star V.val := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.star_apply, kroneckerMap_apply, star_mul']
  rw [Matrix.mem_unitaryGroup_iff, hstar, ← mul_kronecker_mul']
  simp [Matrix.mem_unitaryGroup_iff.mp U.2, Matrix.mem_unitaryGroup_iff.mp V.2,
    Matrix.one_kronecker_one]

theorem star_kronecker {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℂ) (B : Matrix (Fin nb) (Fin nb) ℂ) :
    star (A ⊗ₖ B) = star A ⊗ₖ star B := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, kroneckerMap_apply]

theorem carrier_kronecker_spectral {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    ρA.carrier ⊗ₖ ρB.carrier = kroneckerSpectralForm ha hb ρA ρB := by
  set UA := (ρA.isHermitian.eigenvectorUnitary : Matrix (Fin na) (Fin na) ℂ)
  set UB := (ρB.isHermitian.eigenvectorUnitary : Matrix (Fin nb) (Fin nb) ℂ)
  set lA := rhoDiagA ha ρA
  set lB := rhoDiagB hb ρB
  have hInner : kroneckerSpectralInner ha hb ρA ρB = (rhoDiagA ha ρA) ⊗ₖ (rhoDiagB hb ρB) := by
    classical
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [kroneckerSpectralInner, rhoDiagA, rhoDiagB, Matrix.kroneckerMap_apply, Matrix.diagonal_apply,
      RCLike.ofReal_mul]
    by_cases hik : i = k
    · by_cases hjl : j = l <;> simp [hik, hjl, Matrix.diagonal_apply]
    · simp [hik, Matrix.diagonal_apply]
  have hcalc : ρA.carrier ⊗ₖ ρB.carrier =
      kroneckerSpectralUnitary ha hb ρA ρB * kroneckerSpectralInner ha hb ρA ρB *
        star (kroneckerSpectralUnitary ha hb ρA ρB) := by
    calc
    ρA.carrier ⊗ₖ ρB.carrier
        = (UA * lA * star UA) ⊗ₖ (UB * lB * star UB) := by
          conv_lhs =>
            rw [ρA.isHermitian.spectral_theorem, ρB.isHermitian.spectral_theorem]
          dsimp [rhoDiagA, rhoDiagB, lA, lB]
    _ = (UA ⊗ₖ UB) * (lA ⊗ₖ lB) * star (UA ⊗ₖ UB) := by
          calc
            (UA * lA * star UA) ⊗ₖ (UB * lB * star UB)
                = (UA * (lA * star UA)) ⊗ₖ (UB * (lB * star UB)) := by simp only [mul_assoc]
            _ = (UA ⊗ₖ UB) * ((lA * star UA) ⊗ₖ (lB * star UB)) :=
                  mul_kronecker_mul' (na := na) (nb := nb) UA (lA * star UA) UB (lB * star UB)
            _ = (UA ⊗ₖ UB) * (lA ⊗ₖ lB) * (star UA ⊗ₖ star UB) := by
                  rw [mul_kronecker_mul' (na := na) (nb := nb) lA (star UA) lB (star UB), mul_assoc]
            _ = (UA ⊗ₖ UB) * (lA ⊗ₖ lB) * star (UA ⊗ₖ UB) := by
                  rw [(star_kronecker (na := na) (nb := nb) UA UB).symm]
    _ = kroneckerSpectralUnitary ha hb ρA ρB * kroneckerSpectralInner ha hb ρA ρB *
          star (kroneckerSpectralUnitary ha hb ρA ρB) := by
          simp [kroneckerSpectralUnitary, hInner]
  dsimp [kroneckerSpectralForm]
  simpa using hcalc

theorem charpoly_kronecker_carrier {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (ρA.carrier ⊗ₖ ρB.carrier).charpoly =
      Matrix.charpoly (kroneckerSpectralInner ha hb ρA ρB) := by
  let UA := (ρA.isHermitian.eigenvectorUnitary : Matrix.unitaryGroup (Fin na) ℂ)
  let UB := (ρB.isHermitian.eigenvectorUnitary : Matrix.unitaryGroup (Fin nb) ℂ)
  let W : Matrix.unitaryGroup (Fin na × Fin nb) ℂ :=
    ⟨(UA.val ⊗ₖ UB.val), unitary_kronecker_prod UA UB⟩
  have hspl : ρA.carrier ⊗ₖ ρB.carrier = kroneckerSpectralForm ha hb ρA ρB :=
    carrier_kronecker_spectral ha hb ρA ρB
  rw [hspl]
  simp only [kroneckerSpectralForm]
  exact charpoly_unitary_conj' W (kroneckerSpectralInner ha hb ρA ρB)

/-- Flattened diagonal of pairwise eigenvalue products (`finProdFinEquiv` layout). -/
noncomputable def tensorEigenDiag {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    Matrix (Fin (na * nb)) (Fin (na * nb)) ℂ :=
  diagonal fun k =>
    (ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 : ℂ) *
      (ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2 : ℂ)

theorem charpoly_tensorDensity_carrier {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (tensorDensity ha hb ρA ρB).carrier.charpoly = (tensorEigenDiag ha hb ρA ρB).charpoly := by
  dsimp only [tensorDensity]
  rw [Matrix.charpoly_reindex (e := finProdFinEquiv) (M := ρA.carrier ⊗ₖ ρB.carrier)]
  rw [charpoly_kronecker_carrier ha hb ρA ρB]
  have hflat : tensorEigenDiag ha hb ρA ρB =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (kroneckerSpectralInner ha hb ρA ρB) := by
    ext k l
    simp only [tensorEigenDiag, kroneckerSpectralInner, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.diagonal_apply, finProdFinEquiv.apply_symm_apply]
    by_cases hkl : k = l
    · subst hkl; simp
    · have hneq : finProdFinEquiv.symm k ≠ finProdFinEquiv.symm l :=
        fun h => hkl (finProdFinEquiv.symm.injective h)
      simp only [hkl, ite_false, if_neg, hneq]
  have hcp := congr_arg Matrix.charpoly hflat
  rw [← Matrix.charpoly_reindex finProdFinEquiv, ← hcp]

theorem vonNeumannEntropy_eq_of_carrier_charpoly_eq {n : ℕ} {hn : 0 < n} (ρ σ : DensityMatrix hn)
    (h : ρ.carrier.charpoly = σ.carrier.charpoly) :
    vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  have hms := Matrix.IsHermitian.eigenvalue_multiset_eq_of_charpoly_eq ρ.isHermitian σ.isHermitian h
  have hms' : (Finset.univ.val.map (fun i => ρ.isHermitian.eigenvalues i)).map Complex.ofReal =
      (Finset.univ.val.map (fun i => σ.isHermitian.eigenvalues i)).map Complex.ofReal := by
    simp only [Multiset.map_map, Function.comp]
    exact hms
  have hms_real : Finset.univ.val.map (fun i => ρ.isHermitian.eigenvalues i) =
      Finset.univ.val.map (fun i => σ.isHermitian.eigenvalues i) :=
    Multiset.map_injective Complex.ofReal_injective hms'
  unfold vonNeumannEntropy
  have hmap :
      Finset.univ.val.map (fun i => negMulLog (ρ.isHermitian.eigenvalues i)) =
        Finset.univ.val.map (fun i => negMulLog (σ.isHermitian.eigenvalues i)) := by
    have := congrArg (Multiset.map negMulLog) hms_real
    simp only [Multiset.map_map, Function.comp] at this ⊢
    exact this
  calc
    ∑ i, negMulLog (ρ.isHermitian.eigenvalues i)
        = (Finset.univ.val.map (fun i => negMulLog (ρ.isHermitian.eigenvalues i))).sum := by
          rw [Finset.sum_eq_multiset_sum]
    _ = (Finset.univ.val.map (fun i => negMulLog (σ.isHermitian.eigenvalues i))).sum :=
          congrArg Multiset.sum hmap
    _ = ∑ i, negMulLog (σ.isHermitian.eigenvalues i) := by rw [Finset.sum_eq_multiset_sum]

private noncomputable def tensorRefDensity {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    DensityMatrix (Nat.mul_pos ha hb) where
  carrier := tensorEigenDiag ha hb ρA ρB
  psd := by
    dsimp [tensorEigenDiag]
    have hnn : 0 ≤ fun k =>
        (ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 : ℂ) *
          (ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2 : ℂ) := by
      intro k
      exact mul_nonneg (Complex.zero_le_real.mpr (density_eigenvalues_nonneg ρA _))
        (Complex.zero_le_real.mpr (density_eigenvalues_nonneg ρB _))
    exact PosSemidef.diagonal hnn
  trace_one := by
    simp only [tensorEigenDiag, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply, ite_true]
    have hsum :
        (∑ p : Fin na × Fin nb,
            Complex.ofReal (ρA.isHermitian.eigenvalues p.1 * ρB.isHermitian.eigenvalues p.2)) = 1 := by
      rw [Fintype.sum_prod_type]
      calc
        ∑ i : Fin na, ∑ j : Fin nb,
            Complex.ofReal (ρA.isHermitian.eigenvalues i * ρB.isHermitian.eigenvalues j)
            = ∑ i : Fin na,
                (ρA.isHermitian.eigenvalues i : ℂ) *
                  ∑ j : Fin nb, (ρB.isHermitian.eigenvalues j : ℂ) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              calc
                ∑ j : Fin nb,
                    Complex.ofReal (ρA.isHermitian.eigenvalues i * ρB.isHermitian.eigenvalues j)
                    = ∑ j : Fin nb,
                        (ρA.isHermitian.eigenvalues i : ℂ) *
                          (ρB.isHermitian.eigenvalues j : ℂ) :=
                      Finset.sum_congr rfl fun j _ => Complex.ofReal_mul _ _
                _ = (ρA.isHermitian.eigenvalues i : ℂ) *
                      ∑ j : Fin nb, (ρB.isHermitian.eigenvalues j : ℂ) := by
                      rw [← Finset.mul_sum]
        _ = 1 := by
          set T := ∑ j : Fin nb, (ρB.isHermitian.eigenvalues j : ℂ)
          have hT : T = 1 := density_eigenvalues_sum_eq_one ρB
          calc
            ∑ i : Fin na, (ρA.isHermitian.eigenvalues i : ℂ) * T
                = T * ∑ i : Fin na, (ρA.isHermitian.eigenvalues i : ℂ) := by
                    rw [← Finset.sum_mul, mul_comm]
            _ = 1 := by rw [hT, density_eigenvalues_sum_eq_one ρA, one_mul]
    rw [Fintype.sum_equiv (finProdFinEquiv (m := na) (n := nb)).symm
      (fun k =>
        (ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 : ℂ) *
          (ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2 : ℂ))
      (fun p =>
        Complex.ofReal (ρA.isHermitian.eigenvalues p.1 * ρB.isHermitian.eigenvalues p.2))
      fun k => by simp [Complex.ofReal_mul]]
    exact hsum

private theorem tensorRefDensity_diagonal_carrier {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (tensorRefDensity ha hb ρA ρB).carrier =
      diagonal fun k =>
        Complex.ofReal (ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 *
          ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2) := by
  unfold tensorRefDensity tensorEigenDiag
  ext k l
  by_cases h : k = l <;> simp [Matrix.diagonal_apply, Complex.ofReal_mul, h]

theorem sum_negMulLog_tensor_eigenvalues {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (∑ k : Fin (na * nb),
        negMulLog
          (ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 *
            ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2)) =
      vonNeumannEntropy ρA + vonNeumannEntropy ρB := by
  classical
  rw [Fintype.sum_equiv (finProdFinEquiv (m := na) (n := nb)).symm
    (fun k =>
      negMulLog
        (ρA.isHermitian.eigenvalues (finProdFinEquiv.symm k).1 *
          ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2))
    (fun p => negMulLog (ρA.isHermitian.eigenvalues p.1 * ρB.isHermitian.eigenvalues p.2))
    fun _ => rfl]
  rw [Fintype.sum_prod_type]
  calc
    ∑ i : Fin na, ∑ j : Fin nb,
        negMulLog (ρA.isHermitian.eigenvalues i * ρB.isHermitian.eigenvalues j)
        = ∑ i : Fin na, ∑ j : Fin nb,
            (ρB.isHermitian.eigenvalues j * negMulLog (ρA.isHermitian.eigenvalues i) +
              ρA.isHermitian.eigenvalues i * negMulLog (ρB.isHermitian.eigenvalues j)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [negMulLog_mul]
    _ = (∑ j : Fin nb, ρB.isHermitian.eigenvalues j) *
          (∑ i : Fin na, negMulLog (ρA.isHermitian.eigenvalues i)) +
        (∑ i : Fin na, ρA.isHermitian.eigenvalues i) *
          (∑ j : Fin nb, negMulLog (ρB.isHermitian.eigenvalues j)) := by
          calc
            ∑ i : Fin na, ∑ j : Fin nb,
                (ρB.isHermitian.eigenvalues j * negMulLog (ρA.isHermitian.eigenvalues i) +
                  ρA.isHermitian.eigenvalues i * negMulLog (ρB.isHermitian.eigenvalues j))
                = ∑ i : Fin na,
                    ((∑ j : Fin nb, ρB.isHermitian.eigenvalues j) *
                        negMulLog (ρA.isHermitian.eigenvalues i) +
                      ρA.isHermitian.eigenvalues i *
                        ∑ j : Fin nb, negMulLog (ρB.isHermitian.eigenvalues j)) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.mul_sum]
            _ = (∑ j : Fin nb, ρB.isHermitian.eigenvalues j) *
                  (∑ i : Fin na, negMulLog (ρA.isHermitian.eigenvalues i)) +
                (∑ i : Fin na, ρA.isHermitian.eigenvalues i) *
                  (∑ j : Fin nb, negMulLog (ρB.isHermitian.eigenvalues j)) := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ = vonNeumannEntropy ρA + vonNeumannEntropy ρB := by
          simp [vonNeumannEntropy, density_eigenvalues_sum_eq_one_real, one_mul, mul_comm]

theorem vonNeumannEntropy_tensorDensity_eq {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
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
          ρB.isHermitian.eigenvalues (finProdFinEquiv.symm k).2)
      (tensorRefDensity_diagonal_carrier ha hb ρA ρB)
  rw [hS, hdiag, sum_negMulLog_tensor_eigenvalues ha hb ρA ρB]

end UMST.Quantum

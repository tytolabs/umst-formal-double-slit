/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import DensityState
import LandauerBound
import VonNeumannEntropy

/-!
# GeneralResidualCoherence — purity-based Residual Coherence Capacity for `Fin n`

The **purity decomposition** of a density matrix splits `Tr(ρ²)` into diagonal and
off-diagonal contributions:

`Tr(ρ²) = ∑ᵢ pᵢ² + ∑_{i≠j} |ρᵢⱼ|²`

The **general residual coherence capacity** is the ratio of off-diagonal purity to
the maximum possible off-diagonal purity:

`RCC_n(ρ) = (Tr(ρ²) - ∑ᵢ pᵢ²) / (1 - ∑ᵢ pᵢ²)`

Properties:
- `RCC_n ∈ [0, 1]`
- `RCC_n = 0` iff `ρ` is diagonal (no coherence)
- `RCC_n = 1` iff `ρ` is pure (`Tr(ρ²) = 1`)
- For qubits (`n = 2`), reduces to `|ρ₀₁|² / (p₀ p₁)` (the existing qubit RCC)
-/

namespace UMST.Quantum

open scoped Matrix ComplexOrder BigOperators
open Matrix Complex

variable {n : ℕ} {hn : 0 < n}

/-- Sum of squared diagonal entries: `∑ᵢ pᵢ²` where `pᵢ = Re(ρᵢᵢ)`. -/
noncomputable def diagonalPurity (ρ : DensityMatrix hn) : ℝ :=
  ∑ i : Fin n, (ρ.carrier i i).re ^ 2

/-- Off-diagonal purity: `Tr(ρ²) - ∑ᵢ pᵢ²`, i.e. `∑_{i≠j} |ρᵢⱼ|²`. -/
noncomputable def offDiagonalPurity (ρ : DensityMatrix hn) : ℝ :=
  (trace (ρ.carrier * ρ.carrier)).re - diagonalPurity ρ

/-- General residual coherence capacity (purity-based):
`RCC_n(ρ) = offDiagonalPurity ρ / (1 - diagonalPurity ρ)`. -/
noncomputable def residualCoherenceCapacity_purity (ρ : DensityMatrix hn)
    (h : diagonalPurity ρ < 1) : ℝ :=
  offDiagonalPurity ρ / (1 - diagonalPurity ρ)

/-! ### Basic properties of diagonal purity -/

theorem diagonalPurity_nonneg (ρ : DensityMatrix hn) : 0 ≤ diagonalPurity ρ := by
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

theorem diagonalPurity_le_one (ρ : DensityMatrix hn) : diagonalPurity ρ ≤ 1 := by
  have hsum := DensityMat.trace_re_eq_one_n ρ
  have hnn : ∀ i : Fin n, 0 ≤ (ρ.carrier i i).re := fun i => DensityMat.diag_re_nonneg_n ρ i
  have hle : ∀ i : Fin n, (ρ.carrier i i).re ≤ 1 := fun i => DensityMat.diag_re_le_one_n ρ i
  calc diagonalPurity ρ = ∑ i : Fin n, (ρ.carrier i i).re ^ 2 := rfl
    _ ≤ ∑ i : Fin n, (ρ.carrier i i).re := by
        apply Finset.sum_le_sum; intro i _
        exact sq_le_self' (by linarith [hnn i]) (hle i)
    _ = 1 := hsum

/-! ### Hermiticity helpers -/

/-- For a Hermitian matrix, `(A * A) i i = ∑ j, ‖A i j‖²` (real and nonneg). -/
theorem hermitian_sq_diag_eq_sum_normSq (ρ : DensityMatrix hn) (i : Fin n) :
    ((ρ.carrier * ρ.carrier) i i).re = ∑ j : Fin n, Complex.normSq (ρ.carrier i j) := by
  simp only [Matrix.mul_apply]
  have hH := DensityMat.isHermitian ρ
  conv_lhs => rw [show (∑ j, ρ.carrier i j * ρ.carrier j i) =
    ∑ j, ρ.carrier i j * starRingEnd ℂ (ρ.carrier i j) from by
    congr 1; ext j
    have : ρ.carrier j i = starRingEnd ℂ (ρ.carrier i j) := by
      have h := hH.apply i j
      simp [Matrix.IsHermitian, Matrix.conjTranspose_apply] at h
      rw [← h]; simp [star]
    rw [this]]
  rw [map_sum]
  congr 1; ext j
  rw [Complex.mul_conj]
  simp [Complex.ofReal_re]

/-- `Tr(ρ²)` equals `∑ᵢ ∑ⱼ ‖ρᵢⱼ‖²` for a Hermitian matrix. -/
theorem trace_sq_eq_sum_normSq (ρ : DensityMatrix hn) :
    (trace (ρ.carrier * ρ.carrier)).re = ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (ρ.carrier i j) := by
  unfold Matrix.trace
  rw [map_sum]
  congr 1; ext i
  exact hermitian_sq_diag_eq_sum_normSq ρ i

/-- Diagonal entry satisfies `‖ρᵢᵢ‖² = Re(ρᵢᵢ)²` (since imaginary part is zero for Hermitian). -/
theorem normSq_diag_eq_re_sq (ρ : DensityMatrix hn) (i : Fin n) :
    Complex.normSq (ρ.carrier i i) = (ρ.carrier i i).re ^ 2 := by
  have hH := DensityMat.isHermitian ρ
  have him : (ρ.carrier i i).im = 0 := by
    have h := hH.apply i i
    simp [Matrix.IsHermitian, Matrix.conjTranspose_apply, star] at h
    rw [Complex.ext_iff] at h
    linarith [h.2]
  simp [Complex.normSq_apply, him, sq]

/-! ### Off-diagonal purity is a sum of `‖ρᵢⱼ‖²` for `i ≠ j` -/

/-- Off-diagonal purity equals `∑_{i≠j} ‖ρᵢⱼ‖²`. -/
theorem offDiagonalPurity_eq_sum_offdiag (ρ : DensityMatrix hn) :
    offDiagonalPurity ρ = ∑ i : Fin n, ∑ j in Finset.univ.erase i, Complex.normSq (ρ.carrier i j) := by
  unfold offDiagonalPurity diagonalPurity
  rw [trace_sq_eq_sum_normSq ρ]
  have key : ∀ i : Fin n,
      (∑ j : Fin n, Complex.normSq (ρ.carrier i j)) =
        Complex.normSq (ρ.carrier i i) + ∑ j in Finset.univ.erase i, Complex.normSq (ρ.carrier i j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp_rw [key, normSq_diag_eq_re_sq ρ]
  simp [Finset.sum_add_distrib, add_sub_cancel_left]

/-- Off-diagonal purity is nonneg: each `‖ρᵢⱼ‖² ≥ 0`. -/
theorem offDiagonalPurity_nonneg (ρ : DensityMatrix hn) : 0 ≤ offDiagonalPurity ρ := by
  rw [offDiagonalPurity_eq_sum_offdiag]
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact Complex.normSq_nonneg _

/-! ### `Tr(ρ²) ≤ 1` -/

/-- For a density matrix, `Tr(ρ²) ≤ 1` (spectral proof: `VonNeumannEntropy.density_trace_sq_re_le_one`). -/
theorem trace_sq_le_one (ρ : DensityMatrix hn) :
    (trace (ρ.carrier * ρ.carrier)).re ≤ 1 :=
  density_trace_sq_re_le_one ρ

/-! ### RCC properties -/

/-- `offDiagonalPurity ≤ 1 - diagonalPurity`, equivalently `Tr(ρ²) ≤ 1`. -/
theorem offDiagonalPurity_le_complement (ρ : DensityMatrix hn) :
    offDiagonalPurity ρ ≤ 1 - diagonalPurity ρ := by
  unfold offDiagonalPurity
  linarith [trace_sq_le_one ρ]

/-- Residual coherence capacity is nonneg (off-diagonal purity ≥ 0, denominator > 0). -/
theorem residualCoherenceCapacity_purity_nonneg (ρ : DensityMatrix hn) (h : diagonalPurity ρ < 1) :
    0 ≤ residualCoherenceCapacity_purity ρ h := by
  unfold residualCoherenceCapacity_purity
  apply div_nonneg (offDiagonalPurity_nonneg ρ)
  linarith

/-- Residual coherence capacity is at most 1 (off-diagonal purity ≤ 1 - diagonal purity). -/
theorem residualCoherenceCapacity_purity_le_one (ρ : DensityMatrix hn) (h : diagonalPurity ρ < 1) :
    residualCoherenceCapacity_purity ρ h ≤ 1 := by
  unfold residualCoherenceCapacity_purity
  rw [div_le_one (by linarith : 0 < 1 - diagonalPurity ρ)]
  exact offDiagonalPurity_le_complement ρ

/-- Residual coherence capacity lies in `[0, 1]`. -/
theorem residualCoherenceCapacity_purity_mem_Icc (ρ : DensityMatrix hn) (h : diagonalPurity ρ < 1) :
    residualCoherenceCapacity_purity ρ h ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨residualCoherenceCapacity_purity_nonneg ρ h, residualCoherenceCapacity_purity_le_one ρ h⟩

/-! ### Characterization theorems -/

/-- Off-diagonal purity is zero iff all off-diagonal entries vanish. -/
theorem offDiagonalPurity_eq_zero_iff_diagonal (ρ : DensityMatrix hn) :
    offDiagonalPurity ρ = 0 ↔ ∀ i j : Fin n, i ≠ j → ρ.carrier i j = 0 := by
  rw [offDiagonalPurity_eq_sum_offdiag]
  constructor
  · intro h i j hij
    have hle : ∀ i : Fin n, 0 ≤ ∑ j in Finset.univ.erase i, Complex.normSq (ρ.carrier i j) :=
      fun i => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
    have hzero := Finset.sum_eq_zero_iff_of_nonneg hle |>.mp h
    have hrow := hzero i (Finset.mem_univ i)
    have hle2 : ∀ k ∈ Finset.univ.erase i, 0 ≤ Complex.normSq (ρ.carrier i k) :=
      fun k _ => Complex.normSq_nonneg _
    have hcol := Finset.sum_eq_zero_iff_of_nonneg hle2 |>.mp hrow
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩
    have := hcol j hmem
    rwa [Complex.normSq_eq_zero] at this
  · intro h
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j hj
    have hij : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [h i j (Ne.symm hij)]
    exact Complex.normSq_zero

/-- RCC = 1 iff `Tr(ρ²) = 1` (the state is pure). -/
theorem residualCoherenceCapacity_purity_eq_one_iff_pure (ρ : DensityMatrix hn) (h : diagonalPurity ρ < 1) :
    residualCoherenceCapacity_purity ρ h = 1 ↔ (trace (ρ.carrier * ρ.carrier)).re = 1 := by
  unfold residualCoherenceCapacity_purity offDiagonalPurity
  constructor
  · intro heq
    have hpos : 0 < 1 - diagonalPurity ρ := by linarith
    rw [div_eq_one_iff_eq (ne_of_gt hpos)] at heq
    linarith
  · intro htr
    have hpos : 0 < 1 - diagonalPurity ρ := by linarith
    rw [div_eq_one_iff_eq (ne_of_gt hpos)]
    linarith

/-! ### Qubit compatibility -/

/-- For a qubit (`n = 2`), diagonal purity equals `p₀² + p₁²`. -/
theorem diagonalPurity_qubit (ρ : DensityMatrix hnQubit) :
    diagonalPurity ρ = (ρ.carrier 0 0).re ^ 2 + (ρ.carrier 1 1).re ^ 2 := by
  unfold diagonalPurity
  rw [Fin.sum_univ_two]

/-- For a qubit, `1 - diagonalPurity = 2 p₀ p₁`. -/
theorem one_sub_diagonalPurity_qubit (ρ : DensityMatrix hnQubit) :
    1 - diagonalPurity ρ = 2 * (ρ.carrier 0 0).re * (ρ.carrier 1 1).re := by
  rw [diagonalPurity_qubit]
  have hsum := DensityMat.trace_re_eq_one_n ρ
  rw [Fin.sum_univ_two] at hsum
  nlinarith [hsum]

/-- For a qubit, `offDiagonalPurity = 2 ‖ρ₀₁‖²`. -/
theorem offDiagonalPurity_qubit (ρ : DensityMatrix hnQubit) :
    offDiagonalPurity ρ = 2 * Complex.normSq (ρ.carrier 0 1) := by
  rw [offDiagonalPurity_eq_sum_offdiag]
  rw [Fin.sum_univ_two]
  simp only [Finset.univ, Fintype.elems_fin]
  -- Each inner sum has exactly one term (the other index)
  have h0 : ∑ j in ({0, 1} : Finset (Fin 2)).erase 0, Complex.normSq (ρ.carrier 0 j) =
      Complex.normSq (ρ.carrier 0 1) := by
    simp [Finset.sum_singleton]
  have h1 : ∑ j in ({0, 1} : Finset (Fin 2)).erase 1, Complex.normSq (ρ.carrier 1 j) =
      Complex.normSq (ρ.carrier 1 0) := by
    simp [Finset.sum_singleton]
  rw [h0, h1]
  -- ‖ρ₁₀‖² = ‖ρ₀₁‖² by Hermiticity
  have hH := DensityMat.isHermitian ρ
  have h10 : ρ.carrier 1 0 = starRingEnd ℂ (ρ.carrier 0 1) := by
    have := hH.apply 0 1
    simp [Matrix.IsHermitian, Matrix.conjTranspose_apply, star] at this
    rw [← this]; simp [star]
  rw [h10, map_starRingEnd, Complex.normSq_conj]
  ring

/-- For a qubit with nonzero off-diagonal, `RCC_purity = ‖ρ₀₁‖² / (p₀ p₁)`. -/
theorem residualCoherenceCapacity_purity_qubit (ρ : DensityMatrix hnQubit)
    (h : diagonalPurity ρ < 1) :
    residualCoherenceCapacity_purity ρ h =
      Complex.normSq (ρ.carrier 0 1) / ((ρ.carrier 0 0).re * (ρ.carrier 1 1).re) := by
  unfold residualCoherenceCapacity_purity
  rw [offDiagonalPurity_qubit, one_sub_diagonalPurity_qubit]
  field_simp
  ring

end UMST.Quantum

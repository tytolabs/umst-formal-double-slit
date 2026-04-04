/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Data.Complex.BigOperators

import DensityState
import LandauerBound

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
    (_ : diagonalPurity ρ < 1) : ℝ :=
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
        nlinarith [hnn i, hle i, sq_nonneg ((ρ.carrier i i).re - 1)]
    _ = 1 := hsum

/-! ### Hermiticity helpers -/

/-- For a Hermitian matrix, `(A * A) i i = ∑ j, ‖A i j‖²` (real and nonneg). -/
theorem hermitian_sq_diag_eq_sum_normSq (ρ : DensityMatrix hn) (i : Fin n) :
    ((ρ.carrier * ρ.carrier) i i).re = ∑ j : Fin n, Complex.normSq (ρ.carrier i j) := by
  have hH := DensityMat.isHermitian ρ
  simp only [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hij : ρ.carrier j i = starRingEnd ℂ (ρ.carrier i j) := by
    rw [starRingEnd_apply]
    exact (hH.apply j i).symm
  rw [hij, Complex.mul_conj]
  simp

/-- `Tr(ρ²)` equals `∑ᵢ ∑ⱼ ‖ρᵢⱼ‖²` for a Hermitian matrix. -/
theorem trace_sq_eq_sum_normSq (ρ : DensityMatrix hn) :
    (trace (ρ.carrier * ρ.carrier)).re = ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (ρ.carrier i j) := by
  unfold Matrix.trace
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact hermitian_sq_diag_eq_sum_normSq ρ i

/-- Diagonal entry satisfies `‖ρᵢᵢ‖² = Re(ρᵢᵢ)²` (since imaginary part is zero for Hermitian). -/
theorem normSq_diag_eq_re_sq (ρ : DensityMatrix hn) (i : Fin n) :
    Complex.normSq (ρ.carrier i i) = (ρ.carrier i i).re ^ 2 := by
  have h := (DensityMat.isHermitian ρ).apply i i
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_apply, starRingEnd_apply] at h
  have him : (ρ.carrier i i).im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
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

/-- PSD entry bound: `‖ρᵢⱼ‖² ≤ (ρᵢᵢ).re · (ρⱼⱼ).re` (Schur complement on a 2×2 principal submatrix).
For a density matrix, `Tr(ρ²) ≤ 1` follows from eigenvalues in `[0,1]` summing to `1`. -/
theorem normSq_entry_le_diag_mul (ρ : DensityMatrix hn) (i j : Fin n) :
    Complex.normSq (ρ.carrier i j) ≤ (ρ.carrier i i).re * (ρ.carrier j j).re := by
  by_cases hij : i = j
  · -- Diagonal case: normSq(ρᵢᵢ) = (ρᵢᵢ).re² = (ρᵢᵢ).re * (ρᵢᵢ).re
    subst hij
    rw [normSq_diag_eq_re_sq]
    simp [pow_two, le_refl]
  · -- Off-diagonal case: use 2×2 submatrix PSD argument
    set b := ρ.carrier i j with hb_def
    set p := (ρ.carrier i i).re with hp_def
    set q := (ρ.carrier j j).re with hq_def
    -- The 2×2 submatrix is PSD
    have h2psd : (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n)
        (![i, j] : Fin 2 → Fin n)).PosSemidef :=
      ρ.psd.submatrix (![i, j] : Fin 2 → Fin n)
    -- Hermiticity gives ρ j i = conj(ρ i j) = conj(b)
    have hji : ρ.carrier j i = starRingEnd ℂ b := by
      rw [hb_def]
      exact (DensityMat.isHermitian ρ).apply j i |>.symm
    -- Diagonal entries are real: ρ i i = ↑p, ρ j j = ↑q
    have hii_re : (ρ.carrier i i).im = 0 := by
      have h := (DensityMat.isHermitian ρ).apply i i
      simp only [Matrix.IsHermitian, Matrix.conjTranspose_apply, starRingEnd_apply] at h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hjj_re : (ρ.carrier j j).im = 0 := by
      have h := (DensityMat.isHermitian ρ).apply j j
      simp only [Matrix.IsHermitian, Matrix.conjTranspose_apply, starRingEnd_apply] at h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hii_eq : ρ.carrier i i = (p : ℂ) := by
      apply Complex.ext
      · simp [hp_def]
      · simp [hii_re]
    have hjj_eq : ρ.carrier j j = (q : ℂ) := by
      apply Complex.ext
      · simp [hq_def]
      · simp [hjj_re]
    -- The submatrix entries
    have hsub_00 : ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) 0 0 = (p : ℂ) := by
      simp [Matrix.submatrix, hii_eq]
    have hsub_01 : ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) 0 1 = b := by
      simp [Matrix.submatrix, hb_def]
    have hsub_10 : ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) 1 0 = starRingEnd ℂ b := by
      simp [Matrix.submatrix, hji]
    have hsub_11 : ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) 1 1 = (q : ℂ) := by
      simp [Matrix.submatrix, hjj_eq]
    -- Helper: b * starRingEnd ℂ b = normSq b (as complex)
    have hbc : b * starRingEnd ℂ b = (Complex.normSq b : ℂ) := Complex.mul_conj b
    -- Apply PSD to vector ![-b, (p:ℂ)] to get 0 ≤ p*(p*q - normSq(b))
    have H1 : (0 : ℂ) ≤ Matrix.dotProduct (star (![-b, (p : ℂ)] : Fin 2 → ℂ))
        (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![-b, (p : ℂ)]) :=
      h2psd.2 ![-b, (p : ℂ)]
    -- Apply PSD to vector ![(q:ℂ), -starRingEnd ℂ b] to get 0 ≤ q*(p*q - normSq(b))
    have H2 : (0 : ℂ) ≤ Matrix.dotProduct (star (![(q : ℂ), -starRingEnd ℂ b] : Fin 2 → ℂ))
        (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(q : ℂ), -starRingEnd ℂ b]) :=
      h2psd.2 ![(q : ℂ), -starRingEnd ℂ b]
    -- Compute dot product for H1: result is p * (p*q - normSq b)
    have H1_val : Matrix.dotProduct (star (![-b, (p : ℂ)] : Fin 2 → ℂ))
        (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![-b, (p : ℂ)]) =
        (p : ℂ) * ((p : ℂ) * (q : ℂ) - Complex.normSq b) := by
      simp only [Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Pi.star_apply, star_neg, starRingEnd_apply]
      simp only [hsub_00, hsub_01, hsub_10, hsub_11]
      have hsp : star (p : ℂ) = (p : ℂ) := Complex.conj_ofReal p
      rw [hsp]
      ring_nf
      rw [show (p : ℂ) * b * starRingEnd ℂ b = (p : ℂ) * (b * starRingEnd ℂ b) from by ring]
      rw [hbc]
    -- Compute dot product for H2: result is q * (p*q - normSq b)
    have H2_val : Matrix.dotProduct (star (![(q : ℂ), -starRingEnd ℂ b] : Fin 2 → ℂ))
        (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(q : ℂ), -starRingEnd ℂ b]) =
        (q : ℂ) * ((p : ℂ) * (q : ℂ) - Complex.normSq b) := by
      simp only [Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Pi.star_apply, star_neg, starRingEnd_apply, star_star]
      simp only [hsub_00, hsub_01, hsub_10, hsub_11]
      have hsq : star (q : ℂ) = (q : ℂ) := Complex.conj_ofReal q
      rw [hsq]
      ring_nf
      rw [show (q : ℂ) * b * starRingEnd ℂ b = (q : ℂ) * (b * starRingEnd ℂ b) from by ring]
      rw [hbc]
    rw [H1_val] at H1
    rw [H2_val] at H2
    -- Extract real parts: H1 gives 0 ≤ p*(p*q - normSq b), H2 gives 0 ≤ q*(p*q - normSq b)
    have H1_re : 0 ≤ p * (p * q - Complex.normSq b) := by
      have h := (Complex.nonneg_iff.mp H1).1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.normSq_apply, mul_zero, sub_zero] at h
      convert h using 1
      simp [Complex.normSq_apply]
    have H2_re : 0 ≤ q * (p * q - Complex.normSq b) := by
      have h := (Complex.nonneg_iff.mp H2).1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.normSq_apply, mul_zero, sub_zero] at h
      convert h using 1
      simp [Complex.normSq_apply]
    -- normSq b ≥ 0
    have hnsq : 0 ≤ Complex.normSq b := Complex.normSq_nonneg _
    have hp_nn : 0 ≤ p := DensityMat.diag_re_nonneg_n ρ i
    have hq_nn : 0 ≤ q := DensityMat.diag_re_nonneg_n ρ j
    -- Case split on p
    by_cases hp0 : p = 0
    · -- p = 0
      by_cases hq0 : q = 0
      · -- p = 0, q = 0: use PSD with ![1, r] for r = 1, -1, I, -I to show b = 0
        -- For any vector ![1, r], dotProduct = b*r + star(b*r) = 2*Re(b*r) ≥ 0
        -- Taking r=1: 2*Re(b) ≥ 0; r=-1: -2*Re(b) ≥ 0 → Re(b)=0
        -- Taking r=I: -2*Im(b) ≥ 0; r=-I: 2*Im(b) ≥ 0 → Im(b)=0
        -- hsub entries with p=0, q=0:
        -- M = [[0, b], [starRingEnd ℂ b, 0]]
        have H3 : (0 : ℂ) ≤ Matrix.dotProduct (star (![(1:ℂ), (1:ℂ)] : Fin 2 → ℂ))
            (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(1:ℂ), (1:ℂ)]) :=
          h2psd.2 ![(1:ℂ), (1:ℂ)]
        have H4 : (0 : ℂ) ≤ Matrix.dotProduct (star (![(1:ℂ), -(1:ℂ)] : Fin 2 → ℂ))
            (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(1:ℂ), -(1:ℂ)]) :=
          h2psd.2 ![(1:ℂ), -(1:ℂ)]
        have H5 : (0 : ℂ) ≤ Matrix.dotProduct (star (![(1:ℂ), Complex.I] : Fin 2 → ℂ))
            (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(1:ℂ), Complex.I]) :=
          h2psd.2 ![(1:ℂ), Complex.I]
        have H6 : (0 : ℂ) ≤ Matrix.dotProduct (star (![(1:ℂ), -Complex.I] : Fin 2 → ℂ))
            (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(1:ℂ), -Complex.I]) :=
          h2psd.2 ![(1:ℂ), -Complex.I]
        -- Compute dot products
        -- For ![1, 1]: 1*(0*1+b*1) + 1*(cj(b)*1+0*1) = b + cj(b)
        have H3_val : Matrix.dotProduct (star (![(1:ℂ), (1:ℂ)] : Fin 2 → ℂ))
            (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(1:ℂ), (1:ℂ)]) =
            b + starRingEnd ℂ b := by
          simp only [Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Pi.star_apply, star_one]
          simp only [hsub_00, hsub_01, hsub_10, hsub_11]
          rw [show (p : ℂ) = 0 by simp [hp0], show (q : ℂ) = 0 by simp [hq0]]
          simp only [starRingEnd_apply]
          ring_nf
        -- For ![1, -1]: similarly -(b + cj(b))
        have H4_val : Matrix.dotProduct (star (![(1:ℂ), -(1:ℂ)] : Fin 2 → ℂ))
            (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(1:ℂ), -(1:ℂ)]) =
            -(b + starRingEnd ℂ b) := by
          simp only [Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Pi.star_apply, star_one, star_neg]
          simp only [hsub_00, hsub_01, hsub_10, hsub_11]
          rw [show (p : ℂ) = 0 by simp [hp0], show (q : ℂ) = 0 by simp [hq0]]
          simp only [starRingEnd_apply]
          ring_nf
        -- For ![1, I]: 1*(b*I) + (-I)*(cj(b)) = b*I - I*cj(b); Re = -2*Im(b)
        have H5_val : Matrix.dotProduct (star (![(1:ℂ), Complex.I] : Fin 2 → ℂ))
            (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(1:ℂ), Complex.I]) =
            b * Complex.I + starRingEnd ℂ (b * Complex.I) := by
          have hstI : star Complex.I = -Complex.I := by
            have : starRingEnd ℂ Complex.I = -Complex.I := Complex.conj_I
            rwa [← Complex.star_def] at this
          simp only [Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Pi.star_apply, star_one, hstI, hsub_00, hsub_01,
            hsub_10, hsub_11, hp0, hq0, Complex.ofReal_zero, zero_mul, add_zero, mul_zero,
            starRingEnd_apply, RingHom.map_mul (starRingEnd ℂ), Complex.conj_I, smul_eq_mul, one_mul,
            neg_mul, mul_one, mul_neg, neg_neg]
          simp [mul_comm, mul_left_comm, mul_assoc, add_comm]
        -- For ![1, -I]: -(b*I + cj(b*I))
        have H6_val : Matrix.dotProduct (star (![(1:ℂ), -Complex.I] : Fin 2 → ℂ))
            (ρ.carrier.submatrix (![i, j] : Fin 2 → Fin n) (![i, j] : Fin 2 → Fin n) *ᵥ ![(1:ℂ), -Complex.I]) =
            -(b * Complex.I + starRingEnd ℂ (b * Complex.I)) := by
          have hstI : star Complex.I = -Complex.I := by
            have : starRingEnd ℂ Complex.I = -Complex.I := Complex.conj_I
            rwa [← Complex.star_def] at this
          simp only [Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Pi.star_apply, star_one, star_neg, hstI, hsub_00,
            hsub_01, hsub_10, hsub_11, hp0, hq0, Complex.ofReal_zero, zero_mul, add_zero, mul_zero,
            starRingEnd_apply, RingHom.map_mul (starRingEnd ℂ), Complex.conj_I, map_neg, smul_eq_mul,
            one_mul, neg_mul, mul_one, mul_neg, neg_neg]
          simp [mul_comm, mul_left_comm, mul_assoc, add_comm]
        rw [H3_val] at H3; rw [H4_val] at H4
        rw [H5_val] at H5; rw [H6_val] at H6
        -- From H3 and H4: b + cj(b) ≥ 0 and -(b + cj(b)) ≥ 0 → Re(b) = 0
        have hre : b.re = 0 := by
          rcases Complex.nonneg_iff.mp H3 with ⟨h3r, _⟩
          rcases Complex.nonneg_iff.mp H4 with ⟨h4r, _⟩
          have hres : (starRingEnd ℂ b).re = b.re := by
            rw [starRingEnd_apply, congr_fun Complex.star_def b, Complex.conj_re]
          have hre_sum : (b + starRingEnd ℂ b).re = 2 * b.re := by
            rw [Complex.add_re, hres, two_mul]
          have h4re : (-(b + starRingEnd ℂ b)).re = -(2 * b.re) := by
            rw [Complex.neg_re, Complex.add_re, hres, ← two_mul]
          rw [hre_sum] at h3r
          rw [h4re] at h4r
          linarith
        -- From H5 and H6: b*I + cj(b*I) ≥ 0 and -(b*I + cj(b*I)) ≥ 0 → Im(b) = 0
        have him2 : b.im = 0 := by
          have hbI : b * Complex.I = Complex.ofReal (-b.im) := by
            have hbr : b = (b.im : ℂ) * Complex.I := by
              calc
                b = (b.re : ℂ) + (b.im : ℂ) * Complex.I := (Complex.re_add_im b).symm
                _ = (b.im : ℂ) * Complex.I := by simp [hre, zero_add]
            rw [hbr, mul_assoc, Complex.I_mul_I]
            simp [← Complex.ofReal_neg]
          have hkey :
              b * Complex.I + starRingEnd ℂ (b * Complex.I) = Complex.ofReal (-(2 * b.im)) := by
            rw [hbI, starRingEnd_apply, congr_fun Complex.star_def (Complex.ofReal (-b.im)),
              Complex.add_conj]
            simp [two_mul, neg_mul]
          rw [hkey] at H5
          have hneg :
              -(b * Complex.I + starRingEnd ℂ (b * Complex.I)) = Complex.ofReal (2 * b.im) := by
            rw [hkey]
            simp only [Complex.ofReal_neg, neg_neg]
          rw [hneg] at H6
          rcases Complex.nonneg_iff.mp H5 with ⟨h5r, _⟩
          rcases Complex.nonneg_iff.mp H6 with ⟨h6r, _⟩
          simp only [Complex.ofReal_re, Complex.ofReal_im] at h5r h6r
          linarith
        have hb_zero : b = 0 := Complex.ext hre him2
        rw [hb_zero, hp0, hq0, Complex.normSq_zero]
        simp
      · -- p = 0, q ≠ 0 hence q > 0
        have hq_pos : 0 < q := lt_of_le_of_ne hq_nn (Ne.symm hq0)
        -- From H2_re: 0 ≤ q*(0*q - normSq b) = -q*normSq(b)
        have hnsq_zero : Complex.normSq b = 0 := by
          rw [hp0] at H2_re
          have : 0 ≤ q * (0 * q - Complex.normSq b) := H2_re
          have : q * Complex.normSq b ≤ 0 := by nlinarith
          nlinarith [hq_pos.le]
        rw [hnsq_zero, hp0]
        simp
    · -- p > 0
      have hp_pos : 0 < p := lt_of_le_of_ne hp_nn (Ne.symm hp0)
      have hdiff : 0 ≤ p * q - Complex.normSq b :=
        nonneg_of_mul_nonneg_right H1_re hp_pos
      have key : Complex.normSq b ≤ p * q := by linarith
      linarith

theorem trace_sq_le_one (ρ : DensityMatrix hn) :
    (trace (ρ.carrier * ρ.carrier)).re ≤ 1 := by
  rw [trace_sq_eq_sum_normSq ρ]
  -- Use Cauchy-Schwarz: normSq(ρᵢⱼ) ≤ (ρᵢᵢ).re * (ρⱼⱼ).re
  have hkey : ∀ i j : Fin n, Complex.normSq (ρ.carrier i j) ≤
      (ρ.carrier i i).re * (ρ.carrier j j).re :=
    fun i j => normSq_entry_le_diag_mul ρ i j
  calc ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (ρ.carrier i j)
      ≤ ∑ i : Fin n, ∑ j : Fin n, (ρ.carrier i i).re * (ρ.carrier j j).re := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hkey i j
    _ = (∑ i : Fin n, (ρ.carrier i i).re) * (∑ j : Fin n, (ρ.carrier j j).re) := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
    _ = 1 * 1 := by rw [DensityMat.trace_re_eq_one_n ρ]
    _ = 1 := one_mul 1

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
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ∑ j in Finset.univ.erase i, Complex.normSq (ρ.carrier i j) :=
      fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
    have hzero := Finset.sum_eq_zero_iff_of_nonneg hle |>.mp h
    have hrow := hzero i (Finset.mem_univ i)
    have hle2 : ∀ k ∈ Finset.univ.erase i, 0 ≤ Complex.normSq (ρ.carrier i k) :=
      fun k _ => Complex.normSq_nonneg _
    have hcol := Finset.sum_eq_zero_iff_of_nonneg hle2 |>.mp hrow
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
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
  rw [offDiagonalPurity_eq_sum_offdiag, Fin.sum_univ_two]
  have hErase0 : Finset.univ.erase (0 : Fin 2) = ({1} : Finset (Fin 2)) := by decide
  have hErase1 : Finset.univ.erase (1 : Fin 2) = ({0} : Finset (Fin 2)) := by decide
  simp only [hErase0, hErase1, Finset.sum_singleton]
  have hH := DensityMat.isHermitian ρ
  have h10 : ρ.carrier 1 0 = starRingEnd ℂ (ρ.carrier 0 1) := by
    rw [starRingEnd_apply]
    exact (hH.apply 1 0).symm
  rw [h10]
  have hn :
      Complex.normSq (starRingEnd ℂ (ρ.carrier 0 1)) = Complex.normSq (ρ.carrier 0 1) := by
    rw [starRingEnd_apply, star_def, Complex.normSq_conj]
  rw [hn]
  ring

/-- For a qubit with nonzero off-diagonal, `RCC_purity = ‖ρ₀₁‖² / (p₀ p₁)`. -/
theorem residualCoherenceCapacity_purity_qubit (ρ : DensityMatrix hnQubit)
    (h : diagonalPurity ρ < 1) :
    residualCoherenceCapacity_purity ρ h =
      Complex.normSq (ρ.carrier 0 1) / ((ρ.carrier 0 0).re * (ρ.carrier 1 1).re) := by
  have hp0 : (ρ.carrier 0 0).re ≠ 0 := by
    intro hz
    have hsum := DensityMat.trace_re_eq_one_n ρ
    rw [Fin.sum_univ_two] at hsum
    simp [hz] at hsum
    have hone : diagonalPurity ρ = 1 := by
      rw [diagonalPurity_qubit, hz]; simp [pow_two, hsum]
    linarith [h, hone]
  have hp1 : (ρ.carrier 1 1).re ≠ 0 := by
    intro hz
    have hsum := DensityMat.trace_re_eq_one_n ρ
    rw [Fin.sum_univ_two] at hsum
    have h0 : (ρ.carrier 0 0).re = 1 := by linarith [hsum, hz]
    have hone : diagonalPurity ρ = 1 := by
      rw [diagonalPurity_qubit, hz, h0]; simp [pow_two]
    linarith [h, hone]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hden : 2 * (ρ.carrier 0 0).re * (ρ.carrier 1 1).re ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 hp0) hp1
  unfold residualCoherenceCapacity_purity
  rw [offDiagonalPurity_qubit, one_sub_diagonalPurity_qubit]
  field_simp [hden]
  ring

end UMST.Quantum

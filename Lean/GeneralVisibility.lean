-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import MeasurementChannel
import QuantumClassicalBridge
import GeneralResidualCoherence
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Abs
import Mathlib.Data.Real.Sqrt

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace UMST.Quantum

variable {n : ℕ} (hn : 0 < n)

/-- The l1-norm of coherence is the sum of the absolute values of the off-diagonal elements. -/
noncomputable def coherenceL1 (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℝ) else Complex.abs (ρ i j)

/-- `fringeVisibility_n` generalizes the Double-Slit visibility `V = 2|ρ_01|`
to arbitrary dimensions. It is normalized by `n - 1` so that `0 ≤ V_n ≤ 1`. -/
noncomputable def fringeVisibility_n (ρ : DensityMatrix hn) : ℝ :=
  if _ : n = 1 then
    0
  else
    coherenceL1 ρ.carrier / (n - 1 : ℝ)

theorem fringeVisibility_n_nonneg (ρ : DensityMatrix hn) : 0 ≤ fringeVisibility_n hn ρ := by
  unfold fringeVisibility_n coherenceL1
  split_ifs with h1
  · rfl
  · apply div_nonneg
    · apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro j _
      split_ifs
      · rfl
      · exact Complex.abs.nonneg _
    · have h_gt_one : 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt hn) (Ne.symm h1)
      have h_ge_two : 2 ≤ n := Nat.succ_le_of_lt h_gt_one
      have hnR : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_ge_two
        linarith
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hnR

/-! ## `coherenceL1 ≤ n - 1` (hence `fringeVisibility_n ≤ 1`)

Uses `normSq_entry_le_diag_mul` (PSD Schur bound), Cauchy–Schwarz on `∑ √pᵢ`, and
`(∑ᵢ √pᵢ)² - ∑ᵢ pᵢ = ∑_{i≠j} √(pᵢ pⱼ)` for `pᵢ = (ρᵢᵢ).re`. -/

/-- A positive semidefinite `2 × 2` complex matrix has nonnegative determinant: `det B = λ₀ λ₁` with `λᵢ ≥ 0`. -/
theorem posSemidef_det_nonneg_fin_two (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B.PosSemidef) : 0 ≤ det B := by
  rw [hB.1.det_eq_prod_eigenvalues, Fin.prod_univ_two]
  exact mul_nonneg (Complex.zero_le_real.mpr (hB.eigenvalues_nonneg 0))
    (Complex.zero_le_real.mpr (hB.eigenvalues_nonneg 1))

/-- The `2 × 2` principal minor on rows and columns `i, j`: `det = ρᵢᵢ ρⱼⱼ - ρᵢⱼ ρⱼᵢ`. -/
theorem det_submatrix_two (ρ : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    det (ρ.submatrix ![i, j] ![i, j]) = ρ i i * ρ j j - ρ i j * ρ j i := by
  rw [Matrix.det_fin_two]
  simp

theorem abs_entry_le_sqrt_diag_mul (ρ : DensityMatrix hn) (i j : Fin n) :
    Complex.abs (ρ.carrier i j) ≤ Real.sqrt ((ρ.carrier i i).re * (ρ.carrier j j).re) := by
  have hnsq := normSq_entry_le_diag_mul ρ i j
  have hsq : (Complex.abs (ρ.carrier i j)) ^ 2 ≤ (ρ.carrier i i).re * (ρ.carrier j j).re := by
    simpa [Complex.sq_abs] using hnsq
  exact Real.le_sqrt_of_sq_le hsq

/-- Each `|ρᵢⱼ|` is bounded by `√(ρᵢᵢ ρⱼⱼ)`, so the coherence `ℓ₁` norm is bounded by the off-diagonal double sum
of `√(pᵢ pⱼ)` over the Born weights `pᵢ = (ρᵢᵢ).re`. -/
theorem coherenceL1_le_sqrtDoubleSum (ρ : DensityMatrix hn) :
    coherenceL1 ρ.carrier ≤
      ∑ i : Fin n, ∑ j : Fin n,
        if i = j then (0 : ℝ) else Real.sqrt ((ρ.carrier i i).re * (ρ.carrier j j).re) := by
  unfold coherenceL1
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · rfl
  · exact @abs_entry_le_sqrt_diag_mul n hn ρ i j

/-- For weights `pᵢ ≥ 0` summing to one, the off-diagonal double sum of `√(pᵢ pⱼ)` is `(∑ᵢ √pᵢ)² - 1`. -/
theorem sqrt_doubleSum_eq_sq_sub_one (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i : Fin n, p i = 1) :
    (∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℝ) else Real.sqrt (p i * p j)) =
      (∑ i : Fin n, Real.sqrt (p i)) ^ 2 - 1 := by
  have h_sqrt_mul : ∀ i j, Real.sqrt (p i * p j) = Real.sqrt (p i) * Real.sqrt (p j) := fun i j =>
    Real.sqrt_mul (hp i) (p j)
  have h_grid : (∑ i : Fin n, ∑ j : Fin n, Real.sqrt (p i * p j)) = (∑ i, Real.sqrt (p i)) ^ 2 := by
    simp_rw [h_sqrt_mul]
    rw [pow_two, ← Finset.sum_mul_sum]
  have h_inner (i : Fin n) : (∑ j : Fin n, if i = j then p i else 0) = p i := by
    rw [Finset.sum_ite_eq Finset.univ i (fun _ => p i), if_pos (Finset.mem_univ i)]
  have h_diag_sum : (∑ i : Fin n, ∑ j : Fin n, if i = j then p i else 0) = 1 := by
    rw [Finset.sum_congr rfl fun i _ => h_inner i]
    exact hsum
  have hpt (i j : Fin n) :
      (Real.sqrt (p i * p j) - (if i = j then p i else (0 : ℝ))) =
        (if i = j then (0 : ℝ) else Real.sqrt (p i * p j)) := by
    by_cases h : i = j
    · rcases h with rfl
      simp [Real.sqrt_mul_self (hp i)]
    · simp [if_neg h]
  calc
    (∑ i, ∑ j, if i = j then 0 else Real.sqrt (p i * p j))
        = ∑ i, ∑ j, (Real.sqrt (p i * p j) - if i = j then p i else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hpt i j).symm
    _ = (∑ i, ∑ j, Real.sqrt (p i * p j)) - ∑ i, ∑ j, (if i = j then p i else 0) := by
          simp_rw [Finset.sum_sub_distrib]
    _ = (∑ i, Real.sqrt (p i)) ^ 2 - 1 := by rw [h_grid, h_diag_sum]

/-- Cauchy–Schwarz on `∑ᵢ 1 · √pᵢ`: for weights `pᵢ ≥ 0` summing to one, `(∑ᵢ √pᵢ)² ≤ n`. -/
theorem sum_sqrt_sq_le_card (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i : Fin n, p i = 1) :
    (∑ i : Fin n, Real.sqrt (p i)) ^ 2 ≤ (n : ℝ) := by
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun _ : Fin n => (1 : ℝ)) (fun i => Real.sqrt (p i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hcs
  have hsum_sq : ∑ i : Fin n, (Real.sqrt (p i)) ^ 2 = 1 := by
    simp_rw [Real.sq_sqrt (hp _), hsum]
  simpa [hsum_sq, mul_one] using hcs

/-- For weights `pᵢ ≥ 0` summing to one, the off-diagonal double sum of `√(pᵢ pⱼ)` is at most `n - 1`. -/
theorem sqrt_doubleSum_le_pred (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i : Fin n, p i = 1) :
    (∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℝ) else Real.sqrt (p i * p j)) ≤ (n - 1 : ℝ) := by
  rw [sqrt_doubleSum_eq_sq_sub_one p hp hsum]
  linarith [sum_sqrt_sq_le_card p hp hsum]

/-- The coherence `ℓ₁` norm of a density matrix is at most `n - 1`. -/
theorem coherenceL1_carrier_le (ρ : DensityMatrix hn) :
    coherenceL1 ρ.carrier ≤ (n - 1 : ℝ) :=
  le_trans (coherenceL1_le_sqrtDoubleSum hn ρ)
    (sqrt_doubleSum_le_pred (fun i => (ρ.carrier i i).re) (fun i => DensityMat.diag_re_nonneg_n ρ i)
      (DensityMat.trace_re_eq_one_n ρ))

/-- Fringe visibility is at most $1$: coherence $\ell_1$ is $\le n-1$ by the PSD–Schur and
Cauchy–Schwarz argument in `coherenceL1_carrier_le`.

For the qubit `fringeVisibility` (bridge layer), see
`QuantumClassicalBridge.fringeVisibility_le_one`. -/
theorem fringeVisibility_n_le_one (ρ : DensityMatrix hn) : fringeVisibility_n hn ρ ≤ 1 := by
  unfold fringeVisibility_n
  split_ifs with h1
  · norm_num
  · have h_gt_one : 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt hn) (Ne.symm h1)
    have h_ge_two : 2 ≤ n := Nat.succ_le_of_lt h_gt_one
    have hden : 0 < (n - 1 : ℝ) := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_ge_two
      linarith
    have hcoh := @coherenceL1_carrier_le n hn ρ
    rw [div_le_one hden]
    exact hcoh

@[simp]
theorem fringeVisibility_n_whichPath_apply (ρ : DensityMatrix hnQubit) :
    fringeVisibility_n hnQubit (KrausChannel.whichPathChannel.apply hnQubit ρ) = 0 := by
  unfold fringeVisibility_n
  simp [show ¬(2 : ℕ) = 1 from by norm_num]
  unfold coherenceL1
  have hcar :
      (KrausChannel.whichPathChannel.apply hnQubit ρ).carrier =
        KrausChannel.whichPathChannel.map ρ.carrier :=
    rfl
  rw [hcar, KrausChannel.whichPath_map_eq_diagonal ρ.carrier]
  have hzero :
      ∑ i : Fin 2, ∑ j : Fin 2, ite (i = j) (0 : ℝ) (Complex.abs (diagonal (fun k => ρ.carrier k k) i j)) =
        0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Matrix.diagonal_apply, Matrix.of_apply]
  rw [hzero]
  simp

end UMST.Quantum

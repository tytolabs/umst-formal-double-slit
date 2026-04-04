/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
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

theorem abs_entry_le_sqrt_diag_mul (ρ : DensityMatrix hn) (i j : Fin n) :
    Complex.abs (ρ.carrier i j) ≤ Real.sqrt ((ρ.carrier i i).re * (ρ.carrier j j).re) := by
  have hnsq := normSq_entry_le_diag_mul ρ i j
  have hsq : (Complex.abs (ρ.carrier i j)) ^ 2 ≤ (ρ.carrier i i).re * (ρ.carrier j j).re := by
    simpa [Complex.sq_abs] using hnsq
  exact Real.le_sqrt_of_sq_le hsq

theorem coherenceL1_carrier_le (ρ : DensityMatrix hn) :
    coherenceL1 ρ.carrier ≤ (n - 1 : ℝ) := by
  classical
  let p : Fin n → ℝ := fun i => (ρ.carrier i i).re
  have hp_nn : ∀ i, 0 ≤ p i := fun i => DensityMat.diag_re_nonneg_n ρ i
  have hp_sum : (∑ i : Fin n, p i) = 1 := DensityMat.trace_re_eq_one_n ρ
  have h_step1 :
      coherenceL1 ρ.carrier ≤ ∑ i, ∑ j, if i = j then (0 : ℝ) else Real.sqrt (p i * p j) := by
    unfold coherenceL1
    refine Finset.sum_le_sum ?_
    intro i _
    refine Finset.sum_le_sum ?_
    intro j _
    split_ifs with h_ij
    · rfl
    · exact @abs_entry_le_sqrt_diag_mul n hn ρ i j
  have h_sqrt_mul : ∀ i j, Real.sqrt (p i * p j) = Real.sqrt (p i) * Real.sqrt (p j) := by
    intro i j; rw [Real.sqrt_mul (hp_nn i) (p j)]
  have h_grid : (∑ i : Fin n, ∑ j : Fin n, Real.sqrt (p i * p j)) = (∑ i, Real.sqrt (p i)) ^ 2 := by
    simp_rw [h_sqrt_mul]
    rw [pow_two, ← Finset.sum_mul_sum]
  have h_inner (i : Fin n) : (∑ j : Fin n, if i = j then p i else 0) = p i := by
    have hs :=
      Finset.sum_eq_single_of_mem (s := Finset.univ) (f := fun j => if i = j then p i else 0) i
        (Finset.mem_univ _) fun j _ hj => by simp [if_neg (Ne.symm hj)]
    rw [hs]
    simp [if_pos rfl]
  have h_diag_sum : (∑ i : Fin n, ∑ j : Fin n, if i = j then p i else 0) = 1 := by
    rw [Finset.sum_congr rfl fun i _ => h_inner i]
    exact hp_sum
  have h_off :
      (∑ i, ∑ j, if i = j then (0 : ℝ) else Real.sqrt (p i * p j)) =
        (∑ i, Real.sqrt (p i)) ^ 2 - 1 := by
    have hpt (i j : Fin n) :
        (Real.sqrt (p i * p j) - (if i = j then p i else (0 : ℝ))) =
          (if i = j then (0 : ℝ) else Real.sqrt (p i * p j)) := by
      by_cases h : i = j
      · rcases h with rfl
        simp [if_pos rfl, Real.sqrt_mul (hp_nn i) (p i), Real.mul_self_sqrt (hp_nn i), sub_self]
      · simp [if_neg h]
    calc
      (∑ i, ∑ j, if i = j then 0 else Real.sqrt (p i * p j))
          = ∑ i, ∑ j, (Real.sqrt (p i * p j) - if i = j then p i else 0) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hpt i j).symm
      _ = (∑ i, ∑ j, Real.sqrt (p i * p j)) - ∑ i, ∑ j, (if i = j then p i else 0) := by
            simp_rw [Finset.sum_sub_distrib]
      _ = (∑ i, Real.sqrt (p i)) ^ 2 - 1 := by rw [h_grid, h_diag_sum]
  have h_cauchy : (∑ i : Fin n, Real.sqrt (p i)) ^ 2 ≤ (n : ℝ) := by
    have hcs :=
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
        (fun _ : Fin n => (1 : ℝ)) (fun i => Real.sqrt (p i))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hcs
    have hsq : ∀ i : Fin n, (Real.sqrt (p i)) ^ 2 = p i := fun i => Real.sq_sqrt (hp_nn i)
    have hsum_sq : ∑ i : Fin n, (Real.sqrt (p i)) ^ 2 = 1 := by simp_rw [hsq, hp_sum]
    simpa [hsum_sq, mul_one] using hcs
  have h_off_le : (∑ i, ∑ j, if i = j then (0 : ℝ) else Real.sqrt (p i * p j)) ≤ (n - 1 : ℝ) := by
    rw [h_off]
    linarith [h_cauchy]
  exact le_trans h_step1 h_off_le

/-- Fringe visibility is at most $1$: coherence $\ell_1$ is $\le n-1$ by the PSD–Schur and
Cauchy–Schwarz argument in `coherenceL1_carrier_le`.

For the qubit `fringeVisibility` (Paper 4 / bridge layer), see
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

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import MeasurementChannel
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Abs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases

open scoped Matrix ComplexOrder BigOperators
open Matrix Fintype Finset

namespace UMST.Quantum

variable {n : ℕ} (hn : 0 < n)

open DensityMat

/-- The l1-norm of coherence is the sum of the absolute values of the off-diagonal elements. -/
noncomputable def coherenceL1 (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℝ) else Complex.abs (ρ i j)

/-- `fringeVisibility_n` generalizes the Double-Slit visibility `V = 2|ρ_01|`
to arbitrary dimensions. It is normalized by `n - 1` so that `0 ≤ V_n ≤ 1`. -/
noncomputable def fringeVisibility_n (ρ : DensityMatrix hn) : ℝ :=
  if h1 : n = 1 then
    0
  else
    coherenceL1 ρ.carrier / (n - 1 : ℝ)

theorem fringeVisibility_n_nonneg (ρ : DensityMatrix hn) : 0 ≤ fringeVisibility_n hn ρ := by
  unfold fringeVisibility_n coherenceL1
  split_ifs
  · rfl
  · apply div_nonneg
    · apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro j _
      split_ifs
      · rfl
      · exact Complex.abs.nonneg _
    · have h_gt_one : 1 < n := by
        obtain ⟨n_val, rfl⟩ : ∃ k, n = k := ⟨n, rfl⟩
        omega
      norm_cast
      linarith

/-! ### PSD principal 2×2 minors: `|ρ_ij|² ≤ ρ_ii ρ_jj` (via `det ≥ 0`) -/

private lemma prod_fin_two {α : Type*} [CommMonoid α] (f : Fin 2 → α) :
    ∏ k : Fin 2, f k = f 0 * f 1 := by
  rw [Fintype.prod_eq_mul (0 : Fin 2) (1 : Fin 2) (by simp)]
  · intro x ⟨_, _⟩; fin_cases x <;> simp at *
  · rfl

private lemma complex_prod_fin_two_nonneg (f : Fin 2 → ℝ) (hf : ∀ k, 0 ≤ f k) :
    0 ≤ (∏ k : Fin 2, (f k : ℂ)) := by
  rw [prod_fin_two]
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · simp_rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_self]
    exact mul_nonneg (hf 0) (hf 1)
  · simp_rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]

private lemma posSemidef_det_nonneg_fin_two (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B.PosSemidef) : 0 ≤ det B := by
  classical
  rw [hB.1.det_eq_prod_eigenvalues, prod_fin_two]
  exact complex_prod_fin_two_nonneg _ fun k => hB.eigenvalues_nonneg k

private lemma det_submatrix_two (ρ : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    det (ρ.submatrix ![i, j] ![i, j]) =
      ρ i i * ρ j j - ρ i j * ρ j i := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma diag_eq_ofReal_re {ρ : DensityMatrix hn} (k : Fin n) :
    ρ.carrier k k = Complex.ofReal (ρ.carrier k k).re := by
  rw [Complex.ext_iff, diag_im_zero_n ρ k]
  simp

private lemma offDiag_normSq_le_diag_re_mul (ρ : DensityMatrix hn) {i j : Fin n} (hij : i ≠ j) :
    Complex.normSq (ρ.carrier i j) ≤ (ρ.carrier i i).re * (ρ.carrier j j).re := by
  let B := ρ.carrier.submatrix ![i, j] ![i, j]
  have hB : B.PosSemidef := ρ.psd.submatrix ![i, j] ![i, j]
  have hdet := posSemidef_det_nonneg_fin_two B hB
  have hdet_eq : det B =
      Complex.ofReal ((ρ.carrier i i).re * (ρ.carrier j j).re - Complex.normSq (ρ.carrier i j)) := by
    rw [det_submatrix_two ρ.carrier i j]
    have hherm : ρ.carrier j i = star (ρ.carrier i j) :=
      congrFun (congrFun (DensityMat.isHermitian ρ).symm j) i
    rw [hherm, Complex.star_def, Complex.mul_conj]
    have hii : ρ.carrier i i = Complex.ofReal (ρ.carrier i i).re := diag_eq_ofReal_re ρ i
    have hjj : ρ.carrier j j = Complex.ofReal (ρ.carrier j j).re := diag_eq_ofReal_re ρ j
    rw [hii, hjj, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    congr 1
    simp [Complex.normSq_apply]
  rw [hdet_eq] at hdet
  have := (Complex.nonneg_iff.mp hdet).1
  simpa using this

private lemma offDiag_abs_le_sqrt_diag (ρ : DensityMatrix hn) {i j : Fin n} (hij : i ≠ j) :
    Complex.abs (ρ.carrier i j) ≤
      Real.sqrt ((ρ.carrier i i).re * (ρ.carrier j j).re) := by
  have hsq : Complex.abs (ρ.carrier i j) ^ 2 ≤ (ρ.carrier i i).re * (ρ.carrier j j).re := by
    rw [Complex.sq_abs]
    exact offDiag_normSq_le_diag_re_mul ρ hij
  exact Real.le_sqrt_of_sq_le hsq

/-! ### Cauchy–Schwarz: `(∑ √p_i)² ≤ n` when `p_i ≥ 0` and `∑ p_i = 1` -/

private lemma sum_sqrt_sq_le_card (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∑ i : Fin n, Real.sqrt (p i)) ^ 2 ≤ (Fintype.card (Fin n) : ℝ) := by
  have hp2 := Real.isConjExponent_two
  have h :=
    Real.inner_le_Lp_mul_Lq (ι := Fin n) (s := univ) (f := fun i => Real.sqrt (p i))
      (g := fun _ => (1 : ℝ)) hp2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_one,
    Real.rpow_two, Real.sq_sqrt (hp _), Finset.mul_one] at h
  nlinarith [h]

private lemma coherenceL1_le_sqrtDoubleSum (ρ : DensityMatrix hn) :
    coherenceL1 ρ.carrier ≤
      ∑ i : Fin n, ∑ j : Fin n,
        if i = j then (0 : ℝ) else Real.sqrt ((ρ.carrier i i).re * (ρ.carrier j j).re) := by
  unfold coherenceL1
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ↓reduceIte]
    exact offDiag_abs_le_sqrt_diag ρ hij

private lemma sqrt_doubleSum_eq_sq_sub_one (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i : Fin n, p i = 1) :
    (∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℝ) else Real.sqrt (p i * p j)) =
      (∑ i : Fin n, Real.sqrt (p i)) ^ 2 - 1 := by
  simp_rw [Real.sqrt_mul (hp _)]
  let a : Fin n → ℝ := fun i => Real.sqrt (p i)
  have ha2 : ∀ i, a i ^ 2 = p i := fun i => Real.sq_sqrt (hp i)
  have step (i : Fin n) :
      ∑ j, (if i = j then (0 : ℝ) else a i * a j) = a i * ∑ j, a j - a i ^ 2 := by
    have h1 :
        ∑ j, (if i = j then (0 : ℝ) else a i * a j) + a i ^ 2 = a i * ∑ j, a j := by
      rw [← Finset.sum_add_distrib]
      simp_rw [show ∀ j,
          (if i = j then (0 : ℝ) else a i * a j) + (if i = j then a i * a j else 0) = a i * a j by
          intro j; split_ifs with h <;> simp [h, sq] <;> ring]
      rw [Finset.sum_mul]
    linarith
  calc
    ∑ i, ∑ j, if i = j then (0 : ℝ) else a i * a j
        = ∑ i, (a i * ∑ j, a j - a i ^ 2) := by simp_rw [step]
    _ = (∑ i, a i) * ∑ j, a j - ∑ i, a i ^ 2 := by
          rw [Finset.sum_sub_distrib]
          congr 1
          · rw [← Finset.sum_mul]
          · rfl
    _ = (∑ i, a i) ^ 2 - ∑ i, p i := by rw [sq, Finset.sum_congr rfl ha2]
    _ = (∑ i, a i) ^ 2 - 1 := by rw [hsum]

private lemma sqrt_doubleSum_le_pred (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i : Fin n, p i = 1) :
    ∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℝ) else Real.sqrt (p i * p j) ≤ n - 1 := by
  rw [sqrt_doubleSum_eq_sq_sub_one p hp hsum]
  have hcard : (Fintype.card (Fin n) : ℝ) = n := by simp
  have hsq := sum_sqrt_sq_le_card p hp
  rw [hcard] at hsq
  linarith

private lemma coherenceL1_le_pred (ρ : DensityMatrix hn) (_hne : n ≠ 1) :
    coherenceL1 ρ.carrier ≤ n - 1 := by
  let p : Fin n → ℝ := fun i => (ρ.carrier i i).re
  have hp : ∀ i, 0 ≤ p i := fun i => diag_re_nonneg_n ρ i
  have hsum : ∑ i, p i = 1 := trace_re_eq_one_n ρ
  refine le_trans (coherenceL1_le_sqrtDoubleSum ρ) ?_
  simpa [p] using sqrt_doubleSum_le_pred p hp hsum

/-- The $l_1$ norm of coherence is upper-bounded by $n - 1$ for any density matrix. -/
theorem fringeVisibility_n_le_one (ρ : DensityMatrix hn) : fringeVisibility_n hn ρ ≤ 1 := by
  unfold fringeVisibility_n
  split_ifs with h1
  · norm_num
  · rw [div_le_one_iff₀]
    swap
    · have : 1 < n := by
        obtain ⟨n_val, rfl⟩ : ∃ k, n = k := ⟨n, rfl⟩
        omega
      norm_cast
      linarith
    exact_mod_cast coherenceL1_le_pred ρ h1

@[simp]
theorem fringeVisibility_n_whichPath_apply (ρ : DensityMatrix hn) :
    fringeVisibility_n hn (KrausChannel.whichPathChannel.apply hn ρ) = 0 := by
  unfold fringeVisibility_n
  split_ifs
  · rfl
  · unfold coherenceL1
    have hzero : ∑ i : Fin n, ∑ j : Fin n, ite (i = j) (0 : ℝ) (Complex.abs ((KrausChannel.whichPathChannel.apply hn ρ).carrier i j)) = 0 := by
      apply Finset.sum_eq_zero; intro i _
      apply Finset.sum_eq_zero; intro j _
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, KrausChannel.whichPathChannel.apply, KrausChannel.apply_entry_ne]
    rw [hzero]
    simp

end UMST.Quantum

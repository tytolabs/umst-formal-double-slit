/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix ComplexOrder BigOperators

variable {n : ℕ} (hn : 0 < n)
local notation "ℂⁿ" => Fin n → ℂ

structure DensityMatrix : Type where
  carrier : Matrix (Fin n) (Fin n) ℂ
  psd : carrier.PosSemidef
  trace_one : Matrix.trace carrier = 1

theorem smul_psd {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (r : ℝ) (hr : 0 ≤ r) :
  ((r : ℂ) • M).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.smul_apply, Matrix.conjTranspose_apply, star_smul]
    have h1 : M i j = star (M j i) := by
      exact (congrFun (congrFun hM.1.symm i) j)
    have hr_conj : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
    rw [hr_conj, h1]
  · intro x
    have h1 := hM.2 x
    have step1 : Matrix.dotProduct (star x) (((r : ℂ) • M) *ᵥ x) = (r : ℂ) * Matrix.dotProduct (star x) (M *ᵥ x) := by
      dsimp [Matrix.dotProduct, Matrix.mulVec, Matrix.smul_apply, Pi.smul_apply]
      calc
        (∑ i : Fin n, star (x i) * ∑ j : Fin n, ((r : ℂ) * M i j) * x j)
          = ∑ i : Fin n, star (x i) * ∑ j : Fin n, (r : ℂ) * (M i j * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = ∑ i : Fin n, star (x i) * ((r : ℂ) * ∑ j : Fin n, M i j * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            exact Eq.symm (Finset.mul_sum (Finset.univ : Finset (Fin n)) (fun j => M i j * x j) (r : ℂ))
        _ = ∑ i : Fin n, (r : ℂ) * (star (x i) * ∑ j : Fin n, M i j * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = (r : ℂ) * ∑ i : Fin n, star (x i) * ∑ j : Fin n, M i j * x j := by
            exact Eq.symm (Finset.mul_sum (Finset.univ : Finset (Fin n)) (fun i => star (x i) * ∑ j : Fin n, M i j * x j) (r : ℂ))
    rw [step1]
    exact mul_nonneg (Complex.zero_le_real.mpr hr) h1

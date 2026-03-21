/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import MeasurementChannel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

/-- The $l_1$ norm of coherence is upper-bounded by $n - 1$ for any density matrix. -/
axiom fringeVisibility_n_le_one (ρ : DensityMatrix hn) : fringeVisibility_n hn ρ ≤ 1

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

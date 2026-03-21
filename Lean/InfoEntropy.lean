/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Fin
import QuantumClassicalBridge

/-!
# InfoEntropy — binary Shannon / diagonal von Neumann entropy (qubit path bit)

Uses `Real.negMulLog` so **`0 · log 0 = 0`** by definition.

For a qubit density matrix, the von Neumann entropy equals the Shannon entropy of the spectrum; in
particular it equals **`shannonBinary (pathWeight ρ 0)`** because `pathWeight ρ 1 = 1 - pathWeight ρ 0`.

**Agrees with Mathlib:** `shannonBinary p = Real.binEntropy p` (`shannonBinary_eq_binEntropy`). Hence
**`shannonBinary p ≤ log 2`** and **`vonNeumannDiagonal ρ ≤ log 2`** (nats).

**General `n` bound:** `vonNeumannDiagonal_n_le_log_n` in **`GeneralDimension.lean`**. **`vonNeumannDiagonal_n_eq_vonNeumannDiagonal`:** on a qubit, `vonNeumannDiagonal_n` = `vonNeumannDiagonal`. **Landauer:** `pathEntropyBits_n`, `landauerCostDiagonal_n_*` in **`LandauerBound.lean`**. **Not yet:** quantum mutual information, DPI.
-/

namespace UMST.Quantum

open Real
open scoped BigOperators

/-- Binary Shannon entropy `H₂(p) = -p log p - (1-p) log(1-p)` with `0 log 0 = 0`. -/
noncomputable def shannonBinary (p : ℝ) : ℝ :=
  negMulLog p + negMulLog (1 - p)

theorem shannonBinary_eq_binEntropy (p : ℝ) : shannonBinary p = binEntropy p := by
  rw [shannonBinary, ← binEntropy_eq_negMulLog_add_negMulLog_one_sub p]

theorem shannonBinary_le_log_two (p : ℝ) : shannonBinary p ≤ log 2 := by
  rw [shannonBinary_eq_binEntropy]
  exact binEntropy_le_log_two

theorem shannonBinary_symm (p : ℝ) : shannonBinary p = shannonBinary (1 - p) := by
  unfold shannonBinary
  abel

theorem pathWeight_le_one (ρ : DensityMatrix hnQubit) (i : Fin 2) : pathWeight ρ i ≤ 1 := by
  fin_cases i
  · have hs := pathWeight_sum ρ
    have h1 := pathWeight_nonneg' ρ 1
    linarith
  · have hs := pathWeight_sum ρ
    have h0 := pathWeight_nonneg' ρ 0
    linarith

/-- Diagonal / spectrum entropy for the path qubit (nats; same functional form as `S(ρ)` here). -/
noncomputable def vonNeumannDiagonal (ρ : DensityMatrix hnQubit) : ℝ :=
  shannonBinary (pathWeight ρ 0)

theorem vonNeumannDiagonal_eq_shannon_path1 (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal ρ = shannonBinary (pathWeight ρ 1) := by
  unfold vonNeumannDiagonal
  have hs := pathWeight_sum ρ
  have : pathWeight ρ 0 = 1 - pathWeight ρ 1 := by linarith
  rw [this, shannonBinary_symm]

theorem vonNeumannDiagonal_nonneg (ρ : DensityMatrix hnQubit) : 0 ≤ vonNeumannDiagonal ρ := by
  unfold vonNeumannDiagonal shannonBinary
  have h0 := pathWeight_nonneg' ρ 0
  have hle := pathWeight_le_one ρ 0
  have h1 : 0 ≤ 1 - pathWeight ρ 0 := by linarith [pathWeight_sum ρ, pathWeight_nonneg' ρ 1]
  have h1le : 1 - pathWeight ρ 0 ≤ 1 := by linarith [pathWeight_nonneg' ρ 0]
  exact add_nonneg (negMulLog_nonneg h0 hle) (negMulLog_nonneg h1 h1le)

/-- General diagonal von Neumann entropy (nats) for arbitrary dimension n -/
noncomputable def vonNeumannDiagonal_n {n : ℕ} {hn : 0 < n} (ρ : DensityMatrix hn) : ℝ :=
  ∑ i : Fin n, negMulLog (ρ.carrier i i).re

theorem vonNeumannDiagonal_n_nonneg {n : ℕ} {hn : 0 < n} (ρ : DensityMatrix hn) : 0 ≤ vonNeumannDiagonal_n ρ := by
  apply Finset.sum_nonneg
  intro i _
  have h0 : 0 ≤ (ρ.carrier i i).re := DensityMat.diag_re_nonneg_n ρ i
  have h1 : (ρ.carrier i i).re ≤ 1 := DensityMat.diag_re_le_one_n ρ i
  exact negMulLog_nonneg h0 h1

/-- On a qubit, the `Fin 2` diagonal sum agrees with the binary Shannon functional on `pathWeight`. -/
theorem vonNeumannDiagonal_n_eq_vonNeumannDiagonal (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal_n ρ = vonNeumannDiagonal ρ := by
  have hdiag1 : (ρ.carrier 1 1).re = 1 - (ρ.carrier 0 0).re := by
    simpa [pathWeight, add_comm, add_left_comm, add_assoc] using (pathWeight_sum ρ)
  unfold vonNeumannDiagonal vonNeumannDiagonal_n shannonBinary
  rw [Fin.sum_univ_two, hdiag1, pathWeight]

theorem vonNeumannDiagonal_le_log_two (ρ : DensityMatrix hnQubit) : vonNeumannDiagonal ρ ≤ log 2 := by
  unfold vonNeumannDiagonal
  exact shannonBinary_le_log_two _

@[simp]
theorem vonNeumannDiagonal_whichPath_apply (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) = vonNeumannDiagonal ρ := by
  simp [vonNeumannDiagonal, shannonBinary, pathWeight_whichPath_apply]

/-! ### Quantum mutual information (diagonal / path-observable) -/

/-- **Quantum mutual information** for the path observable (diagonal form, nats).
For a qubit density matrix, this measures the information gain from path measurement:
`I(ρ) = S_diag(ρ) - S(ρ_post)`, where `S_diag` is the diagonal entropy and `S(ρ_post)` is the
post-measurement entropy. Since measurement diagonalizes the state,
`S(ρ_post) = S_diag(ρ)` and `I(ρ) = S_diag(ρ)` for a complete path measurement.

For partial measurements (fractional probes), MI is defined via `EpistemicMI.lean`. -/
noncomputable def quantumMutualInfo_diagonal (ρ : DensityMatrix hnQubit) : ℝ :=
  vonNeumannDiagonal ρ

/-- Quantum MI for path measurement is nonneg (since diagonal entropy is nonneg). -/
theorem quantumMutualInfo_diagonal_nonneg (ρ : DensityMatrix hnQubit) :
    0 ≤ quantumMutualInfo_diagonal ρ :=
  vonNeumannDiagonal_nonneg ρ

/-- Quantum MI for path measurement is bounded by log 2 (1 bit in nats). -/
theorem quantumMutualInfo_diagonal_le_log_two (ρ : DensityMatrix hnQubit) :
    quantumMutualInfo_diagonal ρ ≤ log 2 :=
  vonNeumannDiagonal_le_log_two ρ

/-- Measurement-invariant: `MI_diag(E(ρ)) = MI_diag(ρ)` for the which-path channel. -/
@[simp]
theorem quantumMutualInfo_diagonal_whichPath (ρ : DensityMatrix hnQubit) :
    quantumMutualInfo_diagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) =
    quantumMutualInfo_diagonal ρ :=
  vonNeumannDiagonal_whichPath_apply ρ

/-- **General quantum mutual information** for an n-dimensional path observable (diagonal form).
`I_n(ρ) = vonNeumannDiagonal_n(ρ)` — the diagonal entropy in nats. -/
noncomputable def quantumMutualInfo_diagonal_n {n : ℕ} {hn : 0 < n} (ρ : DensityMatrix hn) : ℝ :=
  vonNeumannDiagonal_n ρ

theorem quantumMutualInfo_diagonal_n_nonneg {n : ℕ} {hn : 0 < n} (ρ : DensityMatrix hn) :
    0 ≤ quantumMutualInfo_diagonal_n ρ :=
  vonNeumannDiagonal_n_nonneg ρ

/-- For qubits, `quantumMutualInfo_diagonal_n` reduces to `quantumMutualInfo_diagonal`. -/
theorem quantumMutualInfo_diagonal_n_qubit_eq (ρ : DensityMatrix hnQubit) :
    quantumMutualInfo_diagonal_n ρ = quantumMutualInfo_diagonal ρ :=
  vonNeumannDiagonal_n_eq_vonNeumannDiagonal ρ

end UMST.Quantum

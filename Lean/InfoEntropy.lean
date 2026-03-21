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

**Not yet:** general `n`, quantum mutual information, DPI.
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
  have h0 : 0 ≤ (ρ.carrier i i).re := DensityMatrix.diag_re_nonneg_n ρ i
  have h1 : (ρ.carrier i i).re ≤ 1 := DensityMatrix.diag_re_le_one_n ρ i
  exact negMulLog_nonneg h0 h1

theorem vonNeumannDiagonal_le_log_two (ρ : DensityMatrix hnQubit) : vonNeumannDiagonal ρ ≤ log 2 := by
  unfold vonNeumannDiagonal
  exact shannonBinary_le_log_two _

@[simp]
theorem vonNeumannDiagonal_whichPath_apply (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) = vonNeumannDiagonal ρ := by
  simp [vonNeumannDiagonal, shannonBinary, pathWeight_whichPath_apply]

end UMST.Quantum

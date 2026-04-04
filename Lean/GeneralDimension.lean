/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators
import InfoEntropy

/-!
# GeneralDimension — diagonal entropy in dimension `n`

`InfoEntropy` defines `vonNeumannDiagonal_n` (sum of `negMulLog` on diagonal reals). This file
proves the standard **max-entropy bound** (nats):

`vonNeumannDiagonal_n ρ ≤ log n`.

**Proof idea:** `negMulLog` is concave on `Ici 0`. Apply Jensen with uniform weights `1/n` at the
scaled points `n · ρᵢᵢ` (mean `1`), then expand `negMulLog(n·p)` algebraically.

**Not here:** quantum mutual information, DPI, or Landauer scaling specialized to `Fin n` (see gap plan).
-/

namespace UMST.Quantum

open Real Set
open scoped BigOperators

variable {n : ℕ}

private lemma negMulLog_nat_mul (hn : 0 < n) (p : ℝ) (hp : 0 ≤ p) :
    negMulLog ((n : ℝ) * p) = (n : ℝ) * negMulLog p - (n : ℝ) * p * log n := by
  by_cases hp0 : p = 0
  · subst hp0
    simp [negMulLog_zero, mul_zero, sub_self]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    calc
      negMulLog ((n : ℝ) * p)
          = -((n : ℝ) * p) * log ((n : ℝ) * p) := by simp [negMulLog]
      _ = -((n : ℝ) * p) * (log (n : ℝ) + log p) := by rw [log_mul hnne hp_pos.ne']
      _ = (n : ℝ) * negMulLog p - (n : ℝ) * p * log n := by
            simp [negMulLog, mul_add, mul_assoc, mul_comm, mul_left_comm]; abel

private lemma sum_negMulLog_scaled_diag (ρ : DensityMatrix hn) :
    ∑ i : Fin n, negMulLog ((n : ℝ) * (ρ.carrier i i).re) =
      (n : ℝ) * vonNeumannDiagonal_n ρ - (n : ℝ) * log n := by
  have hterm (i : Fin n) :
      negMulLog ((n : ℝ) * (ρ.carrier i i).re) =
        (n : ℝ) * negMulLog (ρ.carrier i i).re - (n : ℝ) * (ρ.carrier i i).re * log n :=
    negMulLog_nat_mul hn (ρ.carrier i i).re (DensityMat.diag_re_nonneg_n ρ i)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.mul_sum]
    rfl
  · have hsplit :
        ∀ i : Fin n, (n : ℝ) * (ρ.carrier i i).re * log n = ((n : ℝ) * log n) * (ρ.carrier i i).re := by
      intro i; ring
    simp_rw [hsplit, ← Finset.mul_sum, DensityMat.trace_re_eq_one_n ρ]
    ring

/-- Diagonal Shannon / von Neumann entropy (nats) is at most `log n` (uniform distribution maximizes
entropy on `n` outcomes). -/
theorem vonNeumannDiagonal_n_le_log_n {n : ℕ} {hn : 0 < n} (ρ : DensityMatrix hn) :
    vonNeumannDiagonal_n ρ ≤ log n := by
  classical
  let w : Fin n → ℝ := fun _ => (1 / n : ℝ)
  let x : Fin n → ℝ := fun i => (n : ℝ) * (ρ.carrier i i).re
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i := fun _ _ => by positivity
  have hw1 : ∑ i : Fin n, w i = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn)]
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ Ici (0 : ℝ) := by
    intro i _
    exact mul_nonneg (Nat.cast_nonneg n) (DensityMat.diag_re_nonneg_n ρ i)
  have hJ :=
    ConcaveOn.le_map_sum (𝕜 := ℝ) (E := ℝ) (β := ℝ) (s := Ici (0 : ℝ)) (f := negMulLog)
      concaveOn_negMulLog (t := Finset.univ) (w := w) (p := x) hw0 hw1 hmem
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcm : ∑ i : Fin n, w i * x i = 1 := by
    dsimp [w, x]
    simp_rw [← mul_assoc, div_mul_cancel₀ (1 : ℝ) hnne, one_mul]
    exact DensityMat.trace_re_eq_one_n ρ
  have hrhs : negMulLog (∑ i : Fin n, w i * x i) = 0 := by rw [hcm, negMulLog_one]
  have hLHS :
      ∑ i : Fin n, w i * negMulLog (x i) =
        (1 / n : ℝ) * ∑ i : Fin n, negMulLog ((n : ℝ) * (ρ.carrier i i).re) := by
    simp_rw [w, x, Finset.mul_sum]
  have hJnats : ∑ i : Fin n, negMulLog ((n : ℝ) * (ρ.carrier i i).re) ≤ 0 := by
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hJ' : ∑ i : Fin n, w i * negMulLog (x i) ≤ 0 := by
      simpa [hcm, negMulLog_one, smul_eq_mul] using hJ
    have hle :
        (1 / n : ℝ) * ∑ i : Fin n, negMulLog ((n : ℝ) * (ρ.carrier i i).re) ≤ 0 := by
      rw [← hLHS]
      simpa [smul_eq_mul] using hJ'
    let S := ∑ i : Fin n, negMulLog ((n : ℝ) * (ρ.carrier i i).re)
    calc
      S = (n : ℝ) * (S / n) := (mul_div_cancel₀ S hnne).symm
      _ = (n : ℝ) * ((1 / n : ℝ) * S) := by ring_nf
      _ ≤ (n : ℝ) * 0 := mul_le_mul_of_nonneg_left hle (le_of_lt hnpos)
      _ = 0 := mul_zero _
  have hsum := sum_negMulLog_scaled_diag ρ
  have hcomb : (n : ℝ) * vonNeumannDiagonal_n ρ - (n : ℝ) * log n ≤ 0 := by
    rw [← hsum]
    exact hJnats
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul : (n : ℝ) * vonNeumannDiagonal_n ρ ≤ (n : ℝ) * log n := by linarith [hcomb]
  exact (mul_le_mul_iff_of_pos_left hnR).1 hmul

end UMST.Quantum

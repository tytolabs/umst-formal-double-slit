-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal-Double-Slit: CompressionCost.lean

  The cost of compressing N equally likely states to one, from the second law of umst-formal:

  * the uniform distribution on N states has Shannon entropy ln N (`shannonEntropy_uniform`), so the compression
    lowers the entropy by ln N (`compressionEntropyDrop`);
  * under the second law in SI form the compression costs at least k_B T ln N joules (`compressionBoundSI`);
  * the whole bits destroyed, ⌊log₂ N⌋, never exceed that entropy (`floorBits_le_entropy`), so their Landauer
    cost ⌊log₂ N⌋ k_B T ln 2 is a lower bound on the work as well (`floorBitsCost_le_work`), attained exactly
    when N is a power of two.
-/

import LandauerLaw
import Process

open Real UMST.LandauerLaw

namespace UMST.DoubleSlit.CompressionCost

/-- The uniform distribution on `N` states has Shannon entropy `ln N`. -/
theorem shannonEntropy_uniform (N : ℕ) (hN : 0 < N) : shannonEntropy (uniformDist N hN) = log N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [shannonEntropy, uniformDist, ProbDist.mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, one_div, Real.log_inv]
  field_simp

/-- Compressing `N` equally likely states to one lowers the entropy by `ln N`. -/
theorem compressionEntropyDrop (N : ℕ) (hN : 0 < N) :
    shannonEntropy (uniformDist N hN) - shannonEntropy (diracDist (⟨0, hN⟩ : Fin N)) = log N := by
  rw [shannonEntropy_uniform, diracEntropy_zero hN, sub_zero]

/-- **Compression bound.** Under the second law in SI form, compressing `N` equally likely states to one at
    temperature `T` costs at least `k_B T ln N` joules. -/
theorem compressionBoundSI {N : ℕ} {T W : ℝ} (hT : 0 < T)
    (h : UMST.ProcessFamily.eraseSecondLawSI T hT (log N) W) : kB * T * log N ≤ W := by
  unfold UMST.ProcessFamily.eraseSecondLawSI at h
  rw [le_div_iff₀ (mul_pos kB_pos hT)] at h
  linarith [show kB * T * log N = log N * (kB * T) by ring]

/-- The whole bits destroyed never exceed the entropy: `2 ^ ⌊log₂ N⌋ ≤ N`. -/
theorem floorBits_le_entropy (N : ℕ) (hN : 0 < N) : (Nat.log2 N : ℝ) * log 2 ≤ log N := by
  have hpow : ((2 ^ Nat.log2 N : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.log2_self_le hN.ne'
  rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  apply Real.log_le_log (by positivity)
  simpa [Real.rpow_natCast] using hpow

/-- The Landauer cost of the whole bits destroyed is a lower bound on the compression work. -/
theorem floorBitsCost_le_work {N : ℕ} (hN : 0 < N) {T W : ℝ} (hT : 0 < T)
    (h : UMST.ProcessFamily.eraseSecondLawSI T hT (log N) W) : (Nat.log2 N : ℝ) * (kB * T * log 2) ≤ W := by
  have hb := compressionBoundSI hT h
  have hf := floorBits_le_entropy N hN
  have hkT : 0 ≤ kB * T := (mul_pos kB_pos hT).le
  nlinarith

/-- For a power of two the floor is exact: `N = 2 ^ b` destroys exactly `b` bits, `b ln 2 = ln N`. -/
theorem floorBits_pow_two (b : ℕ) : (Nat.log2 (2 ^ b) : ℝ) * log 2 = log ((2 ^ b : ℕ) : ℝ) := by
  rw [Nat.log2_two_pow]
  push_cast
  rw [Real.log_pow]

end UMST.DoubleSlit.CompressionCost

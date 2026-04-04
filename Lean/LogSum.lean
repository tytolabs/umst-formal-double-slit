/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.Basic

/-!
# Log-Sum Inequality

The **log-sum inequality** for non-negative `a` and strictly positive `b`:

  `∑ aᵢ log(aᵢ/bᵢ) ≥ (∑ aᵢ) log((∑ aᵢ)/(∑ bᵢ))`

Proof via `convexOn_mul_log` (Mathlib) and `ConvexOn.map_sum_le` (Jensen).
-/

set_option maxHeartbeats 1200000

open Real Finset

namespace UMST.Quantum.LogSum

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Log-sum inequality.** -/
lemma log_sum_ineq (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i)
    (_ha_sum : 0 < ∑ i, a i) :
    (∑ i, a i * log (a i / b i)) ≥ (∑ i, a i) * log ((∑ i, a i) / (∑ i, b i)) := by
  let B := ∑ i, b i
  have hB : 0 < B := Finset.sum_pos (fun i _ => hb i) univ_nonempty
  have hBne : B ≠ 0 := ne_of_gt hB
  -- Apply Jensen to f(x) = x log x (convex on [0,∞))
  -- with weights wᵢ = bᵢ/B ∈ [0,1] summing to 1, points rᵢ = aᵢ/bᵢ ∈ [0,∞)
  have hJ := convexOn_mul_log.map_sum_le
    (show ∀ i ∈ univ, (0:ℝ) ≤ b i / B from fun i _ => div_nonneg (le_of_lt (hb i)) (le_of_lt hB))
    (show ∑ i ∈ univ, b i / B = 1 from by
      change ∑ i : ι, b i / B = 1
      have : ∑ i : ι, b i / B = (∑ i : ι, b i) / B :=
        (Finset.sum_div (Finset.univ) (fun i => b i) B).symm
      rw [this]; exact div_self hBne)
    (show ∀ i ∈ univ, a i / b i ∈ Set.Ici (0:ℝ) from
      fun i _ => Set.mem_Ici.mpr (div_nonneg (ha i) (le_of_lt (hb i))))
  -- hJ has the form:
  --   (∑ᵢ (bᵢ/B) • (aᵢ/bᵢ)) * log (∑ᵢ (bᵢ/B) • (aᵢ/bᵢ))
  --   ≤ ∑ᵢ (bᵢ/B) • ((aᵢ/bᵢ) * log(aᵢ/bᵢ))
  -- Step 1: show ∑ᵢ (bᵢ/B) • (aᵢ/bᵢ) = (∑ aᵢ) / B
  have hL : ∑ i ∈ univ, (b i / B) • (a i / b i) = (∑ i, a i) / B := by
    change ∑ i : ι, (b i / B) * (a i / b i) = (∑ i, a i) / B
    have : ∀ i, (b i / B) * (a i / b i) = a i / B := fun i => by
      rw [div_mul_div_comm, mul_comm (b i), mul_div_mul_right _ _ (ne_of_gt (hb i))]
    simp_rw [this]
    exact (Finset.sum_div (Finset.univ) (fun i => a i) B).symm
  -- Step 2: show ∑ᵢ (bᵢ/B) • f(aᵢ/bᵢ) = (∑ aᵢ log(aᵢ/bᵢ)) / B
  have hR : ∑ i ∈ univ, (b i / B) • (a i / b i * log (a i / b i)) =
      (∑ i, a i * log (a i / b i)) / B := by
    change ∑ i : ι, (b i / B) * (a i / b i * log (a i / b i)) =
      (∑ i, a i * log (a i / b i)) / B
    have : ∀ i, (b i / B) * (a i / b i * log (a i / b i)) =
        (a i * log (a i / b i)) / B := fun i => by
      have hbi : (b i) ≠ 0 := ne_of_gt (hb i)
      field_simp [hbi, hBne]
      ring
    simp_rw [this]
    exact (Finset.sum_div (Finset.univ) (fun i => a i * log (a i / b i)) B).symm
  simp only [hL, hR] at hJ
  -- hJ : (∑ aᵢ)/B * log((∑ aᵢ)/B) ≤ (∑ aᵢ log(aᵢ/bᵢ))/B
  -- Multiply by B > 0 and simplify
  rw [ge_iff_le]
  have h := mul_le_mul_of_nonneg_right hJ (le_of_lt hB)
  rw [div_mul_cancel₀ _ hBne] at h
  linarith [show (∑ i, a i) / B * log ((∑ i, a i) / B) * B =
      (∑ i, a i) * log ((∑ i, a i) / B) from by
    rw [mul_comm (_ * _) B, ← mul_assoc, mul_div_cancel₀ _ hBne]]

end UMST.Quantum.LogSum

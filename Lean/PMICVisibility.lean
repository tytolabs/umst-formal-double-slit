/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import InfoEntropy
import LandauerBound
import PMICEntropyInterior

/-!
# PMICVisibility — visibility vs residual coherence (thermodynamic–optic complementarity)

**Englert (quantum):** `fringeVisibility² + whichPathDistinguishability² ≤ 1`.

**PMIC (thermodynamic diagonal hook):** we relate **fringe visibility** to
`residualCoherenceCapacity = 1 - pathEntropyBits` built from diagonal Shannon entropy.

Main target (proved):

`fringeVisibility ρ ^ 2 + residualCoherenceCapacity ρ ≤ 1`.

Proof chain (qubit path bit, `p = pathWeight ρ 0`):

1. `V² ≤ 4 p (1-p)` — PSD principal minor (`normSq_coherence_le_product`).
2. `4 p (1-p) * log 2 ≤ binEntropy p` — binary entropy lower envelope (nats); see `PMICEntropyInterior`.
   Divide by `log 2` for **bits** (`quadratic_le_entropy_bits`).
3. Hence `V² ≤ pathEntropyBits ρ` and `V² + (1 - pathEntropyBits ρ) ≤ 1`.
-/

namespace UMST.DoubleSlit

open UMST.Quantum Real

lemma log_two_pos' : 0 < log 2 :=
  log_pos (by norm_num : (1 : ℝ) < 2)

/-- Nats form: `4 x (1-x) · log 2 ≤ binEntropy x` on `Icc 0 1` (**fully proved**).

Interior `0 < x < 1/2` is `four_mul_x_one_sub_x_mul_log_two_interior` in `PMICEntropyInterior`;
`x > 1/2` uses `binEntropy_one_sub`. -/
lemma four_mul_x_one_sub_x_mul_log_two_le_binEntropy (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    4 * x * (1 - x) * log 2 ≤ binEntropy x := by
  rcases hx0.eq_or_lt with rfl | hx0'
  · simp
  rcases hx1.eq_or_lt with rfl | hx1'
  · simp [binEntropy_one]
  by_cases h : x ≤ (1 / 2 : ℝ)
  · by_cases h12 : x = (1 / 2 : ℝ)
    · subst h12
      have hq : (4 : ℝ) * (1 / 2) * (1 - (1 / 2)) * log 2 = log 2 := by ring
      have hmid : binEntropy (1 / 2 : ℝ) = log 2 := by
        rw [← inv_eq_one_div (2 : ℝ), binEntropy_two_inv]
      rw [hq, hmid]
      exact le_rfl
    · have hlt : x < (1 / 2 : ℝ) := lt_of_le_of_ne h h12
      exact four_mul_x_one_sub_x_mul_log_two_interior x hx0' hlt
  · -- `1/2 < x < 1`: reduce by symmetry `binEntropy x = binEntropy (1-x)`.
    rw [← binEntropy_one_sub x]
    have hs : 4 * x * (1 - x) * log 2 = 4 * (1 - x) * (1 - (1 - x)) * log 2 := by ring
    rw [hs]
    refine four_mul_x_one_sub_x_mul_log_two_le_binEntropy (1 - x) ?_ ?_
    · nlinarith
    · nlinarith

/-- In **bit units**, the symmetric quadratic `4 x (1-x)` is bounded by Shannon entropy
`shannonBinary x / log 2` on `x ∈ [0,1]`. -/
lemma quadratic_le_entropy_bits (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    4 * x * (1 - x) ≤ shannonBinary x / log 2 := by
  have hlog := log_two_pos'
  rw [shannonBinary_eq_binEntropy x, le_div_iff₀ hlog]
  exact four_mul_x_one_sub_x_mul_log_two_le_binEntropy x hx0 hx1

/-- **PMIC–visibility inequality:** thermodynamic residual coherence plus squared visibility
does not exceed unity (same scale as Englert, different partner than `I`). -/
theorem visibility_sq_le_coherence_capacity (ρ : DensityMatrix hnQubit) :
    fringeVisibility ρ ^ 2 + residualCoherenceCapacity ρ ≤ 1 := by
  have hp0 := pathWeight_nonneg' ρ 0
  have hp0le := pathWeight_le_one ρ 0
  have hp1 : pathWeight ρ 1 = 1 - pathWeight ρ 0 := by linarith [pathWeight_sum ρ]
  have hVsq : fringeVisibility ρ ^ 2 ≤ 4 * pathWeight ρ 0 * (1 - pathWeight ρ 0) := by
    rw [← hp1]
    unfold fringeVisibility
    rw [mul_pow, sq (2 : ℝ), ← Complex.sq_abs]
    nlinarith [normSq_coherence_le_product ρ]
  have hbits : fringeVisibility ρ ^ 2 ≤ pathEntropyBits ρ :=
    le_trans hVsq (quadratic_le_entropy_bits (pathWeight ρ 0) hp0 hp0le)
  unfold residualCoherenceCapacity
  linarith [hbits]

end UMST.DoubleSlit

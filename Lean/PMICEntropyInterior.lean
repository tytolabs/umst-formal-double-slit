-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-!
# PMIC entropy–quadratic bound on `(0, 1/2)`

Closes the interior case for
`4 * x * (1 - x) * log 2 ≤ binEntropy x` (nats), used in `PMICVisibility`.

**Idea.** For `u = (1-x)/x > 1`, set
`k(u) = (u² - 1) * log (1 + u) - u² * log u`.
Then `k(1) = 0` and `k'(u) = 2u * log ((1+u)/u) - 1 = (2/v) * log (1 + v) - 1` with `v = 1/u ∈ (0,1)`.
The elementary bound `2 * log (1 + v) > v` on `(0,1)` gives `k'(u) > 0`, hence `k(u) > 0` for `u > 1`
(MVT).  Algebraically `k ((1-x)/x) > 0` is equivalent to
`(1-x)² * log (1-x) < x² * log x`, i.e. the numerator of the derivative of
`binEntropy t / (t * (1 - t))` is negative.  Strict antitone of that ratio on `[x, 1/2]` then
implies `binEntropy x / (x * (1-x)) > 4 * log 2`.
-/

open scoped Topology

open _root_.Real Set

namespace UMST.DoubleSlit

noncomputable section

/-- Auxiliary `k` from the change of variables `u = (1-x)/x`. -/
noncomputable def entropyBoundK (u : ℝ) : ℝ :=
  (u ^ 2 - 1) * log (1 + u) - u ^ 2 * log u

/-- `log (1 + v) > v / 2` on `(0, 1]`: `log x > 1 - 1/x` for `x ≠ 1` (from `log y < y - 1` at `y = 1/x`),
and `v / (1 + v) ≥ v / 2` when `v ≤ 1`. -/
private lemma log_one_add_sub_half_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) :
    0 < log (1 + v) - v / 2 := by
  have hx : 0 < 1 + v := by linarith
  have hne : (1 + v)⁻¹ ≠ 1 := by
    intro h
    have : 1 + v = 1 := by simpa using congrArg (·⁻¹) h
    linarith
  have hlt := log_lt_sub_one_of_pos (inv_pos.mpr hx) hne
  rw [log_inv] at hlt
  have key : v / 2 ≤ 1 - (1 + v)⁻¹ := by
    rw [show 1 - (1 + v)⁻¹ = v / (1 + v) by field_simp]
    rw [div_le_div_iff₀ (by norm_num) hx]
    nlinarith
  linarith

lemma two_mul_log_one_add_gt {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : v < 2 * log (1 + v) := by
  have := log_one_add_sub_half_pos hv0 (le_of_lt hv1)
  linarith

lemma entropyBoundK_one : entropyBoundK 1 = 0 := by
  simp [entropyBoundK]

/-- `k'(u) = 2u log((1+u)/u) - 1` for `u > 0`. -/
lemma hasDerivAt_entropyBoundK {u : ℝ} (hu : 0 < u) :
    HasDerivAt entropyBoundK (2 * u * log ((1 + u) / u) - 1) u := by
  have h1pu : (1 + u) ≠ 0 := by linarith
  have hA : HasDerivAt (fun y : ℝ => (y ^ 2 - 1) * log (1 + y))
      ((2 * u) * log (1 + u) + (u ^ 2 - 1) * (1 / (1 + u))) u := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * u) u := by
      simpa using (hasDerivAt_pow 2 u).sub_const 1
    have h2 : HasDerivAt (fun y : ℝ => log (1 + y)) (1 / (1 + u)) u := by
      simpa using ((hasDerivAt_id u).const_add 1).log h1pu
    exact h1.mul h2
  have hB : HasDerivAt (fun y : ℝ => y ^ 2 * log y) ((2 * u) * log u + u ^ 2 * (1 / u)) u := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
    have h2 : HasDerivAt (fun y : ℝ => log y) (1 / u) u := by
      simpa [one_div] using hasDerivAt_log hu.ne'
    exact h1.mul h2
  have h := hA.sub hB
  convert h using 1
  rw [log_div h1pu hu.ne']
  field_simp
  ring

lemma deriv_entropyBoundK_pos {u : ℝ} (hu : 1 < u) : 0 < deriv entropyBoundK u := by
  have hu0 : 0 < u := by linarith
  rw [(hasDerivAt_entropyBoundK hu0).deriv]
  set v := u⁻¹ with hv
  have hv0 : 0 < v := inv_pos.mpr hu0
  have hv1 : v < 1 := inv_lt_one_of_one_lt₀ hu
  have hmain := two_mul_log_one_add_gt hv0 hv1
  have hdiv : (1 + u) / u = 1 + v := by rw [hv]; field_simp; ring
  rw [hdiv]
  have huv : u = 1 / v := by rw [hv, one_div, inv_inv]
  rw [huv]
  have : 1 < 2 * (1 / v) * log (1 + v) := by
    rw [show 2 * (1 / v) * log (1 + v) = (2 * log (1 + v)) / v by ring]
    exact (one_lt_div hv0).mpr hmain
  linarith

lemma differentiableOn_entropyBoundK_Ioo_one {u : ℝ} (_hu : 1 < u) :
    DifferentiableOn ℝ entropyBoundK (Ioo 1 u) := fun y hy =>
  (hasDerivAt_entropyBoundK (by linarith [hy.1])).differentiableAt.differentiableWithinAt

lemma continuousOn_entropyBoundK_Ici_one : ContinuousOn entropyBoundK (Ici (1 : ℝ)) := fun y hy =>
  (hasDerivAt_entropyBoundK (by linarith [mem_Ici.mp hy])).continuousAt.continuousWithinAt

lemma entropyBoundK_pos {u : ℝ} (hu : 1 < u) : 0 < entropyBoundK u := by
  have hcont : ContinuousOn entropyBoundK (Icc 1 u) :=
    continuousOn_entropyBoundK_Ici_one.mono Icc_subset_Ici_self
  rcases exists_deriv_eq_slope entropyBoundK hu hcont (differentiableOn_entropyBoundK_Ioo_one hu)
    with ⟨c, hc, hc_slope⟩
  have hpos := deriv_entropyBoundK_pos hc.1
  have hunz : u - 1 ≠ 0 := sub_ne_zero.mpr hu.ne'
  have hk_eq : entropyBoundK u = (u - 1) * deriv entropyBoundK c := by
    rw [hc_slope, entropyBoundK_one]
    field_simp
  rw [hk_eq]
  exact mul_pos (sub_pos.mpr hu) hpos

/-- For `x ∈ (0, 1/2)`, the “`W`–expression” is strictly negative. -/
lemma quad_log_lt_of_lt_half {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    (1 - x) ^ 2 * log (1 - x) < x ^ 2 * log x := by
  set u := (1 - x) / x with hu_def
  have hx_ne : x ≠ 0 := ne_of_gt hx0
  have h1mx_pos : 0 < 1 - x := by linarith
  have hu1 : 1 < u := by rw [hu_def, lt_div_iff₀ hx0]; linarith
  have hk := entropyBoundK_pos hu1
  have h1pu : 1 + u = x⁻¹ := by rw [hu_def]; field_simp
  have hlog1pu : log (1 + u) = -log x := by rw [h1pu, log_inv x]
  have hlogu : log u = log (1 - x) - log x := by
    rw [hu_def, log_div h1mx_pos.ne' hx_ne]
  have hk_exp : entropyBoundK u = log x - u ^ 2 * log (1 - x) := by
    simp only [entropyBoundK, hlog1pu, hlogu]
    ring
  rw [hk_exp] at hk
  have hcmp : u ^ 2 * log (1 - x) < log x := by linarith
  have hsq : (1 - x) ^ 2 = x ^ 2 * u ^ 2 := by rw [hu_def]; field_simp
  calc
    (1 - x) ^ 2 * log (1 - x) = x ^ 2 * (u ^ 2 * log (1 - x)) := by rw [hsq]; ring
    _ < x ^ 2 * log x := mul_lt_mul_of_pos_left hcmp (pow_pos hx0 2)

noncomputable def binEntropyOverQuad (t : ℝ) : ℝ :=
  binEntropy t / (t * (1 - t))

lemma binEntropyOverQuad_half :
    binEntropyOverQuad (1 / 2 : ℝ) = 4 * log 2 := by
  have hmid : binEntropy (1 / 2 : ℝ) = log 2 := by
    rw [one_div, binEntropy_two_inv]
  rw [binEntropyOverQuad, hmid]
  ring

lemma hasDerivAt_binEntropyOverQuad {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt binEntropyOverQuad
      (((log (1 - y) - log y) * (y * (1 - y)) - binEntropy y * (1 - 2 * y)) / (y * (1 - y)) ^ 2) y := by
  have hden : y * (1 - y) ≠ 0 := mul_ne_zero hy0.ne' (by linarith)
  have hN := hasDerivAt_binEntropy hy0.ne' hy1.ne
  have hD : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * y) y := by
    have := (hasDerivAt_id y).mul ((hasDerivAt_id y).const_sub 1)
    convert this using 1
    simp only [id]
    ring
  exact hN.div hD hden

lemma deriv_binEntropyOverQuad_neg {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 2) :
    deriv binEntropyOverQuad y < 0 := by
  have hy01 : y < 1 := by linarith
  have h1my : 0 < 1 - y := by linarith
  have hden : y * (1 - y) ≠ 0 := mul_ne_zero hy0.ne' h1my.ne'
  rw [(hasDerivAt_binEntropyOverQuad hy0 hy01).deriv]
  have hW : (log (1 - y) - log y) * (y * (1 - y)) - binEntropy y * (1 - 2 * y) =
      (1 - y) ^ 2 * log (1 - y) - y ^ 2 * log y := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub y]
    simp only [negMulLog]
    ring
  rw [hW]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (quad_log_lt_of_lt_half hy0 hy1)) (pow_pos
    (lt_of_le_of_ne (mul_nonneg hy0.le h1my.le) (Ne.symm hden)) 2)

lemma four_mul_x_one_sub_x_mul_log_two_interior {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    4 * x * (1 - x) * log 2 ≤ binEntropy x := by
  have hcont : ContinuousOn binEntropyOverQuad (Icc x (1 / 2 : ℝ)) := fun t ht =>
    (hasDerivAt_binEntropyOverQuad (lt_of_lt_of_le hx0 ht.1) (by linarith [ht.2])).continuousAt.continuousWithinAt
  have hmono :=
    strictAntiOn_of_deriv_neg (convex_Icc x (1 / 2 : ℝ)) hcont fun y hy => by
      simp only [interior_Icc, mem_Ioo] at hy
      exact deriv_binEntropyOverQuad_neg (lt_trans hx0 hy.1) hy.2
  have hxIcc : x ∈ Icc x (1 / 2 : ℝ) := ⟨le_rfl, le_of_lt hx1⟩
  have hmIcc : (1 / 2 : ℝ) ∈ Icc x (1 / 2 : ℝ) := ⟨le_of_lt hx1, le_rfl⟩
  have hcmp : binEntropyOverQuad (1 / 2 : ℝ) < binEntropyOverQuad x := hmono hxIcc hmIcc hx1
  rw [binEntropyOverQuad_half, binEntropyOverQuad] at hcmp
  have hpos : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  rw [lt_div_iff₀ hpos] at hcmp
  linarith

end

end UMST.DoubleSlit

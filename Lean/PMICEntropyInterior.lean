/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
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

open Real Set

namespace UMST.DoubleSlit

noncomputable section

/-- Auxiliary `k` from the change of variables `u = (1-x)/x`. -/
noncomputable def entropyBoundK (u : ℝ) : ℝ :=
  (u ^ 2 - 1) * log (1 + u) - u ^ 2 * log u

private lemma log_one_add_sub_half_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) :
    0 < log (1 + v) - v / 2 := by
  let f : ℝ → ℝ := fun t => log (1 + t) - t / 2
  have hf0 : f 0 = 0 := by simp [f]
  have hmono : StrictMonoOn f (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · -- `ContinuousOn f (Icc 0 1)`
      unfold f
      refine ContinuousOn.sub ?_ ?_
      · refine ContinuousOn.comp continuousOn_log ?_
        · exact continuousOn_id.const_add (1 : ℝ) |>.mono (fun _ hx => by linarith [hx.1])
      · exact continuous_ofReal.continuousOn.div continuousOn_const continuousOn_id fun _ _ => by
          simp
    · intro x hx
      simp only [f, interior_Icc, mem_Ioo] at hx ⊢
      have hxp : 0 < 1 + x := by linarith
      rw [deriv_sub]
      · rw [deriv.log (differentiableAt_id.const_add (1 : ℝ))]
        · simp only [deriv_id'', deriv_const, zero_add, one_mul]
          field_simp
          nlinarith [hx.1, hx.2]
        · exact ne_of_gt hxp
      · fun_prop (disch := linarith)
      · fun_prop
  have hvIcc : v ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hv0, hv1⟩
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have : f 0 < f v := (hmono.lt_iff_lt h0mem hvIcc).2 hv0
  simpa [hf0, f, sub_pos] using this

lemma two_mul_log_one_add_gt {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : v < 2 * log (1 + v) := by
  have := log_one_add_sub_half_pos v hv0 (le_of_lt hv1)
  linarith

lemma entropyBoundK_one : entropyBoundK 1 = 0 := by
  simp [entropyBoundK]

lemma deriv_entropyBoundK_pos {u : ℝ} (hu : 1 < u) : 0 < deriv entropyBoundK u := by
  have hu0 : 0 < u := by linarith
  have hu_ne : u ≠ 0 := ne_of_gt hu0
  have h1pu : 0 < 1 + u := by linarith
  have hden : deriv entropyBoundK u = 2 * u * log ((1 + u) / u) - 1 := by
    unfold entropyBoundK
    -- `k' = 2u log(1+u) + (u²-1)/(1+u) - 2u log u - u` and `(u²-1)/(u+1) = u-1` for `u ≠ -1`.
    have hu_ne' : u + 1 ≠ 0 := by linarith
    have hdiv : (u ^ 2 - 1) / (u + 1) = u - 1 := by
      field_simp [hu_ne']
      ring
    simp_rw [deriv_sub, deriv_mul, deriv_log hu_ne, deriv_log h1pu.ne.symm, deriv_id'', mul_one,
      one_mul]
    field_simp [hu_ne, h1pu.ne.symm]
    rw [hdiv]
    have hlog : log ((1 + u) / u) = log (1 + u) - log u := by rw [log_div h1pu.ne.symm hu_ne]
    rw [hlog]
    ring
  set v := u⁻¹ with hv
  have hv0 : 0 < v := inv_pos.mpr hu0
  have hv1 : v < 1 := by rw [hv]; nlinarith [hu]
  have hmain := two_mul_log_one_add_gt v hv0 hv1
  rw [hden]
  have h1 : (1 + u) / u = 1 + u⁻¹ := by field_simp [hu_ne]
  rw [h1]
  have hex : 2 * u * log (1 + u⁻¹) - 1 = (2 / v) * log (1 + v) - 1 := by
    rw [hv]
    field_simp [hu_ne]
  rw [hex]
  have hscale : 1 < (2 / v) * log (1 + v) := (one_lt_div hv0).mpr hmain
  linarith [hscale]

lemma differentiableOn_entropyBoundK_Ioo {a b : ℝ} (hab : a < b) (ha : 1 < a) :
    DifferentiableOn ℝ entropyBoundK (Ioo a b) := by
  intro y hy
  have hy1 : 1 < y := lt_trans ha hy.1
  have hy0 : 0 < y := by linarith
  have hy_ne : y ≠ 0 := ne_of_gt hy0
  have h1py : 0 < 1 + y := by linarith
  unfold entropyBoundK
  refine DifferentiableAt.sub ?_ ?_
  · refine DifferentiableAt.mul (differentiableAt_pow 2) ?_
    exact differentiableAt_log h1py.ne.symm
  · refine DifferentiableAt.mul (differentiableAt_pow 2) ?_
    exact differentiableAt_log hy_ne

lemma continuousOn_entropyBoundK_Ici_one : ContinuousOn entropyBoundK (Ici (1 : ℝ)) := by
  unfold entropyBoundK
  refine ContinuousOn.sub (ContinuousOn.mul ?_ ?_) (ContinuousOn.mul ?_ ?_)
  · refine ContinuousOn.mul (ContinuousOn.sub (continuousOn_id.pow 2) continuousOn_const) ?_
    · refine ContinuousOn.log ?_ fun x hx => ?_
      · exact (continuousOn_const.add continuousOn_id).mono fun _ _ => trivial
      · have : (0 : ℝ) < 1 + x := by linarith [hx]
        exact this.ne.symm
  · refine ContinuousOn.mul (continuousOn_id.pow 2) ?_
    · refine ContinuousOn.log continuousOn_id fun x hx => ne_of_gt ?_
      linarith [hx]

lemma entropyBoundK_pos {u : ℝ} (hu : 1 < u) : 0 < entropyBoundK u := by
  have hab : (1 : ℝ) < u := hu
  have hcont : ContinuousOn entropyBoundK (Icc 1 u) :=
    continuousOn_entropyBoundK_Ici_one.mono Icc_subset_Ici_self
  have hdiff : DifferentiableOn ℝ entropyBoundK (Ioo 1 u) :=
    differentiableOn_entropyBoundK_Ioo hab (by rfl)
  rcases exists_deriv_eq_slope entropyBoundK hab hcont hdiff with ⟨c, hc, hc_slope⟩
  have hc1 : 1 < c := hc.1
  have hcpu : c < u := hc.2
  have hk1 : entropyBoundK 1 = 0 := entropyBoundK_one
  have hpos_deriv : 0 < deriv entropyBoundK c := deriv_entropyBoundK_pos hc1
  have hunz : u - 1 ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hk_eq : entropyBoundK u = (u - 1) * deriv entropyBoundK c := by
    have hslope := hc_slope
    field_simp [hunz] at hslope
    linarith [hk1, hslope]
  rw [hk_eq]
  exact mul_pos (sub_pos.mpr hab) hpos_deriv

/-- For `x ∈ (0, 1/2)`, the “`W`–expression” is strictly negative. -/
lemma quad_log_lt_of_lt_half {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    (1 - x) ^ 2 * log (1 - x) < x ^ 2 * log x := by
  set u := (1 - x) / x with hu_def
  have hu1 : 1 < u := by rw [hu_def]; nlinarith
  have hk := entropyBoundK_pos hu1
  have hx_ne : x ≠ 0 := ne_of_gt hx0
  have h1mx_pos : 0 < 1 - x := by nlinarith
  have h1pu : 1 + u = x⁻¹ := by
    rw [hu_def]
    field_simp [hx_ne]
    ring
  have hlog1pu : log (1 + u) = -log x := by rw [h1pu, log_inv hx_ne]
  have hlogu : log u = log (1 - x) - log x := by
    rw [hu_def, log_div h1mx_pos.ne.symm hx_ne]
  -- expand `entropyBoundK u > 0` to `log x > u² * log (1-x)` then multiply by `x²`
  have hk_exp :
      entropyBoundK u = log x - u ^ 2 * log (1 - x) := by
    simp only [entropyBoundK, hlog1pu, hlogu]
    ring
  rw [hk_exp] at hk
  have hcmp : u ^ 2 * log (1 - x) < log x := by linarith [hk]
  have hu_x : u * x = 1 - x := by rw [hu_def]; field_simp [hx_ne]
  have hsq : (u * x) ^ 2 = (1 - x) ^ 2 := by rw [hu_x]
  calc
    (1 - x) ^ 2 * log (1 - x) = x ^ 2 * (u ^ 2 * log (1 - x)) := by
      have : (1 - x) ^ 2 = x ^ 2 * u ^ 2 := by
        calc
          (1 - x) ^ 2 = (u * x) ^ 2 := by rw [← hsq]
          _ = x ^ 2 * u ^ 2 := by ring
      rw [this]
      ring
    _ < x ^ 2 * log x := mul_lt_mul_of_pos_left hcmp (sq_pos_of_pos hx0)

noncomputable def binEntropyOverQuad (t : ℝ) : ℝ :=
  binEntropy t / (t * (1 - t))

lemma binEntropyOverQuad_half :
    binEntropyOverQuad (1 / 2 : ℝ) = 4 * log 2 := by
  have hmid : binEntropy (1 / 2 : ℝ) = log 2 := by
    rw [← inv_eq_one_div (2 : ℝ), binEntropy_two_inv]
  simp [binEntropyOverQuad, hmid]
  ring

lemma deriv_binEntropyOverQuad_neg {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 2) :
    deriv binEntropyOverQuad y < 0 := by
  have hy01 : y < 1 := by linarith [hy1]
  have hy_ne : y ≠ 0 := ne_of_gt hy0
  have h1my : 0 < 1 - y := by nlinarith
  have hden0 : y * (1 - y) ≠ 0 := mul_ne_zero hy_ne (ne_of_gt h1my)
  have hy_ne_one : y ≠ 1 := ne_of_lt hy01
  have hdiff_bin :
      DifferentiableAt ℝ binEntropy y := differentiableAt_binEntropy hy_ne hy_ne_one
  have hdiff_den : DifferentiableAt ℝ (fun t : ℝ => t * (1 - t)) y := by fun_prop (disch := nlinarith)
  have hN : deriv binEntropy y = log ((1 - y) / y) := by
    rw [deriv_binEntropy y, log_sub_log, log_div h1my.ne.symm hy_ne]
  have hD : deriv (fun t : ℝ => t * (1 - t)) y = 1 - 2 * y := by simp [deriv_sub, deriv_mul, deriv_id'']
  have hW :
      log ((1 - y) / y) * (y * (1 - y)) - binEntropy y * (1 - 2 * y) =
        (1 - y) ^ 2 * log (1 - y) - y ^ 2 * log y := by
    rw [hN]
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub y]
    simp only [negMulLog]
    ring_nf
  have hWneg : log ((1 - y) / y) * (y * (1 - y)) - binEntropy y * (1 - 2 * y) < 0 := by
    rw [hW]
    exact quad_log_lt_of_lt_half hy0 hy1
  have hderiv :
      deriv binEntropyOverQuad y =
        (log ((1 - y) / y) * (y * (1 - y)) - binEntropy y * (1 - 2 * y)) / (y * (1 - y)) ^ 2 := by
    simp only [binEntropyOverQuad]
    rw [deriv_div hdiff_bin hdiff_den]
    · simp [hN, hD]
      ring
    · simpa using hden0
  rw [hderiv]
  apply div_neg_of_neg_of_pos hWneg
  exact sq_pos_of_ne_zero (pow_ne_zero 2 hden0)

lemma four_mul_x_one_sub_x_mul_log_two_interior {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    4 * x * (1 - x) * log 2 ≤ binEntropy x := by
  have hcont :
      ContinuousOn binEntropyOverQuad (Icc x (1 / 2 : ℝ)) := by
    unfold binEntropyOverQuad
    refine ContinuousOn.div ?_ ?_ ?_
    · exact binEntropy_continuous.continuousOn
    · refine ContinuousOn.mul continuousOn_id ?_
      exact continuousOn_const.sub continuousOn_id
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hx0 ht.1
      have ht1 : t < 1 := by nlinarith [ht.2]
      exact mul_ne_zero ht0.ne' (sub_ne_zero.mpr (ne_of_gt (by nlinarith : 0 < 1 - t)))
  have hmono :=
    strictAntiOn_of_deriv_neg (convex_Icc x (1 / 2 : ℝ)) hcont fun y hy => by
      simp only [interior_Icc, mem_Ioo] at hy
      exact deriv_binEntropyOverQuad_neg hy.1 hy.2
  have hxIcc : x ∈ Icc x (1 / 2 : ℝ) := ⟨le_rfl, le_of_lt hx1⟩
  have hmIcc : (1 / 2 : ℝ) ∈ Icc x (1 / 2 : ℝ) := ⟨le_of_lt hx1, le_rfl⟩
  have hcmp : binEntropyOverQuad (1 / 2 : ℝ) < binEntropyOverQuad x :=
    (StrictAntiOn.lt_iff_lt hmono hmIcc hxIcc).mpr hx1
  rw [binEntropyOverQuad_half] at hcmp
  have hpos : 0 < x * (1 - x) := mul_pos hx0 (by nlinarith : 0 < 1 - x)
  have hlt := mul_lt_mul_of_pos_right hcmp hpos
  have hsimp : binEntropy x / (x * (1 - x)) * (x * (1 - x)) = binEntropy x := by field_simp [hpos.ne']
  rw [← hsimp] at hlt
  have hlt' : 4 * x * (1 - x) * log 2 < binEntropy x := by
    convert hlt using 1
    ring
  exact le_of_lt hlt'

end

end UMST.DoubleSlit

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Abs
import Mathlib.Data.Complex.Order
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import DensityState
import DoubleSlitCore
import MeasurementChannel

/-!
# Quantum–classical bridge (2-level path)

Read **computational-basis path probabilities** from the diagonal of a `2 × 2` density matrix, and
package **`UMST.DoubleSlit.ObservationState`**.

- Diagonal **Born weights** `pathWeight`, coarse **`whichPathDistinguishability`** `I = |p₀ − p₁|`.
- **Fringe visibility** `V = 2 |ρ₀₁|` from off-diagonal coherence; **`complementarity_fringe_path`** proves
  `V² + I² ≤ 1` for every `2 × 2` density matrix (PSD + trace 1).
- **`observationStateCanonical ρ`**: packages the canonical `(I, V)` pair satisfying complementarity.
**Entropy (binary diagonal):** see `InfoEntropy.lean` for Shannon / von Neumann on `pathWeight`.

**Linked to `whichPathChannel`:** diagonal weights and `I` are **invariant** under Lüders path
measurement (`pathWeight_whichPath_apply`); **`fringeVisibility_whichPath_apply`** shows `V` drops to `0`.

**Entropy / DPI ledger (read order):** `pathWeight` here → `vonNeumannDiagonal` / `shannonBinary`
(`InfoEntropy.lean`) → spectral entropy `vonNeumannEntropy` (`VonNeumannEntropy.lean`) →
`vonNeumannDiagonal_ge_vonNeumannEntropy` and **algebraic unital DPI** for this channel
`vonNeumannEntropy_nondecreasing_unital_whichPath` (`DataProcessingInequality.lean`).
Product-state additivity `vonNeumannEntropy_tensorDensity_eq` is proved in `KroneckerEigen.lean`
(consumed by `QuantumMutualInfo.lean`).
-/

open scoped Matrix ComplexOrder BigOperators

open Matrix

namespace UMST.Quantum

/-- Witness for `Fin 2` Hilbert dimension. -/
def hnQubit : 0 < 2 := by decide

variable {ρ : DensityMatrix hnQubit}

theorem isHermitian_carrier (ρ : DensityMatrix hnQubit) : ρ.carrier.IsHermitian :=
  ρ.psd.isHermitian

theorem diag_star_eq (ρ : DensityMatrix hnQubit) (i : Fin 2) :
    star (ρ.carrier i i) = ρ.carrier i i :=
  (isHermitian_carrier ρ).apply i i

theorem diag_im_zero (ρ : DensityMatrix hnQubit) (i : Fin 2) : (ρ.carrier i i).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← Complex.star_def]
  exact diag_star_eq ρ i

theorem diag_nonneg_complex (ρ : DensityMatrix hnQubit) (i : Fin 2) : (0 : ℂ) ≤ ρ.carrier i i :=
  DensityMat.diag_nonneg_complex_n ρ i

theorem pathWeight_nonneg (ρ : DensityMatrix hnQubit) (i : Fin 2) : 0 ≤ (ρ.carrier i i).re :=
  (Complex.nonneg_iff.mp (diag_nonneg_complex ρ i)).1

theorem pathWeight0_add_pathWeight1 (ρ : DensityMatrix hnQubit) :
    (ρ.carrier 0 0).re + (ρ.carrier 1 1).re = 1 := by
  have ht := ρ.trace_one
  rw [Matrix.trace_fin_two] at ht
  apply_fun Complex.re at ht
  simpa only [Complex.add_re, Complex.one_re] using ht

/-- Born / Lüders probability for path `i` in the computational basis. -/
noncomputable def pathWeight (ρ : DensityMatrix hnQubit) (i : Fin 2) : ℝ :=
  (ρ.carrier i i).re

theorem pathWeight_nonneg' (ρ : DensityMatrix hnQubit) (i : Fin 2) : 0 ≤ pathWeight ρ i :=
  pathWeight_nonneg ρ i

theorem pathWeight_sum (ρ : DensityMatrix hnQubit) : pathWeight ρ 0 + pathWeight ρ 1 = 1 := by
  simpa [pathWeight] using pathWeight0_add_pathWeight1 ρ

/-- Coarse which-path score in `[0, 1]`: balanced mixture `0`, orthogonal projectors `1`. -/
noncomputable def whichPathDistinguishability (ρ : DensityMatrix hnQubit) : ℝ :=
  |pathWeight ρ 0 - pathWeight ρ 1|

theorem whichPathDistinguishability_nonneg (ρ : DensityMatrix hnQubit) :
    0 ≤ whichPathDistinguishability ρ :=
  abs_nonneg _

theorem whichPathDistinguishability_le_one (ρ : DensityMatrix hnQubit) :
    whichPathDistinguishability ρ ≤ 1 := by
  unfold whichPathDistinguishability pathWeight
  set a := (ρ.carrier 0 0).re with ha
  set b := (ρ.carrier 1 1).re with hb
  have hs : a + b = 1 := by simpa [ha, hb] using pathWeight0_add_pathWeight1 ρ
  have ha0 : 0 ≤ a := by rw [ha]; exact pathWeight_nonneg ρ 0
  have hb0 : 0 ≤ b := by rw [hb]; exact pathWeight_nonneg ρ 1
  rw [ha, hb, abs_le]
  constructor <;> nlinarith [hs, ha0, hb0]

theorem whichPathDistinguishability_mem_Icc (ρ : DensityMatrix hnQubit) :
    whichPathDistinguishability ρ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨whichPathDistinguishability_nonneg ρ, whichPathDistinguishability_le_one ρ⟩

/-- Lüders path measurement preserves computational-basis Born weights (diagonal entries). -/
theorem pathWeight_whichPath_apply (ρ : DensityMatrix hnQubit) (i : Fin 2) :
    pathWeight (KrausChannel.whichPathChannel.apply hnQubit ρ) i = pathWeight ρ i := by
  simp only [pathWeight, KrausChannel.apply, KrausChannel.whichPath_map_apply_entry]
  fin_cases i <;> simp

@[simp]
theorem whichPathDistinguishability_whichPath_apply (ρ : DensityMatrix hnQubit) :
    whichPathDistinguishability (KrausChannel.whichPathChannel.apply hnQubit ρ) =
      whichPathDistinguishability ρ := by
  simp [whichPathDistinguishability, pathWeight_whichPath_apply]

/-- Off-diagonal coherence is bounded by the product of Born weights (PSD `2 × 2` principal minor). -/
theorem normSq_coherence_le_product (ρ : DensityMatrix hnQubit) :
    Complex.normSq (ρ.carrier 0 1) ≤ pathWeight ρ 0 * pathWeight ρ 1 := by
  set A := ρ.carrier
  set hρ := DensityMat.isHermitian ρ
  set l0 : ℝ := hρ.eigenvalues 0
  set l1 : ℝ := hρ.eigenvalues 1
  set p0 : ℝ := pathWeight ρ 0
  set p1 : ℝ := pathWeight ρ 1
  have hprod_det : (l0 * l1 : ℂ) = A.det := by
    dsimp [l0, l1]
    rw [hρ.det_eq_prod_eigenvalues, Fin.prod_univ_two]
    rfl
  have hdet2 : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
  have h01 : A 1 0 = star (A 0 1) := by rw [← Matrix.conjTranspose_apply, hρ.eq]
  have hp0c : (p0 : ℂ) = A 0 0 := by simpa [p0, pathWeight, A] using IsHermitian.coe_re_apply_self hρ 0
  have hp1c : (p1 : ℂ) = A 1 1 := by simpa [p1, pathWeight, A] using IsHermitian.coe_re_apply_self hρ 1
  have hdet3 : A.det = (p0 * p1 : ℂ) - (Complex.normSq (A 0 1) : ℂ) := by
    rw [hdet2, h01, ← hp0c, ← hp1c]
    congr 1
    rw [congr_fun Complex.star_def (A 0 1), Complex.mul_conj]
  have hl1R : l0 * l1 = (A.det).re := by
    have hre := congrArg Complex.re hprod_det
    simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using hre
  have hre_det : (A.det).re = p0 * p1 - Complex.normSq (A 0 1) := by
    rw [hdet3, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re]
    simp [Complex.normSq]
  have hll : 0 ≤ l0 * l1 :=
    mul_nonneg (PosSemidef.eigenvalues_nonneg ρ.psd 0) (PosSemidef.eigenvalues_nonneg ρ.psd 1)
  have hcombo : Complex.normSq (A 0 1) = p0 * p1 - l0 * l1 := by linarith [hl1R, hre_det]
  rw [hcombo]
  linarith [hll]

/-- Fringe visibility `V = 2 |ρ₀₁|` (standard double-slit convention for a qubit path bit). -/
noncomputable def fringeVisibility (ρ : DensityMatrix hnQubit) : ℝ :=
  2 * Complex.abs (ρ.carrier 0 1)

/-- Fringe visibility is zero iff the off-diagonal coherence `ρ₀₁` vanishes. -/
theorem fringeVisibility_eq_zero_iff (ρ : DensityMatrix hnQubit) :
    fringeVisibility ρ = 0 ↔ ρ.carrier 0 1 = 0 := by
  unfold fringeVisibility
  constructor
  · intro h
    have : Complex.abs (ρ.carrier 0 1) = 0 := by linarith [Complex.abs.nonneg (ρ.carrier 0 1)]
    rwa [map_eq_zero] at this
  · intro h
    rw [h, map_zero, mul_zero]

/-- Fringe visibility is positive iff the off-diagonal coherence `ρ₀₁` is nonzero. -/
theorem fringeVisibility_pos_iff (ρ : DensityMatrix hnQubit) :
    0 < fringeVisibility ρ ↔ ρ.carrier 0 1 ≠ 0 := by
  rw [lt_iff_le_and_ne, and_iff_right (by unfold fringeVisibility; exact mul_nonneg (by norm_num) (Complex.abs.nonneg _)),
      ne_comm, ← not_iff_not, not_not, not_not]
  exact fringeVisibility_eq_zero_iff ρ

theorem fringeVisibility_nonneg (ρ : DensityMatrix hnQubit) : 0 ≤ fringeVisibility ρ := by
  unfold fringeVisibility
  exact mul_nonneg (by norm_num) (Complex.abs.nonneg _)

theorem pathWeight_prod_le_quarter (ρ : DensityMatrix hnQubit) :
    pathWeight ρ 0 * pathWeight ρ 1 ≤ 1 / 4 := by
  set a := pathWeight ρ 0 with ha
  set b := pathWeight ρ 1 with hb
  have hs : a + b = 1 := by rw [ha, hb]; exact pathWeight_sum ρ
  have ha0 : 0 ≤ a := by rw [ha]; exact pathWeight_nonneg' ρ 0
  have hb0 : 0 ≤ b := by rw [hb]; exact pathWeight_nonneg' ρ 1
  have hb1 : b = 1 - a := by linarith
  rw [hb1]
  nlinarith [sq_nonneg (a - 1 / 2)]

theorem fringeVisibility_le_one (ρ : DensityMatrix hnQubit) : fringeVisibility ρ ≤ 1 := by
  have hsq : fringeVisibility ρ ^ 2 ≤ 1 := by
    unfold fringeVisibility
    rw [mul_pow, sq (2 : ℝ), Complex.sq_abs]
    have hnc := normSq_coherence_le_product ρ
    have hp := pathWeight_prod_le_quarter ρ
    nlinarith
  exact (sq_le_one_iff₀ (fringeVisibility_nonneg ρ)).1 hsq

@[simp]
theorem fringeVisibility_whichPath_apply (ρ : DensityMatrix hnQubit) :
    fringeVisibility (KrausChannel.whichPathChannel.apply hnQubit ρ) = 0 := by
  unfold fringeVisibility KrausChannel.apply
  simp [KrausChannel.whichPath_map_apply_entry]

/-- **Englert-style complementarity** for the coarse `(I, V)` pair: `V² + I² ≤ 1`. -/
theorem complementarity_fringe_path (ρ : DensityMatrix hnQubit) :
    fringeVisibility ρ ^ 2 + whichPathDistinguishability ρ ^ 2 ≤ 1 := by
  unfold fringeVisibility whichPathDistinguishability pathWeight
  set a := (ρ.carrier 0 0).re with ha
  set b := (ρ.carrier 1 1).re with hb
  set c := ρ.carrier 0 1 with hc
  have hs : a + b = 1 := by rw [ha, hb]; exact pathWeight_sum ρ
  have hnc : Complex.normSq c ≤ a * b := by rw [ha, hb, hc]; exact normSq_coherence_le_product ρ
  rw [hc, mul_pow, sq (2 : ℝ), Complex.sq_abs, sq_abs (a - b)]
  have four_eq : (2 : ℝ) * (2 : ℝ) * Complex.normSq c = 4 * Complex.normSq c := by ring
  rw [four_eq]
  have step : 4 * Complex.normSq c + (a - b) ^ 2 ≤ 4 * (a * b) + (a - b) ^ 2 := by nlinarith [hnc]
  calc
    4 * Complex.normSq c + (a - b) ^ 2 ≤ 4 * (a * b) + (a - b) ^ 2 := step
    _ = (a + b) ^ 2 := by ring
    _ = 1 := by rw [hs]; ring

open UMST.DoubleSlit in
/-- Canonical observation state: `I` from diagonal weights, `V` from fringe visibility; complementarity
holds automatically (`complementarity_fringe_path`). -/
noncomputable def observationStateCanonical (ρ : DensityMatrix hnQubit) : UMST.DoubleSlit.ObservationState :=
  { I := whichPathDistinguishability ρ
    V := fringeVisibility ρ
    hI := ⟨whichPathDistinguishability_nonneg ρ, whichPathDistinguishability_le_one ρ⟩
    hV := ⟨fringeVisibility_nonneg ρ, fringeVisibility_le_one ρ⟩ }

theorem observationStateCanonical_complementary (ρ : DensityMatrix hnQubit) :
    UMST.DoubleSlit.Complementary (observationStateCanonical ρ) := by
  simpa [observationStateCanonical, UMST.DoubleSlit.Complementary] using complementarity_fringe_path ρ

/-- Build a `DoubleSlitCore` observation state: `I` from diagonal path weights, `V` supplied externally. -/
noncomputable def observationStateOf (ρ : DensityMatrix hnQubit) (V : ℝ) (hV : 0 ≤ V ∧ V ≤ 1)
    (_hComp : V ^ 2 + whichPathDistinguishability ρ ^ 2 ≤ 1) : UMST.DoubleSlit.ObservationState :=
  { I := whichPathDistinguishability ρ
    V := V
    hI := ⟨whichPathDistinguishability_nonneg ρ, whichPathDistinguishability_le_one ρ⟩
    hV := hV }

theorem observationStateOf_complementary (ρ : DensityMatrix hnQubit) (V : ℝ) (hV : 0 ≤ V ∧ V ≤ 1)
    (hComp : V ^ 2 + whichPathDistinguishability ρ ^ 2 ≤ 1) :
    UMST.DoubleSlit.Complementary (observationStateOf ρ V hV hComp) := by
  unfold UMST.DoubleSlit.Complementary observationStateOf
  exact hComp

/-- Using the measured fringe visibility, `observationStateOf` is complementary by `complementarity_fringe_path`. -/
theorem observationStateOf_fringe_complementary (ρ : DensityMatrix hnQubit) :
    UMST.DoubleSlit.Complementary
        (observationStateOf ρ (fringeVisibility ρ)
          ⟨fringeVisibility_nonneg ρ, fringeVisibility_le_one ρ⟩
          (complementarity_fringe_path ρ)) := by
  unfold UMST.DoubleSlit.Complementary observationStateOf
  exact complementarity_fringe_path ρ

end UMST.Quantum

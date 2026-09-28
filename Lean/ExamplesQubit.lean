-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import Mathlib.Algebra.BigOperators.Fin
import ProbeOptimization

/-!
# ExamplesQubit — computational |+⟩, |0⟩, and coarse `(I, V)`

- **|+⟩** (`rhoPlus`): balanced diagonal, **`V = 1`**, **`I = 0`**, maximal diagonal entropy / Landauer hook.
- **|0⟩** (`rhoZero`) and **|1⟩** (`rhoOne`): definite paths, **`V = 0`**, **`I = 1`**, zero diagonal entropy.

Imports **`DoubleSlit`** so this file also regression-tests the **full chain** (including
`measurementUpdateWhichPath`).

**`rhoPlus` + which-path:** fringe visibility drops to `0`; diagonal / entropy / Landauer hook unchanged.
-/

namespace UMST.Quantum.Examples

open scoped BigOperators

open Matrix Real Complex UMST.DoubleSlit UMST.Quantum

/-- Computational-basis amplitudes for |+⟩ = (|0⟩ + |1⟩) / √2. -/
noncomputable def psiPlus : Fin 2 → ℂ :=
  fun _ => (1 : ℂ) / (Real.sqrt 2 : ℂ)

lemma sqrt2_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

lemma sqrt2_ne_zero : Real.sqrt 2 ≠ 0 :=
  ne_of_gt sqrt2_pos

lemma psiPlus_normalized : dotProduct psiPlus (star psiPlus) = 1 := by
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt2_ne_zero
  simp only [dotProduct, Fin.sum_univ_two, psiPlus, Pi.star_apply, star_div₀, star_one,
    Complex.star_def, Complex.conj_ofReal]
  field_simp
  have : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, hs]; norm_num
  rw [this]; norm_num

/-- Pure |+⟩ state on the path qubit. -/
noncomputable def rhoPlus : DensityMatrix hnQubit :=
  pureDensity (hn := hnQubit) psiPlus psiPlus_normalized

lemma rhoPlus_carrier_apply (i j : Fin 2) :
    rhoPlus.carrier i j = psiPlus i * star (psiPlus j) := by
  simp [rhoPlus, pureDensity_carrier, pureCarrier, Matrix.mul_apply, Fintype.sum_unique, col_apply,
    row_apply]

/-- Normal form: every entry of |+⟩⟨+| equals 1/2. All |+⟩ facts below reduce to this one lemma. -/
lemma psiPlus_mul_star (i j : Fin 2) : psiPlus i * star (psiPlus j) = (1 / 2 : ℂ) := by
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt2_ne_zero
  simp only [psiPlus, star_div₀, star_one, Complex.star_def, Complex.conj_ofReal]
  field_simp
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma rhoPlus_carrier_half (i j : Fin 2) : rhoPlus.carrier i j = (1 / 2 : ℂ) := by
  rw [rhoPlus_carrier_apply, psiPlus_mul_star]

lemma psi_times_conj : psiPlus 0 * star (psiPlus 1) = (1 / 2 : ℂ) := psiPlus_mul_star 0 1

theorem rhoPlus_pathWeight0 : pathWeight rhoPlus 0 = 1 / 2 := by
  simp only [pathWeight, rhoPlus_carrier_half]; norm_num

theorem rhoPlus_pathWeight1 : pathWeight rhoPlus 1 = 1 / 2 := by
  simp only [pathWeight, rhoPlus_carrier_half]; norm_num

theorem rhoPlus_fringeVisibility : fringeVisibility rhoPlus = 1 := by
  unfold fringeVisibility
  rw [rhoPlus_carrier_half]
  have : ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.abs_of_nonneg (by norm_num)]
  norm_num

theorem rhoPlus_whichPathDistinguishability : whichPathDistinguishability rhoPlus = 0 := by
  unfold whichPathDistinguishability
  rw [rhoPlus_pathWeight0, rhoPlus_pathWeight1, sub_self, abs_zero]

theorem rhoPlus_vonNeumannDiagonal_eq_log_two : vonNeumannDiagonal rhoPlus = Real.log 2 := by
  unfold vonNeumannDiagonal
  rw [shannonBinary_eq_binEntropy, rhoPlus_pathWeight0, one_div]
  exact Real.binEntropy_two_inv

/-- Englert-style sum equals `1` (complementarity saturated: full `V`, zero `I`). -/
theorem rhoPlus_complementarity_squared_eq_one :
    fringeVisibility rhoPlus ^ 2 + whichPathDistinguishability rhoPlus ^ 2 = 1 := by
  rw [rhoPlus_fringeVisibility, rhoPlus_whichPathDistinguishability]
  norm_num

theorem rhoPlus_observationCanonical_I : (observationStateCanonical rhoPlus).I = 0 := by
  simp [observationStateCanonical, rhoPlus_whichPathDistinguishability]

theorem rhoPlus_observationCanonical_V : (observationStateCanonical rhoPlus).V = 1 := by
  simp [observationStateCanonical, rhoPlus_fringeVisibility]

/-- One full Landauer **bit-equivalent** of diagonal entropy (maximum for a qubit path bit). -/
theorem rhoPlus_pathEntropyBits_eq_one : pathEntropyBits rhoPlus = 1 := by
  unfold pathEntropyBits
  rw [rhoPlus_vonNeumannDiagonal_eq_log_two, div_self (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]

theorem rhoPlus_landauerCostDiagonal_eq_landauerBitEnergy (T : ℝ) :
    landauerCostDiagonal rhoPlus T = landauerBitEnergy T := by
  simp [landauerCostDiagonal, infoEnergyLowerBound, rhoPlus_pathEntropyBits_eq_one]

/-- Lüders which-path removes all fringe visibility but leaves balanced Born weights (hence `I = 0`). -/
theorem rhoPlus_whichPathApply_fringeVisibility :
    fringeVisibility (KrausChannel.whichPathChannel.apply hnQubit rhoPlus) = 0 :=
  fringeVisibility_whichPath_apply rhoPlus

theorem rhoPlus_whichPathApply_whichPathDistinguishability :
    whichPathDistinguishability (KrausChannel.whichPathChannel.apply hnQubit rhoPlus) = 0 := by
  rw [whichPathDistinguishability_whichPath_apply, rhoPlus_whichPathDistinguishability]

theorem rhoPlus_whichPathApply_pathEntropyBits :
    pathEntropyBits (KrausChannel.whichPathChannel.apply hnQubit rhoPlus) = 1 := by
  simpa [pathEntropyBits, vonNeumannDiagonal_whichPath_apply] using rhoPlus_pathEntropyBits_eq_one

/-- Coarse `measurementUpdateWhichPath` on `rhoPlus` ends with **`V = 0`**. -/
theorem rhoPlus_measurementUpdate_new_V_eq_zero :
    (measurementUpdateWhichPath rhoPlus).newState.V = 0 :=
  measurementUpdateWhichPath_new_V rhoPlus

-- ---------------------------------------------------------------------------
-- |0⟩ — definite path, no coherence
-- ---------------------------------------------------------------------------

/-- Computational basis **|0⟩**. -/
noncomputable def psiZero : Fin 2 → ℂ := fun i => ite (i = 0) (1 : ℂ) 0

lemma psiZero_normalized : dotProduct psiZero (star psiZero) = 1 := by
  simp [dotProduct, Fin.sum_univ_two, psiZero]

/-- Pure |0⟩ on the path qubit. -/
noncomputable def rhoZero : DensityMatrix hnQubit :=
  pureDensity (hn := hnQubit) psiZero psiZero_normalized

theorem rhoZero_pathWeight0 : pathWeight rhoZero 0 = 1 := by
  simp [pathWeight, rhoZero, pureDensity_carrier, pureCarrier, Matrix.mul_apply, Fintype.sum_unique,
    col_apply, row_apply, psiZero]

theorem rhoZero_pathWeight1 : pathWeight rhoZero 1 = 0 := by
  simp [pathWeight, rhoZero, pureDensity_carrier, pureCarrier, Matrix.mul_apply, Fintype.sum_unique,
    col_apply, row_apply, psiZero, Fin.ext_iff]

theorem rhoZero_fringeVisibility : fringeVisibility rhoZero = 0 := by
  unfold fringeVisibility
  simp [rhoZero, pureDensity_carrier, pureCarrier, Matrix.mul_apply, Fintype.sum_unique, col_apply,
    row_apply, psiZero, Fin.ext_iff, map_zero, mul_zero]

theorem rhoZero_whichPathDistinguishability : whichPathDistinguishability rhoZero = 1 := by
  unfold whichPathDistinguishability
  rw [rhoZero_pathWeight0, rhoZero_pathWeight1, sub_zero, abs_one]

theorem rhoZero_vonNeumannDiagonal : vonNeumannDiagonal rhoZero = 0 := by
  unfold vonNeumannDiagonal shannonBinary
  simp [rhoZero_pathWeight0, Real.negMulLog_zero, Real.negMulLog_one]

theorem rhoZero_pathEntropyBits : pathEntropyBits rhoZero = 0 := by
  unfold pathEntropyBits
  rw [rhoZero_vonNeumannDiagonal]
  field_simp [ne_of_gt log_two_pos]

theorem rhoZero_landauerCostDiagonal (T : ℝ) : landauerCostDiagonal rhoZero T = 0 := by
  simp [landauerCostDiagonal, infoEnergyLowerBound, pathEntropyBits, rhoZero_vonNeumannDiagonal,
    zero_div, mul_zero, log_two_pos.ne']

theorem rhoZero_complementarity_squared_eq_one :
    fringeVisibility rhoZero ^ 2 + whichPathDistinguishability rhoZero ^ 2 = 1 := by
  rw [rhoZero_fringeVisibility, rhoZero_whichPathDistinguishability]
  norm_num

theorem rhoZero_observationCanonical_eq_after_whichPath :
    observationStateCanonical rhoZero =
      observationStateCanonical (KrausChannel.whichPathChannel.apply hnQubit rhoZero) := by
  apply ObservationState.ext
  · simp only [observationStateCanonical]
    rw [whichPathDistinguishability_whichPath_apply]
  · simp only [observationStateCanonical]
    rw [fringeVisibility_whichPath_apply, rhoZero_fringeVisibility]

/-- `measurementUpdateWhichPath` is **idle** on the coarse interface for |0⟩ (already diagonal). -/
theorem rhoZero_measurementUpdate_states_eq :
    (measurementUpdateWhichPath rhoZero).oldState = (measurementUpdateWhichPath rhoZero).newState := by
  simp [measurementUpdateWhichPath, rhoZero_observationCanonical_eq_after_whichPath]

-- ---------------------------------------------------------------------------
-- |1⟩ — definite path, no coherence
-- ---------------------------------------------------------------------------

/-- Computational basis **|1⟩**. -/
noncomputable def psiOne : Fin 2 → ℂ := fun i => ite (i = 1) (1 : ℂ) 0

lemma psiOne_normalized : dotProduct psiOne (star psiOne) = 1 := by
  simp [dotProduct, Fin.sum_univ_two, psiOne]

/-- Pure |1⟩ on the path qubit. -/
noncomputable def rhoOne : DensityMatrix hnQubit :=
  pureDensity (hn := hnQubit) psiOne psiOne_normalized

theorem rhoOne_pathWeight0 : pathWeight rhoOne 0 = 0 := by
  simp [pathWeight, rhoOne, pureDensity_carrier, pureCarrier, Matrix.mul_apply, Fintype.sum_unique,
    col_apply, row_apply, psiOne, Fin.ext_iff]

theorem rhoOne_pathWeight1 : pathWeight rhoOne 1 = 1 := by
  simp [pathWeight, rhoOne, pureDensity_carrier, pureCarrier, Matrix.mul_apply, Fintype.sum_unique,
    col_apply, row_apply, psiOne]

theorem rhoOne_fringeVisibility : fringeVisibility rhoOne = 0 := by
  unfold fringeVisibility
  simp [rhoOne, pureDensity_carrier, pureCarrier, Matrix.mul_apply, Fintype.sum_unique, col_apply,
    row_apply, psiOne, Fin.ext_iff, map_zero, mul_zero]

theorem rhoOne_whichPathDistinguishability : whichPathDistinguishability rhoOne = 1 := by
  unfold whichPathDistinguishability
  rw [rhoOne_pathWeight0, rhoOne_pathWeight1, zero_sub, abs_neg, abs_one]

theorem rhoOne_vonNeumannDiagonal : vonNeumannDiagonal rhoOne = 0 := by
  unfold vonNeumannDiagonal shannonBinary
  simp [rhoOne_pathWeight0, Real.negMulLog_zero, Real.negMulLog_one]

theorem rhoOne_pathEntropyBits : pathEntropyBits rhoOne = 0 := by
  unfold pathEntropyBits
  rw [rhoOne_vonNeumannDiagonal]
  field_simp [ne_of_gt log_two_pos]

theorem rhoOne_landauerCostDiagonal (T : ℝ) : landauerCostDiagonal rhoOne T = 0 := by
  simp [landauerCostDiagonal, infoEnergyLowerBound, pathEntropyBits, rhoOne_vonNeumannDiagonal,
    zero_div, mul_zero, log_two_pos.ne']

theorem rhoOne_complementarity_squared_eq_one :
    fringeVisibility rhoOne ^ 2 + whichPathDistinguishability rhoOne ^ 2 = 1 := by
  rw [rhoOne_fringeVisibility, rhoOne_whichPathDistinguishability]
  norm_num

theorem rhoOne_observationCanonical_eq_after_whichPath :
    observationStateCanonical rhoOne =
      observationStateCanonical (KrausChannel.whichPathChannel.apply hnQubit rhoOne) := by
  apply ObservationState.ext
  · simp only [observationStateCanonical]
    rw [whichPathDistinguishability_whichPath_apply]
  · simp only [observationStateCanonical]
    rw [fringeVisibility_whichPath_apply, rhoOne_fringeVisibility]

theorem rhoOne_measurementUpdate_states_eq :
    (measurementUpdateWhichPath rhoOne).oldState = (measurementUpdateWhichPath rhoOne).newState := by
  simp [measurementUpdateWhichPath, rhoOne_observationCanonical_eq_after_whichPath]

theorem rhoZero_argmax_nullWhichFamily :
    argmaxProbeIndexAt nullWhichFamily rhoZero = 1 := by
  apply argmax_nullWhichFamily_eq_which_of_pos
  simp [rhoZero_whichPathDistinguishability]

theorem rhoOne_argmax_nullWhichFamily :
    argmaxProbeIndexAt nullWhichFamily rhoOne = 1 := by
  apply argmax_nullWhichFamily_eq_which_of_pos
  simp [rhoOne_whichPathDistinguishability]

theorem rhoZero_exists_constrainedOptimal_nullWhichFamily
    (T : ℝ) (hT : 0 < T) (penalty : ℝ) :
    ∃ i, IsConstrainedOptimalAt nullWhichFamily rhoZero T hT penalty i :=
  exists_constrainedOptimalAt nullWhichFamily rhoZero T hT penalty
    ⟨0, by simp [AdmissibleProbeIndices, nullWhichFamily, ProbeSelectionAdmissible_nullProbe]⟩

theorem rhoOne_exists_constrainedOptimal_nullWhichFamily
    (T : ℝ) (hT : 0 < T) (penalty : ℝ) :
    ∃ i, IsConstrainedOptimalAt nullWhichFamily rhoOne T hT penalty i :=
  exists_constrainedOptimalAt nullWhichFamily rhoOne T hT penalty
    ⟨1, by simp [AdmissibleProbeIndices, nullWhichFamily, ProbeSelectionAdmissible_whichPathProbe]⟩

end UMST.Quantum.Examples

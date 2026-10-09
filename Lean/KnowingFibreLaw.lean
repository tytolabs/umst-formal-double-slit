-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal-Double-Slit: KnowingFibreLaw.lean

  The knowing fibre's physics stated through the one predicate `UMST.ProcessFamily.SecondLaw` of umst-formal
  (`Process.lean`); this module adds no law of its own.

  * The which-path record: a Lüders path measurement leaves a record perfectly correlated with the path
    (`pathRecordJoint`); its mutual information is the probe's epistemic information (`pathRecordJoint_mutualInformation`),
    and the readout at the cost `k_B T I` is a `measureFeedback` instance (`whichPath_measureFeedback_secondLaw`).
  * Information is worth at most one bit: every admissible feedback on a path record extracts at most
    `-ΔF + k_B T ln 2` (`measureFeedback_extWork_le_landauerBitEnergy`); a probe's readout admissible under the
    measure-feedback case costs at most `k_B T ln 2` (`readoutCost_le_landauerBitEnergy_of_secondLaw`).
  * Each bit costs `k_B T ln 2` to forget: erasing the path record under the erase case costs at least
    `k_B T ln 2` per bit of path entropy (`erase_pathRecord_cost_ge_bits`), at least `k_B T (1 − D²) / 2`
    (`erase_pathRecord_cost_ge_complementarity`), and, through Englert's `V² + D² ≤ 1`, at least `k_B T V² / 2`
    (`erase_pathRecord_cost_ge_visibility_sq`).
  * The Szilard balance on the path qubit: the work a feedback extracts from the record never exceeds the work of
    erasing it at the same bath (`measure_then_erase_no_net_work`).
  * The reset process of `LandauerBound` takes its bound from the erase case (`resetProcess_of_secondLaw`).
-/

import KnowingFibreInstance
import QuantumClassicalBridge
import LandauerBound

open UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist
open UMST.Quantum UMST.DoubleSlit UMST.DoubleSlit.KnowingFibreInstance

namespace UMST.DoubleSlit.KnowingFibreLaw

/-- The record of a Lüders which-path measurement: the joint law of (path, record), with the record equal to the
    path and the path distributed by its Born weights. -/
noncomputable def pathRecordJoint (ρ : DensityMatrix hnQubit) : JointDist 2 2 where
  mass := fun xy => if xy.1 = xy.2 then pathWeight ρ xy.1 else 0
  nonneg := fun xy => by
    by_cases h : xy.1 = xy.2
    · simp only [h, if_true]
      exact pathWeight_nonneg' ρ xy.2
    · simp [h]
  sumOne := by
    rw [Fintype.sum_prod_type]
    simp [Fin.sum_univ_two, pathWeight_sum ρ]

theorem pathRecordJoint_marginalX (ρ : DensityMatrix hnQubit) :
    marginalX (pathRecordJoint ρ) = pathBornDist ρ := by
  apply ProbDist.ext_mass
  funext i
  simp only [marginalX, pathRecordJoint, pathBornDist, Fin.sum_univ_two]
  fin_cases i <;> simp

theorem pathRecordJoint_marginalY (ρ : DensityMatrix hnQubit) :
    marginalY (pathRecordJoint ρ) = pathBornDist ρ := by
  apply ProbDist.ext_mass
  funext j
  simp only [marginalY, pathRecordJoint, pathBornDist, Fin.sum_univ_two]
  fin_cases j <;> simp

theorem pathRecordJoint_jointEntropy (ρ : DensityMatrix hnQubit) :
    jointEntropy (pathRecordJoint ρ) = shannonEntropy (pathBornDist ρ) := by
  unfold jointEntropy shannonEntropy
  rw [Fintype.sum_prod_type]
  simp [pathRecordJoint, pathBornDist, Fin.sum_univ_two]

/-- The record carries exactly the which-path probe's epistemic information. -/
theorem pathRecordJoint_mutualInformation (ρ : DensityMatrix hnQubit) :
    mutualInformation (pathRecordJoint ρ) = EpistemicMI PathProbe.whichPath ρ := by
  unfold mutualInformation
  rw [pathRecordJoint_marginalX, pathRecordJoint_marginalY, pathRecordJoint_jointEntropy,
    shannonEntropy_pathBornDist, epistemicMI_whichPath]
  unfold whichPathMI
  ring

/-- The which-path readout at its cost `k_B T I` is an instance of the measure-feedback case, with equality. -/
theorem whichPath_measureFeedback_secondLaw (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) :
    UMST.ProcessFamily.SecondLaw
      (.measureFeedback (epistemicMeasureFeedback PathProbe.whichPath ρ T hT)) (.feedback (pathRecordJoint ρ)) :=
  (measureFeedback_admissible_iff PathProbe.whichPath ρ T hT (pathRecordJoint ρ)
    (pathRecordJoint_mutualInformation ρ)).2 (measurementCost_eq_kBT_epistemicMI PathProbe.whichPath ρ T).le

theorem landauerBitEnergy_eq_kB (T : ℝ) : landauerBitEnergy T = kB * T * Real.log 2 := by
  unfold landauerBitEnergy kBoltzmannSI kB
  ring

/-- **Information is worth at most one bit.** A feedback admissible under the second law on a record whose mutual
    information is a path probe's extracts at most `-ΔF + k_B T ln 2`. -/
theorem measureFeedback_extWork_le_landauerBitEnergy (f : UMST.ProcessFamily.FeedbackProcess) (p : PathProbe)
    (ρ : DensityMatrix hnQubit) {n m : ℕ} (J : JointDist n m) (hmi : mutualInformation J = EpistemicMI p ρ)
    (h : UMST.ProcessFamily.SecondLaw (.measureFeedback f) (.feedback J)) :
    f.extWork ≤ -f.deltaFreeEnergy + landauerBitEnergy f.bath.bathTemp.val := by
  have h' : f.extWork ≤ -f.deltaFreeEnergy + kB * f.bath.bathTemp.val * mutualInformation J := h
  rw [hmi] at h'
  have hk : 0 ≤ kB * f.bath.bathTemp.val := mul_nonneg kB_pos.le f.bath.bathTemp.property.le
  have hI : kB * f.bath.bathTemp.val * EpistemicMI p ρ ≤ kB * f.bath.bathTemp.val * Real.log 2 :=
    mul_le_mul_of_nonneg_left (epistemicMI_le_log_two p ρ) hk
  rw [landauerBitEnergy_eq_kB]
  linarith

/-- **The readout costs at most one bit, through the law.** A probe's readout (work its measurement cost, no
    free-energy change) that satisfies the measure-feedback case against a record carrying the probe's information
    costs at most `k_B T ln 2`: the cost bound of `MeasurementCost` taken from the second law. -/
theorem readoutCost_le_landauerBitEnergy_of_secondLaw (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ)
    (hT : 0 < T) {n m : ℕ} (J : JointDist n m) (hmi : mutualInformation J = EpistemicMI p ρ)
    (h : UMST.ProcessFamily.SecondLaw (.measureFeedback (epistemicMeasureFeedback p ρ T hT)) (.feedback J)) :
    measurementCost p ρ T ≤ landauerBitEnergy T := by
  have h' : measurementCost p ρ T ≤ -0 + landauerBitEnergy T :=
    measureFeedback_extWork_le_landauerBitEnergy _ p ρ J hmi h
  linarith

/-- The erase case on the path record, unfolded: the bath temperature times the path entropy is at most the work. -/
theorem erase_pathRecord_work (e : LandauerLaw.ErasureProcess) (ρ : DensityMatrix hnQubit)
    (h : UMST.ProcessFamily.SecondLaw (.erase e) (.erasure (pathBornDist ρ))) :
    vonNeumannDiagonal ρ * e.bath.bathTemp.val ≤ e.work := by
  have h' : shannonEntropy (pathBornDist ρ) - shannonEntropy (diracDist (0 : Fin 2)) ≤
      e.work / e.bath.bathTemp.val := h
  rwa [diracEntropy_zero LandauerLaw.two_pos (0 : Fin 2), sub_zero, shannonEntropy_pathBornDist,
    le_div_iff₀ e.bath.bathTemp.property] at h'

/-- **Each bit costs `k_B T ln 2`.** Erasing the path record under the erase case costs, in joules, at least
    `k_B T ln 2` per bit of path entropy. -/
theorem erase_pathRecord_cost_ge_bits (e : LandauerLaw.ErasureProcess) (ρ : DensityMatrix hnQubit)
    (h : UMST.ProcessFamily.SecondLaw (.erase e) (.erasure (pathBornDist ρ))) :
    landauerBitEnergy e.bath.bathTemp.val * pathEntropyBits ρ ≤ kB * e.work := by
  have hw := erase_pathRecord_work e ρ h
  have hbit : landauerBitEnergy e.bath.bathTemp.val * pathEntropyBits ρ =
      kB * (vonNeumannDiagonal ρ * e.bath.bathTemp.val) := by
    rw [landauerBitEnergy_eq_kB]
    unfold pathEntropyBits
    field_simp [ne_of_gt log_two_pos]
    ring
  rw [hbit]
  exact mul_le_mul_of_nonneg_left hw kB_pos.le

/-- The entropy of one outcome against `ln x ≤ x − 1`: `−x ln x ≥ x (1 − x)` on `[0, 1]`. -/
theorem negMulLog_ge_mul_one_sub (x : ℝ) (hx0 : 0 ≤ x) :
    x * (1 - x) ≤ Real.negMulLog x := by
  unfold Real.negMulLog
  rcases hx0.eq_or_lt with rfl | hpos
  · simp
  have hl := Real.log_le_sub_one_of_pos hpos
  nlinarith [mul_le_mul_of_nonneg_left hl hpos.le]

/-- **The Englert partner bounds the path entropy.** Twice the path entropy (nats) is at least `1 − D²`, with
    `D = |p₀ − p₁|` the which-path distinguishability: `H(p) ≥ 2 p₀ p₁ = (1 − D²) / 2`. -/
theorem one_sub_distinguishability_sq_le_two_mul_entropy (ρ : DensityMatrix hnQubit) :
    1 - whichPathDistinguishability ρ ^ 2 ≤ 2 * vonNeumannDiagonal ρ := by
  have hs := pathWeight_sum ρ
  have h0 := negMulLog_ge_mul_one_sub (pathWeight ρ 0) (pathWeight_nonneg' ρ 0)
  have h1 := negMulLog_ge_mul_one_sub (1 - pathWeight ρ 0) (by linarith [pathWeight_nonneg' ρ 1])
  have hD : whichPathDistinguishability ρ ^ 2 = (pathWeight ρ 0 - pathWeight ρ 1) ^ 2 := by
    unfold whichPathDistinguishability
    exact sq_abs _
  have hp1 : pathWeight ρ 1 = 1 - pathWeight ρ 0 := by linarith
  rw [hD, hp1]
  unfold vonNeumannDiagonal shannonBinary
  nlinarith [h0, h1]

/-- Erasing the path record costs at least `k_B T (1 − D²) / 2`. -/
theorem erase_pathRecord_cost_ge_complementarity (e : LandauerLaw.ErasureProcess) (ρ : DensityMatrix hnQubit)
    (h : UMST.ProcessFamily.SecondLaw (.erase e) (.erasure (pathBornDist ρ))) :
    kB * e.bath.bathTemp.val * (1 - whichPathDistinguishability ρ ^ 2) / 2 ≤ kB * e.work := by
  have hw := erase_pathRecord_work e ρ h
  have hE := one_sub_distinguishability_sq_le_two_mul_entropy ρ
  have hkT : 0 ≤ kB * e.bath.bathTemp.val := mul_nonneg kB_pos.le e.bath.bathTemp.property.le
  have h1 : kB * e.bath.bathTemp.val * (1 - whichPathDistinguishability ρ ^ 2) ≤
      kB * e.bath.bathTemp.val * (2 * vonNeumannDiagonal ρ) := mul_le_mul_of_nonneg_left hE hkT
  have h2 : kB * (vonNeumannDiagonal ρ * e.bath.bathTemp.val) ≤ kB * e.work :=
    mul_le_mul_of_nonneg_left hw kB_pos.le
  nlinarith [h1, h2]

/-- **Fringes cost to forget.** Through Englert's `V² + D² ≤ 1`, erasing the path record of a state of fringe
    visibility `V` costs at least `k_B T V² / 2`. -/
theorem erase_pathRecord_cost_ge_visibility_sq (e : LandauerLaw.ErasureProcess) (ρ : DensityMatrix hnQubit)
    (h : UMST.ProcessFamily.SecondLaw (.erase e) (.erasure (pathBornDist ρ))) :
    kB * e.bath.bathTemp.val * fringeVisibility ρ ^ 2 / 2 ≤ kB * e.work := by
  have hE := complementarity_fringe_path ρ
  have hV : fringeVisibility ρ ^ 2 ≤ 1 - whichPathDistinguishability ρ ^ 2 := by linarith
  have hkT : 0 ≤ kB * e.bath.bathTemp.val := mul_nonneg kB_pos.le e.bath.bathTemp.property.le
  have h1 := mul_le_mul_of_nonneg_left hV hkT
  have h2 := erase_pathRecord_cost_ge_complementarity e ρ h
  linarith

/-- **Szilard balance on the path qubit.** Measure the path with feedback at no free-energy change, then erase
    the record at the same bath: when both steps satisfy the second law, the extracted work is at most the erasure
    work in joules, so the cycle yields no net work. -/
theorem measure_then_erase_no_net_work (ρ : DensityMatrix hnQubit) (f : UMST.ProcessFamily.FeedbackProcess)
    (e : LandauerLaw.ErasureProcess) (hbath : f.bath = e.bath) (hF : f.deltaFreeEnergy = 0)
    (hmeas : UMST.ProcessFamily.SecondLaw (.measureFeedback f) (.feedback (pathRecordJoint ρ)))
    (herase : UMST.ProcessFamily.SecondLaw (.erase e) (.erasure (pathBornDist ρ))) :
    f.extWork ≤ kB * e.work := by
  have hm : f.extWork ≤ -f.deltaFreeEnergy + kB * f.bath.bathTemp.val * mutualInformation (pathRecordJoint ρ) :=
    hmeas
  rw [pathRecordJoint_mutualInformation, epistemicMI_whichPath, hF, hbath] at hm
  have hw := erase_pathRecord_work e ρ herase
  have hk : kB * (vonNeumannDiagonal ρ * e.bath.bathTemp.val) ≤ kB * e.work :=
    mul_le_mul_of_nonneg_left hw kB_pos.le
  unfold whichPathMI at hm
  linarith

/-- The reset process of `LandauerBound` whose dissipated heat is the erasure work in joules: its bound
    `landauerCostDiagonal ≤ dissipatedHeat` is discharged by the erase case of the second law. -/
noncomputable def resetProcess_of_secondLaw (e : LandauerLaw.ErasureProcess) (ρ : DensityMatrix hnQubit)
    (h : UMST.ProcessFamily.SecondLaw (.erase e) (.erasure (pathBornDist ρ))) :
    UMST.DoubleSlit.ErasureProcess e.bath.bathTemp.val where
  initial := ρ
  dissipatedHeat := kB * e.work
  secondLaw := erase_pathRecord_cost_ge_bits e ρ h

end UMST.DoubleSlit.KnowingFibreLaw

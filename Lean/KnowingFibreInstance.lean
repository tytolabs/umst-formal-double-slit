-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal-Double-Slit: KnowingFibreInstance.lean (P0-10)

  Knowing-fibre **instances** of `UMST.ProcessFamily.SecondLaw` — not a new physical law here.
  `MeasurementCost`, `ErasureChannel`, epistemic MI, and diagonal data-processing facts are
  restated as consequences of `measureFeedback` / `erase` hypotheses imported from `umst-formal`
  (`Process.lean`, P0-8). No standalone Landauer bound is introduced in double-slit.
-/

import Process
import MeasurementCost
import EpistemicMI
import InfoEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open UMST.LandauerLaw UMST.InfoTheory UMST.InfoTheory.JointDist
open UMST.Quantum UMST.DoubleSlit

namespace UMST.DoubleSlit.KnowingFibreInstance

/-- Process-family pin: sole thermodynamic law lives in `umst-formal`; double-slit adds instances only. -/
def processFamilyPin : String := "UMST.ProcessFamily.SecondLaw"

theorem processFamilyPin_eq : processFamilyPin = "UMST.ProcessFamily.SecondLaw" := rfl

/-- Born weights of the path qubit as a `ProbDist 2` (prior for erase instances). -/
noncomputable def pathBornDist (ρ : DensityMatrix hnQubit) : ProbDist 2 where
  mass := pathWeight ρ
  nonneg := fun i => pathWeight_nonneg' ρ i
  sumOne := by
    rw [Fin.sum_univ_two]
    exact pathWeight_sum ρ

theorem shannonEntropy_pathBornDist (ρ : DensityMatrix hnQubit) :
    shannonEntropy (pathBornDist ρ) = vonNeumannDiagonal ρ := by
  have hsum : shannonEntropy (pathBornDist ρ) = Real.binEntropy (pathWeight ρ 0) := by
    dsimp [shannonEntropy, pathBornDist, ProbDist.mass, pathWeight]
    rw [Fin.sum_univ_two]
    have hdiag : (ρ.carrier 1 1).re = 1 - (ρ.carrier 0 0).re := by
      have hs := pathWeight_sum ρ
      simp [pathWeight] at hs
      linarith
    simp only [hdiag, Real.binEntropy, Real.log_inv]
    ring
  rw [hsum, ← shannonBinary_eq_binEntropy, vonNeumannDiagonal]

/-- Erasure process at tight equality for the path Born prior (entropy units: `work = T · S`). -/
noncomputable def pathBornEraseProcess (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) :
    LandauerLaw.ErasureProcess where
  bath := { bathTemp := ⟨T, hT⟩ }
  work := T * shannonEntropy (pathBornDist ρ)

theorem pathBornErase_secondLaw (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) :
    eraseSecondLaw (pathBornEraseProcess ρ T hT) (pathBornDist ρ) := by
  dsimp [eraseSecondLaw, eraseSecondLawStep, pathBornEraseProcess]
  rw [diracEntropy_zero LandauerLaw.two_pos (0 : Fin 2), sub_zero, shannonEntropy_pathBornDist,
    le_div_iff₀ hT, mul_comm T (vonNeumannDiagonal ρ)]

theorem pathBornErase_processFamily (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) :
    UMST.ProcessFamily.SecondLaw (.erase (pathBornEraseProcess ρ T hT)) (.erasure (pathBornDist ρ)) :=
  pathBornErase_secondLaw ρ T hT

theorem landauerCostDiagonal_eq_kB_eraseWork (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) :
    landauerCostDiagonal ρ T = kB * (pathBornEraseProcess ρ T hT).work := by
  unfold landauerCostDiagonal infoEnergyLowerBound pathEntropyBits pathBornEraseProcess
  rw [shannonEntropy_pathBornDist]
  have hbit : landauerBitEnergy T = kB * T * Real.log 2 := by
    unfold landauerBitEnergy kBoltzmannSI kB
    ring
  rw [hbit]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  field_simp [hlog]
  ring

/-- **Erase hypothesis** for the path qubit: admissibility in the unified process family. -/
structure PathEraseHypothesis (ρ : DensityMatrix hnQubit) (T : ℝ) where
  hT : 0 < T
  admissible :
    UMST.ProcessFamily.SecondLaw (.erase (pathBornEraseProcess ρ T hT)) (.erasure (pathBornDist ρ))

theorem pathEraseHypothesis_default (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) :
    PathEraseHypothesis ρ T :=
  ⟨hT, pathBornErase_processFamily ρ T hT⟩

-- `ErasureChannel.idealResetErasure` links via `landauerCostDiagonal_eq_kB_eraseWork` + `PathEraseHypothesis`.

/-- Sagawa–Ueda `measureFeedback` packaging for probe-indexed readout work (`measurementCost`). -/
noncomputable def epistemicMeasureFeedback (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ)
    (hT : 0 < T) : UMST.ProcessFamily.FeedbackProcess where
  bath := { bathTemp := ⟨T, hT⟩ }
  extWork := measurementCost p ρ T
  deltaFreeEnergy := 0

theorem measurementCost_eq_kBT_epistemicMI (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) :
    measurementCost p ρ T = kB * T * EpistemicMI p ρ := by
  unfold measurementCost epistemicLandauerCost infoEnergyLowerBound epistemicMIBits landauerBitEnergy
    kBoltzmannSI kB
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  field_simp [hlog]
  ring

/-- **Measure-feedback hypothesis**: typed `SecondLaw` instance with aligned joint MI. -/
structure MeasureFeedbackHypothesis (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) where
  hT : 0 < T
  J : JointDist 2 2
  miAlign : mutualInformation J = EpistemicMI p ρ
  admissible :
    UMST.ProcessFamily.SecondLaw (.measureFeedback (epistemicMeasureFeedback p ρ T hT)) (.feedback J)

theorem measureFeedback_admissible_iff (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T)
    (J : JointDist 2 2) (hmi : mutualInformation J = EpistemicMI p ρ) :
    UMST.ProcessFamily.SecondLaw (.measureFeedback (epistemicMeasureFeedback p ρ T hT)) (.feedback J) ↔
      measurementCost p ρ T ≤ kB * T * EpistemicMI p ρ := by
  dsimp [UMST.ProcessFamily.SecondLaw, epistemicMeasureFeedback]
  simp [hmi, measurementCost_eq_kBT_epistemicMI p ρ T]

theorem measureFeedback_null_instance (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) :
    UMST.ProcessFamily.SecondLaw (.measureFeedback (epistemicMeasureFeedback PathProbe.null ρ T hT))
      (.feedback (productJoint uniformBinary uniformBinary)) := by
  dsimp [UMST.ProcessFamily.SecondLaw, epistemicMeasureFeedback]
  rw [mutualInformation_product_zero uniformBinary uniformBinary]
  simp [measurementCost_null, epistemicMI_null, neg_zero, zero_add]

theorem measurementCost_nonneg_from_measureFeedback (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ measurementCost p ρ T :=
  measurementCost_nonneg p ρ T hT

theorem measurementCost_null_from_measureFeedback (ρ : DensityMatrix hnQubit) (T : ℝ) :
    measurementCost PathProbe.null ρ T = 0 :=
  measurementCost_null ρ T

theorem measurementCost_le_landauerBitEnergy_from_measureFeedback (p : PathProbe)
    (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    measurementCost p ρ T ≤ landauerBitEnergy T :=
  measurementCost_le_landauerBitEnergy p ρ T hT

/-- Diagonal data-processing (MI invariance) composes with measure-feedback alignment; not a Landauer law. -/
theorem dataProcessing_epistemicMI_whichPath_invariant (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.whichPath (KrausChannel.whichPathChannel.apply hnQubit ρ) =
      EpistemicMI PathProbe.whichPath ρ :=
  epistemicMI_whichPath_apply ρ

theorem dataProcessing_diagonal_entropy_invariant (ρ : DensityMatrix hnQubit) :
    vonNeumannDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) = vonNeumannDiagonal ρ :=
  vonNeumannDiagonal_whichPath_apply ρ

def knowingFibrePhysicsGreenAuthorized : Prop := False

theorem knowingFibrePhysicsGreenAuthorized_false : ¬knowingFibrePhysicsGreenAuthorized := id

end UMST.DoubleSlit.KnowingFibreInstance

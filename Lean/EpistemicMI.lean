import EpistemicSensing

/-!
# EpistemicMI — probe-indexed mutual information (nats and bits)

This module makes epistemic information explicit by probe kind:

- `PathProbe.null`: no readout, MI = 0
- `PathProbe.whichPath`: Lüders path readout, MI = `whichPathMI = vonNeumannDiagonal`

It then derives bit-equivalent and Landauer-cost links.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

/-- Minimal probe kind for the path-qubit epistemic MI layer. -/
inductive PathProbe
  | null
  | whichPath
  deriving DecidableEq, Repr

/-- Realized `QuantumProbe` for each `PathProbe` kind. -/
noncomputable def PathProbe.toQuantumProbe : PathProbe → QuantumProbe
  | .null => nullProbe
  | .whichPath => whichPathProbe

/-- Epistemic mutual-information surrogate in nats, indexed by probe kind. -/
noncomputable def EpistemicMI (p : PathProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  match p with
  | .null => 0
  | .whichPath => whichPathMI ρ

@[simp]
theorem epistemicMI_null (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.null ρ = 0 :=
  rfl

@[simp]
theorem epistemicMI_whichPath (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.whichPath ρ = whichPathMI ρ :=
  rfl

theorem epistemicMI_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ EpistemicMI p ρ := by
  cases p <;> simp [EpistemicMI, whichPathMI_nonneg]

theorem epistemicMI_le_log_two (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    EpistemicMI p ρ ≤ Real.log 2 := by
  cases p <;> simp [EpistemicMI, whichPathMI_le_log_two]

/-- Bit-equivalent form of `EpistemicMI`. -/
noncomputable def epistemicMIBits (p : PathProbe) (ρ : DensityMatrix hnQubit) : ℝ :=
  EpistemicMI p ρ / Real.log 2

theorem epistemicMIBits_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    0 ≤ epistemicMIBits p ρ :=
  div_nonneg (epistemicMI_nonneg p ρ) (le_of_lt log_two_pos)

theorem epistemicMIBits_le_one (p : PathProbe) (ρ : DensityMatrix hnQubit) :
    epistemicMIBits p ρ ≤ 1 := by
  unfold epistemicMIBits
  rw [div_le_one log_two_pos]
  exact epistemicMI_le_log_two p ρ

@[simp]
theorem epistemicMIBits_null (ρ : DensityMatrix hnQubit) :
    epistemicMIBits PathProbe.null ρ = 0 := by
  simp [epistemicMIBits]

@[simp]
theorem epistemicMIBits_whichPath (ρ : DensityMatrix hnQubit) :
    epistemicMIBits PathProbe.whichPath ρ = pathEntropyBits ρ := by
  unfold epistemicMIBits pathEntropyBits
  simp [EpistemicMI, whichPathMI]

@[simp]
theorem epistemicMI_whichPath_apply (ρ : DensityMatrix hnQubit) :
    EpistemicMI PathProbe.whichPath (whichPathProbe.apply ρ) =
      EpistemicMI PathProbe.whichPath ρ := by
  simpa [EpistemicMI] using whichPathMI_whichPath_apply ρ

/-- Landauer hook from probe-indexed epistemic MI bits. -/
noncomputable def epistemicLandauerCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  infoEnergyLowerBound (epistemicMIBits p ρ) T

theorem epistemicLandauerCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : 0 ≤ epistemicLandauerCost p ρ T := by
  unfold epistemicLandauerCost
  exact infoEnergyLowerBound_nonneg _ _ (epistemicMIBits_nonneg p ρ) hT

theorem epistemicLandauerCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : epistemicLandauerCost p ρ T ≤ landauerBitEnergy T := by
  unfold epistemicLandauerCost infoEnergyLowerBound
  rw [← mul_one (landauerBitEnergy T)]
  exact mul_le_mul_of_nonneg_left (epistemicMIBits_le_one p ρ) (landauerBitEnergy_nonneg hT)

@[simp]
theorem epistemicLandauerCost_null (ρ : DensityMatrix hnQubit) (T : ℝ) :
    epistemicLandauerCost PathProbe.null ρ T = 0 := by
  simp [epistemicLandauerCost]

@[simp]
theorem epistemicLandauerCost_whichPath (ρ : DensityMatrix hnQubit) (T : ℝ) :
    epistemicLandauerCost PathProbe.whichPath ρ T = landauerCostDiagonal ρ T := by
  simp [epistemicLandauerCost, landauerCostDiagonal]

end UMST.DoubleSlit

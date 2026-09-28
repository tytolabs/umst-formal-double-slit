-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import EpistemicSensing
import GateCompat
import LandauerBound

/-!
# ProbeOptimization — finite probe selection with thermodynamic penalty

Builds a concrete optimization layer over `EpistemicSensing`:

- `ProbeUtility`: score = probe-strength minus `λ` times normalized Landauer hook.
- existence of maximizers over finite probe families (`exists_optimalProbeIndexAt`).
- admissibility-constrained selection (`IsConstrainedOptimalAt`, `exists_constrainedOptimalAt`).

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

/-- Positive-temperature Landauer scale is strictly positive. -/
theorem landauerBitEnergy_pos {T : ℝ} (hT : 0 < T) : 0 < landauerBitEnergy T := by
  unfold landauerBitEnergy
  exact mul_pos (mul_pos kBoltzmannSI_pos hT) (Real.log_pos (by norm_num))

/-- Cost-penalized utility (dimensionless): strength minus `λ`-weighted normalized Landauer hook. -/
noncomputable def ProbeUtility (P : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (_hT : 0 < T) (penalty : ℝ) : ℝ :=
  ProbeStrength P ρ - penalty * (LandauerCostFromProbeStrength P ρ T / landauerBitEnergy T)

theorem ProbeUtility_le_strength (P : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (penalty : ℝ) (hpenalty : 0 ≤ penalty) :
    ProbeUtility P ρ T hT penalty ≤ ProbeStrength P ρ := by
  unfold ProbeUtility
  have hnonneg : 0 ≤ penalty * (LandauerCostFromProbeStrength P ρ T / landauerBitEnergy T) := by
    exact mul_nonneg hpenalty
      (div_nonneg (LandauerCostFromProbeStrength_nonneg P ρ T (le_of_lt hT))
        (le_of_lt (landauerBitEnergy_pos hT)))
  linarith

theorem ProbeUtility_eq_strength_at_lambda_zero (P : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) :
    ProbeUtility P ρ T hT 0 = ProbeStrength P ρ := by
  simp [ProbeUtility]

/-- Pointwise utility optimality in a finite probe family. -/
def IsOptimalProbeIndexAt {ι : Type*} (family : ι → QuantumProbe)
    (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (penalty : ℝ) (i : ι) : Prop :=
  ∀ j, ProbeUtility (family j) ρ T hT penalty ≤ ProbeUtility (family i) ρ T hT penalty

theorem exists_optimalProbeIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (penalty : ℝ) :
    ∃ i, IsOptimalProbeIndexAt family ρ T hT penalty i := by
  obtain ⟨i, -, hmax⟩ :=
    (Finset.univ : Finset ι).exists_max_image
      (fun j => ProbeUtility (family j) ρ T hT penalty) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  intro j
  exact hmax j (Finset.mem_univ j)

/-- Chosen argmax index for utility over a finite probe family. -/
noncomputable def argmaxUtilityProbeIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (penalty : ℝ) : ι :=
  Classical.choose (exists_optimalProbeIndexAt family ρ T hT penalty)

theorem argmaxUtilityProbeIndexAt_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (penalty : ℝ) :
    IsOptimalProbeIndexAt family ρ T hT penalty (argmaxUtilityProbeIndexAt family ρ T hT penalty) :=
  Classical.choose_spec (exists_optimalProbeIndexAt family ρ T hT penalty)

/-- Probe-induced transition is admissible on the knowing `DensityMatrix` thermo system. -/
def ProbeSelectionAdmissible (T : ℝ) (P : QuantumProbe) (ρ : DensityMatrix hnQubit) : Prop :=
  @CoreAdmissible ℝ _ _ (DensityMatrix hnQubit) (densityMatrixThermoSystem T) ρ (P.apply ρ)

theorem ProbeSelectionAdmissible_nullProbe (T : ℝ) (ρ : DensityMatrix hnQubit) :
    ProbeSelectionAdmissible T nullProbe ρ := by
  unfold ProbeSelectionAdmissible
  rw [nullProbe_apply]
  have h := @UMST.Core.coreAdmissibleN_refl ℝ _ _ (DensityMatrix hnQubit) (densityMatrixThermoSystem T) 1 ρ
  exact (@UMST.Core.coreAdmissibleN_one ℝ _ _ (DensityMatrix hnQubit) (densityMatrixThermoSystem T) ρ ρ).mp h

theorem ProbeSelectionAdmissible_whichPathProbe (T : ℝ) (ρ : DensityMatrix hnQubit) :
    ProbeSelectionAdmissible T whichPathProbe ρ := by
  unfold ProbeSelectionAdmissible
  simpa [whichPathProbe_apply] using admissible_thermoFromQubitPath_whichPath T ρ

/-- Admissible indices in a finite probe family. -/
noncomputable def AdmissibleProbeIndices {ι : Type*} [Fintype ι] (family : ι → QuantumProbe)
    (T : ℝ) (ρ : DensityMatrix hnQubit) : Finset ι :=
  @Finset.filter ι (fun i => ProbeSelectionAdmissible T (family i) ρ)
    (Classical.decPred _) Finset.univ

/-- Constrained optimality among admissible probe indices. -/
def IsConstrainedOptimalAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (penalty : ℝ) (i : ι) : Prop :=
  i ∈ AdmissibleProbeIndices family T ρ ∧
  ∀ j ∈ AdmissibleProbeIndices family T ρ,
    ProbeUtility (family j) ρ T hT penalty ≤ ProbeUtility (family i) ρ T hT penalty

theorem exists_constrainedOptimalAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (penalty : ℝ)
    (hne : (AdmissibleProbeIndices family T ρ).Nonempty) :
    ∃ i, IsConstrainedOptimalAt family ρ T hT penalty i := by
  obtain ⟨i, hi, hmax⟩ :=
    (AdmissibleProbeIndices family T ρ).exists_max_image
      (fun j => ProbeUtility (family j) ρ T hT penalty) hne
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact hmax j hj

end UMST.DoubleSlit

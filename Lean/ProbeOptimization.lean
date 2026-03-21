/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import EpistemicSensing
import GateCompat

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
  exact mul_pos (mul_pos kB_pos hT) (Real.log_pos (by norm_num))

/-- Cost-penalized utility (dimensionless): strength minus `λ`-weighted normalized Landauer hook. -/
noncomputable def ProbeUtility (P : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) : ℝ :=
  ProbeStrength P ρ - λ * (LandauerCostFromProbeStrength P ρ T / landauerBitEnergy T)

theorem ProbeUtility_le_strength (P : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) (hλ : 0 ≤ λ) :
    ProbeUtility P ρ T hT λ ≤ ProbeStrength P ρ := by
  unfold ProbeUtility
  have hnonneg : 0 ≤ λ * (LandauerCostFromProbeStrength P ρ T / landauerBitEnergy T) := by
    exact mul_nonneg hλ
      (div_nonneg (LandauerCostFromProbeStrength_nonneg P ρ T (le_of_lt hT))
        (le_of_lt (landauerBitEnergy_pos hT)))
  linarith

theorem ProbeUtility_eq_strength_at_lambda_zero (P : QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) :
    ProbeUtility P ρ T hT 0 = ProbeStrength P ρ := by
  simp [ProbeUtility]

/-- Pointwise utility optimality in a finite probe family. -/
def IsOptimalProbeIndexAt {ι : Type*} (family : ι → QuantumProbe)
    (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (λ : ℝ) (i : ι) : Prop :=
  ∀ j, ProbeUtility (family j) ρ T hT λ ≤ ProbeUtility (family i) ρ T hT λ

theorem exists_optimalProbeIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (λ : ℝ) :
    ∃ i, IsOptimalProbeIndexAt family ρ T hT λ i := by
  obtain ⟨i, -, hmax⟩ :=
    (Finset.univ : Finset ι).exists_max_image
      (fun j => ProbeUtility (family j) ρ T hT λ) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  intro j
  exact hmax j (Finset.mem_univ j)

/-- Chosen argmax index for utility over a finite probe family. -/
noncomputable def argmaxUtilityProbeIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (λ : ℝ) : ι :=
  Classical.choose (exists_optimalProbeIndexAt family ρ T hT λ)

theorem argmaxUtilityProbeIndexAt_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (λ : ℝ) :
    IsOptimalProbeIndexAt family ρ T hT λ (argmaxUtilityProbeIndexAt family ρ T hT λ) :=
  Classical.choose_spec (exists_optimalProbeIndexAt family ρ T hT λ)

/-- Probe-induced transition is thermodynamically admissible under `thermoFromQubitPath`. -/
def ProbeSelectionAdmissible (P : QuantumProbe) (ρ : DensityMatrix hnQubit) : Prop :=
  Admissible (thermoFromQubitPath ρ) (thermoFromQubitPath (P.apply ρ))

theorem ProbeSelectionAdmissible_nullProbe (ρ : DensityMatrix hnQubit) :
    ProbeSelectionAdmissible nullProbe ρ := by
  unfold ProbeSelectionAdmissible
  rw [nullProbe_apply]
  exact admissibleRefl _

theorem ProbeSelectionAdmissible_whichPathProbe (ρ : DensityMatrix hnQubit) :
    ProbeSelectionAdmissible whichPathProbe ρ := by
  unfold ProbeSelectionAdmissible
  simpa [whichPathProbe_apply] using admissible_thermoFromQubitPath_whichPath ρ

/-- Admissible indices in a finite probe family. -/
def AdmissibleProbeIndices {ι : Type*} [Fintype ι] (family : ι → QuantumProbe)
    (ρ : DensityMatrix hnQubit) : Finset ι :=
  Finset.univ.filter (fun i => ProbeSelectionAdmissible (family i) ρ)

/-- Constrained optimality among admissible probe indices. -/
def IsConstrainedOptimalAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) (i : ι) : Prop :=
  i ∈ AdmissibleProbeIndices family ρ ∧
  ∀ j ∈ AdmissibleProbeIndices family ρ,
    ProbeUtility (family j) ρ T hT λ ≤ ProbeUtility (family i) ρ T hT λ

theorem exists_constrainedOptimalAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → QuantumProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ)
    (hne : (AdmissibleProbeIndices family ρ).Nonempty) :
    ∃ i, IsConstrainedOptimalAt family ρ T hT λ i := by
  obtain ⟨i, hi, hmax⟩ :=
    (AdmissibleProbeIndices family ρ).exists_max_image
      (fun j => ProbeUtility (family j) ρ T hT λ) hne
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact hmax j hj

end UMST.DoubleSlit

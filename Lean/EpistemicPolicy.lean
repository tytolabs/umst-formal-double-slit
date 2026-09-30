-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import EpistemicTrajectoryMI
import ProbeOptimization

/-!
# EpistemicPolicy — finite-horizon policy utility and constrained selection

Optimizes over families of policies `π : ℕ → PathProbe` at fixed horizon.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Probe policy type for finite-horizon rollouts. -/
abbrev ProbePolicy := ℕ → PathProbe

/-- Cost-penalized utility of a policy over horizon `n`. -/
noncomputable def policyUtility (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (_hT : 0 < T) (lam : ℝ) : ℝ :=
  cumulativeEpistemicMI π n ρ0
    - lam * (cumulativeEpistemicLandauerCost π n ρ0 T / landauerBitEnergy T)

theorem policyUtility_le_cumulativeMI (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) (hlam : 0 ≤ lam) :
    policyUtility π n ρ0 T hT lam ≤ cumulativeEpistemicMI π n ρ0 := by
  unfold policyUtility
  have hnonneg : 0 ≤ lam * (cumulativeEpistemicLandauerCost π n ρ0 T / landauerBitEnergy T) := by
    exact mul_nonneg hlam
      (div_nonneg (cumulativeEpistemicLandauerCost_nonneg π n ρ0 T (le_of_lt hT))
        (le_of_lt (landauerBitEnergy_pos hT)))
  linarith

/-- Optimal index for policy utility in a finite policy family. -/
def IsOptimalPolicyIndexAt {ι : Type*} (family : ι → ProbePolicy)
    (n : ℕ) (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (lam : ℝ) (i : ι) : Prop :=
  ∀ j, policyUtility (family j) n ρ0 T hT lam ≤ policyUtility (family i) n ρ0 T hT lam

theorem exists_optimalPolicyIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) :
    ∃ i, IsOptimalPolicyIndexAt family n ρ0 T hT lam i := by
  obtain ⟨i, -, hmax⟩ :=
    (Finset.univ : Finset ι).exists_max_image
      (fun j => policyUtility (family j) n ρ0 T hT lam) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  intro j
  exact hmax j (Finset.mem_univ j)

/-- Chosen argmax index for policy utility over a finite policy family. -/
noncomputable def argmaxPolicyIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) : ι :=
  Classical.choose (exists_optimalPolicyIndexAt family n ρ0 T hT lam)

theorem argmaxPolicyIndexAt_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) :
    IsOptimalPolicyIndexAt family n ρ0 T hT lam (argmaxPolicyIndexAt family n ρ0 T hT lam) :=
  Classical.choose_spec (exists_optimalPolicyIndexAt family n ρ0 T hT lam)

/-- Stepwise admissibility of a policy along the first `n` rollout states: each step passes the
thermodynamic gate at bath temperature `T`. -/
def PolicyAdmissible (T : ℝ) (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit) : Prop :=
  ∀ k, k < n → ProbeSelectionAdmissible T (PathProbe.toQuantumProbe (π k)) (rollout π k ρ0)

theorem policyAdmissible_nullPolicy (T : ℝ) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    PolicyAdmissible T nullPolicy n ρ0 := by
  intro k _
  simpa [nullPolicy, rollout_nullPolicy, PathProbe.toQuantumProbe] using
    (ProbeSelectionAdmissible_nullProbe T (rollout nullPolicy k ρ0))

theorem policyAdmissible_whichPathPolicy (T : ℝ) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    PolicyAdmissible T whichPathPolicy n ρ0 := by
  intro k _
  simpa [whichPathPolicy, PathProbe.toQuantumProbe] using
    (ProbeSelectionAdmissible_whichPathProbe T (rollout whichPathPolicy k ρ0))

/-- Admissible indices in a finite policy family at fixed horizon/state. -/
noncomputable def AdmissiblePolicyIndices {ι : Type*} [Fintype ι] (family : ι → ProbePolicy)
    (T : ℝ) (n : ℕ) (ρ0 : DensityMatrix hnQubit) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => PolicyAdmissible T (family i) n ρ0)

/-- Constrained optimality among admissible policy indices. -/
def IsConstrainedOptimalPolicyAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) (i : ι) : Prop :=
  i ∈ AdmissiblePolicyIndices family T n ρ0 ∧
  ∀ j ∈ AdmissiblePolicyIndices family T n ρ0,
    policyUtility (family j) n ρ0 T hT lam ≤ policyUtility (family i) n ρ0 T hT lam

theorem exists_constrainedOptimalPolicyAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hne : (AdmissiblePolicyIndices family T n ρ0).Nonempty) :
    ∃ i, IsConstrainedOptimalPolicyAt family n ρ0 T hT lam i := by
  obtain ⟨i, hi, hmax⟩ :=
    (AdmissiblePolicyIndices family T n ρ0).exists_max_image
      (fun j => policyUtility (family j) n ρ0 T hT lam) hne
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact hmax j hj

/-- Baseline two-policy family: always-null vs always-which-path. -/
def basicPolicyFamily : Fin 2 → ProbePolicy
  | 0 => nullPolicy
  | 1 => whichPathPolicy

theorem exists_constrainedOptimal_basicPolicyFamily (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) :
    ∃ i, IsConstrainedOptimalPolicyAt basicPolicyFamily n ρ0 T hT lam i := by
  apply exists_constrainedOptimalPolicyAt
  refine ⟨0, ?_⟩
  classical
  simp [AdmissiblePolicyIndices, basicPolicyFamily, policyAdmissible_nullPolicy T]

end UMST.DoubleSlit

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
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
    (T : ℝ) (hT : 0 < T) (λ : ℝ) : ℝ :=
  cumulativeEpistemicMI π n ρ0
    - λ * (cumulativeEpistemicLandauerCost π n ρ0 T / landauerBitEnergy T)

theorem policyUtility_le_cumulativeMI (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) (hλ : 0 ≤ λ) :
    policyUtility π n ρ0 T hT λ ≤ cumulativeEpistemicMI π n ρ0 := by
  unfold policyUtility
  have hnonneg : 0 ≤ λ * (cumulativeEpistemicLandauerCost π n ρ0 T / landauerBitEnergy T) := by
    exact mul_nonneg hλ
      (div_nonneg (cumulativeEpistemicLandauerCost_nonneg π n ρ0 T (le_of_lt hT))
        (le_of_lt (landauerBitEnergy_pos hT)))
  linarith

/-- Optimal index for policy utility in a finite policy family. -/
def IsOptimalPolicyIndexAt {ι : Type*} (family : ι → ProbePolicy)
    (n : ℕ) (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 < T) (λ : ℝ) (i : ι) : Prop :=
  ∀ j, policyUtility (family j) n ρ0 T hT λ ≤ policyUtility (family i) n ρ0 T hT λ

theorem exists_optimalPolicyIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) :
    ∃ i, IsOptimalPolicyIndexAt family n ρ0 T hT λ i := by
  obtain ⟨i, -, hmax⟩ :=
    (Finset.univ : Finset ι).exists_max_image
      (fun j => policyUtility (family j) n ρ0 T hT λ) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  intro j
  exact hmax j (Finset.mem_univ j)

/-- Chosen argmax index for policy utility over a finite policy family. -/
noncomputable def argmaxPolicyIndexAt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) : ι :=
  Classical.choose (exists_optimalPolicyIndexAt family n ρ0 T hT λ)

theorem argmaxPolicyIndexAt_spec {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) :
    IsOptimalPolicyIndexAt family n ρ0 T hT λ (argmaxPolicyIndexAt family n ρ0 T hT λ) :=
  Classical.choose_spec (exists_optimalPolicyIndexAt family n ρ0 T hT λ)

/-- Stepwise admissibility of a policy along the first `n` rollout states. -/
def PolicyAdmissible (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit) : Prop :=
  ∀ k, k < n → ProbeSelectionAdmissible ((PathProbe.toQuantumProbe (π k))) (rollout π k ρ0)

theorem policyAdmissible_nullPolicy (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    PolicyAdmissible nullPolicy n ρ0 := by
  intro k hk
  simpa [nullPolicy, rollout_nullPolicy, PathProbe.toQuantumProbe] using
    (ProbeSelectionAdmissible_nullProbe (rollout nullPolicy k ρ0))

theorem policyAdmissible_whichPathPolicy (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    PolicyAdmissible whichPathPolicy n ρ0 := by
  intro k hk
  simpa [whichPathPolicy, PathProbe.toQuantumProbe] using
    (ProbeSelectionAdmissible_whichPathProbe (rollout whichPathPolicy k ρ0))

/-- Admissible indices in a finite policy family at fixed horizon/state. -/
def AdmissiblePolicyIndices {ι : Type*} [Fintype ι] (family : ι → ProbePolicy)
    (n : ℕ) (ρ0 : DensityMatrix hnQubit) : Finset ι :=
  Finset.univ.filter (fun i => PolicyAdmissible (family i) n ρ0)

/-- Constrained optimality among admissible policy indices. -/
def IsConstrainedOptimalPolicyAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) (i : ι) : Prop :=
  i ∈ AdmissiblePolicyIndices family n ρ0 ∧
  ∀ j ∈ AdmissiblePolicyIndices family n ρ0,
    policyUtility (family j) n ρ0 T hT λ ≤ policyUtility (family i) n ρ0 T hT λ

theorem exists_constrainedOptimalPolicyAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ)
    (hne : (AdmissiblePolicyIndices family n ρ0).Nonempty) :
    ∃ i, IsConstrainedOptimalPolicyAt family n ρ0 T hT λ i := by
  obtain ⟨i, hi, hmax⟩ :=
    (AdmissiblePolicyIndices family n ρ0).exists_max_image
      (fun j => policyUtility (family j) n ρ0 T hT λ) hne
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact hmax j hj

/-- Baseline two-policy family: always-null vs always-which-path. -/
def basicPolicyFamily : Fin 2 → ProbePolicy
  | 0 => nullPolicy
  | 1 => whichPathPolicy

theorem exists_constrainedOptimal_basicPolicyFamily (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) :
    ∃ i, IsConstrainedOptimalPolicyAt basicPolicyFamily n ρ0 T hT λ i := by
  apply exists_constrainedOptimalPolicyAt
  refine ⟨0, ?_⟩
  simp [AdmissiblePolicyIndices, basicPolicyFamily, policyAdmissible_nullPolicy]

end UMST.DoubleSlit

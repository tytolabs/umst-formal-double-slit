import EpistemicDynamics

/-!
# EpistemicTrajectoryMI — cumulative information and cost over rollouts

Finite-horizon aggregation of probe-indexed epistemic MI and corresponding Landauer hooks.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- Cumulative epistemic MI (nats) along first `n` rollout steps. -/
noncomputable def cumulativeEpistemicMI (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) : ℝ :=
  ∑ k in Finset.range n, EpistemicMI (π k) (rollout π k ρ0)

theorem cumulativeEpistemicMI_nonneg (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    0 ≤ cumulativeEpistemicMI π n ρ0 := by
  unfold cumulativeEpistemicMI
  exact Finset.sum_nonneg (fun k hk => epistemicMI_nonneg (π k) (rollout π k ρ0))

theorem cumulativeEpistemicMI_le (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    cumulativeEpistemicMI π n ρ0 ≤ n * Real.log 2 := by
  unfold cumulativeEpistemicMI
  calc
    ∑ k in Finset.range n, EpistemicMI (π k) (rollout π k ρ0)
      ≤ ∑ k in Finset.range n, Real.log 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact epistemicMI_le_log_two (π k) (rollout π k ρ0)
    _ = n * Real.log 2 := by simp

/-- Cumulative bit-equivalent epistemic MI along first `n` rollout steps. -/
noncomputable def cumulativeEpistemicMIBits (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) : ℝ :=
  ∑ k in Finset.range n, epistemicMIBits (π k) (rollout π k ρ0)

theorem cumulativeEpistemicMIBits_nonneg (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    0 ≤ cumulativeEpistemicMIBits π n ρ0 := by
  unfold cumulativeEpistemicMIBits
  exact Finset.sum_nonneg (fun k hk => epistemicMIBits_nonneg (π k) (rollout π k ρ0))

theorem cumulativeEpistemicMIBits_le (π : ℕ → PathProbe) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    cumulativeEpistemicMIBits π n ρ0 ≤ n := by
  unfold cumulativeEpistemicMIBits
  calc
    ∑ k in Finset.range n, epistemicMIBits (π k) (rollout π k ρ0)
      ≤ ∑ k in Finset.range n, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact epistemicMIBits_le_one (π k) (rollout π k ρ0)
    _ = n := by simp

/-- Cumulative Landauer hook from epistemic MI bits over the first `n` steps. -/
noncomputable def cumulativeEpistemicLandauerCost (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  ∑ k in Finset.range n, epistemicLandauerCost (π k) (rollout π k ρ0) T

theorem cumulativeEpistemicLandauerCost_nonneg (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ cumulativeEpistemicLandauerCost π n ρ0 T := by
  unfold cumulativeEpistemicLandauerCost
  exact Finset.sum_nonneg (fun k hk =>
    epistemicLandauerCost_nonneg (π k) (rollout π k ρ0) T hT)

theorem cumulativeEpistemicLandauerCost_le (π : ℕ → PathProbe) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    cumulativeEpistemicLandauerCost π n ρ0 T ≤ n * landauerBitEnergy T := by
  unfold cumulativeEpistemicLandauerCost
  calc
    ∑ k in Finset.range n, epistemicLandauerCost (π k) (rollout π k ρ0) T
      ≤ ∑ k in Finset.range n, landauerBitEnergy T := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact epistemicLandauerCost_le_landauerBitEnergy (π k) (rollout π k ρ0) T hT
    _ = n * landauerBitEnergy T := by simp

@[simp]
theorem cumulativeEpistemicMI_nullPolicy (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    cumulativeEpistemicMI nullPolicy n ρ0 = 0 := by
  unfold cumulativeEpistemicMI
  refine Finset.sum_eq_zero (fun k hk => ?_)
  simp [nullPolicy, rollout_nullPolicy, EpistemicMI]

@[simp]
theorem cumulativeEpistemicLandauerCost_nullPolicy (n : ℕ) (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    cumulativeEpistemicLandauerCost nullPolicy n ρ0 T = 0 := by
  unfold cumulativeEpistemicLandauerCost
  refine Finset.sum_eq_zero (fun k hk => ?_)
  simp [nullPolicy, rollout_nullPolicy, epistemicLandauerCost_null]

end UMST.DoubleSlit

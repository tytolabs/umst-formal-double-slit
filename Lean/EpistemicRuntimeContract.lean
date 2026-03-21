import EpistemicPolicy

/-!
# EpistemicRuntimeContract — bridge from abstract policy to rollout traces

This module exposes an explicit contract between runtime traces and the abstract policy layer.

- Runtime state at step `k` is `rollout π k ρ0`.
- Aggregate MI and Landauer expressions in policy theorems are exactly sums over these trace steps.

No new axioms are introduced.
-/

namespace UMST.DoubleSlit

open scoped BigOperators
open UMST.Core UMST.Quantum

/-- State at step `k` of the rollout trace (canonical runtime observation). -/
abbrev traceStateAt (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (k : ℕ) :
    DensityMatrix hnQubit :=
  rollout π k ρ0

/-- Probe choice at step `k` of the rollout trace. -/
abbrev traceProbeAt (π : ProbePolicy) (k : ℕ) : PathProbe :=
  π k

/-- Coherence of runtime trace with the rollout recursion. -/
def RuntimeTraceCoherent (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit) : Prop :=
  traceStateAt π ρ0 0 = ρ0 ∧
  ∀ k, k < n → traceStateAt π ρ0 (k + 1) = stepProbe (π k) (traceStateAt π ρ0 k)

/-- Runtime contract for cumulative MI. -/
def RuntimeTraceContractMI (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit) : Prop :=
  cumulativeEpistemicMI π n ρ0 = ∑ k in Finset.range n, EpistemicMI (π k) (traceStateAt π ρ0 k)

/-- Runtime contract for cumulative Landauer hook. -/
def RuntimeTraceContractLandauer (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) : Prop :=
  cumulativeEpistemicLandauerCost π n ρ0 T =
    ∑ k in Finset.range n, epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T

@[simp]
theorem traceStateAt_zero (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) :
    traceStateAt π ρ0 0 = ρ0 :=
  rfl

@[simp]
theorem traceStateAt_succ (π : ProbePolicy) (ρ0 : DensityMatrix hnQubit) (k : ℕ) :
    traceStateAt π ρ0 (k + 1) = stepProbe (π k) (traceStateAt π ρ0 k) :=
  rfl

theorem rollout_satisfies_traceCoherent (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    RuntimeTraceCoherent π n ρ0 := by
  constructor
  · rfl
  · intro k hk
    simpa using (traceStateAt_succ π ρ0 k)

theorem rollout_satisfies_traceContractMI (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit) :
    RuntimeTraceContractMI π n ρ0 :=
  rfl

theorem rollout_satisfies_traceContractLandauer (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) (T : ℝ) :
    RuntimeTraceContractLandauer π n ρ0 T :=
  rfl

/-- Policy admissibility is exactly stepwise admissibility along the rollout trace. -/
theorem policyAdmissible_iff_traceStepsAdmissible (π : ProbePolicy) (n : ℕ)
    (ρ0 : DensityMatrix hnQubit) :
    PolicyAdmissible π n ρ0 ↔
      ∀ k, k < n → ProbeSelectionAdmissible (PathProbe.toQuantumProbe (π k)) (traceStateAt π ρ0 k) :=
  Iff.rfl

/-- Constrained-optimal policy index dominates every admissible competitor in utility. -/
theorem constrainedOptimal_traceUtilityDominates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 < T) (λ : ℝ) (i : ι)
    (hopt : IsConstrainedOptimalPolicyAt family n ρ0 T hT λ i)
    (j : ι) (hadm : j ∈ AdmissiblePolicyIndices family n ρ0) :
    policyUtility (family j) n ρ0 T hT λ ≤ policyUtility (family i) n ρ0 T hT λ :=
  hopt.2 j hadm

theorem traceStep_MI_le_log_two (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (k : ℕ) (hk : k < n) :
    EpistemicMI (π k) (traceStateAt π ρ0 k) ≤ Real.log 2 :=
  epistemicMI_le_log_two (π k) (traceStateAt π ρ0 k)

theorem traceStep_landauer_le_bitEnergy (π : ProbePolicy) (n : ℕ) (ρ0 : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) (hk : k < n) :
    epistemicLandauerCost (π k) (traceStateAt π ρ0 k) T ≤ landauerBitEnergy T :=
  epistemicLandauerCost_le_landauerBitEnergy (π k) (traceStateAt π ρ0 k) T hT

end UMST.DoubleSlit

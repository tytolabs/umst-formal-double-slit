import DoubleSlitCore
import InfoEntropy

/-!
# LandauerBound — diagonal path entropy ↔ Landauer energy scale

`vonNeumannDiagonal ρ` is in **nats** (`Real.log`). Landauer bit energy uses the same `log`, so
bit-equivalent entropy is **`vonNeumannDiagonal ρ / log 2`**.

This layer records a **nonnegative SI joule** scale `landauerCostDiagonal ρ T` via existing
`infoEnergyLowerBound`. It does **not** assert that a particular physical process attains equality;
that requires a full erasure / dissipation model.

**Proved:** costing is nonnegative for `T ≥ 0`, **invariant under `whichPathChannel.apply`**, and
`pathEntropyBits ρ ≤ 1` hence **`landauerCostDiagonal ρ T ≤ landauerBitEnergy T`** for `T ≥ 0`
(one Landauer bit-energy unit bounds the diagonal-entropy hook).
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum Real

lemma log_two_pos : 0 < log 2 :=
  log_pos (by norm_num : (1 : ℝ) < 2)

/-- Diagonal path entropy (nats) expressed in Landauer **bit-equivalents** (`/ log 2`). -/
noncomputable def pathEntropyBits (ρ : DensityMatrix hnQubit) : ℝ :=
  vonNeumannDiagonal ρ / log 2

theorem pathEntropyBits_nonneg (ρ : DensityMatrix hnQubit) : 0 ≤ pathEntropyBits ρ :=
  div_nonneg (vonNeumannDiagonal_nonneg ρ) (le_of_lt log_two_pos)

theorem pathEntropyBits_le_one (ρ : DensityMatrix hnQubit) : pathEntropyBits ρ ≤ 1 := by
  unfold pathEntropyBits
  rw [div_le_one log_two_pos]
  exact vonNeumannDiagonal_le_log_two ρ

/-- SI joules: `k_B T log 2` times bit-equivalent diagonal entropy. -/
noncomputable def landauerCostDiagonal (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  infoEnergyLowerBound (pathEntropyBits ρ) T

theorem landauerCostDiagonal_nonneg (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ landauerCostDiagonal ρ T := by
  unfold landauerCostDiagonal
  exact infoEnergyLowerBound_nonneg _ _ (pathEntropyBits_nonneg ρ) hT

theorem landauerCostDiagonal_le_landauerBitEnergy (ρ : DensityMatrix hnQubit) (T : ℝ) (hT : 0 ≤ T) :
    landauerCostDiagonal ρ T ≤ landauerBitEnergy T := by
  unfold landauerCostDiagonal infoEnergyLowerBound
  rw [← mul_one (landauerBitEnergy T)]
  exact mul_le_mul_of_nonneg_left (pathEntropyBits_le_one ρ) (landauerBitEnergy_nonneg hT)

@[simp]
theorem landauerCostDiagonal_whichPathInvariant (ρ : DensityMatrix hnQubit) (T : ℝ) :
    landauerCostDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) T =
      landauerCostDiagonal ρ T := by
  simp [landauerCostDiagonal, pathEntropyBits, vonNeumannDiagonal_whichPath_apply]

/-- A concrete physical erasure process that resets the qubit, dissipating heat to a bath at temperature T.
We idealize erasure such that the bound is physically saturated by an active bounding axiom. -/
structure ErasureProcess (T : ℝ) where
  initial : DensityMatrix hnQubit
  dissipatedHeat : ℝ
  /-- The Second Law binds the physical dissipation strongly to the informational entropy drop.
  Since the final state is pure (0 entropy), the drop is exactly the initial entropy cost. -/
  secondLaw : landauerCostDiagonal initial T ≤ dissipatedHeat

/-- A direct consequence of the Second Law connection: resetting any state dissipates nonnegative heat. -/
theorem erasure_dissipation_nonneg (T : ℝ) (hT : 0 ≤ T) (proc : ErasureProcess T) :
    0 ≤ proc.dissipatedHeat := by
  have h := proc.secondLaw
  have h0 := landauerCostDiagonal_nonneg proc.initial T hT
  linarith

end UMST.DoubleSlit

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import EpistemicMI
import LandauerBound

/-!
# MeasurementCost — probe-indexed dissipation scale (knowing-fibre instance layer)

Thermodynamic content is **`UMST.ProcessFamily.SecondLaw`** on `measureFeedback` / `erase`
instances (`KnowingFibreInstance.lean`, P0-10) — not a standalone Landauer law in double-slit.

This module keeps the **operational alias** `measurementCost = epistemicLandauerCost` for
cross-lang sync. Consequences under typed `SecondLaw` hypotheses are proved there.

Key algebraic properties (unchanged API):
1. The cost is **nonneg** for `T ≥ 0`.
2. **Null probe** → cost = 0 (zero information, zero mandatory dissipation).
3. **Which-path probe** → cost equals `landauerCostDiagonal ρ T`, bounded by
   one Landauer bit-energy.
4. **Invariance**: after the which-path channel has been applied the cost formula
   yields the same value (diagonal entropy is channel-invariant).
5. **History**: a sequence of `n` readouts costs at most `n` Landauer bit-energies, nothing under the null
   policy, and exactly `n` times the first readout when the which-path probe is repeated on the state it leaves.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum _root_.Real

-- ============================================================
-- Re-export / abbreviation for cross-lang documentation
-- ============================================================

/-- The minimum thermodynamic work needed to acquire the information provided by
    probe `p` on state `ρ` at bath temperature `T`, in joules (`landauerBitEnergy` carries the SI `k_B`).
    Directly aliases `epistemicLandauerCost` so this module is the canonical entry
    point for the "MeasurementCost" ticket. -/
noncomputable def measurementCost (p : PathProbe) (ρ : DensityMatrix hnQubit) (T : ℝ) : ℝ :=
  epistemicLandauerCost p ρ T

-- ============================================================
-- Basic properties
-- ============================================================

theorem measurementCost_nonneg (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : 0 ≤ measurementCost p ρ T :=
  epistemicLandauerCost_nonneg p ρ T hT

/-- No information acquired → no mandatory energy dissipation. -/
theorem measurementCost_null (ρ : DensityMatrix hnQubit) (T : ℝ) :
    measurementCost PathProbe.null ρ T = 0 := by
  simp [measurementCost]

/-- Which-path readout cost equals the diagonal Landauer cost. -/
theorem measurementCost_whichPath (ρ : DensityMatrix hnQubit) (T : ℝ) :
    measurementCost PathProbe.whichPath ρ T = landauerCostDiagonal ρ T := by
  simp [measurementCost]

/-- The cost is bounded by one Landauer bit-energy (path entropy ≤ 1 bit). -/
theorem measurementCost_le_landauerBitEnergy (p : PathProbe) (ρ : DensityMatrix hnQubit)
    (T : ℝ) (hT : 0 ≤ T) : measurementCost p ρ T ≤ landauerBitEnergy T :=
  epistemicLandauerCost_le_landauerBitEnergy p ρ T hT

-- ============================================================
-- Channel invariance
-- ============================================================

/-- After applying the which-path channel, the which-path cost is unchanged
    (diagonal entropy is invariant under the Lüders channel). -/
theorem measurementCost_whichPath_channel_invariant (ρ : DensityMatrix hnQubit) (T : ℝ) :
    measurementCost PathProbe.whichPath
        (KrausChannel.whichPathChannel.apply hnQubit ρ) T =
      measurementCost PathProbe.whichPath ρ T := by
  simp [measurementCost, epistemicLandauerCost, landauerCostDiagonal,
        infoEnergyLowerBound, pathEntropyBits,
        vonNeumannDiagonal_whichPath_apply]

-- ============================================================
-- History of readouts
-- ============================================================

/-- The cost of the readouts `probes 0, …, probes (n-1)` on the states `ρ 0, …, ρ (n-1)`, for any dynamics producing them. -/
noncomputable def historyCost (probes : ℕ → PathProbe) (ρ : ℕ → DensityMatrix hnQubit) (n : ℕ) (T : ℝ) : ℝ :=
  ∑ k in Finset.range n, measurementCost (probes k) (ρ k) T

theorem historyCost_nonneg (probes : ℕ → PathProbe) (ρ : ℕ → DensityMatrix hnQubit) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ historyCost probes ρ n T :=
  Finset.sum_nonneg fun k _ => measurementCost_nonneg (probes k) (ρ k) T hT

/-- `n` readouts cost at most `n` Landauer bit-energies. -/
theorem historyCost_le (probes : ℕ → PathProbe) (ρ : ℕ → DensityMatrix hnQubit) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    historyCost probes ρ n T ≤ n * landauerBitEnergy T := by
  unfold historyCost
  calc ∑ k in Finset.range n, measurementCost (probes k) (ρ k) T
      ≤ ∑ _k in Finset.range n, landauerBitEnergy T :=
        Finset.sum_le_sum fun k _ => measurementCost_le_landauerBitEnergy (probes k) (ρ k) T hT
    _ = n * landauerBitEnergy T := by simp

/-- A history of null readouts costs nothing. -/
theorem historyCost_null (ρ : ℕ → DensityMatrix hnQubit) (n : ℕ) (T : ℝ) :
    historyCost (fun _ => PathProbe.null) ρ n T = 0 := by
  simp [historyCost, measurementCost_null]

/-- The states left by repeating the which-path readout: `ρ`, then the which-path channel applied `k` times. -/
noncomputable def whichPathRollout (ρ : DensityMatrix hnQubit) : ℕ → DensityMatrix hnQubit
  | 0 => ρ
  | k + 1 => KrausChannel.whichPathChannel.apply hnQubit (whichPathRollout ρ k)

/-- Every repetition of the which-path readout costs what the first one did. -/
theorem measurementCost_whichPathRollout (ρ : DensityMatrix hnQubit) (T : ℝ) (k : ℕ) :
    measurementCost PathProbe.whichPath (whichPathRollout ρ k) T = measurementCost PathProbe.whichPath ρ T := by
  induction k with
  | zero => rfl
  | succ k ih => rw [whichPathRollout, measurementCost_whichPath_channel_invariant, ih]

/-- Repeating the which-path readout `n` times costs `n` times the first readout: decoherence by the first look
    does not make later looks cheaper. -/
theorem historyCost_whichPath_repeat (ρ : DensityMatrix hnQubit) (n : ℕ) (T : ℝ) :
    historyCost (fun _ => PathProbe.whichPath) (whichPathRollout ρ) n T =
      n * measurementCost PathProbe.whichPath ρ T := by
  simp [historyCost, measurementCost_whichPathRollout]

end UMST.DoubleSlit

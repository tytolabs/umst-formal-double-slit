import EpistemicMI
import LandauerBound

/-!
# MeasurementCost — physical energy lower bound for quantum path measurement

Formal statement of the **measurement cost principle** in the double-slit context:

- Any readout that acquires `epistemicMIBits p ρ` bits of which-path information
  requires at minimum `epistemicLandauerCost p ρ T` joules of dissipated work at
  temperature `T` (Landauer's principle applied to the acquired information).

Key results:
1. The cost is **nonneg** for `T ≥ 0`.
2. **Null probe** → cost = 0 (zero information, zero mandatory dissipation).
3. **Which-path probe** → cost equals `landauerCostDiagonal ρ T`, bounded by
   one Landauer bit-energy.
4. **Invariance**: after the which-path channel has been applied the cost formula
   yields the same value (diagonal entropy is channel-invariant).
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum Real

-- ============================================================
-- Re-export / abbreviation for cross-lang documentation
-- ============================================================

/-- The minimum thermodynamic work needed to acquire the information provided by
    probe `p` on state `ρ` at bath temperature `T` (joules, k_B = 1 convention).
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

end UMST.DoubleSlit

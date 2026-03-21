import UMSTCore
import MeasurementChannel
import QuantumClassicalBridge

/-!
# GateCompat — UMST `Admissible` shape vs qubit path statistics

Maps a `2 × 2` density matrix to a **minimal** `ThermodynamicState` so that the four `UMST.Core`
conjuncts can be checked. The mapping is intentionally **schematic**: Born weights sit in `density`
and `freeEnergy`; `hydration` and `strength` are fixed at `0` so the latter two conjuncts are trivial.

**Proved:** after **`whichPathChannel.apply`**, the scaffold is **unchanged** (diagonal / Born weights
invariant), hence **`Admissible` holds** between before/after (in fact reflexively on the image).

**Not yet:** physically motivated `ℝ` calibration, or nontrivial hydration/strength from QM.
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

/-- Minimal ℝ scaffold from computational-basis path weights. -/
noncomputable def thermoFromQubitPath (ρ : DensityMatrix hnQubit) : ThermodynamicState where
  density := pathWeight ρ 0
  freeEnergy := pathWeight ρ 1
  hydration := 0
  strength := 0

@[simp]
theorem thermoFromQubitPath_whichPath (ρ : DensityMatrix hnQubit) :
    thermoFromQubitPath (KrausChannel.whichPathChannel.apply hnQubit ρ) = thermoFromQubitPath ρ := by
  simp [thermoFromQubitPath, pathWeight_whichPath_apply]

theorem admissible_thermoFromQubitPath_whichPath (ρ : DensityMatrix hnQubit) :
    Admissible (thermoFromQubitPath ρ)
      (thermoFromQubitPath (KrausChannel.whichPathChannel.apply hnQubit ρ)) := by
  rw [thermoFromQubitPath_whichPath]
  exact admissibleRefl _

end UMST.DoubleSlit

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Complementarity
import DoubleSlitMeasurementUpdate
import GateCompat
import LandauerBound

/-!
# DoubleSlit — full-chain import closure + which-path measurement update

Import this module (or run `lake build`) to ensure **complementarity**, **Landauer diagonal costing**,
and **gate compatibility** layers all compile together.

**`measurementUpdateWhichPath`:** packages Lüders which-path on a qubit density matrix as a
`DoubleSlitCore.MeasurementUpdate`: `I` unchanged (diagonal Born weights), `V` drops to `0`, both
ends complementary.

Main entry points:
* `UMST.DoubleSlit.complementarityEnglert`
* `UMST.DoubleSlit.landauerCostDiagonal_nonneg`, `landauerCostDiagonal_whichPathInvariant`
* `UMST.DoubleSlit.admissible_thermoFromQubitPath_whichPath`
* `UMST.DoubleSlit.measurementUpdateWhichPath`, `measurementUpdateWhichPath_new_V`
* `UMST.DoubleSlit.measurementUpdateWhichPath_landauer_eq`
* `UMST.DoubleSlit.measurementUpdateWhichPath_landauer_le_landauerBitEnergy`
* `UMST.DoubleSlit.interference_preserved_identity`
* `UMST.DoubleSlit.collapse_fringe_on_whichPath`
* `UMST.DoubleSlit.measurementUpdateWhichPath_gateEnforcement`
* `UMST.DoubleSlit.principle_of_maximal_information_collapse`
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

/-- Combined gate narrative: admissible thermo update + Landauer invariance + one-bit cap. -/
theorem measurementUpdateWhichPath_gateEnforcement (ρ : DensityMatrix hnQubit) (T : ℝ)
    (hT : 0 ≤ T) :
    Admissible (thermoFromQubitPath ρ)
      (thermoFromQubitPath (KrausChannel.whichPathChannel.apply hnQubit ρ)) ∧
    landauerCostDiagonal ρ T =
      landauerCostDiagonal (KrausChannel.whichPathChannel.apply hnQubit ρ) T ∧
    landauerCostDiagonal ρ T ≤ landauerBitEnergy T :=
  ⟨admissible_thermoFromQubitPath_whichPath ρ,
    (landauerCostDiagonal_whichPathInvariant ρ T).symm,
    landauerCostDiagonal_le_landauerBitEnergy ρ T hT⟩

end UMST.DoubleSlit

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import QuantumClassicalBridge
import GateCompat
import LandauerBound
import TensorPartialTrace
import WhichPathMeasurementUpdate

/-!
# DoubleSlit — full-chain import closure + which-path measurement update

Import this module (or run `lake build`) to ensure **complementarity**, **Landauer diagonal costing**,
and **gate compatibility** layers all compile together.

**`measurementUpdateWhichPath`** and fringe/channel lemmas live in `WhichPathMeasurementUpdate` (single
source of truth).

Main entry points:
* `UMST.Quantum.complementarity_fringe_path`
* `UMST.DoubleSlit.landauerCostDiagonal_nonneg`, `landauerCostDiagonal_whichPathInvariant`
* `UMST.DoubleSlit.admissible_densityMatrix_whichPath`
* `UMST.DoubleSlit.measurementUpdateWhichPath`, `measurementUpdateWhichPath_new_V`
* `UMST.DoubleSlit.measurementUpdateWhichPath_landauer_eq`
* `UMST.DoubleSlit.measurementUpdateWhichPath_landauer_le_landauerBitEnergy`
* `UMST.DoubleSlit.interference_preserved_identity`
* `UMST.Quantum.fringeVisibility_whichPath_apply`
* `UMST.DoubleSlit.principle_of_maximal_information_collapse`
-/

namespace UMST.DoubleSlit

open UMST.Core UMST.Quantum

end UMST.DoubleSlit

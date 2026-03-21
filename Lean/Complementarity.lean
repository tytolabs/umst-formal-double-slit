/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import QuantumClassicalBridge

/-!
# Complementarity — discoverability shim

The Englert-style inequality is proved in `QuantumClassicalBridge`. This module repeats it under
`UMST.DoubleSlit` next to `Complementary` / `ObservationState` for grep-friendly discovery.
-/

namespace UMST.DoubleSlit

open UMST.Quantum

/-- `V² + I² ≤ 1` for canonical fringe visibility and coarse which-path score. -/
theorem complementarityEnglert (ρ : DensityMatrix hnQubit) :
    fringeVisibility ρ ^ 2 + whichPathDistinguishability ρ ^ 2 ≤ 1 :=
  complementarity_fringe_path ρ

theorem observationCanonical_complementary (ρ : DensityMatrix hnQubit) :
    Complementary (observationStateCanonical ρ) :=
  observationStateCanonical_complementary ρ

end UMST.DoubleSlit

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Core.Gate
import GateCompat

/-!
# QRBridge — Formal Coercion from ℚ `UMST.Core` to ℝ `RealThermodynamicState`

This file provides the formal bridge theorem explicitly connecting the discrete
`UMST.Core.CoreAdmissible` (over `ℚ`) back to the continuous `RealAdmissible` scaffold
used by the quantum measurement states.

While we cannot define the continuous quantum states natively as instances of the
`ℚ`-hardcoded `ThermodynamicSystem` without arbitrary truncation, this theorem proves
that *if* a system satisfies the upstream ℚ-admissibility bounds, its exact ℝ-casted
projection structurally satisfies the continuous `RealAdmissible` bounds.
-/

namespace UMST.DoubleSlit

open UMST.Core

/-- Formal embedding of the upstream ℚ-valued thermodynamic typeclass properties into the ℝ scaffold. -/
noncomputable def thermodynamicSystemToReal {S : Type} [ThermodynamicSystem S] (s : S) : RealThermodynamicState where
  density := (ThermodynamicSystem.density s : ℝ)
  freeEnergy := (ThermodynamicSystem.freeEnergy s : ℝ)

/-- 
Bridge Theorem: The upstream exact `CoreAdmissible` (which uses ℚ bounds) strictly 
implies the continuous `RealAdmissible` bounds under the `ℚ → ℝ` coercion. 
This definitively connects the two disconnected scaffolds via a one-directional formal proof.
-/
theorem admissible_thermodynamicSystemToReal {S : Type} [ThermodynamicSystem S]
    {old new : S} (h : CoreAdmissible old new) :
    RealAdmissible (thermodynamicSystemToReal old) (thermodynamicSystemToReal new) := by
  constructor
  · -- Mass Density: |new - old| <= δMass
    simp [thermodynamicSystemToReal]
    have hcast : ((|ThermodynamicSystem.density new - ThermodynamicSystem.density old| : ℚ) : ℝ) =
        |((ThermodynamicSystem.density new : ℝ) - (ThermodynamicSystem.density old : ℝ))| := by
      rw [← Rat.cast_sub, Rat.cast_abs]
    rw [← hcast]
    -- Since the upstream condition is |Δρ|_ℚ <= δMass_ℚ, casting preserves the inequality
    exact_mod_cast h.massDensity
  · -- Clausius Duhem: new <= old
    simp [thermodynamicSystemToReal]
    exact_mod_cast h.clausiusDuhem

end UMST.DoubleSlit

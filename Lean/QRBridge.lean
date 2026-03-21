/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Gate
import UMSTCore

/-!
# QRBridge — ℚ thermodynamic gate ↔ ℝ `UMSTCore` scaffold

The upstream `Gate.lean` layer uses **ℚ-valued** `ThermodynamicState` and `Admissible`.
`UMSTCore` uses **ℝ** for composition with quantum / classical projections.

This file gives the canonical coercion and proves that **ℚ admissibility implies ℝ admissibility**
for the same four conjuncts (mass, Clausius–Duhem, hydration, strength).
-/

namespace UMST.DoubleSlit

open UMST

/-- Embed a ℚ-valued UMST thermodynamic state into the ℝ scaffold used by `GateCompat` / sim hooks. -/
noncomputable def thermodynamicStateToReal (s : ThermodynamicState) : UMST.Core.ThermodynamicState where
  density := s.density
  freeEnergy := s.freeEnergy
  hydration := s.hydration
  strength := s.strength

theorem admissible_thermodynamicStateToReal {old new : ThermodynamicState} (h : Admissible old new) :
    UMST.Core.Admissible (thermodynamicStateToReal old) (thermodynamicStateToReal new) := by
  rcases h with ⟨hm, hc, hh, hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Mass: `|↑Δρ| = ↑( |Δρ|_ℚ )` and `↑100` matches `Core.δMass`.
    simp [UMST.Core.MassCond, thermodynamicStateToReal, UMST.Core.δMass]
    have hcast :
        ((|new.density - old.density| : ℚ) : ℝ) = |((new.density : ℝ) - (old.density : ℝ))| := by
      rw [← Rat.cast_sub, Rat.cast_abs]
    rw [← hcast]
    exact_mod_cast hm
  · simp [UMST.Core.DissipCond, thermodynamicStateToReal]; exact_mod_cast hc
  · simp [UMST.Core.HydratCond, thermodynamicStateToReal]; exact_mod_cast hh
  · simp [UMST.Core.StrengthCond, thermodynamicStateToReal]; exact_mod_cast hs

end UMST.DoubleSlit

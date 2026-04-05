/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import LindbladDynamics
import Mathlib.Topology.Instances.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# LindbladStreamD — discrete stream-D sampling of the dephasing semigroup

Placed as **`LindbladStreamD.lean`** (not `LindbladDynamics/StreamD_*.lean`) to avoid a Lake
**module name clash** between `LindbladDynamics.lean` and a `LindbladDynamics/` directory.

**`streamD_sampling`:** evaluate `dephasingSolution ρ (n : ℝ)` at integer times `n : ℕ`.
This is the natural discrete “stream-D” readout of the same closed-form Lindblad dephasing
trajectory already analyzed continuously in `LindbladDynamics.lean`.
-/

open scoped Topology

open Filter

namespace UMST.Quantum

/-- Discrete stream-D samples of the qubit dephasing solution at times `t = n : ℝ`. -/
noncomputable def streamD_sampling (ρ : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  dephasingSolution ρ (n : ℝ)

/-- As `n → ∞`, each matrix entry converges to the **computational Lüders / diagonal** limit:
on-diagonal entries stay at `ρᵢᵢ`, off-diagonals tend to `0` (same data as `dephasingSolution_tendsto_diagonal`,
composed with `Nat.cast` tending to `+∞`). -/
theorem streamD_limit_to_Lueders_states (ρ : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    Tendsto (fun n : ℕ => streamD_sampling ρ n a b) atTop
      (nhds (if a = b then ρ a a else 0 : ℂ)) := by
  by_cases hab : a = b
  · subst hab
    simp [streamD_sampling, dephasingSolution]
    exact tendsto_const_nhds
  · simp [streamD_sampling, dephasingSolution, hab]
    exact (dephasingSolution_tendsto_diagonal ρ a b hab).comp tendsto_natCast_atTop_atTop

end UMST.Quantum

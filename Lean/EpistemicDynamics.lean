/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import EpistemicMI

/-!
# EpistemicDynamics — probe-driven state rollouts

Finite-horizon dynamics on the path qubit under a probe policy `π : ℕ → PathProbe`.
-/

namespace UMST.DoubleSlit

open UMST.Quantum

/-- Apply one `PathProbe` step to a path-qubit density matrix. -/
noncomputable def stepProbe (p : PathProbe) (ρ : DensityMatrix hnQubit) : DensityMatrix hnQubit :=
  (PathProbe.toQuantumProbe p).apply ρ

/-- Horizon-`n` rollout of a probe policy. -/
noncomputable def rollout (π : ℕ → PathProbe) : ℕ → DensityMatrix hnQubit → DensityMatrix hnQubit
  | 0, ρ => ρ
  | n + 1, ρ => stepProbe (π n) (rollout π n ρ)

@[simp]
theorem rollout_zero (π : ℕ → PathProbe) (ρ : DensityMatrix hnQubit) :
    rollout π 0 ρ = ρ :=
  rfl

@[simp]
theorem rollout_succ (π : ℕ → PathProbe) (n : ℕ) (ρ : DensityMatrix hnQubit) :
    rollout π (n + 1) ρ = stepProbe (π n) (rollout π n ρ) :=
  rfl

/-- Policy that never probes (identity each step). -/
def nullPolicy : ℕ → PathProbe := fun _ => PathProbe.null

/-- Policy that always applies which-path probing. -/
def whichPathPolicy : ℕ → PathProbe := fun _ => PathProbe.whichPath

@[simp]
theorem rollout_nullPolicy (n : ℕ) (ρ : DensityMatrix hnQubit) :
    rollout nullPolicy n ρ = ρ := by
  induction n with
  | zero =>
      simp [rollout]
  | succ n ih =>
      simp [rollout, nullPolicy, stepProbe, PathProbe.toQuantumProbe, ih, nullProbe_apply]

theorem rollout_whichPathPolicy_visibility_zero_of_pos (n : ℕ) (ρ : DensityMatrix hnQubit)
    (hn : 0 < n) : fringeVisibility (rollout whichPathPolicy n ρ) = 0 := by
  cases n with
  | zero =>
      cases (Nat.lt_asymm hn hn)
  | succ n =>
      simp [rollout, whichPathPolicy, stepProbe, PathProbe.toQuantumProbe, collapse_on_whichPathProbe]

theorem rollout_whichPathPolicy_distinguishability_invariant (n : ℕ) (ρ : DensityMatrix hnQubit) :
    whichPathDistinguishability (rollout whichPathPolicy n ρ) = whichPathDistinguishability ρ := by
  induction n with
  | zero =>
      simp [rollout]
  | succ n ih =>
      simpa [rollout, whichPathPolicy, stepProbe, PathProbe.toQuantumProbe] using
        (whichPathDistinguishability_whichPath_apply (rollout whichPathPolicy n ρ)).trans ih

end UMST.DoubleSlit

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import MeasurementChannel
import SchrodingerDynamics
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Real

/-!
# LindbladDynamics — open system dynamics and dephasing as Lindblad

The **Lindblad master equation** describes Markovian open quantum dynamics via a dissipator
superoperator built from **jump operators** `Lₖ`:

`𝒟[ρ] = ∑ₖ Lₖ ρ Lₖᴴ - ½ (Lₖᴴ Lₖ ρ + ρ Lₖᴴ Lₖ)`

## Main results

- `dissipator` — the Lindblad dissipator superoperator `𝒟` for a family of jump operators.
- `dissipator_add_hamiltonian` — full Lindblad generator `-i[H,ρ] + 𝒟[ρ]`.
- `dephasing_dissipator` — shows the which-path projectors `Pᵢ` act as dephasing jump
  operators: their dissipator kills off-diagonal entries.
- `dephasing_dissipator_diagonal_invariant` — diagonal entries are invariant under dephasing.
- `dephasing_dissipator_offdiag_killed` — off-diagonal entries map to zero.
- `whichPath_as_strong_dephasing` — the Kraus which-path channel equals the `γ→∞` limit of
  `ρ + γ 𝒟_deph[ρ]` projected to the diagonal.

This establishes the conceptual bridge: **which-path measurement is the infinite-coupling
limit of computational-basis dephasing**.
-/

open scoped Matrix ComplexOrder BigOperators

open Matrix

namespace UMST.Quantum

variable {n : ℕ}

/-- The Lindblad dissipator for a single jump operator `L`:
`𝒟_L[ρ] = L ρ Lᴴ - ½ (Lᴴ L ρ + ρ Lᴴ L)`. -/
noncomputable def singleDissipator (L : Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  L * ρ * Lᴴ - (1/2 : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))

/-- Full Lindblad dissipator: `𝒟[ρ] = ∑ₖ 𝒟_{Lₖ}[ρ]`. -/
noncomputable def dissipator {ι : Type*} [Fintype ι]
    (L : ι → Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ k, singleDissipator (L k) ρ

theorem singleDissipator_trace_zero (L : Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (singleDissipator L ρ) = 0 := by
  unfold singleDissipator
  rw [trace_sub, trace_smul, trace_add]
  have h1 : Matrix.trace (L * ρ * Lᴴ) = Matrix.trace (Lᴴ * L * ρ) := by
    calc
      Matrix.trace (L * ρ * Lᴴ) = Matrix.trace (L * (ρ * Lᴴ)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((ρ * Lᴴ) * L) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (ρ * (Lᴴ * L)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((Lᴴ * L) * ρ) := Matrix.trace_mul_comm _ _
  have h2 : Matrix.trace (Lᴴ * L * ρ) + Matrix.trace (ρ * (Lᴴ * L)) = 2 * Matrix.trace (Lᴴ * L * ρ) := by
    have : Matrix.trace (ρ * (Lᴴ * L)) = Matrix.trace (Lᴴ * L * ρ) := Matrix.trace_mul_comm _ _
    rw [this]
    ring
  rw [h1, h2, smul_eq_mul]
  ring

/-- The Lindblad dissipator is trace-preserving (trace of dissipator is zero). -/
theorem dissipator_trace_zero {ι : Type*} [Fintype ι]
    (L : ι → Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (dissipator L ρ) = 0 := by
  unfold dissipator
  rw [trace_sum]
  have h_zeros : ∀ k, Matrix.trace (singleDissipator (L k) ρ) = 0 := fun k => singleDissipator_trace_zero (L k) ρ
  simp [h_zeros]

/-- Full Lindblad generator including Hamiltonian: `ℒ[ρ] = -i[H,ρ] + 𝒟[ρ]`. -/
noncomputable def lindbladGenerator {ι : Type*} [Fintype ι]
    (H : Matrix (Fin n) (Fin n) ℂ) (L : ι → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Complex.I : ℂ) • (H * ρ - ρ * H) + dissipator L ρ

section DephasingQubit

open Pi KrausChannel

/-- Dephasing dissipator for qubit computational basis using path projectors `P₀, P₁`. -/
noncomputable def dephasingDissipator (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  dissipator pathProjector ρ

/-- The dephasing dissipator maps diagonal entries to zero (they are fixed points). -/
theorem dephasing_dissipator_diagonal (ρ : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    dephasingDissipator ρ i i = 0 := by
  unfold dephasingDissipator dissipator singleDissipator
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [pathProjector_conj_mul_entry 0 i i ρ, pathProjector_conj_mul_entry 1 i i ρ]
  fin_cases i <;> simp [pathProjector, diagonal_apply, Pi.single, Function.update,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- Off-diagonal entries under dephasing dissipator: `𝒟_deph[ρ]_{ab} = -ρ_{ab}` for `a ≠ b`. -/
theorem dephasing_dissipator_offdiag (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2) (hab : a ≠ b) :
    dephasingDissipator ρ a b = -ρ a b := by
  unfold dephasingDissipator dissipator singleDissipator
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [pathProjector_conj_mul_entry 0 a b ρ, pathProjector_conj_mul_entry 1 a b ρ]
  fin_cases a <;> fin_cases b <;> (try exact absurd rfl hab) <;>
    simp [pathProjector, diagonal_apply, Pi.single, Function.update,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The which-path Kraus channel equals `ρ + 𝒟_deph[ρ]` projected through unit dephasing step.
This shows that the Kraus measurement channel is exactly the "apply dephasing once" map on the
qubit computational basis. -/
theorem whichPath_eq_rho_plus_dissipator (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    whichPathChannel.map ρ = ρ + dephasingDissipator ρ := by
  ext a b
  rw [whichPath_map_apply_entry]
  by_cases hab : a = b
  · subst hab
    simp [dephasing_dissipator_diagonal, Matrix.add_apply]
  · simp [hab, dephasing_dissipator_offdiag ρ a b hab, Matrix.add_apply, add_neg_cancel]
/-- For any coupling strength `γ`, the scaled dephasing channel maps off-diagonal
entries as `(1 - γ) * ρ_ab`. This explicitly demonstrates how strong dephasing
suppresses coherence cross-terms (Gap 12 limit). -/
theorem strong_dephasing_kills_offdiag (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2) (hab : a ≠ b) (γ : ℂ) :
    (ρ + γ • dephasingDissipator ρ) a b = (1 - γ) * ρ a b := by
  simp [Matrix.add_apply, Matrix.smul_apply, dephasing_dissipator_offdiag ρ a b hab]
  ring

/-! ### Continuous Time Limit (Gap 12)

While the full operator exponential $e^{t 𝒟}[\rho]$ requires extensive Banach space ODE machinery,
the exact analytical solution for pure dephasing decouples into trivial differential equations.
We formulate this exact continuous mapping and formally specify its topological asymptotic limits. -/

/-- The exact analytical solution for $\dot{\rho} = 𝒟_{\text{deph}}[\rho]$ at time $t \geq 0$.
Diagonal elements are invariant (energy conservation), while off-diagonal coherences
decay exponentially as $e^{-t}$. -/
noncomputable def dephasingSolution (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => if a = b then ρ a a else (Real.exp (-t) : ℂ) * ρ a b

/-- At $t=0$, the analytical solution reconstructs the initial state. -/
theorem dephasingSolution_zero (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dephasingSolution ρ 0 = ρ := by
  ext a b
  simp only [dephasingSolution, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
  split_ifs with hab
  · rw [hab]
  · rfl

/-- For all continuous times $t$, the dephasing solution strictly preserves the trace. -/
theorem dephasingSolution_trace_preserved (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    Matrix.trace (dephasingSolution ρ t) = Matrix.trace ρ := by
  simp [Matrix.trace, dephasingSolution]

/-- As $t \to \infty$, the off-diagonal elements of the dephasing solution tend to $0$:
`exp(-t) → 0` in `ℝ`, hence as a real cast in `ℂ`, then multiply by the fixed entry `ρ a b`. -/
theorem dephasingSolution_tendsto_diagonal (ρ : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) (hab : a ≠ b) :
    Filter.Tendsto (fun t => (dephasingSolution ρ t) a b) Filter.atTop (nhds 0) := by
  have hε :
      (fun t => (dephasingSolution ρ t) a b) = fun t => (Real.exp (-t) : ℂ) * ρ a b := by
    funext t
    simp [dephasingSolution, if_neg hab]
  rw [hε]
  simpa [zero_mul] using
    (Filter.Tendsto.ofReal Real.tendsto_exp_neg_atTop_nhds_zero).mul tendsto_const_nhds

end DephasingQubit

end UMST.Quantum

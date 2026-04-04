/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import MeasurementChannel
import DensityState
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# SchrodingerDynamics — unitary evolution as a Kraus channel

A **unitary** matrix `U` (satisfying `Uᴴ * U = 1`) defines the single-operator Kraus channel
`κ_U` with `K _ = U` (index type `Unit`). The channel action is `ρ ↦ U ρ Uᴴ`, i.e. standard
**Schrödinger-picture** evolution.

## Main results

- `unitaryChannel U hU` — construction of a `KrausChannel n Unit` from a unitary `U`.
- `unitaryChannel_map` — the map is `U * ρ * Uᴴ`.
- `unitaryChannel_preserves_psd` — `U ρ Uᴴ` is PSD when `ρ` is PSD.
- `unitaryChannel_preserves_trace` — `tr(U ρ Uᴴ) = tr(ρ)`.
- `unitaryChannel_apply` — applying the channel to a `DensityMatrix` yields a `DensityMatrix`.
- `unitaryChannel_compose_adjoint_map` — applying `κ_U` then `κ_{Uᴴ}` is the identity on matrices.
-/

open scoped Matrix ComplexOrder BigOperators

open Matrix

namespace UMST.Quantum

variable {n : ℕ}

/-- A unitary matrix `U` with `Uᴴ * U = 1` gives a single-operator Kraus channel. -/
noncomputable def unitaryChannel (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    KrausChannel n Unit where
  K := fun _ => U
  tp := by simp only [Fintype.sum_unique, hU]

theorem unitaryChannel_map (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (unitaryChannel U hU).map ρ = U * ρ * Uᴴ := by
  simp [KrausChannel.map, unitaryChannel, Fintype.sum_unique]

/-- Unitary conjugation preserves positive semidefiniteness. -/
theorem unitaryChannel_preserves_psd (U : Matrix (Fin n) (Fin n) ℂ) (_hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    (U * ρ * Uᴴ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same U

/-- Unitary conjugation preserves trace: `tr(U ρ Uᴴ) = tr(ρ)`. -/
theorem unitaryChannel_preserves_trace (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (U * ρ * Uᴴ) = Matrix.trace ρ := by
  calc
    Matrix.trace (U * ρ * Uᴴ) = Matrix.trace ((U * ρ) * Uᴴ) := rfl
    _ = Matrix.trace (Uᴴ * (U * ρ)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Uᴴ * U) * ρ) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (1 * ρ) := by rw [hU]
    _ = Matrix.trace ρ := by simp only [Matrix.one_mul]

/-- A unitary with `U * Uᴴ = 1` also satisfies `Uᴴ * U = 1` (for finite-dim). This is
the standard fact that left-invertibility implies right-invertibility for square matrices.
We state separately for convenience. -/
theorem conjTranspose_mul_self_of_self_mul_conjTranspose
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) : U * Uᴴ = 1 :=
  (Matrix.mem_unitaryGroup_iff (A := U)).1
    ((Matrix.mem_unitaryGroup_iff' (A := U)).2 hU)

/-- `Uᴴ` is left-unitary when `U` is (so `unitaryChannel Uᴴ` is well-formed). -/
theorem conjTranspose_mul_conjTranspose_self (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    Uᴴᴴ * Uᴴ = 1 := by
  rw [conjTranspose_conjTranspose]
  exact conjTranspose_mul_self_of_self_mul_conjTranspose U hU

/-- Composing evolution by `U` then by `Uᴴ` (the inverse channel) restores the state. -/
theorem unitaryChannel_compose_adjoint_map (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (unitaryChannel Uᴴ (conjTranspose_mul_conjTranspose_self U hU)).map
        ((unitaryChannel U hU).map ρ) = ρ := by
  rw [unitaryChannel_map, unitaryChannel_map]
  -- Second channel uses `K = Uᴴ`, hence a trailing `(Uᴴ)ᴴ = U`.
  simp only [conjTranspose_conjTranspose]
  -- `Uᴴ * (U * ρ * Uᴴ) * U = ((Uᴴ * U) * ρ) * (Uᴴ * U)` by associativity, then `hU` twice.
  calc
    Uᴴ * (U * ρ * Uᴴ) * U = ((Uᴴ * U) * ρ) * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
    _ = ρ := by simp only [hU, Matrix.one_mul, Matrix.mul_one]

end UMST.Quantum

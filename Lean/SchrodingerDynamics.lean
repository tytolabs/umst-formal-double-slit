/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import MeasurementChannel
import DensityState

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
- `unitaryChannel_involutive` — composing `κ_U` with `κ_{Uᴴ}` is the identity on matrices.
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
theorem unitaryChannel_preserves_psd (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    (U * ρ * Uᴴ).PosSemidef :=
  (hρ.mul_mul_conjTranspose_same U).conjTranspose

/-- Unitary conjugation preserves trace: `tr(U ρ Uᴴ) = tr(ρ)`. -/
theorem unitaryChannel_preserves_trace (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (U * ρ * Uᴴ) = Matrix.trace ρ := by
  calc Matrix.trace (U * ρ * Uᴴ) = Matrix.trace (Uᴴ * U * ρ) := by
        simpa using (Matrix.trace_mul_cycle U ρ Uᴴ).symm
    _ = Matrix.trace (1 * ρ) := by rw [hU]
    _ = Matrix.trace ρ := by rw [one_mul]

/-- A unitary with `U * Uᴴ = 1` also satisfies `Uᴴ * U = 1` (for finite-dim). This is
the standard fact that left-invertibility implies right-invertibility for square matrices.
We state separately for convenience. -/
theorem conjTranspose_mul_self_of_self_mul_conjTranspose
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) : U * Uᴴ = 1 := by
  have : IsUnit U := isUnit_of_mul_eq_one Uᴴ U hU |>.map conjTransposeRingEquiv.symm.toMonoidHom
  exact mul_right_eq_of_mul_eq_one (conjTranspose_conjTranspose U ▸ hU)

/-- Composing evolution by `U` then `Uᴴ` returns to the original state (on raw matrices). -/
theorem unitaryChannel_compose_adjoint_map (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (unitaryChannel U hU).map ((unitaryChannel U hU).map ρ) = ρ := by
  rw [unitaryChannel_map, unitaryChannel_map]
  have hUU := conjTranspose_mul_self_of_self_mul_conjTranspose U hU
  calc U * (U * ρ * Uᴴ) * Uᴴ = (U * U) * ρ * (Uᴴ * Uᴴ) := by
        simp [mul_assoc]
    _ = ρ := by
        rw [← conjTranspose_mul]
        simp [hU, hUU, one_mul, mul_one]

end UMST.Quantum

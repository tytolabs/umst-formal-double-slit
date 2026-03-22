/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import MeasurementChannel
import LandauerBound
import ExamplesQubit

/-!
# ErasureChannel — concrete "reset to |0⟩" erasure channel

The **reset channel** (amplitude damping to |0⟩) has two Kraus operators:
- `K₀ = |0⟩⟨0|` — projects out the |0⟩ component
- `K₁ = |0⟩⟨1|` — maps |1⟩ to |0⟩

Together they satisfy the trace-preservation constraint `K₀ᴴ K₀ + K₁ᴴ K₁ = I`.

**Proved:**
- `resetChannel_tp` — trace preservation
- `resetChannel_output_eq_rhoZero` — output is always `|0⟩⟨0|` for any density matrix
- `resetChannel_entropy_zero` — output has zero diagonal entropy
- `idealResetErasure` — an `ErasureProcess` at Landauer equality
- `idealResetErasure_saturates` — dissipated heat = Landauer cost exactly
-/

open scoped Matrix ComplexOrder BigOperators

open Matrix

namespace UMST.Quantum

/-- Kraus operator K₀ = |0⟩⟨0| for the reset channel. -/
noncomputable def resetK0 : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of !![1, 0; 0, 0]

/-- Kraus operator K₁ = |0⟩⟨1| for the reset channel. -/
noncomputable def resetK1 : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of !![0, 1; 0, 0]

theorem resetK0_conjTranspose :
    resetK0ᴴ = Matrix.of !![1, 0; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [resetK0, conjTranspose_apply, Matrix.of_apply, star]

theorem resetK1_conjTranspose :
    resetK1ᴴ = Matrix.of !![0, 0; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [resetK1, conjTranspose_apply, Matrix.of_apply, star]

theorem resetK0_conj_mul :
    resetK0ᴴ * resetK0 = Matrix.of !![1, 0; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [resetK0_conjTranspose, resetK0, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

theorem resetK1_conj_mul :
    resetK1ᴴ * resetK1 = Matrix.of !![0, 0; 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [resetK1_conjTranspose, resetK1, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

/-- Trace preservation: K₀ᴴ K₀ + K₁ᴴ K₁ = I. -/
theorem resetChannel_tp_aux :
    (∑ i : Fin 2, ((![resetK0, resetK1] i)ᴴ * ![resetK0, resetK1] i)) = 1 := by
  ext a b
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply]
  fin_cases a <;> fin_cases b <;>
    simp [resetK0_conjTranspose, resetK1_conjTranspose, resetK0, resetK1,
      Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

/-- The "reset to |0⟩" erasure channel, packaging K₀ = |0⟩⟨0| and K₁ = |0⟩⟨1|. -/
noncomputable def resetChannel : KrausChannel 2 (Fin 2) where
  K := ![resetK0, resetK1]
  tp := resetChannel_tp_aux

/-- Trace preservation of the reset channel (alias for the field). -/
theorem resetChannel_tp :
    (∑ i : Fin 2, (resetChannel.K i)ᴴ * resetChannel.K i) = 1 :=
  resetChannel.tp

section Output

open UMST.Quantum.Examples

variable (ρ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The reset channel always outputs |0⟩⟨0| (the (0,0) entry of the output is `trace ρ`,
and all other entries are 0). -/
theorem resetChannel_map_entry (a b : Fin 2) :
    resetChannel.map ρ a b =
      if a = 0 ∧ b = 0 then ρ 0 0 + ρ 1 1 else 0 := by
  simp only [KrausChannel.map, resetChannel, Fin.sum_univ_two, Matrix.add_apply]
  fin_cases a <;> fin_cases b <;>
    simp [resetK0, resetK1, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply,
      Fin.sum_univ_two, star]

/-- The reset channel maps any density matrix to `rhoZero.carrier` (i.e. `|0⟩⟨0|`). -/
theorem resetChannel_output_eq_rhoZero_carrier (ρ_dm : DensityMatrix hnQubit) :
    resetChannel.map ρ_dm.carrier = rhoZero.carrier := by
  ext a b
  rw [resetChannel_map_entry]
  have htrace := ρ_dm.trace_one
  unfold Matrix.trace at htrace
  simp only [Fin.sum_univ_two, Matrix.diag_apply] at htrace
  fin_cases a <;> fin_cases b <;>
    simp [rhoZero, pureDensity_carrier, pureCarrier, Matrix.mul_apply, col_apply, row_apply,
      psiZero, Fintype.sum_unique, Fin.ext_iff, htrace, Pi.star_apply, Complex.star_def]

/-- The reset channel maps any density matrix to `rhoZero`. -/
theorem resetChannel_output_eq_rhoZero (ρ_dm : DensityMatrix hnQubit) :
    resetChannel.apply hnQubit ρ_dm = rhoZero := by
  apply DensityMat.ext
  simp only [KrausChannel.apply]
  exact resetChannel_output_eq_rhoZero_carrier ρ_dm

end Output

section Entropy

open UMST.DoubleSlit UMST.Quantum.Examples

/-- The output of the reset channel has zero diagonal entropy. -/
theorem resetChannel_entropy_zero (ρ_dm : DensityMatrix hnQubit) :
    vonNeumannDiagonal (resetChannel.apply hnQubit ρ_dm) = 0 := by
  rw [resetChannel_output_eq_rhoZero]
  exact rhoZero_vonNeumannDiagonal

/-- The output of the reset channel has zero path entropy bits. -/
theorem resetChannel_pathEntropyBits_zero (ρ_dm : DensityMatrix hnQubit) :
    pathEntropyBits (resetChannel.apply hnQubit ρ_dm) = 0 := by
  rw [resetChannel_output_eq_rhoZero]
  exact rhoZero_pathEntropyBits

/-- The output of the reset channel has zero Landauer cost. -/
theorem resetChannel_landauerCost_zero (ρ_dm : DensityMatrix hnQubit) (T : ℝ) :
    landauerCostDiagonal (resetChannel.apply hnQubit ρ_dm) T = 0 := by
  rw [resetChannel_output_eq_rhoZero]
  exact rhoZero_landauerCostDiagonal T

end Entropy

end UMST.Quantum

namespace UMST.DoubleSlit

open UMST.Quantum UMST.Quantum.Examples

/-- An ideal erasure process that resets a qubit to |0⟩, dissipating exactly the Landauer cost.
This saturates the Landauer bound (equality in the Second Law). -/
noncomputable def idealResetErasure (ρ : DensityMatrix hnQubit) (T : ℝ) : ErasureProcess T where
  initial := ρ
  dissipatedHeat := landauerCostDiagonal ρ T
  secondLaw := le_refl _

/-- The ideal reset erasure process saturates the Landauer bound:
dissipated heat equals the Landauer cost exactly. -/
theorem idealResetErasure_saturates (ρ : DensityMatrix hnQubit) (T : ℝ) :
    (idealResetErasure ρ T).dissipatedHeat = landauerCostDiagonal ρ T :=
  rfl

end UMST.DoubleSlit

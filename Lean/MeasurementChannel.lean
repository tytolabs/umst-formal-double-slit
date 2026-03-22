/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Tactic.FinCases
import DensityState

/-!
# MeasurementChannel — finite Kraus maps (minimal CPTP layer)

For a finite family `K : ι → Matrix (Fin n) (Fin n) ℂ`, the **Kraus** (Heisenberg dual)
action on density matrices is

`Φ(ρ) = ∑ i, K i * ρ * (K i)ᴴ`.

**Trace preservation** holds for all `ρ` iff **`∑ i, (K i)ᴴ * K i = 1`** (standard TP / Stinespring
constraint). **Complete positivity** on the full matrix algebra follows from this Kraus form;
here we only prove **preservation of `PosSemidef`** termwise and under finite sums.

**Which-path (qubit computational basis):** `whichPathChannel : KrausChannel 2 (Fin 2)` uses orthogonal
projectors `Pᵢ = diagonal (Pi.single i 1)` with `∑ Pᵢ = 1`. This is the standard Lüders / projective
measurement channel on the path degree of freedom. **`whichPath_map_eq_diagonal`**: the channel maps
`ρ` to `diagonal (fun i => ρ i i)` (dephasing; diagonal entries fixed, off-diagonal zeroed).

**Composition:** `κ₂.compose κ₁` (indices `(i,j)`, operators `K₂ⱼ K₁ᵢ`) satisfies **`compose_map`**:
`map` agrees with applying `κ₁` then `κ₂`. Corollary **`apply_compose`** for `DensityMatrix.apply`.

**Unital / entropy (Tier 2 base case):** `KrausChannel.IsUnital` and von Neumann entropy under the identity
channel are in **`DataProcessingInequality.lean`** (`identity_isUnital`, `vonNeumannEntropy_identity_apply`).

This module does **not** yet import `DoubleSlitCore` (classical `I`/`V` interface stays separate).
-/

open scoped Matrix ComplexOrder BigOperators

open Matrix

namespace UMST.Quantum

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Kraus operators on `Fin n` with the trace-preserving identity `∑ Kᵢᴴ Kᵢ = 1`. -/
structure KrausChannel (n : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- Kraus operators `Kᵢ : ℂⁿ×ⁿ`. -/
  K : ι → Matrix (Fin n) (Fin n) ℂ
  /-- Trace-preserving (TP) constraint. -/
  tp : (∑ i, (K i)ᴴ * K i) = 1

noncomputable def KrausChannel.map (κ : KrausChannel n ι) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, κ.K i * ρ * (κ.K i)ᴴ

namespace KrausChannel

variable (κ : KrausChannel n ι)

@[simp]
theorem map_expand (ρ : Matrix (Fin n) (Fin n) ℂ) :
    κ.map ρ = ∑ i, κ.K i * ρ * (κ.K i)ᴴ :=
  rfl

/-- Each Kraus conjugation `ρ ↦ K ρ Kᴴ` preserves positive semidefiniteness. -/
theorem posSemidef_map_term (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) (i : ι) :
    (κ.K i * ρ * (κ.K i)ᴴ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same (κ.K i)

theorem posSemidef_finset_sum (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i ∈ s, (f i).PosSemidef) : (∑ i ∈ s, f i).PosSemidef := by
  classical
  refine Finset.induction_on s (p := fun s' => (∀ i ∈ s', (f i).PosSemidef) → (∑ i ∈ s', f i).PosSemidef)
    ?_ ?_ hf
  · intro; simp [Finset.sum_empty, PosSemidef.zero]
  · intro a t hat ih hins
    rw [Finset.sum_insert hat]
    exact Matrix.PosSemidef.add (hins a (Finset.mem_insert_self _ _))
      (ih fun i hi => hins i (Finset.mem_insert_of_mem hi))

theorem posSemidef_sum (f : ι → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ i, (f i).PosSemidef) :
    (∑ i, f i).PosSemidef := by
  classical
  exact posSemidef_finset_sum Finset.univ f (fun i _ => hf i)

theorem map_posSemidef (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    (κ.map ρ).PosSemidef := by
  dsimp [KrausChannel.map]
  refine posSemidef_sum _ fun i => posSemidef_map_term κ ρ hρ i

theorem trace_mul_sum (ρ : Matrix (Fin n) (Fin n) ℂ) (f : ι → Matrix (Fin n) (Fin n) ℂ)
    (s : Finset ι) :
    (∑ i ∈ s, Matrix.trace (ρ * f i)) = Matrix.trace (ρ * ∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Finset.sum_empty]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mul_add, Matrix.trace_add, ih]

set_option maxHeartbeats 0 in
theorem trace_map_eq (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (κ.map ρ) = Matrix.trace (ρ * ∑ i, (κ.K i)ᴴ * κ.K i) := by
  classical
  dsimp [KrausChannel.map]
  have step (i : ι) :
      Matrix.trace (κ.K i * ρ * (κ.K i)ᴴ) = Matrix.trace (ρ * ((κ.K i)ᴴ * κ.K i)) := by
    rw [Matrix.trace_mul_cycle (κ.K i) ρ (κ.K i)ᴴ, Matrix.trace_mul_comm]
  calc
    Matrix.trace (∑ i, κ.K i * ρ * (κ.K i)ᴴ) = ∑ i, Matrix.trace (κ.K i * ρ * (κ.K i)ᴴ) := by
      simpa using (Matrix.trace_sum Finset.univ fun i => κ.K i * ρ * (κ.K i)ᴴ).symm
    _ = ∑ i, Matrix.trace (ρ * ((κ.K i)ᴴ * κ.K i)) := by
      refine Finset.sum_congr rfl fun i _ => step i
    _ = Matrix.trace (ρ * ∑ i, (κ.K i)ᴴ * κ.K i) :=
      trace_mul_sum ρ (fun i => (κ.K i)ᴴ * κ.K i) Finset.univ

theorem trace_map_one (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : Matrix.trace ρ = 1) :
    Matrix.trace (κ.map ρ) = 1 := by
  rw [trace_map_eq, κ.tp, mul_one, hρ]

/-- Apply a trace-preserving Kraus channel to a density matrix. -/
noncomputable def apply (hn : 0 < n) (ρ : DensityMatrix hn) : DensityMatrix hn where
  carrier := κ.map ρ.carrier
  psd := map_posSemidef κ ρ.carrier ρ.psd
  trace_one := trace_map_one κ ρ.carrier ρ.trace_one

/-- **Identity channel:** single Kraus operator `I` (index type `Unit`). -/
noncomputable def identity (n : ℕ) : KrausChannel n Unit where
  K := fun _ => 1
  tp := by
    simp only [conjTranspose_one, one_mul, Fintype.sum_unique]

theorem identity_map (n : ℕ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (identity n).map ρ = ρ := by
  unfold KrausChannel.map identity
  simp [Fintype.sum_unique, one_mul, mul_one]

section Composition

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]

set_option maxHeartbeats 0 in
/-- Sequential composition: first `κ₁`, then `κ₂`.

**Parameter order:** arguments are `(κ₂, κ₁)` so that dot notation `κ₂.compose κ₁` reads naturally
and Kraus operators are `K₂ⱼ K₁ᵢ` on index `(i, j) ∈ ι₁ × ι₂`. -/
noncomputable def compose (κ₂ : KrausChannel n ι₂) (κ₁ : KrausChannel n ι₁) :
    KrausChannel n (ι₁ × ι₂) where
  K := fun p => κ₂.K p.2 * κ₁.K p.1
  tp := by
    classical
    rw [show (Finset.univ : Finset (ι₁ × ι₂)) = Finset.univ ×ˢ Finset.univ from
      Finset.univ_product_univ.symm]
    rw [Finset.sum_product]
    simp_rw [Matrix.conjTranspose_mul]
    have inner (i : ι₁) :
        (∑ j : ι₂, (κ₁.K i)ᴴ * (κ₂.K j)ᴴ * κ₂.K j * κ₁.K i) = (κ₁.K i)ᴴ * κ₁.K i := by
      calc
        ∑ j : ι₂, (κ₁.K i)ᴴ * (κ₂.K j)ᴴ * κ₂.K j * κ₁.K i
            = ∑ j : ι₂, ((κ₁.K i)ᴴ * ((κ₂.K j)ᴴ * κ₂.K j)) * κ₁.K i := by
                  simp_rw [← mul_assoc]
        _ = (∑ j : ι₂, (κ₁.K i)ᴴ * ((κ₂.K j)ᴴ * κ₂.K j)) * κ₁.K i := by
              rw [Matrix.sum_mul]
        _ = ((κ₁.K i)ᴴ * ∑ j : ι₂, (κ₂.K j)ᴴ * κ₂.K j) * κ₁.K i := by
              rw [← Matrix.mul_sum]
        _ = ((κ₁.K i)ᴴ * (1 : Matrix (Fin n) (Fin n) ℂ)) * κ₁.K i := by rw [κ₂.tp]
        _ = (κ₁.K i)ᴴ * κ₁.K i := by rw [Matrix.mul_one]
    have bridge (i : ι₁) :
        (∑ y : ι₂, (κ₁.K (i, y).1)ᴴ * (κ₂.K (i, y).2)ᴴ * (κ₂.K (i, y).2 * κ₁.K (i, y).1)) =
          ∑ j : ι₂, (κ₁.K i)ᴴ * (κ₂.K j)ᴴ * κ₂.K j * κ₁.K i := by
      simp_rw [← mul_assoc]
    rw [← κ₁.tp]
    refine Finset.sum_congr rfl fun i _ => (bridge i).trans (inner i)

theorem compose_map (κ₁ : KrausChannel n ι₁) (κ₂ : KrausChannel n ι₂)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (κ₂.compose κ₁).map ρ = κ₂.map (κ₁.map ρ) := by
  classical
  dsimp [KrausChannel.map, compose]
  rw [show (Finset.univ : Finset (ι₁ × ι₂)) = Finset.univ ×ˢ Finset.univ from
    Finset.univ_product_univ.symm]
  rw [Finset.sum_product]
  simp_rw [Matrix.conjTranspose_mul, ← mul_assoc]
  rw [← Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  calc
    ∑ i : ι₁, κ₂.K j * κ₁.K i * ρ * (κ₁.K i)ᴴ * (κ₂.K j)ᴴ
        = ∑ i : ι₁, κ₂.K j * (κ₁.K i * ρ * (κ₁.K i)ᴴ) * (κ₂.K j)ᴴ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp_rw [← mul_assoc]
    _ = (∑ i : ι₁, κ₂.K j * (κ₁.K i * ρ * (κ₁.K i)ᴴ)) * (κ₂.K j)ᴴ := by
          rw [← Matrix.sum_mul]
    _ = (κ₂.K j * ∑ i : ι₁, κ₁.K i * ρ * (κ₁.K i)ᴴ) * (κ₂.K j)ᴴ := by
          rw [Matrix.mul_sum]

/-- Applying a composed Kraus channel equals applying the factors in order. -/
theorem apply_compose (hn : 0 < n) (κ₁ : KrausChannel n ι₁) (κ₂ : KrausChannel n ι₂)
    (ρ : DensityMatrix hn) :
    (κ₂.compose κ₁).apply hn ρ = κ₂.apply hn (κ₁.apply hn ρ) := by
  refine DensityMat.ext ?_
  simp only [apply, compose_map]

end Composition

section WhichPathQubit

open Pi

/-- Orthogonal projector onto the `i`-th path (`|i⟩⟨i|`) in the computational basis of `Fin 2`. -/
noncomputable def pathProjector (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (single i (1 : ℂ))

theorem pathProjector_conjTranspose (i : Fin 2) :
    (pathProjector i)ᴴ = pathProjector i := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [pathProjector, diagonal, conjTranspose_apply, Pi.single, Function.update, star, Complex.ext_iff]

theorem pathProjector_mul_self (i : Fin 2) : pathProjector i * pathProjector i = pathProjector i := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [pathProjector, Matrix.mul_apply, diagonal_apply, Pi.single, Function.update, Fin.sum_univ_two]

theorem pathProjector_mul_orthogonal {i j : Fin 2} (hij : i ≠ j) :
    pathProjector i * pathProjector j = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl hij
          | simp [pathProjector, Matrix.mul_apply, diagonal_apply, Matrix.zero_apply,
                  Pi.single, Function.update, Fin.sum_univ_two]

theorem pathProjector_tp_aux :
    (∑ i : Fin 2, (pathProjector i)ᴴ * pathProjector i) = 1 := by
  simp only [pathProjector_conjTranspose]
  ext a b
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply]
  fin_cases a <;> fin_cases b <;>
    simp [pathProjector, diagonal, Pi.single, Function.update, Matrix.mul_apply, Fin.sum_univ_two]

/-- Lüders measurement in the computational basis of a 2-level path system. -/
noncomputable def whichPathChannel : KrausChannel 2 (Fin 2) where
  K := pathProjector
  tp := pathProjector_tp_aux

/-- One Kraus term `Pᵢ ρ Pᵢ` picks out the `(i,i)` diagonal entry and zeros all other matrix
elements. -/
theorem pathProjector_conj_mul_entry (i a b : Fin 2) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (pathProjector i * ρ * pathProjector i) a b = if a = i ∧ b = i then ρ i i else 0 := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [pathProjector, Matrix.mul_apply, diagonal_apply, Pi.single, Function.update, Fin.sum_univ_two]

/-- Path measurement **dephases** to the diagonal: off-diagonal entries vanish, diagonal is unchanged. -/
theorem whichPath_map_eq_diagonal (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    whichPathChannel.map ρ = diagonal (fun i : Fin 2 => ρ i i) := by
  ext a b
  simp only [KrausChannel.map, whichPathChannel, Fin.sum_univ_two, Matrix.add_apply,
    diagonal_apply, pathProjector_conjTranspose]
  rw [pathProjector_conj_mul_entry 0, pathProjector_conj_mul_entry 1]
  fin_cases a <;> fin_cases b <;> simp

theorem whichPath_map_apply_entry (ρ : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    whichPathChannel.map ρ a b = if a = b then ρ a a else 0 := by
  rw [whichPath_map_eq_diagonal, diagonal_apply]

end WhichPathQubit

end KrausChannel

end UMST.Quantum

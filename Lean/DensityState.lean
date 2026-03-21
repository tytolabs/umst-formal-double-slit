import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# DensityState — finite-dimensional density matrices (minimal layer)

`n × n` complex matrices that are **positive semidefinite** and have **trace 1**, matching the
standard quantum density-operator interface.

**In this file:**
- `DensityMatrix n` — bundled PSD + `trace = 1` (requires `0 < n`).
- `pureDensity ψ h` — rank-one projector `|ψ⟩⟨ψ|` from a normalized vector (`dotProduct ψ (star ψ) = 1`).

**Not yet:** general mixed states `∑ tᵢ ρᵢ`, partial trace, or connection to `DoubleSlitCore`.
-/

open scoped Matrix ComplexOrder BigOperators

namespace UMST.Quantum

variable {n : ℕ} (hn : 0 < n)

local notation "ℂⁿ" => Fin n → ℂ

/-- Density matrix on `Fin n` (complex, PSD, trace 1). -/
structure DensityMatrix : Type where
  carrier : Matrix (Fin n) (Fin n) ℂ
  psd : carrier.PosSemidef
  trace_one : Matrix.trace carrier = 1

namespace DensityMatrix

/-- Two density matrices are equal if their underlying matrices agree (PSD / trace proofs are
propositions, hence unique). -/
@[ext]
theorem ext {ρ σ : @DensityMatrix n} (h : ρ.carrier = σ.carrier) : ρ = σ := by
  rcases ρ with ⟨c, hp, ht⟩
  rcases σ with ⟨c', hp', ht'⟩
  subst h
  rfl

@[simp]
theorem trace_eq_one (ρ : @DensityMatrix n) : Matrix.trace ρ.carrier = 1 :=
  ρ.trace_one

theorem isHermitian (ρ : @DensityMatrix n) : ρ.carrier.IsHermitian :=
  ρ.psd.isHermitian

theorem diag_nonneg_complex_n (ρ : @DensityMatrix n) (i : Fin n) : (0 : ℂ) ≤ ρ.carrier i i := by
  have h := ρ.psd.2 (Pi.single i (1 : ℂ))
  have key : dotProduct (star (Pi.single i (1 : ℂ))) (ρ.carrier *ᵥ Pi.single i (1 : ℂ)) = ρ.carrier i i := by
    simp only [Pi.star_single, star_one, mulVec_single, dotProduct_single_one, mul_one]
  rwa [key] at h

theorem diag_re_nonneg_n (ρ : @DensityMatrix n) (i : Fin n) : 0 ≤ (ρ.carrier i i).re :=
  (Complex.nonneg_iff.mp (diag_nonneg_complex_n ρ i)).1

theorem trace_re_eq_one_n (ρ : @DensityMatrix n) : ∑ i : Fin n, (ρ.carrier i i).re = 1 := by
  have h := ρ.trace_one
  unfold Matrix.trace at h
  apply_fun Complex.re at h
  simp only [map_sum, Complex.one_re] at h
  exact h

theorem diag_re_le_one_n (ρ : @DensityMatrix n) (i : Fin n) : (ρ.carrier i i).re ≤ 1 := by
  have hsum := trace_re_eq_one_n ρ
  have hrest : ∑ j in Finset.univ.erase i, (ρ.carrier j j).re ≥ 0 :=
    Finset.sum_nonneg (fun j _ => diag_re_nonneg_n ρ j)
  have heq : (ρ.carrier i i).re + ∑ j in Finset.univ.erase i, (ρ.carrier j j).re = 1 := by
    rw [← Finset.add_sum_erase Fintype.univ i (Finset.mem_univ i)]
    exact hsum
  linarith

end DensityMatrix

open Matrix

/-- Rank-one projector `col ψ * row (star ψ)` (i.e. `|ψ⟩⟨ψ|` in bra-ket notation). -/
noncomputable def pureCarrier (ψ : ℂⁿ) : Matrix (Fin n) (Fin n) ℂ :=
  col Unit ψ * row Unit (star ψ)

theorem pureCarrier_posSemidef (ψ : ℂⁿ) : (pureCarrier ψ).PosSemidef := by
  simpa [pureCarrier] using posSemidef_self_mul_conjTranspose (col Unit ψ)

theorem pureCarrier_trace (ψ : ℂⁿ) :
    Matrix.trace (pureCarrier ψ) = dotProduct ψ (star ψ) := by
  simpa [pureCarrier] using trace_col_mul_row (ι := Unit) ψ (star ψ)

/-- Pure state from a vector normalized in the `dotProduct ψ (star ψ) = 1` convention. -/
noncomputable def pureDensity (ψ : ℂⁿ) (hψ : dotProduct ψ (star ψ) = 1) : @DensityMatrix n where
  carrier := pureCarrier ψ
  psd := pureCarrier_posSemidef ψ
  trace_one := by rw [pureCarrier_trace, hψ]

@[simp]
theorem pureDensity_carrier (ψ : ℂⁿ) (hψ : dotProduct ψ (star ψ) = 1) :
    (pureDensity ψ hψ).carrier = pureCarrier ψ :=
  rfl

end UMST.Quantum

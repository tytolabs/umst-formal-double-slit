import DensityState
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Matrix ComplexOrder BigOperators Complex

namespace UMST.Quantum

variable {n : ℕ} {hn : 0 < n} (ρ : DensityMatrix hn)

theorem diag_nonneg_complex (i : Fin n) : (0 : ℂ) ≤ ρ.carrier i i := by
  have h := ρ.psd.2 (Pi.single i (1 : ℂ))
  have key : dotProduct (star (Pi.single i (1 : ℂ))) (ρ.carrier *ᵥ Pi.single i (1 : ℂ)) = ρ.carrier i i := by
    simp only [Pi.star_single, star_one, mulVec_single, dotProduct_single_one, mul_one]
  rwa [key] at h

theorem diag_re_nonneg (i : Fin n) : 0 ≤ (ρ.carrier i i).re :=
  (Complex.nonneg_iff.mp (diag_nonneg_complex ρ i)).1

theorem trace_re_eq_one : ∑ i : Fin n, (ρ.carrier i i).re = 1 := by
  have h := ρ.trace_one
  unfold Matrix.trace at h
  apply_fun Complex.re at h
  simp only [map_sum, Complex.one_re] at h
  exact h

noncomputable def vonNeumannDiagonal_n : ℝ :=
  ∑ i : Fin n, Real.negMulLog (ρ.carrier i i).re

theorem vonNeumannDiagonal_n_nonneg : 0 ≤ vonNeumannDiagonal_n ρ := by
  apply Finset.sum_nonneg
  intro i _
  have h0 : 0 ≤ (ρ.carrier i i).re := diag_re_nonneg ρ i
  have h1 : (ρ.carrier i i).re ≤ 1 := by
    have hsum := trace_re_eq_one ρ
    have hrest : ∑ j in Finset.univ.erase i, (ρ.carrier j j).re ≥ 0 := by
      apply Finset.sum_nonneg
      intro j _
      exact diag_re_nonneg ρ j
    have heq : (ρ.carrier i i).re + ∑ j in Finset.univ.erase i, (ρ.carrier j j).re = 1 := by
      rw [← Finset.add_sum_erase Fintype.univ i (Finset.mem_univ i)]
      exact hsum
    linarith
  exact Real.negMulLog_nonneg h0 h1

end UMST.Quantum

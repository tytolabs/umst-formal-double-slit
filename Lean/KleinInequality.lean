-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import VonNeumannEntropy
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Complex.BigOperators

/-!
# Klein's Inequality — Non-negativity of Quantum Relative Entropy

This module formally establishes Klein's inequality for finite-dimensional density
matrices via the spectral decomposition route, avoiding the need for a matrix
logarithm as an operator-level construction.

## Strategy

We define quantum relative entropy spectrally, then reduce non-negativity to the
**classical Gibbs inequality** (KL divergence ≥ 0) via two Jensen applications.

## Key Results

- `gibbs_inequality` — classical KL divergence non-negativity for finite distributions
- `spectralRelativeEntropy` — quantum relative entropy via spectral overlap
- `spectralRelativeEntropy_nonneg` — S(ρ‖σ) ≥ 0 in the spectral-overlap form (proved)
- `vonNeumannEntropy_le_sum_negMulLog_diag_unitary_conj` — measuring in any orthonormal basis (columns of a
  unitary `W`) does not lower the entropy: `S(ρ) ≤ H(diag(Wᴴ ρ W))` (row-wise Jensen on concave `negMulLog`,
  column unitarity)

## References

- Nielsen & Chuang, Theorem 11.7 (Klein's inequality)
- Cover & Thomas, Theorem 2.6.3 (Gibbs' inequality / Information inequality)
-/

set_option maxHeartbeats 800000

namespace UMST.Quantum

open _root_.Real Finset Matrix Set
open scoped BigOperators

variable {n : ℕ} {hn : 0 < n}

/-! ### Classical Gibbs Inequality

For probability distributions `p, q` on `Fin n` with `∑ pᵢ = ∑ qᵢ = 1`,
the KL divergence `D(p‖q) = ∑ pᵢ log(pᵢ/qᵢ) ≥ 0`.

Proof via convexity of `x * log x` (Mathlib: `convexOn_mul_log`) and Jensen's
inequality (`ConvexOn.map_sum_le`). -/

/-- **Gibbs' inequality (classical):** For probability distributions `p, q` on `Fin n`
with strictly positive entries, `∑ pᵢ log(pᵢ/qᵢ) ≥ 0`.

This is D_KL(p‖q) ≥ 0, the information inequality. -/
theorem gibbs_inequality
    (p q : Fin n → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    ∑ i, p i * log (p i / q i) ≥ 0 := by
  -- Jensen for the convex f(x) = x log x on [0, ∞), weights qᵢ, points rᵢ = pᵢ / qᵢ:
  -- f(∑ qᵢ rᵢ) ≤ ∑ qᵢ f(rᵢ), with ∑ qᵢ rᵢ = ∑ pᵢ = 1 and qᵢ f(rᵢ) = pᵢ log(pᵢ / qᵢ).
  have hJ := (convexOn_mul_log).map_sum_le (t := Finset.univ) (w := q) (p := fun i => p i / q i)
    (fun i _ => (hq_pos i).le) (by simpa using hq_sum)
    (fun i _ => Set.mem_Ici.mpr (div_nonneg (hp_nn i) (hq_pos i).le))
  have hlhs : ∑ i, q i • (p i / q i) = 1 := by
    rw [← hp_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [smul_eq_mul, mul_div_cancel₀ _ (hq_pos i).ne']
  have hrhs : ∑ i, q i • ((p i / q i) * log (p i / q i)) = ∑ i, p i * log (p i / q i) :=
    Finset.sum_congr rfl fun i _ => by
      rw [smul_eq_mul, ← mul_assoc, mul_div_cancel₀ _ (hq_pos i).ne']
  simp only [hlhs, hrhs, one_mul, log_one] at hJ
  linarith

/-! ### Unitary row/column squared-modulus sums -/

private lemma unitary_row_diagonal_mul_star (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j : Fin n, T i j * star (T i j) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hT
  rw [Matrix.star_eq_conjTranspose] at h
  simpa [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.conjTranspose_apply] using congr_arg (fun M => M i i) h

theorem unitary_row_normSq_sum (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j : Fin n, (Complex.normSq (T i j) : ℝ) = 1 := by
  have hdiag := unitary_row_diagonal_mul_star T hT i
  simp_rw [Complex.star_def, Complex.mul_conj] at hdiag
  exact_mod_cast hdiag

private lemma unitary_col_diagonal_star_mul (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i : Fin n, star (T i j) * T i j = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hT
  rw [Matrix.star_eq_conjTranspose] at h
  simpa [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.conjTranspose_apply] using congr_arg (fun M => M j j) h

theorem unitary_col_normSq_sum (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i : Fin n, (Complex.normSq (T i j) : ℝ) = 1 := by
  have hdiag := unitary_col_diagonal_star_mul T hT j
  simp_rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at hdiag
  exact_mod_cast hdiag

/-- The spectral relative entropy: given eigenvalues `λ` of ρ and `μ` of σ,
and the unitary overlap matrix `T = U†V`, define:

  `S_spec(λ, μ, T) = ∑ᵢ λᵢ log λᵢ - ∑ᵢ λᵢ (∑ⱼ |Tᵢⱼ|² log μⱼ)`

This equals `Tr(ρ(log ρ - log σ))` when ρ = U diag(λ) U† and σ = V diag(μ) V†. -/
noncomputable def spectralRelativeEntropy
    (lam_eig μ_eig : Fin n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (∑ i, lam_eig i * log (lam_eig i)) -
  (∑ i, lam_eig i * (∑ j, (Complex.normSq (T i j) : ℝ) * log (μ_eig j)))

/-- **Klein's inequality (spectral form):** The spectral relative entropy is non-negative
when `λ` and `μ` are strictly positive probability vectors and `T` is unitary.

Proof: row-wise Jensen on concave `log` gives `∑ⱼ |Tᵢⱼ|² log μⱼ ≤ log cᵢ` with
`cᵢ = ∑ⱼ |Tᵢⱼ|² μⱼ`. Column unitarity yields `∑ᵢ cᵢ = ∑ⱼ μⱼ = 1`. Hence
`S_spec ≥ ∑ᵢ λᵢ log(λᵢ/cᵢ) ≥ 0` by `gibbs_inequality`. -/
theorem spectralRelativeEntropy_nonneg
    (lam_eig μ_eig : Fin n → ℝ)
    (hlam_pos : ∀ i, 0 < lam_eig i) (hμ_pos : ∀ i, 0 < μ_eig i)
    (hlam_sum : ∑ i, lam_eig i = 1) (hμ_sum : ∑ i, μ_eig i = 1)
    (T : Matrix (Fin n) (Fin n) ℂ)
    (hT_unitary : T ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    spectralRelativeEntropy lam_eig μ_eig T ≥ 0 := by
  classical
  let c : Fin n → ℝ := fun i => ∑ j, (Complex.normSq (T i j) : ℝ) * μ_eig j
  have hc_pos : ∀ i, 0 < c i := by
    intro i
    dsimp [c]
    obtain ⟨j, hj⟩ : ∃ j, 0 < (Complex.normSq (T i j) : ℝ) := by
      by_contra h'
      push_neg at h'
      have hz : ∀ j, (Complex.normSq (T i j) : ℝ) = 0 := fun j =>
        le_antisymm (h' j) (Complex.normSq_nonneg _)
      have hrow := unitary_row_normSq_sum T hT_unitary i
      simp [hz] at hrow
    exact Finset.sum_pos' (fun j _ => mul_nonneg (Complex.normSq_nonneg _) (hμ_pos j).le)
      ⟨j, Finset.mem_univ j, mul_pos hj (hμ_pos j)⟩
  have hcsum : ∑ i, c i = 1 := by
    dsimp [c]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, unitary_col_normSq_sum T hT_unitary, one_mul]
    exact hμ_sum
  have hJensen (i : Fin n) :
      (∑ j : Fin n, (Complex.normSq (T i j) : ℝ) * log (μ_eig j)) ≤ log (c i) := by
    let w : Fin n → ℝ := fun j => (Complex.normSq (T i j) : ℝ)
    have hw0 : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ w j := fun j _ => Complex.normSq_nonneg _
    have hw1 : ∑ j ∈ (univ : Finset (Fin n)), w j = 1 := by
      simpa [w] using unitary_row_normSq_sum T hT_unitary i
    have hmem : ∀ j ∈ (univ : Finset (Fin n)), μ_eig j ∈ Ioi (0 : ℝ) := fun j _ =>
      mem_Ioi.mpr (hμ_pos j)
    have hJ :=
      strictConcaveOn_log_Ioi.concaveOn.le_map_sum
        (𝕜 := ℝ) (E := ℝ) (β := ℝ) (s := Ioi (0 : ℝ)) (f := log) (ι := Fin n) (t := univ)
        (w := w) (p := μ_eig) hw0 hw1 hmem
    simpa [w, c, smul_eq_mul] using hJ
  set A : ℝ := ∑ i, lam_eig i * log (lam_eig i)
  set B : ℝ := ∑ i, lam_eig i * (∑ j, (Complex.normSq (T i j) : ℝ) * log (μ_eig j))
  set Csum : ℝ := ∑ i, lam_eig i * log (c i)
  have hubound : B ≤ Csum := by
    dsimp [B, Csum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left (hJensen i) (le_of_lt (hlam_pos i))
  have hAC : A - Csum = ∑ i, lam_eig i * log (lam_eig i / c i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [log_div (hlam_pos i).ne' (hc_pos i).ne', mul_sub]
  have hKl : 0 ≤ A - Csum := by
    rw [hAC]
    exact gibbs_inequality lam_eig c (fun i => le_of_lt (hlam_pos i))
      (fun i => hc_pos i) hlam_sum hcsum
  have hEnt : A - Csum ≤ A - B := sub_le_sub le_rfl hubound
  unfold spectralRelativeEntropy
  exact le_trans hKl hEnt

/-! ### Entropy does not decrease under a basis measurement

The diagonal of `Wᴴ ρ W` is `dₖ = ∑ᵢ |Tₖᵢ|² λᵢ` with `T = Wᴴ U` unitary (`U` the eigenvectors of `ρ`), a doubly
stochastic mixture of the spectrum. -/

/-- The `k`-th diagonal entry of `Wᴴ ρ W` is `∑ᵢ |(Wᴴ U)ₖᵢ|² λᵢ`, with `U` the eigenvectors and `λ` the eigenvalues
of `ρ`. -/
theorem diag_unitary_conj_re_eq (ρ : DensityMatrix hn) (W : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    ((Wᴴ * ρ.carrier * W) k k).re =
      ∑ i, Complex.normSq ((Wᴴ * (ρ.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) k i) *
        ρ.isHermitian.eigenvalues i := by
  set U := (ρ.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hspec : ρ.carrier = U * diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues) * star U :=
    ρ.isHermitian.spectral_theorem
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues) with hD
  have hconj : Wᴴ * ρ.carrier * W = (Wᴴ * U) * D * (Wᴴ * U)ᴴ := by
    calc Wᴴ * ρ.carrier * W = Wᴴ * (U * D * star U) * W := by rw [← hspec]
      _ = (Wᴴ * U) * D * (Wᴴ * U)ᴴ := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc, star_eq_conjTranspose]
  rw [hconj, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, conjTranspose_apply, Function.comp_apply]
  rw [mul_right_comm, Complex.star_def, Complex.mul_conj]
  simp [Complex.mul_re]

/-- **Entropy increase under a basis measurement**: for any unitary `W`, `S(ρ) ≤ ∑ₖ η((Wᴴ ρ W)ₖₖ)` with
`η = negMulLog`. -/
theorem vonNeumannEntropy_le_sum_negMulLog_diag_unitary_conj (ρ : DensityMatrix hn)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    vonNeumannEntropy ρ ≤ ∑ k, negMulLog ((Wᴴ * ρ.carrier * W) k k).re := by
  set U := (ρ.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set T := Wᴴ * U
  set lam := ρ.isHermitian.eigenvalues
  have hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    refine Submonoid.mul_mem _ ?_ ρ.isHermitian.eigenvectorUnitary.2
    rw [← star_eq_conjTranspose]
    exact unitary.star_mem hW
  have hjensen (k : Fin n) :
      ∑ i, Complex.normSq (T k i) * negMulLog (lam i) ≤ negMulLog ((Wᴴ * ρ.carrier * W) k k).re := by
    rw [diag_unitary_conj_re_eq ρ W k]
    have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := fun i => Complex.normSq (T k i))
      (p := lam) (fun i _ => Complex.normSq_nonneg _) (by simpa using unitary_row_normSq_sum T hT k)
      (fun i _ => Set.mem_Ici.mpr (density_eigenvalues_nonneg ρ i))
    simpa [smul_eq_mul] using h
  calc vonNeumannEntropy ρ
      = ∑ i, (∑ k, Complex.normSq (T k i)) * negMulLog (lam i) := by
        unfold vonNeumannEntropy
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [unitary_col_normSq_sum T hT i, one_mul]
    _ = ∑ k, ∑ i, Complex.normSq (T k i) * negMulLog (lam i) := by
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
    _ ≤ ∑ k, negMulLog ((Wᴴ * ρ.carrier * W) k k).re := Finset.sum_le_sum fun k _ => hjensen k

end UMST.Quantum

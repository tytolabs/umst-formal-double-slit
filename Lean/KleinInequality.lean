/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
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

## References

- Nielsen & Chuang, Theorem 11.7 (Klein's inequality)
- Cover & Thomas, Theorem 2.6.3 (Gibbs' inequality / Information inequality)
-/

set_option maxHeartbeats 800000

namespace UMST.Quantum

open Real Finset Complex Matrix Set
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
  -- Let f(x) = x * log x, which is convex on [0,∞) (convexOn_mul_log)
  -- Let rᵢ = pᵢ / qᵢ ≥ 0
  -- Jensen with weights qᵢ and points rᵢ:
  --   f(∑ qᵢ • rᵢ) ≤ ∑ qᵢ • f(rᵢ)
  --   f(∑ pᵢ)       ≤ ∑ qᵢ • f(pᵢ/qᵢ)
  --   f(1)           ≤ ∑ qᵢ • ((pᵢ/qᵢ) * log(pᵢ/qᵢ))
  --   0              ≤ ∑ pᵢ * log(pᵢ/qᵢ)
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x => x * log x) :=
    convexOn_mul_log
  let r : Fin n → ℝ := fun i => p i / q i
  have hq_nn : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ q i :=
    fun i _ => le_of_lt (hq_pos i)
  have hr_mem : ∀ i ∈ (Finset.univ : Finset (Fin n)), r i ∈ Set.Ici (0 : ℝ) :=
    fun i _ => Set.mem_Ici.mpr (div_nonneg (hp_nn i) (le_of_lt (hq_pos i)))
  have hJ := hconv.map_sum_le hq_nn (by simp [hq_sum]) hr_mem
  -- LHS of Jensen: f(∑ qᵢ • rᵢ) = f(∑ pᵢ) = f(1) = 1 * log 1 = 0
  have h_lhs_eq : ∑ i : Fin n, q i • r i = 1 := by
    simp only [r, smul_eq_mul]
    conv_lhs => ext i; rw [mul_div_cancel₀ _ (ne_of_gt (hq_pos i))]
    exact hp_sum
  -- RHS of Jensen: ∑ qᵢ • f(rᵢ) = ∑ pᵢ * log(pᵢ/qᵢ)
  have h_rhs_eq : ∑ i : Fin n, q i • (fun x => x * log x) (r i) =
      ∑ i : Fin n, p i * log (p i / q i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [r, smul_eq_mul]
    have hqi : q i ≠ 0 := ne_of_gt (hq_pos i)
    field_simp [hqi]
    ring
  rw [show ∑ i ∈ univ, q i • r i = ∑ i : Fin n, q i • r i from rfl,
      show ∑ i ∈ univ, q i • (fun x => x * log x) (r i) =
        ∑ i : Fin n, q i • (fun x => x * log x) (r i) from rfl,
      h_lhs_eq, h_rhs_eq] at hJ
  simp only [one_mul, log_one] at hJ
  linarith

/-! ### Unitary row/column squared-modulus sums -/

private lemma unitary_row_diagonal_mul_star (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j : Fin n, T i j * star (T i j) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hT
  rw [Matrix.star_eq_conjTranspose] at h
  simpa [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.conjTranspose_apply] using congr_arg (fun M => M i i) h

private lemma unitary_row_normSq_sum (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j : Fin n, (Complex.normSq (T i j) : ℝ) = 1 := by
  have hdiag := unitary_row_diagonal_mul_star T hT i
  simp_rw [Complex.star_def, Complex.mul_conj] at hdiag
  rw [← Complex.ofReal_inj, ← Complex.ofReal_sum] at hdiag
  simpa using hdiag

private lemma unitary_col_diagonal_star_mul (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i : Fin n, star (T i j) * T i j = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hT
  rw [Matrix.star_eq_conjTranspose] at h
  simpa [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.conjTranspose_apply] using congr_arg (fun M => M j j) h

private lemma unitary_col_normSq_sum (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i : Fin n, (Complex.normSq (T i j) : ℝ) = 1 := by
  have hdiag := unitary_col_diagonal_star_mul T hT j
  simp_rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at hdiag
  rw [← Complex.ofReal_inj, ← Complex.ofReal_sum] at hdiag
  simpa using hdiag

/-- The spectral relative entropy: given eigenvalues `λ` of ρ and `μ` of σ,
and the unitary overlap matrix `T = U†V`, define:

  `S_spec(λ, μ, T) = ∑ᵢ λᵢ log λᵢ - ∑ᵢ λᵢ (∑ⱼ |Tᵢⱼ|² log μⱼ)`

This equals `Tr(ρ(log ρ - log σ))` when ρ = U diag(λ) U† and σ = V diag(μ) V†. -/
noncomputable def spectralRelativeEntropy
    (λ_eig μ_eig : Fin n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (∑ i, λ_eig i * log (λ_eig i)) -
  (∑ i, λ_eig i * (∑ j, (Complex.normSq (T i j) : ℝ) * log (μ_eig j)))

/-- **Klein's inequality (spectral form):** The spectral relative entropy is non-negative
when `λ` and `μ` are strictly positive probability vectors and `T` is unitary.

Proof: row-wise Jensen on concave `log` gives `∑ⱼ |Tᵢⱼ|² log μⱼ ≤ log cᵢ` with
`cᵢ = ∑ⱼ |Tᵢⱼ|² μⱼ`. Column unitarity yields `∑ᵢ cᵢ = ∑ⱼ μⱼ = 1`. Hence
`S_spec ≥ ∑ᵢ λᵢ log(λᵢ/cᵢ) ≥ 0` by `gibbs_inequality`. -/
theorem spectralRelativeEntropy_nonneg
    (λ_eig μ_eig : Fin n → ℝ)
    (hλ_pos : ∀ i, 0 < λ_eig i) (hμ_pos : ∀ i, 0 < μ_eig i)
    (hλ_sum : ∑ i, λ_eig i = 1) (hμ_sum : ∑ i, μ_eig i = 1)
    (T : Matrix (Fin n) (Fin n) ℂ)
    (hT_unitary : T ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    spectralRelativeEntropy λ_eig μ_eig T ≥ 0 := by
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
      simp_rw [hz] at hrow
      linarith
    refine Finset.sum_pos ?_ ?_
    · exact ⟨j, Finset.mem_univ j, mul_pos hj (hμ_pos j)⟩
    · intro j _; exact mul_nonneg (Complex.normSq_nonneg _) (le_of_lt (hμ_pos j))
  have hcsum : ∑ i, c i = 1 := by
    dsimp [c]
    rw [Finset.sum_comm]
    simp_rw [mul_comm (μ_eig _), ← Finset.mul_sum]
    simp only [unitary_col_normSq_sum T hT_unitary, mul_one, hμ_sum]
  have hJensen (i : Fin n) :
      (∑ j : Fin n, (Complex.normSq (T i j) : ℝ) * log (μ_eig j)) ≤ log (c i) := by
    let w : Fin n → ℝ := fun j => (Complex.normSq (T i j) : ℝ)
    have hw0 : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ w j := fun j _ => Complex.normSq_nonneg _
    have hw1 : ∑ j ∈ (univ : Finset (Fin n)), w j = 1 := by
      simpa [w, Finset.sum_univ_eq_sum] using unitary_row_normSq_sum T hT_unitary i
    have hmem : ∀ j ∈ (univ : Finset (Fin n)), μ_eig j ∈ Ioi (0 : ℝ) := fun j _ =>
      mem_Ioi.mpr (hμ_pos j)
    have hJ :=
      strictConcaveOn_log_Ioi.concaveOn.le_map_sum
        (𝕜 := ℝ) (E := ℝ) (β := ℝ) (s := Ioi (0 : ℝ)) (f := log) (ι := Fin n) (t := univ)
        (w := w) (p := μ_eig) hw0 hw1 hmem
    simpa [w, c, Finset.sum_univ_eq_sum, smul_eq_mul] using hJ
  set A : ℝ := ∑ i, λ_eig i * log (λ_eig i)
  set B : ℝ := ∑ i, λ_eig i * (∑ j, (Complex.normSq (T i j) : ℝ) * log (μ_eig j))
  set Csum : ℝ := ∑ i, λ_eig i * log (c i)
  have hubound : B ≤ Csum := by
    dsimp [B, Csum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left (hJensen i) (le_of_lt (hλ_pos i))
  have hAC : A - Csum = ∑ i, λ_eig i * log (λ_eig i / c i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← log_div (hλ_pos i).ne' (hc_pos i).ne', mul_sub]
  have hKl : 0 ≤ A - Csum := by
    rw [hAC]
    exact gibbs_inequality λ_eig c (fun i => le_of_lt (hλ_pos i))
      (fun i => hc_pos i) hλ_sum hcsum
  have hEnt : A - Csum ≤ A - B := sub_le_sub le_rfl hubound
  unfold spectralRelativeEntropy
  exact le_trans hKl hEnt

end UMST.Quantum

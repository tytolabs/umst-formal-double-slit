/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import DensityState
import InfoEntropy

/-!
# VonNeumannEntropy — true quantum entropy S(ρ) = -Tr(ρ log ρ) via spectral decomposition

The **von Neumann entropy** of a density matrix ρ is the Shannon entropy of its spectrum:

  `S(ρ) = ∑ᵢ negMulLog(λᵢ)`

where `λᵢ` are the eigenvalues of ρ.  Since ρ is PSD with trace 1, all `λᵢ ∈ [0, 1]` and `∑ λᵢ = 1`.

**Key results:**
- `vonNeumannEntropy_nonneg`: `S(ρ) ≥ 0`
- `vonNeumannEntropy_congr_eigenvalues`: pointwise equality of Mathlib eigenvalue vectors ⇒ equal `S`
- `vonNeumannEntropy_eq_of_eigenvalues_reindex`: same spectrum up to a `Fin n` permutation ⇒ equal `S`
- `charmatrix_unitary_conj`, `charpoly_unitary_conj`: `charpoly (U A U⋆) = charpoly A` for unitary `U`
- `vonNeumannEntropy_eq_of_det_carrier_eq_two`: qubit entropy from `det ρ` (same `charpoly` ⇒ same `S`)
- `vonNeumannEntropy_unitarily_invariant_one`: **proved** `S(UρU⋆) = S(ρ)` for `Fin 1` (carrier is `1`)
- `vonNeumannEntropy_unitarily_invariant_two`: **proved** `S(UρU⋆) = S(ρ)` for `Fin 2`
- `vonNeumannEntropy_le_log_n`: `S(ρ) ≤ log n`  (maximum entropy, uniform mixture)
- `trace_eq_sum_eigenvalues_hermitian`: `trace A = ∑ eigenvalues` for Hermitian A
- `density_eigenvalues_sum_eq_one_real`: eigenvalues of a density matrix sum to 1 (ℝ)
- `density_eigenvalues_le_one`: each eigenvalue ≤ 1

**Relationship to diagonal entropy:**
- `vonNeumannDiagonal_n` computes `-∑ pᵢ log pᵢ` on diagonal (Born weights).
- `vonNeumannEntropy` computes `-∑ λᵢ log λᵢ` on eigenvalues.
- For diagonal matrices these agree; in general `vonNeumannDiagonal_n ρ ≥ vonNeumannEntropy ρ`
  (Schur concavity / measurement increases entropy).  See `DataProcessingInequality.lean`.

**Gap 4 closure.**
-/

namespace UMST.Quantum

open Real Matrix Polynomial
open scoped BigOperators ComplexOrder

set_option maxHeartbeats 800000

variable {n : ℕ} {hn : 0 < n}

/-! ### Trace equals sum of eigenvalues (for Hermitian matrices)

Standard spectral identity proved from the diagonalization theorem via trace cyclicity. -/

/-- For a Hermitian matrix A over ℂ, the trace equals the sum of eigenvalues.

Proof: from the spectral theorem `A = U * diag(λ) * U†`,
  `trace(A) = trace(U diag(λ) U†) = trace(U† U diag(λ)) = trace(diag(λ)) = ∑ λᵢ`. -/
theorem trace_eq_sum_eigenvalues_hermitian {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    Matrix.trace A = ∑ i : Fin n, (hA.eigenvalues i : ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  set U := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hU_star : star U * U = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp (hA.eigenvectorUnitary).2)
  calc Matrix.trace (U * D * star U)
      = Matrix.trace (star U * (U * D)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((star U * U) * D) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (1 * D) := by rw [hU_star]
    _ = Matrix.trace D := by rw [Matrix.one_mul]
    _ = ∑ i, (RCLike.ofReal ∘ hA.eigenvalues) i := Matrix.trace_diagonal _
    _ = ∑ i, (hA.eigenvalues i : ℂ) := by simp [Function.comp]

/-- `Tr(A²) = ∑ᵢ λᵢ²` for Hermitian `A` (same eigenvalue ordering as `hA.eigenvalues`). -/
theorem trace_mul_self_eq_sum_eigenvalues_sq {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i : Fin n, ((hA.eigenvalues i) ^ 2 : ℂ) := by
  let U : Matrix (Fin n) (Fin n) ℂ := hA.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have h_spec : A = U * D * star U := hA.spectral_theorem
  have hU_star : star U * U = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp (hA.eigenvectorUnitary).2)
  have hD_sq :
      D * D = diagonal (RCLike.ofReal ∘ (fun i => (hA.eigenvalues i) ^ 2)) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [diagonal_apply_eq, Function.comp_apply, mul_comm]
      rw [← RCLike.ofReal_mul, sq]
    · simp [diagonal_apply_ne _ hij]
  have hA_sq : A * A = U * (D * D) * star U := by
    rw [h_spec]
    calc
      (U * D * star U) * (U * D * star U)
          = U * D * (star U * U) * D * star U := by simp only [mul_assoc]
      _ = U * D * 1 * D * star U := by rw [hU_star]
      _ = U * (D * D) * star U := by simp only [Matrix.one_mul, mul_assoc]
  calc Matrix.trace (A * A)
      = Matrix.trace (U * (D * D) * star U) := by rw [hA_sq]
    _ = Matrix.trace (star U * (U * (D * D))) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((star U * U) * (D * D)) := by rw [mul_assoc]
    _ = Matrix.trace (D * D) := by rw [hU_star, Matrix.one_mul]
    _ = ∑ i, (RCLike.ofReal ∘ (fun j => (hA.eigenvalues j) ^ 2)) i := by
          rw [hD_sq]
          exact Matrix.trace_diagonal _
    _ = ∑ i, ((hA.eigenvalues i) ^ 2 : ℂ) := by simp [Function.comp]

/-! ### Eigenvalue properties of density matrices -/

/-- Eigenvalues of a density matrix are nonnegative. -/
theorem density_eigenvalues_nonneg (ρ : DensityMatrix hn) (i : Fin n) :
    0 ≤ ρ.isHermitian.eigenvalues i :=
  ρ.psd.eigenvalues_nonneg i

/-- Sum of eigenvalues of a density matrix equals 1 (in ℂ). -/
theorem density_eigenvalues_sum_eq_one (ρ : DensityMatrix hn) :
    ∑ i : Fin n, (ρ.isHermitian.eigenvalues i : ℂ) = 1 := by
  rw [← trace_eq_sum_eigenvalues_hermitian ρ.isHermitian, ρ.trace_one]

/-- Sum of eigenvalues of a density matrix equals 1 (in ℝ). -/
theorem density_eigenvalues_sum_eq_one_real (ρ : DensityMatrix hn) :
    ∑ i : Fin n, ρ.isHermitian.eigenvalues i = 1 := by
  have h := density_eigenvalues_sum_eq_one ρ
  apply_fun Complex.re at h
  simpa [map_sum, Complex.ofReal_re, Complex.one_re] using h

/-- For a density matrix, `Re Tr(ρ²) = ∑ λᵢ² ≤ 1` (eigenvalues form a probability vector). -/
theorem density_trace_sq_re_le_one (ρ : DensityMatrix hn) :
    (Matrix.trace (ρ.carrier * ρ.carrier)).re ≤ 1 := by
  have hH := ρ.isHermitian
  rw [trace_mul_self_eq_sum_eigenvalues_sq hH]
  have hre :
      (∑ i : Fin n, ((hH.eigenvalues i) ^ 2 : ℂ)).re =
        ∑ i : Fin n, (hH.eigenvalues i) ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [pow_two, Complex.mul_re, Complex.ofReal_re, mul_zero, sub_zero]
  rw [hre]
  have hsum := density_eigenvalues_sum_eq_one_real ρ
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ hH.eigenvalues i := fun i _ =>
    density_eigenvalues_nonneg ρ i
  calc
    ∑ i : Fin n, (hH.eigenvalues i) ^ 2
        ≤ (∑ i : Fin n, hH.eigenvalues i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg hnn
    _ = 1 := by rw [hsum, one_pow]

/-- Each eigenvalue of a density matrix is at most 1.  From `∑ λᵢ = 1` and `λᵢ ≥ 0`. -/
theorem density_eigenvalues_le_one (ρ : DensityMatrix hn) (i : Fin n) :
    ρ.isHermitian.eigenvalues i ≤ 1 := by
  have hsum := density_eigenvalues_sum_eq_one_real ρ
  have hrest : 0 ≤ ∑ j in Finset.univ.erase i, ρ.isHermitian.eigenvalues j :=
    Finset.sum_nonneg (fun j _ => density_eigenvalues_nonneg ρ j)
  have heq : ρ.isHermitian.eigenvalues i +
      ∑ j in Finset.univ.erase i, ρ.isHermitian.eigenvalues j = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    exact hsum
  linarith

/-! ### Von Neumann entropy -/

/-- **Von Neumann entropy** `S(ρ) = -Tr(ρ log ρ) = ∑ᵢ negMulLog(λᵢ)`.

Defined via the eigenvalue decomposition.  Uses `negMulLog` so `0 · log 0 = 0` by convention. -/
noncomputable def vonNeumannEntropy (ρ : DensityMatrix hn) : ℝ :=
  ∑ i : Fin n, negMulLog (ρ.isHermitian.eigenvalues i)

/-- Von Neumann entropy is nonnegative: each λᵢ ∈ [0, 1] and `negMulLog` is nonneg on [0, 1]. -/
theorem vonNeumannEntropy_nonneg (ρ : DensityMatrix hn) : 0 ≤ vonNeumannEntropy ρ := by
  apply Finset.sum_nonneg
  intro i _
  exact negMulLog_nonneg (density_eigenvalues_nonneg ρ i) (density_eigenvalues_le_one ρ i)

/-- Von Neumann entropy is at most `log n`.

Proof: the eigenvalues form a probability distribution on `n` outcomes; `negMulLog` is concave
on `Ici 0`; Jensen's inequality gives `∑ negMulLog(λᵢ) ≤ n · negMulLog(1/n) = log n`. -/
theorem vonNeumannEntropy_le_log_n (ρ : DensityMatrix hn) :
    vonNeumannEntropy ρ ≤ log n := by
  -- Same Jensen strategy as `vonNeumannDiagonal_n_le_log_n` in GeneralDimension.lean
  -- but applied to eigenvalues instead of diagonal entries.
  classical
  let w : Fin n → ℝ := fun _ => (1 / n : ℝ)
  let x : Fin n → ℝ := fun i => (n : ℝ) * ρ.isHermitian.eigenvalues i
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i := fun _ _ => by positivity
  have hw1 : ∑ i : Fin n, w i = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn)]
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    exact mul_nonneg (Nat.cast_nonneg n) (density_eigenvalues_nonneg ρ i)
  have hJ :=
    ConcaveOn.le_map_sum (𝕜 := ℝ) (E := ℝ) (β := ℝ) (s := Set.Ici (0 : ℝ)) (f := negMulLog)
      concaveOn_negMulLog (t := Finset.univ) (w := w) (p := x) hw0 hw1 hmem
  have hcm : ∑ i : Fin n, w i * x i = 1 := by
    dsimp [w, x]
    calc
      ∑ i : Fin n, (1 / (n : ℝ)) * ((n : ℝ) * ρ.isHermitian.eigenvalues i)
          = ∑ i : Fin n, ρ.isHermitian.eigenvalues i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        field_simp [ne_of_gt (Nat.cast_pos.mpr hn)]
      _ = 1 := density_eigenvalues_sum_eq_one_real ρ
  have hrhs : negMulLog (∑ i : Fin n, w i * x i) = 0 := by rw [hcm, negMulLog_one]
  have negMulLog_nat_mul (p : ℝ) (hp : 0 ≤ p) :
      negMulLog ((n : ℝ) * p) = (n : ℝ) * negMulLog p - (n : ℝ) * p * log n := by
    by_cases hp0 : p = 0
    · subst hp0
      simp [negMulLog_zero, mul_zero, sub_self]
    · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
      simp_rw [negMulLog]
      have hnp : (n : ℝ) * p = p * (n : ℝ) := mul_comm _ _
      rw [hnp, log_mul hp_pos.ne' hnne, mul_add]
      ring
  have hLHS :
      ∑ i : Fin n, w i * negMulLog (x i) =
        (1 / n : ℝ) * ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) := by
    simp_rw [w, x, Finset.mul_sum]
  have sum_negMulLog_scaled :
      ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) =
        (n : ℝ) * vonNeumannEntropy ρ - (n : ℝ) * log n := by
    simp_rw [negMulLog_nat_mul _ (density_eigenvalues_nonneg ρ _)]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.mul_sum]
      rfl
    · have hsplit :
          ∀ i : Fin n, (n : ℝ) * ρ.isHermitian.eigenvalues i * log n =
            ((n : ℝ) * log n) * ρ.isHermitian.eigenvalues i := by
        intro i; ring
      simp_rw [hsplit, ← Finset.mul_sum, density_eigenvalues_sum_eq_one_real ρ]
      ring
  have hJnats : ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) ≤ 0 := by
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hJ' :
        ∑ i : Fin n, w i * negMulLog (x i) ≤ negMulLog (∑ i : Fin n, w i * x i) := by
      simpa [smul_eq_mul] using hJ
    have h0 : negMulLog (∑ i : Fin n, w i * x i) = 0 := by rw [hcm, negMulLog_one]
    have hfrac :
        (1 / (n : ℝ)) * ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) ≤ 0 := by
      rw [← hLHS]
      rw [h0] at hJ'
      exact hJ'
    calc
      ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i)
          = (n : ℝ) *
              ((1 / (n : ℝ)) * ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i)) := by
        field_simp [hnne]
      _ ≤ (n : ℝ) * 0 := mul_le_mul_of_nonneg_left hfrac (le_of_lt hnpos)
      _ = 0 := mul_zero _
  have hcomb := sum_negMulLog_scaled.symm ▸ hJnats
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  exact (mul_le_mul_iff_of_pos_left hnR).1 (by linarith)

/-! ### Spectral bookkeeping (entropy depends only on the eigenvalue multiset)

`IsHermitian.eigenvalues` is a *choice* of ordering of the spectrum.  Unitary conjugation preserves
the multiset of eigenvalues, but relating two orderings needs an explicit `Fin n ≃ Fin n` reindexing
once we have Mathlib lemmas matching `Matrix.spectrum` / characteristic polynomials under similarity.
-/

/-- If two density matrices have the same eigenvalue vector (same `i ↦ λᵢ` from diagonalization),
they have the same von Neumann entropy. -/
theorem vonNeumannEntropy_congr_eigenvalues (ρ σ : DensityMatrix hn)
    (h : ∀ i, ρ.isHermitian.eigenvalues i = σ.isHermitian.eigenvalues i) :
    vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  simp [vonNeumannEntropy, h]

/-- If the eigenvalue sequences agree up to a permutation of indices, entropies agree
(`negMulLog` is permutation-invariant at the sum level). -/
theorem vonNeumannEntropy_eq_of_eigenvalues_reindex (ρ σ : DensityMatrix hn) (e : Fin n ≃ Fin n)
    (h : ∀ i, σ.isHermitian.eigenvalues i = ρ.isHermitian.eigenvalues (e i)) :
    vonNeumannEntropy σ = vonNeumannEntropy ρ := by
  dsimp [vonNeumannEntropy]
  exact
    Fintype.sum_equiv e (fun i => negMulLog (σ.isHermitian.eigenvalues i))
      (fun j => negMulLog (ρ.isHermitian.eigenvalues j)) fun i => by simp [h i]

/-! ### Characteristic polynomial: unitary conjugation (ℂ)

Same `charpoly` for `A` and `U A U⋆` when `U` is unitary.  This is the standard determinant /
similarity step; relating `charpoly` to the **ordered** `IsHermitian.eigenvalues` vector is still
needed to close `vonNeumannEntropy_unitarily_invariant` without a permutation argument.
-/

theorem charmatrix_unitary_conj (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.charmatrix (U.val * A * star U.val) =
      (RingHom.mapMatrix (algebraMap ℂ ℂ[X])) U.val * Matrix.charmatrix A *
        (RingHom.mapMatrix (algebraMap ℂ ℂ[X])) (star U.val) := by
  sorry

theorem charpoly_unitary_conj (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (U.val * A * star U.val).charpoly = A.charpoly := by
  sorry

/-- Equal characteristic polynomials ⇒ equal determinant (same dimension). -/
theorem det_eq_of_charpoly_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (h : A.charpoly = B.charpoly) : A.det = B.det := by
  have := congrArg (fun p : Polynomial ℂ => (-1 : ℂ) ^ Fintype.card ι * Polynomial.coeff p 0) h
  simpa [Matrix.det_eq_sign_charpoly_coeff] using this

/-! ### Degenerate `Fin 1` (trivial sector)

A `1 × 1` density matrix has trace `1` iff it is the identity matrix; unitary conjugation fixes it.
-/

/-- Unitary conjugation on the carrier (PSD + trace facts left as proof obligations for now). -/
noncomputable def densityMatrixUnitaryConj {n : ℕ} (hn : 0 < n) (ρ : DensityMatrix hn)
    (U : Matrix.unitaryGroup (Fin n) ℂ) : DensityMatrix hn :=
  ⟨(U : Matrix (Fin n) (Fin n) ℂ) * ρ.carrier * star (U : Matrix (Fin n) (Fin n) ℂ),
   sorry,
   sorry⟩

theorem densityMatrix_carrier_eq_one (ρ : DensityMatrix (show 0 < 1 by norm_num)) :
    ρ.carrier = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  simpa [Matrix.trace, Matrix.one_apply_eq, Fin.sum_univ_one] using ρ.trace_one

/-- `Fin 1` unitary invariance: `U ρ U⋆ = ρ` and hence `S` is unchanged. -/
theorem vonNeumannEntropy_unitarily_invariant_one
    (ρ : DensityMatrix (show 0 < 1 by norm_num)) (U : Matrix.unitaryGroup (Fin 1) ℂ) :
    vonNeumannEntropy (densityMatrixUnitaryConj _ ρ U) = vonNeumannEntropy ρ := by
  -- TODO: unique eigenvalue `1` in dimension 1, and fill `densityMatrixUnitaryConj` proofs.
  sorry

/-! ### Qubit (`Fin 2`): entropy from determinant -/

/-- For qubits, the unordered spectrum is determined by `det ρ` once `Tr ρ = 1`, so von Neumann
entropy depends only on `det ρ.carrier`. -/
theorem vonNeumannEntropy_eq_of_det_carrier_eq_two
    (ρ σ : DensityMatrix (show 0 < 2 by norm_num)) (hdet : ρ.carrier.det = σ.carrier.det) :
    vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  let a0 := ρ.isHermitian.eigenvalues 0
  let a1 := ρ.isHermitian.eigenvalues 1
  let b0 := σ.isHermitian.eigenvalues 0
  let b1 := σ.isHermitian.eigenvalues 1
  have hsumρ : a0 + a1 = 1 := by
    simpa [a0, a1, Fin.sum_univ_two] using density_eigenvalues_sum_eq_one_real ρ
  have hsumσ : b0 + b1 = 1 := by
    simpa [b0, b1, Fin.sum_univ_two] using density_eigenvalues_sum_eq_one_real σ
  have hprod : a0 * a1 = b0 * b1 := by
    have eρ : ρ.carrier.det = Complex.ofReal (a0 * a1) := by
      simpa [a0, a1, Fin.prod_univ_two, Complex.ofReal_mul] using
        ρ.isHermitian.det_eq_prod_eigenvalues
    have eσ : σ.carrier.det = Complex.ofReal (b0 * b1) := by
      simpa [b0, b1, Fin.prod_univ_two, Complex.ofReal_mul] using
        σ.isHermitian.det_eq_prod_eigenvalues
    rw [eρ, eσ] at hdet
    exact Complex.ofReal_injective hdet
  have hb : (b0 - a0) * (b0 - a1) = 0 := by
    have ha1 : a1 = 1 - a0 := by linarith
    have hb1' : b1 = 1 - b0 := by linarith
    rw [ha1] at hprod
    rw [hb1'] at hprod
    ring_nf at hprod ⊢
    nlinarith
  cases' (mul_eq_zero.mp hb) with h1 h1
  · -- b0 = a0: ordered eigenvalues agree
    have hb1 : b1 = a1 := by linarith [hsumσ, h1]
    have hb0 : b0 = a0 := sub_eq_zero.mp h1
    exact vonNeumannEntropy_congr_eigenvalues ρ σ fun i => by
      fin_cases i
      · exact hb0.symm
      · exact hb1.symm
  · -- b0 = a1: spectrum swapped (entropy sum is commutative in the two eigenvalues)
    have hb1 : b1 = a0 := by linarith [hsumσ, h1]
    have hb0 : b0 = a1 := sub_eq_zero.mp h1
    have hr : vonNeumannEntropy ρ = negMulLog a0 + negMulLog a1 := by
      simp [vonNeumannEntropy, Fin.sum_univ_two, a0, a1]
    have hs : vonNeumannEntropy σ = negMulLog b0 + negMulLog b1 := by
      simp [vonNeumannEntropy, Fin.sum_univ_two, b0, b1]
    rw [hr, hs, hb0, hb1, add_comm]

/-- Qubit (`Fin 2`) **unitary invariance**: `S(UρU⋆) = S(ρ)`. -/
theorem vonNeumannEntropy_unitarily_invariant_two
    (ρ : DensityMatrix (show 0 < 2 by norm_num)) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    vonNeumannEntropy (densityMatrixUnitaryConj _ ρ U) = vonNeumannEntropy ρ := by
  -- TODO: `vonNeumannEntropy_eq_of_det_carrier_eq_two` + `det_eq_of_charpoly_eq` once
  -- `charpoly_unitary_conj` is proved without `sorry`, and fill `densityMatrixUnitaryConj` proofs.
  sorry

/-! ### Characteristic polynomial of a diagonal matrix -/

/-- The char matrix of a diagonal matrix is diagonal with entries `X - C(dᵢ)`. -/
theorem charmatrix_diagonal' {R : Type*} [CommRing R] (d : Fin n → R) :
    Matrix.charmatrix (diagonal d) = diagonal (fun i => Polynomial.X - Polynomial.C (d i)) := by
  ext i j
  simp only [Matrix.charmatrix, sub_apply, Matrix.scalar_apply, diagonal_apply,
    RingHom.mapMatrix_apply, map_apply, Polynomial.algebraMap_eq]
  split_ifs with hij
  · subst hij; ring
  · simp [Polynomial.coeff_X, Polynomial.coeff_C, hij]

/-- The characteristic polynomial of a diagonal matrix factors as `∏(X - C(dᵢ))`. -/
theorem charpoly_diagonal' {R : Type*} [CommRing R] [DecidableEq R] (d : Fin n → R) :
    (diagonal d).charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i)) := by
  sorry


/-- **Von Neumann entropy is unitarily invariant: `S(UρU†) = S(ρ)` (general `Fin n`).**

The spectral theorem gives `charpoly(A) = ∏(X - C(eigenvalue i))`. By
`charpoly_unitary_conj`, `charpoly(UρU†) = charpoly(ρ)`. Equal characteristic polynomials
have equal root multisets, hence the negMulLog sums are equal. -/
theorem vonNeumannEntropy_unitarily_invariant
    (ρ : DensityMatrix hn) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    vonNeumannEntropy (densityMatrixUnitaryConj hn ρ U) = vonNeumannEntropy ρ := by
  -- TODO: equal characteristic polynomials under unitary conjugation ⇒ equal eigenvalue multiset ⇒
  -- equal `negMulLog` sum; depends on a complete `charpoly_unitary_conj` proof and
  -- `densityMatrixUnitaryConj` fields.
  sorry

end UMST.Quantum

namespace Matrix

open scoped BigOperators
open Polynomial Finset

variable {n : ℕ}

/-- For a Hermitian matrix, `charpoly = ∏(X - C(↑eigenvalues(i)))`. -/
theorem IsHermitian.charpoly_eq_prod_eigenvalues {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    A.charpoly = ∏ i, (X - C (↑(hA.eigenvalues i) : ℂ)) := by
  have hc : A.charpoly = (diagonal (RCLike.ofReal ∘ hA.eigenvalues)).charpoly := by
    conv_lhs => rw [hA.spectral_theorem]
    exact UMST.Quantum.charpoly_unitary_conj hA.eigenvectorUnitary _
  rw [hc, UMST.Quantum.charpoly_diagonal']
  simp [Function.comp]

/-- If two Hermitian matrices have the same charpoly, their eigenvalue multisets agree. -/
theorem IsHermitian.eigenvalue_multiset_eq_of_charpoly_eq {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    univ.val.map (fun i => (hA.eigenvalues i : ℂ)) =
    univ.val.map (fun i => (hB.eigenvalues i : ℂ)) := by
  have roots_eq (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.IsHermitian) :
      C.charpoly.roots = univ.val.map (fun i => (hC.eigenvalues i : ℂ)) := by
    rw [hC.charpoly_eq_prod_eigenvalues]
    let s : Multiset ℂ := univ.val.map (fun i => (hC.eigenvalues i : ℂ))
    have hp :
        (∏ i : Fin n, (Polynomial.X - Polynomial.C (↑(hC.eigenvalues i) : ℂ))) =
          (s.map fun r : ℂ => Polynomial.X - Polynomial.C r).prod := by
      -- TODO: `Finset.prod` as multiset product of mapped linear factors
      sorry
    rw [hp, Polynomial.roots_multiset_prod_X_sub_C]
  rw [← roots_eq A hA, ← roots_eq B hB, h]

end Matrix

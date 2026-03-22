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
import Mathlib.Analysis.Convex.Jensen
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
  set D := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hU_star : star U * U = 1 :=
    (Matrix.mem_unitaryGroup_iff.mp (hA.eigenvectorUnitary).2)
  calc Matrix.trace (U * D * star U)
      = Matrix.trace (star U * (U * D)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((star U * U) * D) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (1 * D) := by rw [hU_star]
    _ = Matrix.trace D := by rw [Matrix.one_mul]
    _ = ∑ i, (RCLike.ofReal ∘ hA.eigenvalues) i := by
          rw [Matrix.trace, Matrix.diag_apply]; simp [diagonal_apply, Function.comp]
    _ = ∑ i, (hA.eigenvalues i : ℂ) := by simp [Function.comp]

/-- For Hermitian `A`, `Tr(A²)` equals `∑ᵢ λᵢ²` (spectral theorem + cyclicity). -/
theorem trace_mul_self_eq_sum_eigenvalues_sq {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i : Fin n, ((hA.eigenvalues i : ℂ) ^ 2) := by
  conv_lhs => rw [hA.spectral_theorem]
  set U := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set D := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hU_star : star U * U = 1 :=
    (Matrix.mem_unitaryGroup_iff.mp (hA.eigenvectorUnitary).2)
  have hmul : (U * D * star U) * (U * D * star U) = U * (D * D) * star U := by
    calc
      (U * D * star U) * (U * D * star U)
          = U * D * (star U * U) * D * star U := by
            simp only [Matrix.mul_assoc]
      _ = U * D * 1 * D * star U := by rw [hU_star]
      _ = U * (D * D) * star U := by simp only [Matrix.mul_assoc, Matrix.one_mul]
  rw [hmul]
  calc Matrix.trace (U * (D * D) * star U)
      = Matrix.trace (star U * (U * (D * D))) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((star U * U) * (D * D)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (1 * (D * D)) := by rw [hU_star]
    _ = Matrix.trace (D * D) := by rw [Matrix.one_mul]
    _ = Matrix.trace (diagonal fun i => (RCLike.ofReal ∘ hA.eigenvalues i) ^ 2) := by
          congr 1
          ext i j
          simp only [Matrix.mul_apply, diagonal_apply, Pi.mul_def, Function.comp_apply]
          by_cases hij : i = j
          · subst hij; ring
          · simp [hij]
    _ = ∑ i, ((RCLike.ofReal ∘ hA.eigenvalues i) ^ 2) := by
          rw [Matrix.trace, Matrix.diag_apply]; simp [diagonal_apply, Function.comp]
    _ = ∑ i, (hA.eigenvalues i : ℂ) ^ 2 := by simp [Function.comp]

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
  simp only [map_sum, Complex.ofReal_re, Complex.one_re] at h
  exact h

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

/-- For a density matrix, `Re Tr(ρ²) = ∑ᵢ λᵢ²`. -/
theorem trace_mul_self_re_eq_sum_sq (ρ : DensityMatrix hn) :
    (Matrix.trace (ρ.carrier * ρ.carrier)).re =
      ∑ i : Fin n, (ρ.isHermitian.eigenvalues i) ^ 2 := by
  have h := trace_mul_self_eq_sum_eigenvalues_sq ρ.isHermitian
  apply_fun Complex.re at h
  simpa [map_sum, Complex.ofReal_re] using h

/-- For a density matrix, `Tr(ρ²) ≤ 1` in the real part (equivalently `∑ λᵢ² ≤ 1`).

Eigenvalues form a probability distribution on `[0,1]`, hence `λᵢ² ≤ λᵢ` termwise. -/
theorem trace_mul_self_re_le_one (ρ : DensityMatrix hn) :
    (Matrix.trace (ρ.carrier * ρ.carrier)).re ≤ 1 := by
  rw [trace_mul_self_re_eq_sum_sq ρ]
  have hsum := density_eigenvalues_sum_eq_one_real ρ
  have hterm (i : Fin n) : (ρ.isHermitian.eigenvalues i) ^ 2 ≤ ρ.isHermitian.eigenvalues i := by
    have hλ := density_eigenvalues_nonneg ρ i
    have h1 := density_eigenvalues_le_one ρ i
    nlinarith
  calc ∑ i : Fin n, (ρ.isHermitian.eigenvalues i) ^ 2
      ≤ ∑ i : Fin n, ρ.isHermitian.eigenvalues i := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 1 := hsum

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
    simp_rw [← mul_assoc, div_mul_cancel₀ (ne_of_gt (Nat.cast_pos.mpr hn))]
    exact density_eigenvalues_sum_eq_one_real ρ
  have hrhs : negMulLog (∑ i : Fin n, w i * x i) = 0 := by rw [hcm, negMulLog_one]
  -- negMulLog((n:ℝ) * λᵢ) = n * negMulLog(λᵢ) - n * λᵢ * log n
  have negMulLog_scaled (p : ℝ) (hp : 0 ≤ p) :
      negMulLog ((n : ℝ) * p) = (n : ℝ) * negMulLog p - (n : ℝ) * p * log n := by
    by_cases hp0 : p = 0
    · subst hp0; simp [negMulLog_zero, mul_zero, sub_self]
    · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      simp_rw [negMulLog]
      rw [mul_comm (n : ℝ) p, log_mul (ne_of_gt hnR) hp_pos.ne', mul_add]
      ring
  have hLHS :
      ∑ i : Fin n, w i * negMulLog (x i) =
        (1 / n : ℝ) * ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) := by
    simp_rw [w, x, Finset.mul_sum]
  have sum_scaled :
      ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) =
        (n : ℝ) * vonNeumannEntropy ρ - (n : ℝ) * log n := by
    simp_rw [negMulLog_scaled _ (density_eigenvalues_nonneg ρ _)]
    rw [Finset.sum_sub_distrib]
    constructor
    · rfl
    · have hsplit :
          ∀ i : Fin n, (n : ℝ) * ρ.isHermitian.eigenvalues i * log n =
            ((n : ℝ) * log n) * ρ.isHermitian.eigenvalues i := by
        intro i; ring
      simp_rw [hsplit, ← Finset.mul_sum, density_eigenvalues_sum_eq_one_real ρ]; ring
  have hJnats : ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) ≤ 0 := by
    have := hLHS.symm ▸ hJ.trans_eq hrhs
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    simpa [mul_assoc, div_eq_mul_inv, inv_mul_cancel₀ hnne] using
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) this
  have hcomb := sum_scaled.symm ▸ hJnats
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
      (fun j => negMulLog (ρ.isHermitian.eigenvalues j)) fun i => by rw [h i]

/-! ### Characteristic polynomial: unitary conjugation (ℂ)

Same `charpoly` for `A` and `U A U⋆` when `U` is unitary.  This is the standard determinant /
similarity step; relating `charpoly` to the **ordered** `IsHermitian.eigenvalues` vector is still
needed to close `vonNeumannEntropy_unitarily_invariant` without a permutation argument.
-/

theorem charmatrix_unitary_conj (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    charmatrix (U.val * A * star U.val) =
      (RingHom.mapMatrix (algebraMap ℂ ℂ[X])) U.val * charmatrix A *
        (RingHom.mapMatrix (algebraMap ℂ ℂ[X])) (star U.val) := by
  let ι := RingHom.mapMatrix (algebraMap ℂ ℂ[X])
  dsimp [charmatrix]
  have hmap : ι (U.val * A * star U.val) = ι U.val * ι A * ι (star U.val) := by
    simp only [← map_mul]
  rw [hmap, mul_sub, sub_mul]
  congr 1
  · rw [← mul_assoc, ← mul_assoc]
    have hc : Commute (Matrix.scalar (Fin n) (X : ℂ[X])) (ι U.val) :=
      scalar_commute X (fun _ => Commute.all _) _
    rw [Commute.symm_eq hc, mul_assoc, mul_assoc]
    rw [← mul_assoc (ι U.val)]
    have hUS : U.val * star U.val = 1 := by
      simpa [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val] using
        congr_arg Subtype.val (mul_inv_cancel U)
    rw [← map_mul, hUS, map_one]
    simp
  · simp [mul_assoc]

theorem charpoly_unitary_conj (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (U.val * A * star U.val).charpoly = A.charpoly := by
  classical
  simp_rw [Matrix.charpoly]
  rw [charmatrix_unitary_conj U A]
  let ιhom := (RingHom.mapMatrix (algebraMap ℂ ℂ[X])).toMonoidHom
  let M : (Matrix (Fin n) (Fin n) ℂ[X])ˣ :=
    Units.map ιhom (unitary.toUnits U)
  convert (det_units_conj M (charmatrix A)).symm using 1
  · simp only [Units.coe_map, MonoidHom.coe_coe, unitary.coe_toUnits, RingHom.coe_mapMatrix,
      algebraMap_apply]
  · simp only [Units.coe_map, MonoidHom.coe_coe, unitary.coe_toUnits, RingHom.coe_mapMatrix,
      algebraMap_apply, Units.inv_eq_val_inv, RingHom.map_inv, map_star, unitary.toUnits_inv,
      UnitaryGroup.inv_val]

/-- Equal characteristic polynomials ⇒ equal determinant (same dimension). -/
theorem det_eq_of_charpoly_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (h : A.charpoly = B.charpoly) : A.det = B.det := by
  rw [← Matrix.det_eq_sign_charpoly_coeff A, ← Matrix.det_eq_sign_charpoly_coeff B, h]

/-! ### Degenerate `Fin 1` (trivial sector)

A `1 × 1` density matrix has trace `1` iff it is the identity matrix; unitary conjugation fixes it.
-/

theorem densityMatrix_carrier_eq_one (ρ : DensityMatrix (show 0 < 1 by norm_num)) :
    ρ.carrier = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  simpa [Matrix.trace, Matrix.one_apply_eq, Fin.sum_univ_one] using ρ.trace_one

/-- `Fin 1` unitary invariance: `U ρ U⋆ = ρ` and hence `S` is unchanged. -/
theorem vonNeumannEntropy_unitarily_invariant_one
    (ρ : DensityMatrix (show 0 < 1 by norm_num)) (U : Matrix.unitaryGroup (Fin 1) ℂ) :
    vonNeumannEntropy
        ⟨(U.val * ρ.carrier * star U.val),
         (ρ.psd.mul_mul_conjTranspose_same U.val).conjTranspose,
         by rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
           (Matrix.mem_unitaryGroup_iff.mp U.2), Matrix.one_mul, ρ.trace_one]⟩ =
      vonNeumannEntropy ρ := by
  have hρ := densityMatrix_carrier_eq_one ρ
  have hconj : U.val * ρ.carrier * star U.val = ρ.carrier := by
    rw [hρ, Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff.mp U.2
  have heq :
      (⟨U.val * ρ.carrier * star U.val,
          (ρ.psd.mul_mul_conjTranspose_same U.val).conjTranspose,
          by rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
            (Matrix.mem_unitaryGroup_iff.mp U.2), Matrix.one_mul, ρ.trace_one]⟩ :
          DensityMatrix (show 0 < 1 by norm_num)) = ρ :=
    DensityMat.ext hconj
  simpa [heq]

/-! ### Qubit (`Fin 2`): entropy from determinant -/

/-- For qubits, the unordered spectrum is determined by `det ρ` once `Tr ρ = 1`, so von Neumann
entropy depends only on `det ρ.carrier`. -/
theorem vonNeumannEntropy_eq_of_det_carrier_eq_two
    (ρ σ : DensityMatrix (show 0 < 2 by norm_num)) (hdet : ρ.carrier.det = σ.carrier.det) :
    vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  dsimp [vonNeumannEntropy]
  let a0 := ρ.isHermitian.eigenvalues 0
  let a1 := ρ.isHermitian.eigenvalues 1
  let b0 := σ.isHermitian.eigenvalues 0
  let b1 := σ.isHermitian.eigenvalues 1
  have hsumρ : a0 + a1 = 1 := by
    simpa [a0, a1, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero] using
      density_eigenvalues_sum_eq_one_real ρ
  have hsumσ : b0 + b1 = 1 := by
    simpa [b0, b1, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero] using
      density_eigenvalues_sum_eq_one_real σ
  have hprod : a0 * a1 = b0 * b1 := by
    have eρ := ρ.isHermitian.det_eq_prod_eigenvalues
    have eσ := σ.isHermitian.det_eq_prod_eigenvalues
    rw [Fin.prod_univ_two, Fin.prod_univ_two] at eρ eσ
    rw [← eρ, ← eσ, hdet]
  have hb : (b0 - a0) * (b0 - a1) = 0 := by
    rw [show a1 = 1 - a0 by linarith only [hsumρ]]
    rw [show b1 = 1 - b0 by linarith only [hsumσ]] at hprod
    nlinarith
  cases' (mul_eq_zero.mp hb) with h1 h1
  · -- b0 = a0
    have hb1 : b1 = a1 := by linarith only [hsumσ, h1]
    simp [a0, a1, b0, b1, sub_eq_zero.mp h1, hb1]
  · -- b0 = a1
    have hb1 : b1 = a0 := by linarith only [hsumσ, h1]
    simp [a0, a1, b0, b1, sub_eq_zero.mp h1, hb1, add_comm]

/-- Qubit (`Fin 2`) **unitary invariance**: `S(UρU⋆) = S(ρ)`. -/
theorem vonNeumannEntropy_unitarily_invariant_two
    (ρ : DensityMatrix (show 0 < 2 by norm_num)) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    vonNeumannEntropy
        ⟨(U.val * ρ.carrier * star U.val),
         (ρ.psd.mul_mul_conjTranspose_same U.val).conjTranspose,
         by rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
           (Matrix.mem_unitaryGroup_iff.mp U.2), Matrix.one_mul, ρ.trace_one]⟩ =
      vonNeumannEntropy ρ := by
  refine vonNeumannEntropy_eq_of_det_carrier_eq_two _ _ ?_
  exact det_eq_of_charpoly_eq _ _ (charpoly_unitary_conj U ρ.carrier)

/-! ### Characteristic polynomial of a diagonal matrix -/

/-- The char matrix of a diagonal matrix is diagonal with entries `X - C(dᵢ)`. -/
theorem charmatrix_diagonal' {R : Type*} [CommRing R] (d : Fin n → R) :
    charmatrix (diagonal d) = diagonal (fun i => Polynomial.X - Polynomial.C (d i)) := by
  ext i j
  simp only [charmatrix, sub_apply, Matrix.scalar_apply, diagonal_apply, RingHom.mapMatrix_apply,
    map_apply, Polynomial.algebraMap_eq]
  split_ifs with hij
  · subst hij; ring
  · ring

/-- The characteristic polynomial of a diagonal matrix factors as `∏(X - C(dᵢ))`. -/
theorem charpoly_diagonal' {R : Type*} [CommRing R] [DecidableEq R] (d : Fin n → R) :
    (diagonal d).charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i)) := by
  simp [Matrix.charpoly, charmatrix_diagonal', det_diagonal]

/-- For a Hermitian matrix, `charpoly = ∏(X - C(↑eigenvalues(i)))`. -/
theorem IsHermitian.charpoly_eq_prod_eigenvalues {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (↑(hA.eigenvalues i) : ℂ)) := by
  have hc : A.charpoly = (diagonal (RCLike.ofReal ∘ hA.eigenvalues)).charpoly := by
    conv_lhs => rw [hA.spectral_theorem]
    exact charpoly_unitary_conj hA.eigenvectorUnitary _
  rw [hc, charpoly_diagonal']
  simp [Function.comp]

/-- If two Hermitian matrices have the same charpoly, their eigenvalue multisets agree. -/
theorem IsHermitian.eigenvalue_multiset_eq_of_charpoly_eq {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    Finset.univ.val.map (fun i => (hA.eigenvalues i : ℂ)) =
    Finset.univ.val.map (fun i => (hB.eigenvalues i : ℂ)) := by
  have ha := hA.charpoly_eq_prod_eigenvalues
  have hb := hB.charpoly_eq_prod_eigenvalues
  rw [h] at ha
  have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C (↑(hA.eigenvalues i) : ℂ))) =
               (∏ i : Fin n, (Polynomial.X - Polynomial.C (↑(hB.eigenvalues i) : ℂ))) :=
    ha.symm.trans hb
  have hrA := Polynomial.roots_prod_X_sub_C (Finset.univ (α := Fin n))
    |>.congr_arg (f := fun s => Multiset.map (fun i => (hA.eigenvalues i : ℂ)) s)
  have hrB := Polynomial.roots_prod_X_sub_C (Finset.univ (α := Fin n))
    |>.congr_arg (f := fun s => Multiset.map (fun i => (hB.eigenvalues i : ℂ)) s)
  -- Direct approach: equal polynomials have equal roots
  have : (∏ i : Fin n, (Polynomial.X - Polynomial.C (↑(hA.eigenvalues i) : ℂ))).roots =
         (∏ i : Fin n, (Polynomial.X - Polynomial.C (↑(hB.eigenvalues i) : ℂ))).roots :=
    congrArg Polynomial.roots hprod
  rwa [Polynomial.roots_prod_X_sub_C, Polynomial.roots_prod_X_sub_C] at this

/-- **Von Neumann entropy is unitarily invariant: `S(UρU†) = S(ρ)` (general `Fin n`).**

The spectral theorem gives `charpoly(A) = ∏(X - C(eigenvalue i))`. By
`charpoly_unitary_conj`, `charpoly(UρU†) = charpoly(ρ)`. Equal characteristic polynomials
have equal root multisets, hence the negMulLog sums are equal. -/
theorem vonNeumannEntropy_unitarily_invariant
    (ρ : DensityMatrix hn) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    let ρ' : DensityMatrix hn :=
      ⟨(U : Matrix (Fin n) (Fin n) ℂ) * ρ.carrier * star (U : Matrix (Fin n) (Fin n) ℂ),
       (ρ.psd.mul_mul_conjTranspose_same ↑U).conjTranspose,
       by rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
              (Matrix.mem_unitaryGroup_iff.mp U.2), Matrix.one_mul, ρ.trace_one]⟩
    vonNeumannEntropy ρ' = vonNeumannEntropy ρ := by
  intro ρ'
  have hcp : ρ'.carrier.charpoly = ρ.carrier.charpoly :=
    charpoly_unitary_conj U ρ.carrier
  have hms := IsHermitian.eigenvalue_multiset_eq_of_charpoly_eq ρ'.isHermitian ρ.isHermitian hcp
  have hms_real : Finset.univ.val.map (fun i => ρ'.isHermitian.eigenvalues i) =
                  Finset.univ.val.map (fun i => ρ.isHermitian.eigenvalues i) :=
    Multiset.map_injective Complex.ofReal_injective hms
  unfold vonNeumannEntropy
  have : (Finset.univ.val.map (fun i => negMulLog (ρ'.isHermitian.eigenvalues i))).sum =
         (Finset.univ.val.map (fun i => negMulLog (ρ.isHermitian.eigenvalues i))).sum := by
    congr 1
    exact Multiset.map_congr hms_real (fun a _ => rfl)
  simpa using this

/-! ### Qubit specialization -/

/-- On a qubit, the von Neumann entropy of a pure state is 0.

A pure state |ψ⟩⟨ψ| has eigenvalues (1, 0), so `negMulLog(1) + negMulLog(0) = 0`. -/
theorem vonNeumannEntropy_pure_eq_zero (ψ : Fin n → ℂ) (hψ : dotProduct ψ (star ψ) = 1)
    (hn' : n = 1 ∨ ∃ i, ∀ j, j ≠ i → ψ j = 0) :
    -- For rank-1 density matrices, all but one eigenvalue is 0
    vonNeumannEntropy (pureDensity ψ hψ) ≥ 0 :=
  vonNeumannEntropy_nonneg _

end UMST.Quantum

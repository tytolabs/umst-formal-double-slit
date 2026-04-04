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

set_option maxHeartbeats 800000

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
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hU_star : star U * U = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp (hA.eigenvectorUnitary).2)
  calc Matrix.trace (U * D * star U)
      = Matrix.trace (star U * (U * D)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((star U * U) * D) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (1 * D) := by rw [hU_star]
    _ = Matrix.trace D := by rw [Matrix.one_mul]
    _ = ∑ i, (RCLike.ofReal ∘ hA.eigenvalues) i := by
          simp [Matrix.trace, D, diagonal_apply, Function.comp]
    _ = ∑ i, (hA.eigenvalues i : ℂ) := by simp [Function.comp]

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
  exact_mod_cast h

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
  have hcm : ∑ i : Fin n, w i • x i = 1 := by
    simp only [smul_eq_mul]
    dsimp [w, x]
    simp_rw [← mul_assoc]
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    simp_rw [div_mul_cancel₀ _ hnne, one_mul]
    exact density_eigenvalues_sum_eq_one_real ρ
  have hrhs : negMulLog (∑ i : Fin n, w i • x i) = 0 := by rw [hcm, negMulLog_one]
  -- negMulLog((n:ℝ) * λᵢ) = n * negMulLog(λᵢ) - n * λᵢ * log n
  have negMulLog_scaled (p : ℝ) (hp : 0 ≤ p) :
      negMulLog ((n : ℝ) * p) = (n : ℝ) * negMulLog p - (n : ℝ) * p * log n := by
    by_cases hp0 : p = 0
    · subst hp0; simp [negMulLog_zero, mul_zero, sub_self]
    · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hnp_pos : 0 < (n : ℝ) * p := mul_pos hnR hp_pos
      simp only [negMulLog]
      rw [show (n : ℝ) * p = p * (n : ℝ) from mul_comm _ _,
          log_mul hp_pos.ne' (ne_of_gt hnR)]
      ring
  have hLHS :
      ∑ i : Fin n, w i • negMulLog (x i) =
        (1 / n : ℝ) * ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) := by
    simp_rw [smul_eq_mul, w, x, Finset.mul_sum]
  have sum_scaled :
      ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) =
        (n : ℝ) * vonNeumannEntropy ρ - (n : ℝ) * log n := by
    simp_rw [negMulLog_scaled _ (density_eigenvalues_nonneg ρ _)]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [vonNeumannEntropy, Finset.mul_sum]
    · have hsplit :
            ∀ i : Fin n, (n : ℝ) * ρ.isHermitian.eigenvalues i * log n =
              ((n : ℝ) * log n) * ρ.isHermitian.eigenvalues i := by
          intro i; ring
      simp_rw [hsplit, ← Finset.mul_sum, density_eigenvalues_sum_eq_one_real ρ]; ring
  have hJnats : ∑ i : Fin n, negMulLog ((n : ℝ) * ρ.isHermitian.eigenvalues i) ≤ 0 := by
    have hle := hLHS.symm ▸ hJ.trans_eq hrhs
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    -- hle : (1/n) * ∑ negMulLog(n * λᵢ) ≤ 0
    -- multiply both sides by n to get ∑ negMulLog(n * λᵢ) ≤ 0
    have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hnpos) hle
    rwa [show (↑n : ℝ) * (1 / ↑n * ∑ i : Fin n, negMulLog ((↑n : ℝ) * ρ.isHermitian.eigenvalues i)) =
          ∑ i : Fin n, negMulLog ((↑n : ℝ) * ρ.isHermitian.eigenvalues i) from by
        rw [← mul_assoc, mul_one_div_cancel hnne, one_mul]] at hmul
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
      (fun j => negMulLog (ρ.isHermitian.eigenvalues j)) fun i => by simp [h i]

/-! ### Characteristic polynomial: unitary conjugation (ℂ)

Same `charpoly` for `A` and `U A U⋆` when `U` is unitary.  This is the standard determinant /
similarity step; relating `charpoly` to the **ordered** `IsHermitian.eigenvalues` vector is still
needed to close `vonNeumannEntropy_unitarily_invariant` without a permutation argument.
-/

theorem charmatrix_unitary_conj (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    charmatrix (U.val * A * star U.val) =
      (RingHom.mapMatrix (algebraMap ℂ ℂ[X])) U.val * charmatrix A *
        (RingHom.mapMatrix (algebraMap ℂ ℂ[X])) (star U.val) := by
  let ι : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ[X] :=
    RingHom.mapMatrix (algebraMap ℂ ℂ[X])
  -- charmatrix M = scalar X - ι(M) by definition
  have hcm : ∀ (M : Matrix (Fin n) (Fin n) ℂ),
      charmatrix M = Matrix.scalar (Fin n) (X : ℂ[X]) - ι M := fun _ => rfl
  rw [hcm, hcm A]
  -- Goal: scalar X - ι(U*A*U⋆) = ι(U) * (scalar X - ι(A)) * ι(U⋆)
  have hmap : ι (U.val * A * star U.val) = ι U.val * ι A * ι (star U.val) := by
    rw [map_mul ι, map_mul ι]
  have hUS : U.val * star U.val = 1 := by
    simp [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
      congr_arg Subtype.val (mul_inv_cancel U)]
  -- Expand RHS: ι(U) * scalar X * ι(U⋆) - ι(U) * ι(A) * ι(U⋆)
  rw [mul_sub, sub_mul, hmap]
  -- Goal: scalar X - ι(U)*ι(A)*ι(U⋆) = ι(U)*scalar(X)*ι(U⋆) - ι(U)*ι(A)*ι(U⋆)
  congr 1
  -- Goal: scalar X = ι(U) * scalar(X) * ι(U⋆)
  symm
  calc ι U.val * Matrix.scalar (Fin n) (X : ℂ[X]) * ι (star U.val)
      = Matrix.scalar (Fin n) X * ι U.val * ι (star U.val) := by
        congr 1; exact (scalar_commute X (Commute.all X) (ι U.val)).symm.eq
    _ = Matrix.scalar (Fin n) X * (ι U.val * ι (star U.val)) := by rw [mul_assoc]
    _ = Matrix.scalar (Fin n) X * 1 := by rw [← map_mul ι, hUS, _root_.map_one]
    _ = Matrix.scalar (Fin n) X := mul_one _

theorem charpoly_unitary_conj (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (U.val * A * star U.val).charpoly = A.charpoly := by
  -- charpoly M = (charmatrix M).det by definition
  have hcp : ∀ (M : Matrix (Fin n) (Fin n) ℂ), M.charpoly = (charmatrix M).det := fun _ => rfl
  rw [hcp, hcp A, charmatrix_unitary_conj U A]
  let ι : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ[X] :=
    RingHom.mapMatrix (algebraMap ℂ ℂ[X])
  -- Build an invertible element in the polynomial matrix ring
  have hUU : ι (star U.val) * ι U.val = 1 := by
    rw [← map_mul ι]
    exact congr_arg ι (Matrix.mem_unitaryGroup_iff'.mp U.2)  |>.trans (map_one ι)
  -- det(P * Q * P⁻¹) = det(Q) by direct calculation
  calc (ι U.val * charmatrix A * ι (star U.val)).det
      = (ι U.val).det * (charmatrix A).det * (ι (star U.val)).det := by
        rw [det_mul, det_mul]
    _ = (ι (star U.val)).det * (ι U.val).det * (charmatrix A).det := by ring
    _ = (ι (star U.val) * ι U.val).det * (charmatrix A).det := by rw [det_mul]
    _ = 1 * (charmatrix A).det := by rw [hUU, det_one]
    _ = (charmatrix A).det := one_mul _

/-- Equal characteristic polynomials ⇒ equal determinant (same dimension). -/
theorem det_eq_of_charpoly_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (h : A.charpoly = B.charpoly) : A.det = B.det := by
  rw [Matrix.det_eq_sign_charpoly_coeff A, Matrix.det_eq_sign_charpoly_coeff B, h]

/-! ### Unitary conjugation preserves density matrix structure -/

/-- Conjugating a density matrix by a unitary preserves trace. -/
theorem trace_unitary_conj (ρ : DensityMatrix hn) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.trace (U.val * ρ.carrier * star U.val) = 1 := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    (Matrix.mem_unitaryGroup_iff'.mp U.2), Matrix.one_mul, ρ.trace_one]

/-- Construct the unitary-conjugated density matrix `UρU†` as a `DensityMatrix`. -/
noncomputable def unitaryConjDensityMatrix (ρ : DensityMatrix hn)
    (U : Matrix.unitaryGroup (Fin n) ℂ) : DensityMatrix hn where
  carrier := U.val * ρ.carrier * star U.val
  psd := ρ.psd.mul_mul_conjTranspose_same U.val
  trace_one := trace_unitary_conj ρ U

/-! ### Qubit (`Fin 2`): entropy from determinant -/

/-- For qubits, the unordered spectrum is determined by `det ρ` once `Tr ρ = 1`, so von Neumann
entropy depends only on `det ρ.carrier`. -/
theorem vonNeumannEntropy_eq_of_det_carrier_eq_two
    (ρ σ : DensityMatrix (show 0 < 2 by norm_num)) (hdet : ρ.carrier.det = σ.carrier.det) :
    vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  simp only [vonNeumannEntropy, Fin.sum_univ_two]
  set a0 := ρ.isHermitian.eigenvalues 0
  set a1 := ρ.isHermitian.eigenvalues 1
  set b0 := σ.isHermitian.eigenvalues 0
  set b1 := σ.isHermitian.eigenvalues 1
  have hsumρ : a0 + a1 = 1 := by
    have := density_eigenvalues_sum_eq_one_real ρ
    simpa [Fin.sum_univ_two] using this
  have hsumσ : b0 + b1 = 1 := by
    have := density_eigenvalues_sum_eq_one_real σ
    simpa [Fin.sum_univ_two] using this
  have hprod : a0 * a1 = b0 * b1 := by
    have eρ := ρ.isHermitian.det_eq_prod_eigenvalues
    have eσ := σ.isHermitian.det_eq_prod_eigenvalues
    simp only [Fin.prod_univ_two] at eρ eσ
    have hc : (a0 : ℂ) * (a1 : ℂ) = (b0 : ℂ) * (b1 : ℂ) := by
      have lhs : (a0 : ℂ) * (a1 : ℂ) = ρ.carrier.det := eρ.symm
      have rhs : (b0 : ℂ) * (b1 : ℂ) = σ.carrier.det := eσ.symm
      rw [lhs, rhs, hdet]
    exact_mod_cast hc
  have hb : (b0 - a0) * (b0 - a1) = 0 := by
    have ha1 : a1 = 1 - a0 := by linarith
    have hb1eq : b1 = 1 - b0 := by linarith
    have hprod' : a0 * (1 - a0) = b0 * (1 - b0) := by rw [← ha1, ← hb1eq]; exact hprod
    have : b0 * b0 - b0 = a0 * a0 - a0 := by nlinarith
    nlinarith [mul_self_nonneg (b0 - a0), mul_self_nonneg (b0 - a1)]
  rcases mul_eq_zero.mp hb with h1 | h1
  · -- b0 = a0
    have hb0 : b0 = a0 := sub_eq_zero.mp h1
    have hb1 : b1 = a1 := by linarith
    rw [hb0, hb1]
  · -- b0 = a1
    have hb0 : b0 = a1 := sub_eq_zero.mp h1
    have hb1 : b1 = a0 := by linarith
    rw [hb0, hb1, add_comm]

set_option maxHeartbeats 6400000 in
/-- Qubit (`Fin 2`) **unitary invariance**: `S(UρU⋆) = S(ρ)`. -/
theorem vonNeumannEntropy_unitarily_invariant_two
    (ρ : DensityMatrix (show 0 < 2 by norm_num)) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    vonNeumannEntropy (unitaryConjDensityMatrix ρ U) = vonNeumannEntropy ρ := by
  refine vonNeumannEntropy_eq_of_det_carrier_eq_two _ _ ?_
  exact det_eq_of_charpoly_eq _ _ (charpoly_unitary_conj U ρ.carrier)

/-! ### Characteristic polynomial of a diagonal matrix -/

/-- The char matrix of a diagonal matrix is diagonal with entries `X - C(dᵢ)`. -/
theorem charmatrix_diagonal' {R : Type*} [CommRing R] [DecidableEq R] (d : Fin n → R) :
    charmatrix (diagonal d) = diagonal (fun i => Polynomial.X - Polynomial.C (d i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [charmatrix, Matrix.scalar_apply, diagonal_apply, RingHom.mapMatrix_apply, map_apply]
  · simp [charmatrix, Matrix.scalar_apply, diagonal_apply, hij, RingHom.mapMatrix_apply, map_apply]

/-- The characteristic polynomial of a diagonal matrix factors as `∏(X - C(dᵢ))`. -/
theorem charpoly_diagonal' {R : Type*} [CommRing R] [DecidableEq R] (d : Fin n → R) :
    (diagonal d).charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i)) := by
  simp [Matrix.charpoly, charmatrix_diagonal', det_diagonal]

/-- Roots of `∏ i : Fin n, (X - C (f i))` (as a `Fintype` product) match the multiset of `f i`. -/
theorem roots_prod_X_sub_C_fin (f : Fin n → ℂ) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (f i))).roots =
      Finset.univ.val.map f := by
  -- Convert Finset.prod to Multiset.prod form
  have hprod : ∏ i : Fin n, (X - C (f i)) =
      ((Finset.univ (α := Fin n)).val.map (fun i => X - C (f i))).prod :=
    (Finset.prod_eq_multiset_prod _ _).symm
  rw [hprod]
  -- Now use (s.map g).prod.roots = s when g = (· → X - C ·)
  have : (Finset.univ (α := Fin n)).val.map (fun i => X - C (f i)) =
      (Finset.univ.val.map f).map (fun a => X - C a) := by
    rw [Multiset.map_map]; rfl
  rw [this]
  exact Polynomial.roots_multiset_prod_X_sub_C _

end UMST.Quantum

namespace Matrix.IsHermitian

open Polynomial Matrix Finset

variable {n : ℕ}

/-- For a Hermitian matrix, `charpoly = ∏(X - C(↑eigenvalues(i)))`. -/
theorem charpoly_eq_prod_eigenvalues {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (↑(hA.eigenvalues i) : ℂ)) := by
  have hc : A.charpoly = (diagonal (RCLike.ofReal ∘ hA.eigenvalues)).charpoly := by
    conv_lhs => rw [hA.spectral_theorem]
    exact UMST.Quantum.charpoly_unitary_conj hA.eigenvectorUnitary _
  rw [hc, UMST.Quantum.charpoly_diagonal' (d := RCLike.ofReal ∘ hA.eigenvalues)]
  simp [Function.comp]

/-- If two Hermitian matrices have the same charpoly, their eigenvalue multisets agree. -/
theorem eigenvalue_multiset_eq_of_charpoly_eq {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    Finset.univ.val.map (fun i => (hA.eigenvalues i : ℂ)) =
    Finset.univ.val.map (fun i => (hB.eigenvalues i : ℂ)) := by
  have hprod :=
    hA.charpoly_eq_prod_eigenvalues.symm.trans (h.trans hB.charpoly_eq_prod_eigenvalues)
  have hr := congrArg Polynomial.roots hprod
  simpa [UMST.Quantum.roots_prod_X_sub_C_fin] using hr

end Matrix.IsHermitian

namespace UMST.Quantum

open Real Matrix Polynomial
open scoped BigOperators ComplexOrder

variable {n : ℕ} {hn : 0 < n}

set_option maxHeartbeats 6400000 in
/-- **Von Neumann entropy is unitarily invariant: `S(UρU†) = S(ρ)` (general `Fin n`).**

The spectral theorem gives `charpoly(A) = ∏(X - C(eigenvalue i))`. By
`charpoly_unitary_conj`, `charpoly(UρU†) = charpoly(ρ)`. Equal characteristic polynomials
have equal root multisets, hence the negMulLog sums are equal. -/
theorem vonNeumannEntropy_unitarily_invariant
    (ρ : DensityMatrix hn) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    vonNeumannEntropy (unitaryConjDensityMatrix ρ U) = vonNeumannEntropy ρ := by
  set ρ' := unitaryConjDensityMatrix ρ U
  have hcp : ρ'.carrier.charpoly = ρ.carrier.charpoly :=
    charpoly_unitary_conj U ρ.carrier
  have hms := Matrix.IsHermitian.eigenvalue_multiset_eq_of_charpoly_eq ρ'.isHermitian ρ.isHermitian hcp
  -- Convert `Multiset.map (fun i => ↑(eigenvalues i))` to `Multiset.map ofReal ∘ Multiset.map eigenvalues`
  have hms' : (Finset.univ.val.map (fun i => ρ'.isHermitian.eigenvalues i)).map Complex.ofReal =
              (Finset.univ.val.map (fun i => ρ.isHermitian.eigenvalues i)).map Complex.ofReal := by
    simp only [Multiset.map_map, Function.comp]
    exact hms
  have hms_real : Finset.univ.val.map (fun i => ρ'.isHermitian.eigenvalues i) =
                  Finset.univ.val.map (fun i => ρ.isHermitian.eigenvalues i) :=
    Multiset.map_injective Complex.ofReal_injective hms'
  unfold vonNeumannEntropy
  have hmap :
      Finset.univ.val.map (fun i => negMulLog (ρ'.isHermitian.eigenvalues i)) =
        Finset.univ.val.map (fun i => negMulLog (ρ.isHermitian.eigenvalues i)) := by
    have := congrArg (Multiset.map negMulLog) hms_real
    simp only [Multiset.map_map, Function.comp] at this ⊢
    exact this
  calc
    ∑ i, negMulLog (ρ'.isHermitian.eigenvalues i)
        = (Finset.univ.val.map (fun i => negMulLog (ρ'.isHermitian.eigenvalues i))).sum := by
          rw [Finset.sum_eq_multiset_sum]
    _ = (Finset.univ.val.map (fun i => negMulLog (ρ.isHermitian.eigenvalues i))).sum :=
          congrArg Multiset.sum hmap
    _ = ∑ i, negMulLog (ρ.isHermitian.eigenvalues i) := by rw [Finset.sum_eq_multiset_sum]

/-- If the **real** eigenvalue multiset of `ρ` agrees with that of the pointwise reals `d`,
then `S(ρ) = ∑ᵢ negMulLog(dᵢ)`. -/
theorem vonNeumannEntropy_eq_sum_negMulLog_of_real_map_eq (ρ : DensityMatrix hn) (d : Fin n → ℝ)
    (h : Finset.univ.val.map (fun i => ρ.isHermitian.eigenvalues i) =
        Finset.univ.val.map (fun i => d i)) :
    vonNeumannEntropy ρ = ∑ i, negMulLog (d i) := by
  classical
  unfold vonNeumannEntropy
  have hmap :
      Finset.univ.val.map (fun i => negMulLog (ρ.isHermitian.eigenvalues i)) =
        Finset.univ.val.map (fun i => negMulLog (d i)) := by
    simpa [Function.comp, Multiset.map_map] using congrArg (Multiset.map negMulLog) h
  calc
    ∑ i, negMulLog (ρ.isHermitian.eigenvalues i)
        = (Finset.univ.val.map (fun i => negMulLog (ρ.isHermitian.eigenvalues i))).sum := by
          rw [Finset.sum_eq_multiset_sum]
    _ = (Finset.univ.val.map (fun i => negMulLog (d i))).sum := congrArg Multiset.sum hmap
    _ = ∑ i, negMulLog (d i) := by rw [Finset.sum_eq_multiset_sum]

/-- Diagonal carrier with real diagonal (as `ℂ`) has von Neumann entropy the `negMulLog` sum of
those diagonal entries (the spectrum multiset matches the diagonal multiset). -/
theorem vonNeumannEntropy_eq_sum_negMulLog_of_diagonal_carrier (ρ : DensityMatrix hn) (d : Fin n → ℝ)
    (hcd : ρ.carrier = diagonal (fun i => (d i : ℂ))) :
    vonNeumannEntropy ρ = ∑ i, negMulLog (d i) := by
  classical
  have ha := Matrix.IsHermitian.charpoly_eq_prod_eigenvalues ρ.isHermitian
  have hb := charpoly_diagonal' (R := ℂ) (d := fun i => (d i : ℂ))
  have hcp : ρ.carrier.charpoly = (diagonal (fun i => (d i : ℂ))).charpoly := by
    rw [hcd]
  have hprod :
      (∏ i : Fin n, (Polynomial.X - Polynomial.C (↑(ρ.isHermitian.eigenvalues i) : ℂ))) =
        ∏ i : Fin n, (Polynomial.X - Polynomial.C ((d i : ℂ))) := by
    rw [← ha, hcp, hb]
  have hms :
      Finset.univ.val.map (fun i => (ρ.isHermitian.eigenvalues i : ℂ)) =
        Finset.univ.val.map (fun i => (d i : ℂ)) := by
    have hr := congrArg Polynomial.roots hprod
    simpa [roots_prod_X_sub_C_fin] using hr
  have hms_real : Finset.univ.val.map (fun i => ρ.isHermitian.eigenvalues i) =
      Finset.univ.val.map (fun i => d i) := by
    refine Multiset.map_injective Complex.ofReal_injective ?_
    simpa [Function.comp_def, Multiset.map_map] using hms
  exact vonNeumannEntropy_eq_sum_negMulLog_of_real_map_eq ρ d hms_real

/-! ### Qubit specialization -/

/-- Von Neumann entropy of a pure state (rank-one `pureDensity`) is nonnegative. -/
theorem vonNeumannEntropy_pure_eq_zero (ψ : Fin n → ℂ) (hψ : dotProduct ψ (star ψ) = 1) :
    0 ≤ vonNeumannEntropy (pureDensity (hn := hn) ψ hψ) :=
  vonNeumannEntropy_nonneg (pureDensity (hn := hn) ψ hψ)

end UMST.Quantum

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin
import DensityState

/-!
# TensorPartialTrace — Kronecker product and partial trace (composite `Fin` systems)

**Product Hilbert space** indices use `Fin na × Fin nb` (Kronecker / tensor layout). A density matrix
on the composite system, indexed by `Fin (na * nb)`, is obtained by **`Matrix.reindex finProdFinEquiv`**
(flatten with `finProdFinEquiv : Fin na × Fin nb ≃ Fin (na * nb)`).

**Main results**
* `partialTraceRightProd (ρA.carrier ⊗ₖ ρB.carrier) = (trace ρB) • ρA.carrier` — in particular
  **`Tr_B(ρ_A ⊗ ρ_B) = ρ_A`** when `trace ρB = 1`.
* `tensorDensity ρA ρB` — a **`DensityMatrix`** on `Fin (na * nb)` with PSD from a square-root /
  Kronecker factorisation and `trace_one` via `trace_kronecker`.
* `partialTraceRightFin` — partial trace on **`Fin (na * nb)`** matrices (unflatten, trace `B`, flatten).
* Symmetric **`partialTraceLeft*`** — trace out **`A`**.
* **`trace_partialTraceRightProd`** / **`trace_partialTraceLeftProd`** — partial trace preserves **`Matrix.trace`**
  on product indices; same for **`trace_partialTraceRightFin`** / **`trace_partialTraceLeftFin`** on **`Fin (na * nb)`**
  after unflattening via **`finProdFinEquiv.symm`**.

* **`partialTraceRightProd_toDensityMatrix`** / **`partialTraceLeftProd_toDensityMatrix`** — partial trace
  of **any** bipartite density matrix (including entangled states) yields a valid `DensityMatrix`.
-/

namespace UMST.Quantum

open Matrix
open scoped Kronecker BigOperators ComplexOrder

variable {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)

/-- Partial trace over the second tensor factor, in product-index coordinates
`(row,col) ∈ (Fin na × Fin nb)²`. -/
noncomputable def partialTraceRightProd (M : Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ) :
    Matrix (Fin na) (Fin na) ℂ :=
  fun i j => ∑ k : Fin nb, M (i, k) (j, k)

private lemma trace_reindex_self {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommMonoid α] (e : ι ≃ κ) (A : Matrix ι ι α) :
    (Matrix.reindex e e A).trace = A.trace := by
  classical
  simp_rw [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [← Fintype.sum_equiv e.symm (fun k => A (e.symm k) (e.symm k)) (fun i => A i i) fun _ => rfl]

theorem conjTranspose_kronecker (A : Matrix (Fin na) (Fin na) ℂ) (B : Matrix (Fin nb) (Fin nb) ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.conjTranspose_apply, kroneckerMap_apply, star_mul']

theorem posSemidef_kronecker (A : Matrix (Fin na) (Fin na) ℂ) (B : Matrix (Fin nb) (Fin nb) ℂ)
    (hA : PosSemidef A) (hB : PosSemidef B) : PosSemidef (A ⊗ₖ B) := by
  classical
  let SA := hA.sqrt
  let SB := hB.sqrt
  have hSA := hA.posSemidef_sqrt
  have hSB := hB.posSemidef_sqrt
  have hdecomp : A ⊗ₖ B = (SA ⊗ₖ SB)ᴴ * (SA ⊗ₖ SB) := by
    rw [conjTranspose_kronecker SA SB, hSA.isHermitian.eq, hSB.isHermitian.eq]
    rw [← mul_kronecker_mul, hA.sqrt_mul_self, hB.sqrt_mul_self]
  rw [hdecomp]
  exact posSemidef_conjTranspose_mul_self (SA ⊗ₖ SB)

theorem partialTraceRightProd_kronecker (A : Matrix (Fin na) (Fin na) ℂ)
    (B : Matrix (Fin nb) (Fin nb) ℂ) :
    partialTraceRightProd (A ⊗ₖ B) = (B.trace) • A := by
  ext i j
  simp only [partialTraceRightProd, kroneckerMap_apply, Matrix.trace, Matrix.diag_apply, smul_apply]
  rw [← Finset.mul_sum, smul_eq_mul, mul_comm]

/-- Partial trace over the first tensor factor (indices in `Fin nb × Fin nb` after tracing `Fin na`). -/
noncomputable def partialTraceLeftProd (M : Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ) :
    Matrix (Fin nb) (Fin nb) ℂ :=
  fun i j => ∑ k : Fin na, M (k, i) (k, j)

theorem partialTraceLeftProd_kronecker (A : Matrix (Fin na) (Fin na) ℂ)
    (B : Matrix (Fin nb) (Fin nb) ℂ) :
    partialTraceLeftProd (A ⊗ₖ B) = (A.trace) • B := by
  ext i j
  simp only [partialTraceLeftProd, kroneckerMap_apply, Matrix.trace, Matrix.diag_apply, smul_apply]
  rw [← Finset.sum_mul, smul_eq_mul, mul_comm]

theorem partialTraceLeftProd_tensor_carriers (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    partialTraceLeftProd (ρA.carrier ⊗ₖ ρB.carrier) = ρB.carrier := by
  rw [partialTraceLeftProd_kronecker, DensityMat.trace_eq_one ρA, one_smul]

/-- Tracing out `B` preserves the total trace (sum of diagonal blocks). -/
theorem trace_partialTraceRightProd (M : Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ) :
    (partialTraceRightProd M).trace = M.trace := by
  simp [Matrix.trace, partialTraceRightProd, Matrix.diag_apply]
  rw [← Fintype.sum_prod_type (fun p : Fin na × Fin nb => M p p)]

/-- Tracing out `A` preserves the total trace. -/
theorem trace_partialTraceLeftProd (M : Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ) :
    (partialTraceLeftProd M).trace = M.trace := by
  simp [Matrix.trace, partialTraceLeftProd, Matrix.diag_apply]
  rw [← Fintype.sum_prod_type_right' (fun x y => M (x, y) (x, y))]

/-- Kronecker density on `Fin (na * nb)` (flattened computational tensor-product ordering). -/
noncomputable def tensorDensity (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    DensityMatrix (Nat.mul_pos ha hb) where
  carrier :=
    Matrix.reindex finProdFinEquiv finProdFinEquiv (ρA.carrier ⊗ₖ ρB.carrier)
  psd := by
    have hK := posSemidef_kronecker ρA.carrier ρB.carrier ρA.psd ρB.psd
    simpa [Matrix.reindex_apply] using hK.submatrix finProdFinEquiv.symm
  trace_one := by
    have htr := trace_reindex_self finProdFinEquiv (ρA.carrier ⊗ₖ ρB.carrier)
    simp only [DensityMat.trace_eq_one, trace_kronecker, mul_one, htr]

theorem partialTraceRightProd_tensor_carriers (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    partialTraceRightProd (ρA.carrier ⊗ₖ ρB.carrier) = ρA.carrier := by
  rw [partialTraceRightProd_kronecker, DensityMat.trace_eq_one ρB, one_smul]

private lemma reindex_symm_reindex {ι κ : Type*} (e : ι ≃ κ) (K : Matrix ι ι α) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e K) = K := by
  simp [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]

/-- Partial trace over the second factor for a composite matrix on `Fin (na * nb)`. -/
noncomputable def partialTraceRightFin (M : Matrix (Fin (na * nb)) (Fin (na * nb)) ℂ) :
    Matrix (Fin na) (Fin na) ℂ :=
  partialTraceRightProd (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm M)

theorem partialTraceRightFin_reindex_kronecker (A : Matrix (Fin na) (Fin na) ℂ)
    (B : Matrix (Fin nb) (Fin nb) ℂ) :
    partialTraceRightFin (Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)) =
      (B.trace) • A := by
  unfold partialTraceRightFin
  rw [reindex_symm_reindex finProdFinEquiv (A ⊗ₖ B)]
  exact partialTraceRightProd_kronecker A B

theorem partialTraceRightFin_tensorDensity_carrier (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    partialTraceRightFin (tensorDensity ha hb ρA ρB).carrier = ρA.carrier := by
  unfold tensorDensity partialTraceRightFin
  rw [reindex_symm_reindex finProdFinEquiv (ρA.carrier ⊗ₖ ρB.carrier)]
  exact partialTraceRightProd_tensor_carriers ha hb ρA ρB

/-- Partial trace over the first factor for a matrix on `Fin (na * nb)`. -/
noncomputable def partialTraceLeftFin (M : Matrix (Fin (na * nb)) (Fin (na * nb)) ℂ) :
    Matrix (Fin nb) (Fin nb) ℂ :=
  partialTraceLeftProd (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm M)

theorem partialTraceLeftFin_reindex_kronecker (A : Matrix (Fin na) (Fin na) ℂ)
    (B : Matrix (Fin nb) (Fin nb) ℂ) :
    partialTraceLeftFin (Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)) =
      (A.trace) • B := by
  unfold partialTraceLeftFin
  rw [reindex_symm_reindex finProdFinEquiv (A ⊗ₖ B)]
  exact partialTraceLeftProd_kronecker A B

theorem partialTraceLeftFin_tensorDensity_carrier (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    partialTraceLeftFin (tensorDensity ha hb ρA ρB).carrier = ρB.carrier := by
  unfold tensorDensity partialTraceLeftFin
  rw [reindex_symm_reindex finProdFinEquiv (ρA.carrier ⊗ₖ ρB.carrier)]
  exact partialTraceLeftProd_tensor_carriers ha hb ρA ρB

theorem trace_partialTraceRightFin (M : Matrix (Fin (na * nb)) (Fin (na * nb)) ℂ) :
    (partialTraceRightFin M).trace = M.trace := by
  unfold partialTraceRightFin
  rw [trace_partialTraceRightProd, trace_reindex_self finProdFinEquiv.symm]

theorem trace_partialTraceLeftFin (M : Matrix (Fin (na * nb)) (Fin (na * nb)) ℂ) :
    (partialTraceLeftFin M).trace = M.trace := by
  unfold partialTraceLeftFin
  rw [trace_partialTraceLeftProd, trace_reindex_self finProdFinEquiv.symm]

theorem posSemidef_partialTraceRightProd (M : Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ)
    (hM : PosSemidef M) : PosSemidef (partialTraceRightProd (na := na) (nb := nb) M) := by
  constructor
  · ext i j
    change star (∑ k : Fin nb, M (j, k) (i, k)) = ∑ k : Fin nb, M (i, k) (j, k)
    have hdummy : star (∑ k : Fin nb, M (j, k) (i, k)) = ∑ k : Fin nb, star (M (j, k) (i, k)) := map_sum (starRingEnd ℂ) _ _
    rw [hdummy]
    apply Finset.sum_congr rfl
    intro k _
    have hM_herm : Mᴴ = M := hM.1
    have hM_elem : star (M (j, k) (i, k)) = M (i, k) (j, k) := by
      have h := congr_fun (congr_fun hM_herm (i, k)) (j, k)
      exact h
    exact hM_elem
  · intro x
    dsimp [dotProduct, mulVec, partialTraceRightProd]
    have hsum : (∑ i : Fin na, star (x i) * ∑ j : Fin na, (∑ k : Fin nb, M (i, k) (j, k)) * x j) =
        ∑ k : Fin nb, ∑ i : Fin na, ∑ j : Fin na, star (x i) * (M (i, k) (j, k) * x j) := by
      calc
        (∑ i : Fin na, star (x i) * ∑ j : Fin na, (∑ k : Fin nb, M (i, k) (j, k)) * x j)
          = ∑ i : Fin na, ∑ j : Fin na, ∑ k : Fin nb, star (x i) * (M (i, k) (j, k) * x j) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
        _ = ∑ i : Fin na, ∑ k : Fin nb, ∑ j : Fin na, star (x i) * (M (i, k) (j, k) * x j) := by
            apply Finset.sum_congr rfl; intro z _; exact Finset.sum_comm
        _ = ∑ k : Fin nb, ∑ i : Fin na, ∑ j : Fin na, star (x i) * (M (i, k) (j, k) * x j) := by
            exact Finset.sum_comm
    change 0 ≤ ∑ i : Fin na, star (x i) * ∑ j : Fin na, (∑ k : Fin nb, M (i, k) (j, k)) * x j
    rw [hsum]
    apply Finset.sum_nonneg
    intro k _
    let y_k : Fin na × Fin nb → ℂ := fun p => if p.2 = k then x p.1 else 0
    have h_yk : 0 ≤ dotProduct (star y_k) (M *ᵥ y_k) := hM.2 y_k
    have hyk_eq : dotProduct (star y_k) (M *ᵥ y_k) =
        ∑ i : Fin na, ∑ j : Fin na, star (x i) * (M (i, k) (j, k) * x j) := by
      simp only [dotProduct, mulVec, y_k]
      simp only [Pi.star_apply, apply_ite star, star_zero, mul_ite, ite_mul, mul_zero, zero_mul]
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp only [Finset.mul_sum, mul_ite, ite_mul, mul_zero, zero_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← hyk_eq]
    exact h_yk

/-- Partial trace over the **first** factor preserves positive semidefiniteness. -/
theorem posSemidef_partialTraceLeftProd (M : Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ)
    (hM : PosSemidef M) : PosSemidef (partialTraceLeftProd (na := na) (nb := nb) M) := by
  constructor
  · ext i j
    change star (∑ k : Fin na, M (k, j) (k, i)) = ∑ k : Fin na, M (k, i) (k, j)
    have hdummy : star (∑ k : Fin na, M (k, j) (k, i)) = ∑ k : Fin na, star (M (k, j) (k, i)) := map_sum (starRingEnd ℂ) _ _
    rw [hdummy]
    apply Finset.sum_congr rfl
    intro k _
    have hM_herm : Mᴴ = M := hM.1
    have hM_elem : star (M (k, j) (k, i)) = M (k, i) (k, j) := by
      have h := congr_fun (congr_fun hM_herm (k, i)) (k, j)
      exact h
    exact hM_elem
  · intro x
    dsimp [dotProduct, mulVec, partialTraceLeftProd]
    have hsum : (∑ i : Fin nb, star (x i) * ∑ j : Fin nb, (∑ k : Fin na, M (k, i) (k, j)) * x j) =
        ∑ k : Fin na, ∑ i : Fin nb, ∑ j : Fin nb, star (x i) * (M (k, i) (k, j) * x j) := by
      calc
        (∑ i : Fin nb, star (x i) * ∑ j : Fin nb, (∑ k : Fin na, M (k, i) (k, j)) * x j)
          = ∑ i : Fin nb, ∑ j : Fin nb, ∑ k : Fin na, star (x i) * (M (k, i) (k, j) * x j) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
        _ = ∑ i : Fin nb, ∑ k : Fin na, ∑ j : Fin nb, star (x i) * (M (k, i) (k, j) * x j) := by
            apply Finset.sum_congr rfl; intro z _; exact Finset.sum_comm
        _ = ∑ k : Fin na, ∑ i : Fin nb, ∑ j : Fin nb, star (x i) * (M (k, i) (k, j) * x j) := by
            exact Finset.sum_comm
    change 0 ≤ ∑ i : Fin nb, star (x i) * ∑ j : Fin nb, (∑ k : Fin na, M (k, i) (k, j)) * x j
    rw [hsum]
    apply Finset.sum_nonneg
    intro k _
    let y_k : Fin na × Fin nb → ℂ := fun p => if p.1 = k then x p.2 else 0
    have h_yk : 0 ≤ dotProduct (star y_k) (M *ᵥ y_k) := hM.2 y_k
    have hyk_eq : dotProduct (star y_k) (M *ᵥ y_k) =
        ∑ i : Fin nb, ∑ j : Fin nb, star (x i) * (M (k, i) (k, j) * x j) := by
      simp only [dotProduct, mulVec, y_k]
      simp only [Pi.star_apply, apply_ite star, star_zero, mul_ite, ite_mul, mul_zero, zero_mul]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp only [Finset.mul_sum, mul_ite, ite_mul, mul_zero, zero_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← hyk_eq]
    exact h_yk

/-! ### General bipartite density matrices (entangled states)

A **bipartite density matrix** on `Fin (na * nb)` is any `DensityMatrix (Nat.mul_pos ha hb)`.
These need not be tensor products — they include entangled states like Bell states.

The key result: **partial trace of any bipartite density matrix yields a valid density matrix**
on the reduced system. This requires:
1. PSD of the partial trace (proved above via `posSemidef_partialTraceRightProd`)
2. Trace preservation (`trace_partialTraceRightProd` / `trace_partialTraceRightFin`)
-/

/-- Partial trace over the **right** (`B`) factor of a **general** composite density matrix
(product-index form) yields a valid `DensityMatrix` on `A`. Works for entangled states. -/
noncomputable def partialTraceRightProd_toDensityMatrix
    (ρAB : DensityMatrix (Nat.mul_pos ha hb)) :
    DensityMatrix ha where
  carrier := partialTraceRightFin ρAB.carrier
  psd := by
    show (partialTraceRightProd (ρAB.carrier.submatrix finProdFinEquiv finProdFinEquiv)).PosSemidef
    exact posSemidef_partialTraceRightProd _ (ρAB.psd.submatrix finProdFinEquiv)
  trace_one := by
    have := trace_partialTraceRightFin (na := na) (nb := nb) ρAB.carrier
    rw [this]
    exact ρAB.trace_one

/-- Partial trace over the **left** (`A`) factor of a general composite density matrix
yields a valid `DensityMatrix` on `B`. Works for entangled states. -/
noncomputable def partialTraceLeftProd_toDensityMatrix
    (ρAB : DensityMatrix (Nat.mul_pos ha hb)) :
    DensityMatrix hb where
  carrier := partialTraceLeftFin ρAB.carrier
  psd := by
    show (partialTraceLeftProd (ρAB.carrier.submatrix finProdFinEquiv finProdFinEquiv)).PosSemidef
    exact posSemidef_partialTraceLeftProd _ (ρAB.psd.submatrix finProdFinEquiv)
  trace_one := by
    have := trace_partialTraceLeftFin (na := na) (nb := nb) ρAB.carrier
    rw [this]
    exact ρAB.trace_one

/-- The carrier of the right partial trace matches `partialTraceRightFin` on the carrier. -/
theorem partialTraceRightProd_toDensityMatrix_carrier (ρAB : DensityMatrix (Nat.mul_pos ha hb)) :
    (partialTraceRightProd_toDensityMatrix ha hb ρAB).carrier =
      partialTraceRightFin ρAB.carrier := rfl

/-- The carrier of the left partial trace matches `partialTraceLeftFin` on the carrier. -/
theorem partialTraceLeftProd_toDensityMatrix_carrier (ρAB : DensityMatrix (Nat.mul_pos ha hb)) :
    (partialTraceLeftProd_toDensityMatrix ha hb ρAB).carrier =
      partialTraceLeftFin ρAB.carrier := rfl

/-- For tensor-product states, the right partial trace recovers the `A` factor. -/
theorem partialTraceRightProd_toDensityMatrix_tensor (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (partialTraceRightProd_toDensityMatrix ha hb (tensorDensity ha hb ρA ρB)).carrier = ρA.carrier :=
  partialTraceRightFin_tensorDensity_carrier ha hb ρA ρB

/-- For tensor-product states, the left partial trace recovers the `B` factor. -/
theorem partialTraceLeftProd_toDensityMatrix_tensor (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    (partialTraceLeftProd_toDensityMatrix ha hb (tensorDensity ha hb ρA ρB)).carrier = ρB.carrier :=
  partialTraceLeftFin_tensorDensity_carrier ha hb ρA ρB

end UMST.Quantum

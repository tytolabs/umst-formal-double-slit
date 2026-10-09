-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import VonNeumannEntropy
import TensorPartialTrace
import KroneckerEigen
import KleinInequality

/-!
# QuantumMutualInfo — bipartite quantum mutual information and conditional entropy

Quantum mutual information of a bipartite density matrix `ρ_AB` on `Fin (na * nb)`:

  `I(A:B) = S(ρ_A) + S(ρ_B) - S(ρ_AB)`

where `S` is the von Neumann entropy and `ρ_A`, `ρ_B` are the reduced states obtained by
partial trace.

**Key results:**
- `quantumMutualInfo` — definition via partial traces and `vonNeumannEntropy`
- `quantumConditionalEntropy` — `S(A|B) = S(ρ_AB) - S(ρ_B)`
- `quantumMutualInfo_eq_entropy_minus_conditional` — `I(A:B) = S(ρ_A) - S(A|B)` (pure algebra)
- `quantumConditionalEntropy_B_given_A` — `S(B|A) = S(ρ_AB) - S(ρ_A)`, with `I(A:B) = S(ρ_B) - S(B|A)`
  (`quantumMutualInfo_eq_entropy_minus_conditional_B_given_A`)
- `quantumMutualInfo_le` — `I(A:B) ≤ log na + log nb` (upper bound)
- `vonNeumannEntropy_tensorDensity_eq` — `S(ρ_A ⊗ ρ_B) = S(ρ_A) + S(ρ_B)` (**proved** in
  `KroneckerEigen.lean`, imported here)
- `quantumMutualInfo_product_eq_zero` — product states have zero mutual information
- `sum_negMulLog_le_sum_negMulLog_marginals` — classical subadditivity `H(p) ≤ H(p_A) + H(p_B)`
- `vonNeumannEntropy_le_add_partialTrace` — subadditivity `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`, hence
  `quantumMutualInfo_nonneg` — `I(A:B) ≥ 0`
-/

namespace UMST.Quantum

open _root_.Real Matrix
open scoped Kronecker ComplexOrder BigOperators

variable {na nb : ℕ} (ha : 0 < na) (hb : 0 < nb)

/-- **Quantum mutual information** `I(A:B) = S(ρ_A) + S(ρ_B) - S(ρ_AB)`. -/
noncomputable def quantumMutualInfo
    (ρAB : DensityMatrix (Nat.mul_pos ha hb)) : ℝ :=
  vonNeumannEntropy (partialTraceRightProd_toDensityMatrix ha hb ρAB) +
  vonNeumannEntropy (partialTraceLeftProd_toDensityMatrix ha hb ρAB) -
  vonNeumannEntropy ρAB

/-- **Quantum conditional entropy** `S(A|B) = S(ρ_AB) - S(ρ_B)`. -/
noncomputable def quantumConditionalEntropy
    (ρAB : DensityMatrix (Nat.mul_pos ha hb)) : ℝ :=
  vonNeumannEntropy ρAB -
  vonNeumannEntropy (partialTraceLeftProd_toDensityMatrix ha hb ρAB)

/-- `I(A:B) = S(ρ_A) - S(A|B)` — pure algebraic rearrangement. -/
theorem quantumMutualInfo_eq_entropy_minus_conditional
    (ρAB : DensityMatrix (Nat.mul_pos ha hb)) :
    quantumMutualInfo ha hb ρAB =
    vonNeumannEntropy (partialTraceRightProd_toDensityMatrix ha hb ρAB) -
    quantumConditionalEntropy ha hb ρAB := by
  simp only [quantumMutualInfo, quantumConditionalEntropy]
  ring

/-- **Quantum conditional entropy** of `B` given `A`: `S(B|A) = S(ρ_AB) - S(ρ_A)`. -/
noncomputable def quantumConditionalEntropy_B_given_A
    (ρAB : DensityMatrix (Nat.mul_pos ha hb)) : ℝ :=
  vonNeumannEntropy ρAB -
  vonNeumannEntropy (partialTraceRightProd_toDensityMatrix ha hb ρAB)

/-- `I(A:B) = S(ρ_B) - S(B|A)` — the mutual information is symmetric in which side is conditioned on. -/
theorem quantumMutualInfo_eq_entropy_minus_conditional_B_given_A
    (ρAB : DensityMatrix (Nat.mul_pos ha hb)) :
    quantumMutualInfo ha hb ρAB =
    vonNeumannEntropy (partialTraceLeftProd_toDensityMatrix ha hb ρAB) -
    quantumConditionalEntropy_B_given_A ha hb ρAB := by
  simp only [quantumMutualInfo, quantumConditionalEntropy_B_given_A]
  ring

/-- **Upper bound**: `I(A:B) ≤ log na + log nb`.

Uses `vonNeumannEntropy_le_log_n` on both marginals and `vonNeumannEntropy_nonneg` on the joint. -/
theorem quantumMutualInfo_le
    (ρAB : DensityMatrix (Nat.mul_pos ha hb)) :
    quantumMutualInfo ha hb ρAB ≤ Real.log na + Real.log nb := by
  unfold quantumMutualInfo
  have hA := vonNeumannEntropy_le_log_n (partialTraceRightProd_toDensityMatrix ha hb ρAB)
  have hB := vonNeumannEntropy_le_log_n (partialTraceLeftProd_toDensityMatrix ha hb ρAB)
  have hAB := vonNeumannEntropy_nonneg ρAB
  linarith

/-- Product states have zero quantum mutual information.

Proof: the marginals of `ρ_A ⊗ ρ_B` are `ρ_A` and `ρ_B` (by partial trace), so
`I(A:B) = S(ρ_A) + S(ρ_B) - S(ρ_A ⊗ ρ_B) = S(ρ_A) + S(ρ_B) - (S(ρ_A) + S(ρ_B)) = 0`. -/
theorem quantumMutualInfo_product_eq_zero
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    quantumMutualInfo ha hb (tensorDensity ha hb ρA ρB) = 0 := by
  unfold quantumMutualInfo
  -- The marginals of a product state recover the factors
  have hRA : (partialTraceRightProd_toDensityMatrix ha hb (tensorDensity ha hb ρA ρB)) = ρA :=
    DensityMat.ext (partialTraceRightProd_toDensityMatrix_tensor ha hb ρA ρB)
  have hRB : (partialTraceLeftProd_toDensityMatrix ha hb (tensorDensity ha hb ρA ρB)) = ρB :=
    DensityMat.ext (partialTraceLeftProd_toDensityMatrix_tensor ha hb ρA ρB)
  rw [hRA, hRB, vonNeumannEntropy_tensorDensity_eq ha hb ρA ρB]
  ring

/-- Classical subadditivity of the Shannon entropy (nats): for a joint distribution `p` on `Fin na × Fin nb`,
`H(p) ≤ H(p_A) + H(p_B)` with the marginals `p_A a = ∑_b p (a, b)` and `p_B b = ∑_a p (a, b)`.

Proof: termwise `p (log p_A + log p_B - log p) ≤ p_A p_B - p` (from `log x ≤ x - 1`, and `p ≤ p_A`, `p ≤ p_B`), and
the right side sums to `1 - 1 = 0`. -/
theorem sum_negMulLog_le_sum_negMulLog_marginals (p : Fin na × Fin nb → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) :
    ∑ x, negMulLog (p x) ≤ ∑ a, negMulLog (∑ b, p (a, b)) + ∑ b, negMulLog (∑ a, p (a, b)) := by
  set pA : Fin na → ℝ := fun a => ∑ b, p (a, b) with hpA
  set pB : Fin nb → ℝ := fun b => ∑ a, p (a, b) with hpB
  have hpA_ge (x : Fin na × Fin nb) : p x ≤ pA x.1 :=
    Finset.single_le_sum (f := fun b => p (x.1, b)) (fun b _ => hp _) (Finset.mem_univ x.2)
  have hpB_ge (x : Fin na × Fin nb) : p x ≤ pB x.2 :=
    Finset.single_le_sum (f := fun a => p (a, x.2)) (fun a _ => hp _) (Finset.mem_univ x.1)
  have hterm (x : Fin na × Fin nb) :
      p x * (log (pA x.1) + log (pB x.2) - log (p x)) ≤ pA x.1 * pB x.2 - p x := by
    rcases (hp x).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, sub_zero]
      exact mul_nonneg (le_trans (hp x) (hpA_ge x)) (le_trans (hp x) (hpB_ge x))
    · have hA : 0 < pA x.1 := lt_of_lt_of_le hpos (hpA_ge x)
      have hB : 0 < pB x.2 := lt_of_lt_of_le hpos (hpB_ge x)
      have hq : 0 < pA x.1 * pB x.2 / p x := div_pos (mul_pos hA hB) hpos
      have hlog : log (pA x.1) + log (pB x.2) - log (p x) = log (pA x.1 * pB x.2 / p x) := by
        rw [log_div (mul_pos hA hB).ne' hpos.ne', log_mul hA.ne' hB.ne']
      rw [hlog]
      calc p x * log (pA x.1 * pB x.2 / p x)
          ≤ p x * (pA x.1 * pB x.2 / p x - 1) :=
            mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hq) hpos.le
        _ = pA x.1 * pB x.2 - p x := by field_simp
  have hprod : ∑ x : Fin na × Fin nb, pA x.1 * pB x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    have h1 : ∑ a, pA a = 1 := by rw [← hsum, Fintype.sum_prod_type]
    have h2 : ∑ b, pB b = 1 := by rw [← hsum, Fintype.sum_prod_type_right]
    rw [h1, h2, one_mul]
  have hbound : ∑ x, p x * (log (pA x.1) + log (pB x.2) - log (p x)) ≤ 0 := by
    calc ∑ x, p x * (log (pA x.1) + log (pB x.2) - log (p x))
        ≤ ∑ x, (pA x.1 * pB x.2 - p x) := Finset.sum_le_sum fun x _ => hterm x
      _ = 0 := by rw [Finset.sum_sub_distrib, hprod, hsum, sub_self]
  have hA_eq : ∑ a, pA a * log (pA a) = ∑ x : Fin na × Fin nb, p x * log (pA x.1) := by
    rw [Fintype.sum_prod_type]
    simp_rw [hpA, Finset.sum_mul]
  have hB_eq : ∑ b, pB b * log (pB b) = ∑ x : Fin na × Fin nb, p x * log (pB x.2) := by
    rw [Fintype.sum_prod_type_right]
    simp_rw [hpB, Finset.sum_mul]
  simp only [negMulLog, neg_mul, Finset.sum_neg_distrib]
  have hsplit : ∑ x, p x * (log (pA x.1) + log (pB x.2) - log (p x)) =
      ∑ x : Fin na × Fin nb, p x * log (pA x.1) + ∑ x : Fin na × Fin nb, p x * log (pB x.2) -
        ∑ x, p x * log (p x) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  change -∑ x, p x * log (p x) ≤ -∑ a, pA a * log (pA a) + -∑ b, pB b * log (pB b)
  linarith [hA_eq, hB_eq, hsplit, hbound]

/-- **Subadditivity of the von Neumann entropy**: `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`.

Proof: measure `ρ_AB` in the product eigenbasis `U_A ⊗ U_B` of its marginals. The entropy of the outcome
distribution `p` bounds `S(ρ_AB)` from above (`vonNeumannEntropy_le_sum_negMulLog_diag_unitary_conj`); the
marginals of `p` are the spectra of `ρ_A` and `ρ_B` (`sum_diag_kronecker_conj_right`, `…_left`); classical
subadditivity (`sum_negMulLog_le_sum_negMulLog_marginals`) finishes. -/
theorem vonNeumannEntropy_le_add_partialTrace (ρAB : DensityMatrix (Nat.mul_pos ha hb)) :
    vonNeumannEntropy ρAB ≤
      vonNeumannEntropy (partialTraceRightProd_toDensityMatrix ha hb ρAB) +
        vonNeumannEntropy (partialTraceLeftProd_toDensityMatrix ha hb ρAB) := by
  set ρA := partialTraceRightProd_toDensityMatrix ha hb ρAB
  set ρB := partialTraceLeftProd_toDensityMatrix ha hb ρAB
  set e : Fin na × Fin nb ≃ Fin (na * nb) := finProdFinEquiv
  set UA := (ρA.isHermitian.eigenvectorUnitary : Matrix (Fin na) (Fin na) ℂ)
  set UB := (ρB.isHermitian.eigenvectorUnitary : Matrix (Fin nb) (Fin nb) ℂ)
  set V : Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ := UA ⊗ₖ UB
  set W : Matrix (Fin (na * nb)) (Fin (na * nb)) ℂ := V.submatrix e.symm e.symm
  set M : Matrix (Fin na × Fin nb) (Fin na × Fin nb) ℂ := ρAB.carrier.submatrix e e
  have hUA : UA * UAᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp ρA.isHermitian.eigenvectorUnitary.2
  have hUB : UB * UBᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp ρB.isHermitian.eigenvectorUnitary.2
  have hV : V ∈ Matrix.unitaryGroup (Fin na × Fin nb) ℂ :=
    unitary_kronecker_prod ρA.isHermitian.eigenvectorUnitary ρB.isHermitian.eigenvectorUnitary
  have hW : W ∈ Matrix.unitaryGroup (Fin (na * nb)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv,
      ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hV, submatrix_one_equiv]
  -- the outcome distribution of the product-basis measurement
  set p : Fin na × Fin nb → ℝ := fun x => ((Vᴴ * M * V) x x).re
  have hdiag (x : Fin na × Fin nb) : ((Wᴴ * ρAB.carrier * W) (e x) (e x)).re = p x := by
    simp only [p, conjTranspose_mul_mul_apply_self]
    rw [← Equiv.sum_comp e]
    refine congrArg Complex.re (Finset.sum_congr rfl fun y _ => ?_)
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [W, M]
  have hp (x : Fin na × Fin nb) : 0 ≤ p x := by
    rw [← hdiag x, diag_unitary_conj_re_eq]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Complex.normSq_nonneg _) (density_eigenvalues_nonneg ρAB i)
  have hMA : partialTraceRightProd M = ρA.carrier := rfl
  have hMB : partialTraceLeftProd M = ρB.carrier := rfl
  have hmargA (a : Fin na) : ∑ b, p (a, b) = ρA.isHermitian.eigenvalues a := by
    simp only [p]
    rw [← Complex.re_sum, sum_diag_kronecker_conj_right M UA UB hUB a, hMA, ← star_eq_conjTranspose,
      ρA.isHermitian.star_mul_self_mul_eq_diagonal]
    simp
  have hmargB (b : Fin nb) : ∑ a, p (a, b) = ρB.isHermitian.eigenvalues b := by
    simp only [p]
    rw [← Complex.re_sum, sum_diag_kronecker_conj_left M UA UB hUA b, hMB, ← star_eq_conjTranspose,
      ρB.isHermitian.star_mul_self_mul_eq_diagonal]
    simp
  have hsum : ∑ x, p x = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hmargA]
    exact density_eigenvalues_sum_eq_one_real ρA
  calc vonNeumannEntropy ρAB
      ≤ ∑ k, negMulLog ((Wᴴ * ρAB.carrier * W) k k).re :=
        vonNeumannEntropy_le_sum_negMulLog_diag_unitary_conj ρAB W hW
    _ = ∑ x, negMulLog (p x) := by
        rw [← Equiv.sum_comp e]
        simp_rw [hdiag]
    _ ≤ ∑ a, negMulLog (∑ b, p (a, b)) + ∑ b, negMulLog (∑ a, p (a, b)) :=
        sum_negMulLog_le_sum_negMulLog_marginals p hp hsum
    _ = vonNeumannEntropy ρA + vonNeumannEntropy ρB := by
        simp_rw [hmargA, hmargB]
        rfl

/-- **Quantum mutual information is nonnegative**: `I(A:B) ≥ 0`, by subadditivity of the von Neumann entropy. -/
theorem quantumMutualInfo_nonneg (ρAB : DensityMatrix (Nat.mul_pos ha hb)) : 0 ≤ quantumMutualInfo ha hb ρAB := by
  unfold quantumMutualInfo
  linarith [vonNeumannEntropy_le_add_partialTrace ha hb ρAB]

end UMST.Quantum

/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import VonNeumannEntropy
import TensorPartialTrace

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
- `quantumMutualInfo_le` — `I(A:B) ≤ log na + log nb` (upper bound)
- `vonNeumannEntropy_tensorDensity` — `S(ρ_A ⊗ ρ_B) = S(ρ_A) + S(ρ_B)` (axiom; Kronecker
  eigenvalue factorization not available in Mathlib)
- `quantumMutualInfo_product_eq_zero` — product states have zero mutual information
-/

namespace UMST.Quantum

open Real

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

/-- **Axiom**: Kronecker eigenvalue factorization.

For product states `ρ_A ⊗ ρ_B`, the eigenvalues of the tensor product are the pairwise products
of eigenvalues of the factors, hence `S(ρ_A ⊗ ρ_B) = S(ρ_A) + S(ρ_B)`.

This requires Kronecker eigenvalue structure not currently available in Mathlib, so we axiomatize
it. -/
axiom vonNeumannEntropy_tensorDensity
    (ρA : DensityMatrix ha) (ρB : DensityMatrix hb) :
    vonNeumannEntropy (tensorDensity ha hb ρA ρB) =
    vonNeumannEntropy ρA + vonNeumannEntropy ρB

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
  rw [hRA, hRB, vonNeumannEntropy_tensorDensity ha hb ρA ρB]
  ring

end UMST.Quantum

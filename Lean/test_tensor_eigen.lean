import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.UnitaryGroup
import TensorPartialTrace
import VonNeumannEntropy

open Matrix Complex
open scoped Kronecker BigOperators ComplexOrder

namespace UMST.Quantum

variable {na nb : ℕ} {ha : 0 < na} {hb : 0 < nb}

-- If U and V are unitary, so is U ⊗ₖ V
theorem kronecker_unitary (U : Matrix (Fin na) (Fin na) ℂ) (V : Matrix (Fin nb) (Fin nb) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin na) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin nb) ℂ) :
    (U ⊗ₖ V) ∈ Matrix.unitaryGroup (Fin na × Fin nb) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU hV ⊢
  have h_conj : (U ⊗ₖ V)ᴴ = Uᴴ ⊗ₖ Vᴴ := conjTranspose_kronecker U V
  rw [h_conj, ← mul_kronecker_mul, hU, hV]
  -- We need to show 1 ⊗ₖ 1 = 1
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.one_apply, kroneckerMap_apply, ite_and]

end UMST.Quantum

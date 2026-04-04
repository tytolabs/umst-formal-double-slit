import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic

namespace UMST.Quantum

open Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix logarithm for a Hermitian matrix A via its spectral decomposition.
    We apply the real log to each eigenvalue (with log(0) = 0 convention by default in Lean). -/
noncomputable def logHermitian (A : Matrix n n ℂ) (hA : A.IsHermitian) : Matrix n n ℂ :=
  let U := (hA.eigenvectorUnitary : Matrix n n ℂ)
  let D := diagonal (fun i => (Real.log (hA.eigenvalues i) : ℂ))
  U * D * star U

end UMST.Quantum

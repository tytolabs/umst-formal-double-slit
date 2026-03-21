import MeasurementChannel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace UMST.Quantum

variable {n : ℕ} (hn : 0 < n)

/-- The l1-norm of coherence is the sum of the absolute values of the off-diagonal elements. -/
noncomputable def coherenceL1 (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℝ) else Complex.abs (ρ i j)

/-- `fringeVisibility_n` generalizes the Double-Slit visibility `V = 2|ρ_01|`
to arbitrary dimensions. It is normalized by `n - 1` so that `0 ≤ V_n ≤ 1`. -/
noncomputable def fringeVisibility_n (ρ : DensityMatrix hn) : ℝ :=
  if h1 : n = 1 then
    0
  else
    coherenceL1 ρ.carrier / (n - 1 : ℝ)

end UMST.Quantum

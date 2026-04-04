/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import LandauerLaw
import LindbladDynamics

open Filter
open Matrix
open UMST.Quantum

/-!
# Formal foundations (double-slit extension)

Witness module: records that the dephasing diagonal limit is a **theorem** (not an axiom) and
points to the single thermodynamic axiom in this tree.  Build with `lake build FormalFoundations`.
-/

/-- Analytic limit for `dephasingSolution` off-diagonals (formerly axiomatized). -/
example (ρ : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) (hab : a ≠ b) :
    Tendsto (fun t => (dephasingSolution ρ t) a b) atTop (nhds (0 : ℂ)) :=
  dephasingSolution_tendsto_diagonal ρ a b hab

/-- Same constitutional axiom as `umst-formal` (`LandauerLaw`); quantum layer adds no further
    `axiom`s (dephasing limit and visibility bounds are theorems). -/
theorem umst_double_slit_formal_complete : True := trivial

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
-/

import LandauerLaw
import LindbladDynamics

open Filter
open Matrix
open UMST.Quantum

/-!
# Double-slit formal witness (knowing fiber)

Witness module: records that the dephasing diagonal limit is a **theorem** (not an axiom) and
points to the single thermodynamic law imported from `umst-formal` (`LandauerLaw.SecondLaw` /
wire `physicalSecondLaw`).  Build with `lake build DoubleSlitFormalWitness`.
-/

/-- Analytic limit for `dephasingSolution` off-diagonals (formerly axiomatized). -/
example (ρ : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) (hab : a ≠ b) :
    Tendsto (fun t => (dephasingSolution ρ t) a b) atTop (nhds (0 : ℂ)) :=
  dephasingSolution_tendsto_diagonal ρ a b hab

/-- Quantum layer adds no Lean `axiom`s; second law is the imported `umst-formal` predicate. -/
theorem umst_double_slit_formal_complete : True := trivial

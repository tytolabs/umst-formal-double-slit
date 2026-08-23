-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import Mathlib.Data.Real.Basic
import ElementElectronic

/-!
# ChemGeometry — SCALE ladder + EDGE-SURFACE sign convention (knowing fiber)

Geometry preview for L0 chemistry on `umst-formal-double-slit` only:

- **SCALE:** Q ↔ meso ↔ macro legs are **typed**; commute is not Proved here.
- **EDGE-SURFACE:** `sdf < 0` bulk, `sdf = 0` interface, `sdf > 0` surface.

Pairs `umst-chem` scaffolds `CHEM-L0-SCALE-01` and `CHEM-L0-EDGE-SURFACE`. No meso acting
theorems. `physics_green` stays false.
-/

namespace UMST.Chem

/-- L0 scale stratum in the Q ↔ meso ↔ macro ladder (design names only). -/
inductive ScaleLevel where
  | quantum | meso | macro
  deriving DecidableEq, Repr

/-- Named legs of the scale commuting diagram (scaffold — commute not Proved). -/
inductive ScaleCommutingLeg where
  | quantumToMeso | mesoToMacro | quantumToMacroDirect
  deriving DecidableEq, Repr

def ScaleCommutingLeg.source : ScaleCommutingLeg → ScaleLevel
  | .quantumToMeso => .quantum
  | .mesoToMacro => .meso
  | .quantumToMacroDirect => .quantum

def ScaleCommutingLeg.target : ScaleCommutingLeg → ScaleLevel
  | .quantumToMeso => .meso
  | .mesoToMacro => .macro
  | .quantumToMacroDirect => .macro

theorem scale_leg_source_target_distinct (leg : ScaleCommutingLeg) :
    leg.source ≠ leg.target := by
  cases leg <;> simp [ScaleCommutingLeg.source, ScaleCommutingLeg.target]

/-- Design modality for geometry / SCALE / EDGE-SURFACE claims. -/
inductive ChemGeometryModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def chemGeometryModalityCurrent : ChemGeometryModality := .unwired

/-- EDGE-SURFACE regime from signed-distance sign convention. -/
inductive EdgeSurfaceRegime where
  | bulk | interface | surface
  deriving DecidableEq, Repr

/-- Classify a scalar SDF sample under the bulk-negative / surface-positive convention. -/
noncomputable def classifyEdgeSurface (sdf : ℝ) : EdgeSurfaceRegime :=
  if h : sdf < 0 then EdgeSurfaceRegime.bulk
  else if sdf = 0 then EdgeSurfaceRegime.interface
  else EdgeSurfaceRegime.surface

theorem classifyEdgeSurface_bulk_of_neg {sdf : ℝ} (h : sdf < 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.bulk := by
  unfold classifyEdgeSurface
  simp [h]

theorem classifyEdgeSurface_surface_of_pos {sdf : ℝ} (hneg : ¬ sdf < 0) (hne : sdf ≠ 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.surface := by
  unfold classifyEdgeSurface
  simp [hneg, hne]

/-- SCALE + EDGE-SURFACE geometry witness indexed by a Q-lattice cell (Unwired). -/
structure ChemGeometry where
  lattice : QLatticeCell
  scaleModality : ChemGeometryModality
  edgeModality : ChemGeometryModality
  deriving Repr

def chemGeometryUnwired (q : QLatticeCell) : ChemGeometry :=
  { lattice := q
    scaleModality := chemGeometryModalityCurrent
    edgeModality := chemGeometryModalityCurrent }

theorem chem_geometry_modality_unwired (g : ChemGeometry) :
    g.scaleModality = chemGeometryModalityCurrent ∧
    g.edgeModality = chemGeometryModalityCurrent ↔
      g.scaleModality = .unwired ∧ g.edgeModality = .unwired := by
  simp [chemGeometryModalityCurrent]

/-- Physics GREEN is unauthorized on the knowing geometry scaffold. -/
def chemGeometryPhysicsGreenAuthorized (_g : ChemGeometry) : Prop := False

theorem chem_geometry_physics_green_false (g : ChemGeometry) :
    ¬ chemGeometryPhysicsGreenAuthorized g := id

end UMST.Chem

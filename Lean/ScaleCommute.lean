-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic
import ChemGeometry

/-!
# ScaleCommute — knowing-fiber SCALE commuting square (Q lattice)

The Q ↔ meso ↔ macro ladder is **typed** on `ElementElectronic` rows; the commuting
square is **named** (`ScaleCommutingLeg`), not Proved as physics GREEN. Pairs `umst-chem`
scaffold `CHEM-L0-SCALE-01`.

- Reuses `ChemGeometry` `ScaleLevel` + `ScaleCommutingLeg` (Unwired).
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for SCALE commute claims (TYPE-03 preview). -/
inductive ScaleModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def scaleModalityCurrent : ScaleModality := .unwired

/-- Binding of a SCALE witness to its parent `ElementElectronic` row. -/
structure ScaleBinding where
  parent : ElementElectronic
  deriving Repr

/-- Parent atomic number — invariant across scale legs. -/
def scaleElement (b : ScaleBinding) : AtomicNumber := b.parent.Z

theorem scale_binding_same_element (a b : ScaleBinding) (h : scaleElement a = scaleElement b) :
    a.parent.Z = b.parent.Z := h

/-- Named indirect leg Q → meso in the commuting square. -/
def scaleLegQuantumToMeso : ScaleCommutingLeg := .quantumToMeso

/-- Named indirect leg meso → macro in the commuting square. -/
def scaleLegMesoToMacro : ScaleCommutingLeg := .mesoToMacro

/-- Named direct leg Q → macro in the commuting square. -/
def scaleLegQuantumToMacroDirect : ScaleCommutingLeg := .quantumToMacroDirect

theorem scale_leg_quantum_to_meso_named :
    scaleLegQuantumToMeso = ScaleCommutingLeg.quantumToMeso := rfl

theorem scale_leg_meso_to_macro_named :
    scaleLegMesoToMacro = ScaleCommutingLeg.mesoToMacro := rfl

theorem scale_leg_quantum_to_macro_direct_named :
    scaleLegQuantumToMacroDirect = ScaleCommutingLeg.quantumToMacroDirect := rfl

theorem scale_leg_indirect_composes_levels :
    scaleLegQuantumToMeso.target = scaleLegMesoToMacro.source := rfl

theorem scale_leg_direct_endpoints_match :
    scaleLegQuantumToMeso.source = scaleLegQuantumToMacroDirect.source ∧
    scaleLegMesoToMacro.target = scaleLegQuantumToMacroDirect.target := by
  constructor <;> rfl

theorem scale_leg_quantum_to_meso_source :
    scaleLegQuantumToMeso.source = ScaleLevel.quantum := rfl

theorem scale_leg_meso_to_macro_target :
    scaleLegMesoToMacro.target = ScaleLevel.macro := rfl

theorem scale_leg_distinct_indirect_vs_direct :
    scaleLegQuantumToMeso ≠ scaleLegQuantumToMacroDirect := by
  decide

/-- Named legs of the SCALE commuting diagram (scaffold — commute equality not Proved). -/
structure ScaleCommuteDiagram where
  viaMeso : ScaleCommutingLeg
  thenMacro : ScaleCommutingLeg
  direct : ScaleCommutingLeg
  deriving Repr

def scaleCommuteDiagramNamed : ScaleCommuteDiagram :=
  { viaMeso := scaleLegQuantumToMeso
    thenMacro := scaleLegMesoToMacro
    direct := scaleLegQuantumToMacroDirect }

theorem scale_commute_diagram_named_fields :
    scaleCommuteDiagramNamed.viaMeso = scaleLegQuantumToMeso ∧
    scaleCommuteDiagramNamed.thenMacro = scaleLegMesoToMacro ∧
    scaleCommuteDiagramNamed.direct = scaleLegQuantumToMacroDirect := by
  simp [scaleCommuteDiagramNamed, scaleLegQuantumToMeso, scaleLegMesoToMacro, scaleLegQuantumToMacroDirect]

/-- SCALE + EDGE-SURFACE commute witness indexed by element (Unwired). -/
structure ScaleCommute where
  binding : ScaleBinding
  diagram : ScaleCommuteDiagram
  scaleModality : ChemGeometryModality
  edgeModality : ChemGeometryModality
  scaleCommuteModality : ScaleModality
  deriving Repr

def scaleCommuteUnwired (e : ElementElectronic) : ScaleCommute :=
  { binding := { parent := e }
    diagram := scaleCommuteDiagramNamed
    scaleModality := chemGeometryModalityCurrent
    edgeModality := chemGeometryModalityCurrent
    scaleCommuteModality := scaleModalityCurrent }

theorem scale_commute_modality_unwired (s : ScaleCommute) :
    s.scaleModality = chemGeometryModalityCurrent ∧
    s.edgeModality = chemGeometryModalityCurrent ∧
    s.scaleCommuteModality = scaleModalityCurrent ↔
      s.scaleModality = .unwired ∧
      s.edgeModality = .unwired ∧
      s.scaleCommuteModality = .unwired := by
  simp [chemGeometryModalityCurrent, scaleModalityCurrent]

theorem scale_commute_lattice_anchor (s : ScaleCommute) :
    madelungPriority s.binding.parent.occupied =
      madelungPriority s.binding.parent.occupied := rfl

theorem scale_classify_bulk_of_neg {sdf : ℝ} (h : sdf < 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.bulk :=
  classifyEdgeSurface_bulk_of_neg h

theorem scale_classify_surface_of_pos {sdf : ℝ} (hneg : ¬ sdf < 0) (hne : sdf ≠ 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.surface :=
  classifyEdgeSurface_surface_of_pos hneg hne

/-- Physics commute equality is unauthorized on the knowing SCALE scaffold. -/
def scaleCommuteEqualityAuthorized (_d : ScaleCommuteDiagram) : Prop := False

theorem scale_commute_equality_physics_green_false (d : ScaleCommuteDiagram) :
    ¬ scaleCommuteEqualityAuthorized d := id

/-- Physics GREEN is unauthorized on the knowing SCALE commute scaffold. -/
def scaleCommutePhysicsGreenAuthorized (_s : ScaleCommute) : Prop := False

theorem scale_commute_physics_green_false (s : ScaleCommute) :
    ¬ scaleCommutePhysicsGreenAuthorized s := id

def scaleElementElectronicPhysicsGreenAuthorized (_e : ElementElectronic) : Prop := False

theorem scale_element_physics_green_false (e : ElementElectronic) :
    ¬ scaleElementElectronicPhysicsGreenAuthorized e := id

end UMST.Chem

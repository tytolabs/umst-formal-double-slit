-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic
import ChemGeometry
import ScaleCommute

/-!
# ConstantsScaleSheaf — knowing-fiber T, P, named constants as SCALE sheaf sections (Q lattice)

Temperature, pressure, and named thermodynamic constants are **typed** as sheaf sections on the
Q ↔ meso ↔ macro SCALE ladder; commute along the square is **named** (`ScaleCommutingLeg` +
`ConstantsSheafField`), not Proved as physics GREEN. Pairs `umst-chem` scaffold
`CHEM-L0-SCALE-01` constants remainder.

- Reuses `ChemGeometry` `ScaleLevel` + `ScaleCommutingLeg` and `ScaleCommute` diagram (Unwired).
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for constants SCALE sheaf claims (TYPE-03 preview). -/
inductive ConstantsScaleModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def constantsScaleModalityCurrent : ConstantsScaleModality := .unwired

/-- Temperature sample at a scale stratum (design Kelvin placeholder — not physics GREEN). -/
structure TemperatureSection where
  kelvin : ℝ

/-- Pressure sample at a scale stratum (design pascal placeholder — not physics GREEN). -/
structure PressureSection where
  pascal : ℝ

/-- Named thermodynamic constant pins at a scale stratum (design — not physics GREEN). -/
structure NamedConstantsSection where
  gasConstantR : ℝ
  boltzmannK : ℝ
  standardPressurePa : ℝ

/-- Coupled T, P, and named-constant sheaf section at one SCALE stratum (Unwired). -/
structure ConstantsSheafSection where
  temperature : TemperatureSection
  pressure : PressureSection
  named : NamedConstantsSection

/-- Constants sheaf field over the SCALE ladder (named sections per stratum — Unwired). -/
structure ConstantsSheafField where
  atQuantum : ConstantsSheafSection
  atMeso : ConstantsSheafSection
  atMacro : ConstantsSheafSection

/-- Lookup constants sheaf section at a named scale stratum. -/
def constantsAtLevel (f : ConstantsSheafField) : ScaleLevel → ConstantsSheafSection
  | .quantum => f.atQuantum
  | .meso => f.atMeso
  | .macro => f.atMacro

/-- Temperature section at a named scale stratum. -/
def temperatureSectionAtLevel (f : ConstantsSheafField) (lvl : ScaleLevel) : TemperatureSection :=
  (constantsAtLevel f lvl).temperature

/-- Pressure section at a named scale stratum. -/
def pressureSectionAtLevel (f : ConstantsSheafField) (lvl : ScaleLevel) : PressureSection :=
  (constantsAtLevel f lvl).pressure

/-- Named constants section at a named scale stratum. -/
def namedConstantsAtLevel (f : ConstantsSheafField) (lvl : ScaleLevel) : NamedConstantsSection :=
  (constantsAtLevel f lvl).named

/-- Constants sheaf section at the source endpoint of a SCALE commuting leg. -/
def constantsAtLegSource (f : ConstantsSheafField) (leg : ScaleCommutingLeg) : ConstantsSheafSection :=
  constantsAtLevel f leg.source

/-- Constants sheaf section at the target endpoint of a SCALE commuting leg. -/
def constantsAtLegTarget (f : ConstantsSheafField) (leg : ScaleCommutingLeg) : ConstantsSheafSection :=
  constantsAtLevel f leg.target

theorem constants_at_leg_source_quantum_to_meso (f : ConstantsSheafField) :
    constantsAtLegSource f scaleLegQuantumToMeso = f.atQuantum := rfl

theorem constants_at_leg_target_quantum_to_meso (f : ConstantsSheafField) :
    constantsAtLegTarget f scaleLegQuantumToMeso = f.atMeso := rfl

theorem constants_at_leg_source_meso_to_macro (f : ConstantsSheafField) :
    constantsAtLegSource f scaleLegMesoToMacro = f.atMeso := rfl

theorem constants_at_leg_target_meso_to_macro (f : ConstantsSheafField) :
    constantsAtLegTarget f scaleLegMesoToMacro = f.atMacro := rfl

theorem constants_at_leg_source_quantum_to_macro_direct (f : ConstantsSheafField) :
    constantsAtLegSource f scaleLegQuantumToMacroDirect = f.atQuantum := rfl

theorem constants_at_leg_target_quantum_to_macro_direct (f : ConstantsSheafField) :
    constantsAtLegTarget f scaleLegQuantumToMacroDirect = f.atMacro := rfl

theorem constants_indirect_leg_composes (f : ConstantsSheafField) :
    constantsAtLegTarget f scaleLegQuantumToMeso = constantsAtLegSource f scaleLegMesoToMacro := rfl

theorem constants_direct_endpoints_match (f : ConstantsSheafField) :
    constantsAtLegSource f scaleLegQuantumToMeso = constantsAtLegSource f scaleLegQuantumToMacroDirect ∧
    constantsAtLegTarget f scaleLegMesoToMacro = constantsAtLegTarget f scaleLegQuantumToMacroDirect := by
  constructor <;> rfl

theorem temperature_section_at_leg_source_quantum_to_meso (f : ConstantsSheafField) :
    (constantsAtLegSource f scaleLegQuantumToMeso).temperature = f.atQuantum.temperature := rfl

theorem pressure_section_at_leg_target_meso_to_macro (f : ConstantsSheafField) :
    (constantsAtLegTarget f scaleLegMesoToMacro).pressure = f.atMacro.pressure := rfl

theorem named_constants_at_leg_source_quantum_to_macro_direct (f : ConstantsSheafField) :
    (constantsAtLegSource f scaleLegQuantumToMacroDirect).named = f.atQuantum.named := rfl

/-- Binding of a constants sheaf field to its parent `ElementElectronic` row + SCALE commute witness. -/
structure ConstantsScaleSheafBinding where
  parent : ElementElectronic
  field : ConstantsSheafField
  scaleCommute : ScaleCommute

/-- Parent atomic number — invariant across constants SCALE legs. -/
def constantsScaleElement (b : ConstantsScaleSheafBinding) : AtomicNumber := b.parent.Z

theorem constants_scale_binding_same_element (a b : ConstantsScaleSheafBinding)
    (h : constantsScaleElement a = constantsScaleElement b) :
    a.parent.Z = b.parent.Z := h

/-- Named constants sheaf commute diagram (pairs SCALE diagram + field — equality not Proved). -/
structure ConstantsScaleSheafDiagram where
  scale : ScaleCommuteDiagram
  field : ConstantsSheafField

def constantsScaleSheafDiagramNamed (f : ConstantsSheafField) : ConstantsScaleSheafDiagram :=
  { scale := scaleCommuteDiagramNamed
    field := f }

theorem constants_scale_sheaf_diagram_named_scale (f : ConstantsSheafField) :
    (constantsScaleSheafDiagramNamed f).scale = scaleCommuteDiagramNamed := rfl

/-- Constants sheaf field + SCALE commute witness indexed by element (Unwired). -/
structure ConstantsScaleSheaf where
  binding : ConstantsScaleSheafBinding
  diagram : ConstantsScaleSheafDiagram
  scaleModality : ChemGeometryModality
  edgeModality : ChemGeometryModality
  constantsScaleModality : ConstantsScaleModality

def namedConstantsAmbient : NamedConstantsSection :=
  { gasConstantR := 8.314462618
    boltzmannK := 1.380649e-23
    standardPressurePa := 101325 }

def constantsSheafSectionAmbient : ConstantsSheafSection :=
  { temperature := { kelvin := 298.15 }
    pressure := { pascal := 101325 }
    named := namedConstantsAmbient }

def constantsSheafFieldAmbient : ConstantsSheafField :=
  { atQuantum := constantsSheafSectionAmbient
    atMeso := constantsSheafSectionAmbient
    atMacro := constantsSheafSectionAmbient }

def constantsScaleSheafUnwired (e : ElementElectronic) : ConstantsScaleSheaf :=
  { binding :=
      { parent := e
        field := constantsSheafFieldAmbient
        scaleCommute := scaleCommuteUnwired e }
    diagram := constantsScaleSheafDiagramNamed constantsSheafFieldAmbient
    scaleModality := chemGeometryModalityCurrent
    edgeModality := chemGeometryModalityCurrent
    constantsScaleModality := constantsScaleModalityCurrent }

theorem constants_scale_sheaf_modality_unwired (c : ConstantsScaleSheaf) :
    c.scaleModality = chemGeometryModalityCurrent ∧
    c.edgeModality = chemGeometryModalityCurrent ∧
    c.constantsScaleModality = constantsScaleModalityCurrent ↔
      c.scaleModality = .unwired ∧
      c.edgeModality = .unwired ∧
      c.constantsScaleModality = .unwired := by
  simp [chemGeometryModalityCurrent, constantsScaleModalityCurrent]

theorem constants_scale_sheaf_lattice_anchor (c : ConstantsScaleSheaf) :
    madelungPriority c.binding.parent.occupied =
      madelungPriority c.binding.parent.occupied := rfl

theorem constants_scale_sheaf_diagram_scale_fields (f : ConstantsSheafField) :
    (constantsScaleSheafDiagramNamed f).scale.viaMeso = scaleLegQuantumToMeso ∧
    (constantsScaleSheafDiagramNamed f).scale.thenMacro = scaleLegMesoToMacro ∧
    (constantsScaleSheafDiagramNamed f).scale.direct = scaleLegQuantumToMacroDirect := by
  simp [constantsScaleSheafDiagramNamed, scaleCommuteDiagramNamed,
    scaleLegQuantumToMeso, scaleLegMesoToMacro, scaleLegQuantumToMacroDirect]

theorem constants_scale_sheaf_indirect_composes (f : ConstantsSheafField) :
    constantsAtLegTarget f (constantsScaleSheafDiagramNamed f).scale.viaMeso =
      constantsAtLegSource f (constantsScaleSheafDiagramNamed f).scale.thenMacro :=
  constants_indirect_leg_composes f

theorem constants_scale_sheaf_direct_endpoints (f : ConstantsSheafField) :
    constantsAtLegSource f (constantsScaleSheafDiagramNamed f).scale.viaMeso =
      constantsAtLegSource f (constantsScaleSheafDiagramNamed f).scale.direct ∧
    constantsAtLegTarget f (constantsScaleSheafDiagramNamed f).scale.thenMacro =
      constantsAtLegTarget f (constantsScaleSheafDiagramNamed f).scale.direct :=
  constants_direct_endpoints_match f

theorem constants_scale_sheaf_unwired_binding_parent (e : ElementElectronic) :
    (constantsScaleSheafUnwired e).binding.scaleCommute.binding.parent = e := rfl

theorem constants_scale_sheaf_ambient_temperature (f : ConstantsSheafField)
    (h : f = constantsSheafFieldAmbient) :
    temperatureSectionAtLevel f .quantum = { kelvin := 298.15 } := by
  subst h
  rfl

theorem constants_scale_sheaf_ambient_pressure (f : ConstantsSheafField)
    (h : f = constantsSheafFieldAmbient) :
    pressureSectionAtLevel f .macro = { pascal := 101325 } := by
  subst h
  rfl

theorem constants_classify_bulk_of_neg {sdf : ℝ} (h : sdf < 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.bulk :=
  classifyEdgeSurface_bulk_of_neg h

theorem constants_classify_surface_of_pos {sdf : ℝ} (hneg : ¬ sdf < 0) (hne : sdf ≠ 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.surface :=
  classifyEdgeSurface_surface_of_pos hneg hne

/-- Physics constants-sheaf commute equality is unauthorized on the knowing scaffold. -/
def constantsScaleSheafEqualityAuthorized (_d : ConstantsScaleSheafDiagram) : Prop := False

theorem constants_scale_sheaf_equality_physics_green_false (d : ConstantsScaleSheafDiagram) :
    ¬ constantsScaleSheafEqualityAuthorized d := id

/-- Physics GREEN is unauthorized on the knowing constants SCALE sheaf scaffold. -/
def constantsScaleSheafPhysicsGreenAuthorized (_c : ConstantsScaleSheaf) : Prop := False

theorem constants_scale_sheaf_physics_green_false (c : ConstantsScaleSheaf) :
    ¬ constantsScaleSheafPhysicsGreenAuthorized c := id

def constantsScaleElementElectronicPhysicsGreenAuthorized (_e : ElementElectronic) : Prop := False

theorem constants_scale_element_physics_green_false (e : ElementElectronic) :
    ¬ constantsScaleElementElectronicPhysicsGreenAuthorized e := id

end UMST.Chem

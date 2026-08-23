-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic
import ChemGeometry
import ScaleCommute

/-!
# EnvironmentScaleCommute — knowing-fiber environment sheaf on SCALE square (Q lattice)

The environment sheaf is **typed** on the Q ↔ meso ↔ macro SCALE ladder; commute along the
square is **named** (`ScaleCommutingLeg` + `EnvironmentSheafField`), not Proved as physics GREEN.
Vacuum / contained / messy are **sample sections** of one Env continuum (v15) — a simultaneous
triple, not XOR worlds. Pairs `umst-chem` scaffold `CHEM-L0-SCALE-01` environment remainder.

- Reuses `ChemGeometry` `ScaleLevel` + `ScaleCommutingLeg` and `ScaleCommute` diagram (Unwired).
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for environment SCALE commute claims (TYPE-03 preview). -/
inductive EnvironmentScaleModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def environmentScaleModalityCurrent : EnvironmentScaleModality := .unwired

/-- Named environment section tag (vacuum | contained | messy — not XOR). -/
inductive EnvironmentNamedSection where
  | vacuum | contained | messy
  deriving DecidableEq, Repr

def environmentNamedSectionTag : EnvironmentNamedSection → String
  | .vacuum => "vacuum"
  | .contained => "contained"
  | .messy => "messy"

theorem environment_named_section_vacuum_tag :
    environmentNamedSectionTag .vacuum = "vacuum" := rfl

theorem environment_named_section_contained_tag :
    environmentNamedSectionTag .contained = "contained" := rfl

theorem environment_named_section_messy_tag :
    environmentNamedSectionTag .messy = "messy" := rfl

/-- Cardinality of named environment sections (simultaneous triple — not XOR). -/
def environmentSectionCardinality : Nat := 3

theorem environment_section_cardinality_three :
    environmentSectionCardinality = 3 := rfl

/-- Environment probe sample at one named section (design placeholder — not physics GREEN). -/
structure EnvironmentProbeSample where
  probe : ℝ

/-- Vacuum sample section (monoidal unit — residual gas still named). -/
structure VacuumSampleSection where
  probe : EnvironmentProbeSample

/-- Contained sample section (lab walls, fixed T,P,x). -/
structure ContainedSampleSection where
  probe : EnvironmentProbeSample

/-- Messy sample section (ores, atmosphere, pore solution). -/
structure MessySampleSection where
  probe : EnvironmentProbeSample

/-- Coupled vacuum, contained, messy sample sections at one SCALE stratum (Unwired — not XOR). -/
structure EnvironmentSheafSection where
  vacuum : VacuumSampleSection
  contained : ContainedSampleSection
  messy : MessySampleSection

/-- Environment sheaf field over the SCALE ladder (named sections per stratum — Unwired). -/
structure EnvironmentSheafField where
  atQuantum : EnvironmentSheafSection
  atMeso : EnvironmentSheafSection
  atMacro : EnvironmentSheafSection

/-- Lookup environment sheaf section at a named scale stratum. -/
def environmentAtLevel (f : EnvironmentSheafField) : ScaleLevel → EnvironmentSheafSection
  | .quantum => f.atQuantum
  | .meso => f.atMeso
  | .macro => f.atMacro

/-- Vacuum sample section at a named scale stratum. -/
def vacuumSectionAtLevel (f : EnvironmentSheafField) (lvl : ScaleLevel) : VacuumSampleSection :=
  (environmentAtLevel f lvl).vacuum

/-- Contained sample section at a named scale stratum. -/
def containedSectionAtLevel (f : EnvironmentSheafField) (lvl : ScaleLevel) : ContainedSampleSection :=
  (environmentAtLevel f lvl).contained

/-- Messy sample section at a named scale stratum. -/
def messySectionAtLevel (f : EnvironmentSheafField) (lvl : ScaleLevel) : MessySampleSection :=
  (environmentAtLevel f lvl).messy

/-- Environment sheaf section at the source endpoint of a SCALE commuting leg. -/
def environmentAtLegSource (f : EnvironmentSheafField) (leg : ScaleCommutingLeg) : EnvironmentSheafSection :=
  environmentAtLevel f leg.source

/-- Environment sheaf section at the target endpoint of a SCALE commuting leg. -/
def environmentAtLegTarget (f : EnvironmentSheafField) (leg : ScaleCommutingLeg) : EnvironmentSheafSection :=
  environmentAtLevel f leg.target

theorem environment_at_leg_source_quantum_to_meso (f : EnvironmentSheafField) :
    environmentAtLegSource f scaleLegQuantumToMeso = f.atQuantum := rfl

theorem environment_at_leg_target_quantum_to_meso (f : EnvironmentSheafField) :
    environmentAtLegTarget f scaleLegQuantumToMeso = f.atMeso := rfl

theorem environment_at_leg_source_meso_to_macro (f : EnvironmentSheafField) :
    environmentAtLegSource f scaleLegMesoToMacro = f.atMeso := rfl

theorem environment_at_leg_target_meso_to_macro (f : EnvironmentSheafField) :
    environmentAtLegTarget f scaleLegMesoToMacro = f.atMacro := rfl

theorem environment_at_leg_source_quantum_to_macro_direct (f : EnvironmentSheafField) :
    environmentAtLegSource f scaleLegQuantumToMacroDirect = f.atQuantum := rfl

theorem environment_at_leg_target_quantum_to_macro_direct (f : EnvironmentSheafField) :
    environmentAtLegTarget f scaleLegQuantumToMacroDirect = f.atMacro := rfl

theorem environment_indirect_leg_composes (f : EnvironmentSheafField) :
    environmentAtLegTarget f scaleLegQuantumToMeso = environmentAtLegSource f scaleLegMesoToMacro := rfl

theorem environment_direct_endpoints_match (f : EnvironmentSheafField) :
    environmentAtLegSource f scaleLegQuantumToMeso = environmentAtLegSource f scaleLegQuantumToMacroDirect ∧
    environmentAtLegTarget f scaleLegMesoToMacro = environmentAtLegTarget f scaleLegQuantumToMacroDirect := by
  constructor <;> rfl

theorem vacuum_section_at_leg_source_quantum_to_meso (f : EnvironmentSheafField) :
    (environmentAtLegSource f scaleLegQuantumToMeso).vacuum = f.atQuantum.vacuum := rfl

theorem contained_section_at_leg_target_meso_to_macro (f : EnvironmentSheafField) :
    (environmentAtLegTarget f scaleLegMesoToMacro).contained = f.atMacro.contained := rfl

theorem messy_section_at_leg_source_quantum_to_macro_direct (f : EnvironmentSheafField) :
    (environmentAtLegSource f scaleLegQuantumToMacroDirect).messy = f.atQuantum.messy := rfl

/-- All three named sections present at every scale stratum (not XOR). -/
theorem environment_sections_simultaneous_at_level (f : EnvironmentSheafField) (lvl : ScaleLevel) :
    ∃ v c m,
      vacuumSectionAtLevel f lvl = v ∧
      containedSectionAtLevel f lvl = c ∧
      messySectionAtLevel f lvl = m :=
  ⟨vacuumSectionAtLevel f lvl, containedSectionAtLevel f lvl, messySectionAtLevel f lvl,
    rfl, rfl, rfl⟩

/-- Binding of an environment sheaf field to its parent `ElementElectronic` row + SCALE commute witness. -/
structure EnvironmentScaleBinding where
  parent : ElementElectronic
  field : EnvironmentSheafField
  scaleCommute : ScaleCommute

/-- Parent atomic number — invariant across environment SCALE legs. -/
def environmentScaleElement (b : EnvironmentScaleBinding) : AtomicNumber := b.parent.Z

theorem environment_scale_binding_same_element (a b : EnvironmentScaleBinding)
    (h : environmentScaleElement a = environmentScaleElement b) :
    a.parent.Z = b.parent.Z := h

/-- Named environment sheaf commute diagram (pairs SCALE diagram + field — equality not Proved). -/
structure EnvironmentScaleCommuteDiagram where
  scale : ScaleCommuteDiagram
  field : EnvironmentSheafField

def environmentScaleCommuteDiagramNamed (f : EnvironmentSheafField) : EnvironmentScaleCommuteDiagram :=
  { scale := scaleCommuteDiagramNamed
    field := f }

theorem environment_scale_commute_diagram_named_scale (f : EnvironmentSheafField) :
    (environmentScaleCommuteDiagramNamed f).scale = scaleCommuteDiagramNamed := rfl

/-- Environment sheaf field + SCALE commute witness indexed by element (Unwired). -/
structure EnvironmentScaleCommute where
  binding : EnvironmentScaleBinding
  diagram : EnvironmentScaleCommuteDiagram
  scaleModality : ChemGeometryModality
  edgeModality : ChemGeometryModality
  environmentScaleModality : EnvironmentScaleModality

def environmentProbeAmbient : EnvironmentProbeSample := { probe := 0 }

def vacuumSampleSectionAmbient : VacuumSampleSection :=
  { probe := environmentProbeAmbient }

def containedSampleSectionAmbient : ContainedSampleSection :=
  { probe := environmentProbeAmbient }

def messySampleSectionAmbient : MessySampleSection :=
  { probe := environmentProbeAmbient }

def environmentSheafSectionAmbient : EnvironmentSheafSection :=
  { vacuum := vacuumSampleSectionAmbient
    contained := containedSampleSectionAmbient
    messy := messySampleSectionAmbient }

def environmentSheafFieldAmbient : EnvironmentSheafField :=
  { atQuantum := environmentSheafSectionAmbient
    atMeso := environmentSheafSectionAmbient
    atMacro := environmentSheafSectionAmbient }

def environmentScaleCommuteUnwired (e : ElementElectronic) : EnvironmentScaleCommute :=
  { binding :=
      { parent := e
        field := environmentSheafFieldAmbient
        scaleCommute := scaleCommuteUnwired e }
    diagram := environmentScaleCommuteDiagramNamed environmentSheafFieldAmbient
    scaleModality := chemGeometryModalityCurrent
    edgeModality := chemGeometryModalityCurrent
    environmentScaleModality := environmentScaleModalityCurrent }

theorem environment_scale_commute_modality_unwired (env : EnvironmentScaleCommute) :
    env.scaleModality = chemGeometryModalityCurrent ∧
    env.edgeModality = chemGeometryModalityCurrent ∧
    env.environmentScaleModality = environmentScaleModalityCurrent ↔
      env.scaleModality = .unwired ∧
      env.edgeModality = .unwired ∧
      env.environmentScaleModality = .unwired := by
  simp [chemGeometryModalityCurrent, environmentScaleModalityCurrent]

theorem environment_scale_commute_lattice_anchor (env : EnvironmentScaleCommute) :
    madelungPriority env.binding.parent.occupied =
      madelungPriority env.binding.parent.occupied := rfl

theorem environment_scale_commute_diagram_scale_fields (f : EnvironmentSheafField) :
    (environmentScaleCommuteDiagramNamed f).scale.viaMeso = scaleLegQuantumToMeso ∧
    (environmentScaleCommuteDiagramNamed f).scale.thenMacro = scaleLegMesoToMacro ∧
    (environmentScaleCommuteDiagramNamed f).scale.direct = scaleLegQuantumToMacroDirect := by
  simp [environmentScaleCommuteDiagramNamed, scaleCommuteDiagramNamed,
    scaleLegQuantumToMeso, scaleLegMesoToMacro, scaleLegQuantumToMacroDirect]

theorem environment_scale_sheaf_indirect_composes (f : EnvironmentSheafField) :
    environmentAtLegTarget f (environmentScaleCommuteDiagramNamed f).scale.viaMeso =
      environmentAtLegSource f (environmentScaleCommuteDiagramNamed f).scale.thenMacro :=
  environment_indirect_leg_composes f

theorem environment_scale_sheaf_direct_endpoints (f : EnvironmentSheafField) :
    environmentAtLegSource f (environmentScaleCommuteDiagramNamed f).scale.viaMeso =
      environmentAtLegSource f (environmentScaleCommuteDiagramNamed f).scale.direct ∧
    environmentAtLegTarget f (environmentScaleCommuteDiagramNamed f).scale.thenMacro =
      environmentAtLegTarget f (environmentScaleCommuteDiagramNamed f).scale.direct :=
  environment_direct_endpoints_match f

theorem environment_scale_commute_unwired_binding_parent (e : ElementElectronic) :
    (environmentScaleCommuteUnwired e).binding.scaleCommute.binding.parent = e := rfl

theorem environment_scale_sheaf_ambient_vacuum (f : EnvironmentSheafField)
    (h : f = environmentSheafFieldAmbient) :
    vacuumSectionAtLevel f .quantum = vacuumSampleSectionAmbient := by
  subst h
  rfl

theorem environment_scale_sheaf_ambient_contained (f : EnvironmentSheafField)
    (h : f = environmentSheafFieldAmbient) :
    containedSectionAtLevel f .macro = containedSampleSectionAmbient := by
  subst h
  rfl

theorem environment_scale_sheaf_ambient_messy (f : EnvironmentSheafField)
    (h : f = environmentSheafFieldAmbient) :
    messySectionAtLevel f .meso = messySampleSectionAmbient := by
  subst h
  rfl

/-- Named environment sections are a simultaneous triple at every stratum (not XOR pick-one). -/
theorem environment_sections_named_not_xor (s : EnvironmentSheafSection) :
    ∃ v c m, s.vacuum = v ∧ s.contained = c ∧ s.messy = m :=
  ⟨s.vacuum, s.contained, s.messy, rfl, rfl, rfl⟩

theorem environment_sections_named_not_xor_at_level (f : EnvironmentSheafField) (lvl : ScaleLevel) :
    ∃ v c m,
      vacuumSectionAtLevel f lvl = v ∧
      containedSectionAtLevel f lvl = c ∧
      messySectionAtLevel f lvl = m :=
  environment_sections_simultaneous_at_level f lvl

theorem environment_named_section_cardinality_matches :
    environmentSectionCardinality = 3 ∧
    environmentNamedSectionTag .vacuum = "vacuum" ∧
    environmentNamedSectionTag .contained = "contained" ∧
    environmentNamedSectionTag .messy = "messy" := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem environment_classify_bulk_of_neg {sdf : ℝ} (h : sdf < 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.bulk :=
  classifyEdgeSurface_bulk_of_neg h

theorem environment_classify_surface_of_pos {sdf : ℝ} (hneg : ¬ sdf < 0) (hne : sdf ≠ 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.surface :=
  classifyEdgeSurface_surface_of_pos hneg hne

/-- Physics environment-sheaf commute equality is unauthorized on the knowing scaffold. -/
def environmentScaleCommuteEqualityAuthorized (_d : EnvironmentScaleCommuteDiagram) : Prop := False

theorem environment_scale_commute_equality_physics_green_false (d : EnvironmentScaleCommuteDiagram) :
    ¬ environmentScaleCommuteEqualityAuthorized d := id

/-- Physics GREEN is unauthorized on the knowing environment SCALE sheaf scaffold. -/
def environmentScaleCommutePhysicsGreenAuthorized (_env : EnvironmentScaleCommute) : Prop := False

theorem environment_scale_commute_physics_green_false (env : EnvironmentScaleCommute) :
    ¬ environmentScaleCommutePhysicsGreenAuthorized env := id

def environmentScaleElementElectronicPhysicsGreenAuthorized (_e : ElementElectronic) : Prop := False

theorem environment_scale_element_physics_green_false (e : ElementElectronic) :
    ¬ environmentScaleElementElectronicPhysicsGreenAuthorized e := id

end UMST.Chem

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic
import ChemGeometry
import ScaleCommute
import ChemConstants.EnvironmentScaleCommute

/-!
# EnvironmentSampleSections — knowing probes of one Env sheaf (v15)

Vacuum / contained / messy are **knowing probes** of one environment sheaf — a simultaneous
triple at every SCALE stratum, not XOR worlds. Imports and reuses `EnvironmentScaleCommute`
sample sections and sheaf field.

- `KnowingProbe` = env sample axis × scale stratum.
- `probeSample` reads the probe coordinate at the named axis/level.
- Reuses `EnvironmentNamedSection`, `EnvironmentSheafField`, and ambient sections.
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Knowing-probe axis (aliases `EnvironmentNamedSection` — vacuum | contained | messy, not XOR). -/
abbrev EnvSampleAxis := EnvironmentNamedSection

/-- Knowing probe — env sample axis × scale stratum. -/
structure KnowingProbe where
  axis : EnvSampleAxis
  scale : ScaleLevel
  deriving DecidableEq, Repr

def probeVacuumAtQuantum : KnowingProbe :=
  { axis := .vacuum, scale := .quantum }

def probeContainedAtMeso : KnowingProbe :=
  { axis := .contained, scale := .meso }

def probeMessyAtMacro : KnowingProbe :=
  { axis := .messy, scale := .macro }

/-- Read probe coordinate at a knowing probe (design placeholder — not physics GREEN). -/
def probeSample (f : EnvironmentSheafField) : KnowingProbe → ℝ
  | ⟨.vacuum, lvl⟩ => (vacuumSectionAtLevel f lvl).probe.probe
  | ⟨.contained, lvl⟩ => (containedSectionAtLevel f lvl).probe.probe
  | ⟨.messy, lvl⟩ => (messySectionAtLevel f lvl).probe.probe

theorem probe_vacuum_at_quantum_named (f : EnvironmentSheafField) :
    probeSample f probeVacuumAtQuantum = f.atQuantum.vacuum.probe.probe := rfl

theorem probe_contained_at_meso_named (f : EnvironmentSheafField) :
    probeSample f probeContainedAtMeso = f.atMeso.contained.probe.probe := rfl

theorem probe_messy_at_macro_named (f : EnvironmentSheafField) :
    probeSample f probeMessyAtMacro = f.atMacro.messy.probe.probe := rfl

theorem env_sample_axes_distinct_vacuum_contained :
    (EnvironmentNamedSection.vacuum : EnvSampleAxis) ≠ .contained := by decide

theorem env_sample_axes_distinct_vacuum_messy :
    (EnvironmentNamedSection.vacuum : EnvSampleAxis) ≠ .messy := by decide

theorem env_sample_axes_distinct_contained_messy :
    (EnvironmentNamedSection.contained : EnvSampleAxis) ≠ .messy := by decide

/-- All three env sample axes are pairwise distinct (not XOR pick-one). -/
theorem env_sample_axes_all_distinct :
    (EnvironmentNamedSection.vacuum : EnvSampleAxis) ≠ .contained ∧
    (EnvironmentNamedSection.vacuum : EnvSampleAxis) ≠ .messy ∧
    (EnvironmentNamedSection.contained : EnvSampleAxis) ≠ .messy := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- Vacuum, contained, messy probes coexist at every scale stratum (simultaneous triple). -/
theorem probe_samples_simultaneous_at_level (f : EnvironmentSheafField) (lvl : ScaleLevel) :
    ∃ v c m,
      probeSample f ⟨.vacuum, lvl⟩ = v ∧
      probeSample f ⟨.contained, lvl⟩ = c ∧
      probeSample f ⟨.messy, lvl⟩ = m :=
  ⟨probeSample f ⟨.vacuum, lvl⟩, probeSample f ⟨.contained, lvl⟩, probeSample f ⟨.messy, lvl⟩,
    rfl, rfl, rfl⟩

/-- Probe at vacuum axis through SCALE leg source matches source stratum vacuum probe. -/
theorem probe_vacuum_at_leg_source_quantum_to_meso (f : EnvironmentSheafField) :
    probeSample f ⟨.vacuum, scaleLegQuantumToMeso.source⟩ =
      f.atQuantum.vacuum.probe.probe := rfl

/-- Probe at contained axis through SCALE leg target matches target stratum contained probe. -/
theorem probe_contained_at_leg_target_meso_to_macro (f : EnvironmentSheafField) :
    probeSample f ⟨.contained, scaleLegMesoToMacro.target⟩ =
      f.atMacro.contained.probe.probe := rfl

/-- Probe at messy axis through direct SCALE leg source matches quantum messy probe. -/
theorem probe_messy_at_leg_source_quantum_to_macro_direct (f : EnvironmentSheafField) :
    probeSample f ⟨.messy, scaleLegQuantumToMacroDirect.source⟩ =
      f.atQuantum.messy.probe.probe := rfl

/-- Ambient knowing probes read zero probe coordinate (Unwired placeholder). -/
theorem probe_sample_ambient_vacuum_quantum :
    probeSample environmentSheafFieldAmbient probeVacuumAtQuantum = 0 := rfl

theorem probe_sample_ambient_contained_meso :
    probeSample environmentSheafFieldAmbient probeContainedAtMeso = 0 := rfl

theorem probe_sample_ambient_messy_macro :
    probeSample environmentSheafFieldAmbient probeMessyAtMacro = 0 := rfl

/-- Cardinality of env sample axes matches named section count (simultaneous triple). -/
theorem env_sample_axis_cardinality_matches :
    environmentSectionCardinality = 3 ∧
    environmentNamedSectionTag .vacuum = "vacuum" ∧
    environmentNamedSectionTag .contained = "contained" ∧
    environmentNamedSectionTag .messy = "messy" :=
  environment_named_section_cardinality_matches

/-- Environment section has all three sample probes present (not XOR). -/
theorem environment_section_has_all_probes (s : EnvironmentSheafSection) :
    ∃ v c m, s.vacuum = v ∧ s.contained = c ∧ s.messy = m :=
  environment_sections_named_not_xor s

/-- Environment section at every stratum has all three probes (not XOR). -/
theorem environment_section_has_all_probes_at_level (f : EnvironmentSheafField) (lvl : ScaleLevel) :
    ∃ v c m,
      vacuumSectionAtLevel f lvl = v ∧
      containedSectionAtLevel f lvl = c ∧
      messySectionAtLevel f lvl = m :=
  environment_sections_named_not_xor_at_level f lvl

/-- Knowing probe triple at ambient field — all three axes readable (not XOR). -/
theorem probe_ambient_triple_not_xor :
    probeSample environmentSheafFieldAmbient probeVacuumAtQuantum = 0 ∧
    probeSample environmentSheafFieldAmbient probeContainedAtMeso = 0 ∧
    probeSample environmentSheafFieldAmbient probeMessyAtMacro = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

/-- Physics knowing-probe equality is unauthorized on the knowing scaffold. -/
def environmentSampleProbeEqualityAuthorized (_p : KnowingProbe) : Prop := False

theorem environment_sample_probe_equality_physics_green_false (p : KnowingProbe) :
    ¬ environmentSampleProbeEqualityAuthorized p := id

/-- Physics GREEN is unauthorized on environment sample knowing probes. -/
def environmentSampleSectionsPhysicsGreenAuthorized (_p : KnowingProbe) : Prop := False

theorem environment_sample_sections_physics_green_false (p : KnowingProbe) :
    ¬ environmentSampleSectionsPhysicsGreenAuthorized p := id

end UMST.Chem

-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic
import ChemGeometry

/-!
# SurfaceBulkSdf — knowing-fiber surface vs bulk SDF geometry (Q lattice)

Surface vs bulk is a **geometry / SDF sign distinction** on `ElementElectronic` rows, not a
parallel chem axiom or duplicate element row. Pairs `umst-chem` scaffold `CHEM-L0-EDGE-SURFACE`.

- Reuses `ChemGeometry` `classifyEdgeSurface` (bulk-negative / surface-positive convention).
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for surface vs bulk SDF claims (TYPE-03 preview). -/
inductive SurfaceBulkModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def surfaceBulkModalityCurrent : SurfaceBulkModality := .unwired

/-- Named SDF sign variants for L0 surface vs bulk (Unwired — no SDF GREEN). -/
inductive SurfaceBulkSdfVariant where
  | bulkNegative | interfaceZero | surfacePositive
  deriving DecidableEq, Repr

/-- Binding of an SDF geometry variant to its parent `ElementElectronic` row. -/
structure SurfaceBulkBinding where
  parent : ElementElectronic
  variant : SurfaceBulkSdfVariant
  deriving Repr

/-- Parent atomic number — invariant across surface vs bulk variants. -/
def surfaceBulkElement (b : SurfaceBulkBinding) : AtomicNumber := b.parent.Z

theorem surface_bulk_binding_same_element (a b : SurfaceBulkBinding)
    (h : surfaceBulkElement a = surfaceBulkElement b) :
    a.parent.Z = b.parent.Z := h

theorem surface_bulk_variant_distinct_bulk_surface :
    SurfaceBulkSdfVariant.bulkNegative ≠ SurfaceBulkSdfVariant.surfacePositive := by
  decide

theorem surface_bulk_variant_distinct_bulk_interface :
    SurfaceBulkSdfVariant.bulkNegative ≠ SurfaceBulkSdfVariant.interfaceZero := by
  decide

theorem surface_bulk_variant_distinct_interface_surface :
    SurfaceBulkSdfVariant.interfaceZero ≠ SurfaceBulkSdfVariant.surfacePositive := by
  decide

/-- Bulk-negative leg of the EDGE-SURFACE sign convention. -/
def surfaceBulkBulkLeg : SurfaceBulkSdfVariant := .bulkNegative

/-- Interface-zero leg of the EDGE-SURFACE sign convention. -/
def surfaceBulkInterfaceLeg : SurfaceBulkSdfVariant := .interfaceZero

/-- Surface-positive leg of the EDGE-SURFACE sign convention. -/
def surfaceBulkSurfaceLeg : SurfaceBulkSdfVariant := .surfacePositive

theorem surface_bulk_bulk_leg_named :
    surfaceBulkBulkLeg = SurfaceBulkSdfVariant.bulkNegative := rfl

theorem surface_bulk_interface_leg_named :
    surfaceBulkInterfaceLeg = SurfaceBulkSdfVariant.interfaceZero := rfl

theorem surface_bulk_surface_leg_named :
    surfaceBulkSurfaceLeg = SurfaceBulkSdfVariant.surfacePositive := rfl

theorem surface_bulk_bulk_surface_legs_distinct :
    surfaceBulkBulkLeg ≠ surfaceBulkSurfaceLeg := by
  decide

/-- Map a named SDF variant to the corresponding `EdgeSurfaceRegime`. -/
def surfaceBulkRegimeOfVariant : SurfaceBulkSdfVariant → EdgeSurfaceRegime
  | .bulkNegative => .bulk
  | .interfaceZero => .interface
  | .surfacePositive => .surface

theorem surface_bulk_regime_bulk_named :
    surfaceBulkRegimeOfVariant .bulkNegative = EdgeSurfaceRegime.bulk := rfl

theorem surface_bulk_regime_surface_named :
    surfaceBulkRegimeOfVariant .surfacePositive = EdgeSurfaceRegime.surface := rfl

theorem surface_bulk_regime_interface_named :
    surfaceBulkRegimeOfVariant .interfaceZero = EdgeSurfaceRegime.interface := rfl

/-- SCALE + EDGE-SURFACE surface vs bulk witness indexed by element + SDF variant (Unwired). -/
structure SurfaceBulkSdf where
  binding : SurfaceBulkBinding
  scaleModality : ChemGeometryModality
  edgeModality : ChemGeometryModality
  surfaceBulkModality : SurfaceBulkModality
  deriving Repr

/-- Electronic identity on the knowing fiber. -/
def surfaceBulkElectronic (s : SurfaceBulkSdf) : ElementElectronic := s.binding.parent

/-- Named SDF variant on the surface vs bulk scaffold. -/
def surfaceBulkVariant (s : SurfaceBulkSdf) : SurfaceBulkSdfVariant := s.binding.variant

def surfaceBulkSdfUnwired (e : ElementElectronic) (v : SurfaceBulkSdfVariant) : SurfaceBulkSdf :=
  { binding := { parent := e, variant := v }
    scaleModality := chemGeometryModalityCurrent
    edgeModality := chemGeometryModalityCurrent
    surfaceBulkModality := surfaceBulkModalityCurrent }

theorem surface_bulk_modality_unwired (s : SurfaceBulkSdf) :
    s.scaleModality = chemGeometryModalityCurrent ∧
    s.edgeModality = chemGeometryModalityCurrent ∧
    s.surfaceBulkModality = surfaceBulkModalityCurrent ↔
      s.scaleModality = .unwired ∧
      s.edgeModality = .unwired ∧
      s.surfaceBulkModality = .unwired := by
  simp [chemGeometryModalityCurrent, surfaceBulkModalityCurrent]

theorem surface_bulk_same_element_distinct_variant
    (e : ElementElectronic) (v1 v2 : SurfaceBulkSdfVariant) (_hne : v1 ≠ v2) :
    surfaceBulkElement { parent := e, variant := v1 } =
      surfaceBulkElement { parent := e, variant := v2 } := rfl

theorem surface_bulk_lattice_anchor (s : SurfaceBulkSdf) :
    madelungPriority s.binding.parent.occupied =
      madelungPriority s.binding.parent.occupied := rfl

theorem surface_bulk_classify_bulk_of_neg {sdf : ℝ} (h : sdf < 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.bulk :=
  classifyEdgeSurface_bulk_of_neg h

theorem surface_bulk_classify_surface_of_pos {sdf : ℝ} (hneg : ¬ sdf < 0) (hne : sdf ≠ 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.surface :=
  classifyEdgeSurface_surface_of_pos hneg hne

theorem surface_bulk_variant_matches_classify_bulk {sdf : ℝ} (h : sdf < 0) :
    surfaceBulkRegimeOfVariant .bulkNegative = classifyEdgeSurface sdf := by
  rw [surface_bulk_regime_bulk_named, surface_bulk_classify_bulk_of_neg h]

theorem surface_bulk_variant_matches_classify_surface {sdf : ℝ} (hneg : ¬ sdf < 0) (hne : sdf ≠ 0) :
    surfaceBulkRegimeOfVariant .surfacePositive = classifyEdgeSurface sdf := by
  rw [surface_bulk_regime_surface_named, surface_bulk_classify_surface_of_pos hneg hne]

/-- Physics GREEN is unauthorized on the knowing surface vs bulk SDF scaffold. -/
def surfaceBulkPhysicsGreenAuthorized (_s : SurfaceBulkSdf) : Prop := False

theorem surface_bulk_physics_green_false (s : SurfaceBulkSdf) :
    ¬ surfaceBulkPhysicsGreenAuthorized s := id

def surfaceBulkElementElectronicPhysicsGreenAuthorized (_e : ElementElectronic) : Prop := False

theorem surface_bulk_element_physics_green_false (e : ElementElectronic) :
    ¬ surfaceBulkElementElectronicPhysicsGreenAuthorized e := id

end UMST.Chem

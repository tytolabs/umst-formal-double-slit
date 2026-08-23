-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic
import ChemGeometry

/-!
# AllotropeGeometry — knowing-fiber allotrope geometry variants (Q lattice)

Allotropes are **geometry variants of the same `ElementElectronic`**, not a parallel axiom
or duplicate element row. Pairs `umst-chem` scaffold `CHEM-L0-EDGE-ALLOTROPE`.

- Reuses `ChemGeometry` SCALE + EDGE-SURFACE modality (Unwired).
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for allotrope geometry claims (TYPE-03 preview). -/
inductive AllotropeModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def allotropeModalityCurrent : AllotropeModality := .unwired

/-- Named geometry-variant placeholders for L0 allotropes (Unwired — no SDF GREEN). -/
inductive AllotropeGeometryVariant where
  | crystallineLattice | layeredGraphitic | amorphousDisordered
  deriving DecidableEq, Repr

/-- Binding of a geometry variant to its parent `ElementElectronic` row. -/
structure AllotropeBinding where
  parent : ElementElectronic
  variant : AllotropeGeometryVariant
  deriving Repr

/-- Parent atomic number — invariant across allotrope variants. -/
def allotropeElement (b : AllotropeBinding) : AtomicNumber := b.parent.Z

theorem allotrope_binding_same_element (a b : AllotropeBinding) (h : allotropeElement a = allotropeElement b) :
    a.parent.Z = b.parent.Z := h

theorem allotrope_variant_distinct_crystalline_amorphous :
    AllotropeGeometryVariant.crystallineLattice ≠ AllotropeGeometryVariant.amorphousDisordered := by
  decide

/-- SCALE + EDGE-SURFACE allotrope geometry witness indexed by element + variant (Unwired). -/
structure AllotropeGeometry where
  binding : AllotropeBinding
  scaleModality : ChemGeometryModality
  edgeModality : ChemGeometryModality
  allotropeModality : AllotropeModality
  deriving Repr

def allotropeGeometryUnwired (e : ElementElectronic) (v : AllotropeGeometryVariant) : AllotropeGeometry :=
  { binding := { parent := e, variant := v }
    scaleModality := chemGeometryModalityCurrent
    edgeModality := chemGeometryModalityCurrent
    allotropeModality := allotropeModalityCurrent }

theorem allotrope_geometry_modality_unwired (g : AllotropeGeometry) :
    g.scaleModality = chemGeometryModalityCurrent ∧
    g.edgeModality = chemGeometryModalityCurrent ∧
    g.allotropeModality = allotropeModalityCurrent ↔
      g.scaleModality = .unwired ∧
      g.edgeModality = .unwired ∧
      g.allotropeModality = .unwired := by
  simp [chemGeometryModalityCurrent, allotropeModalityCurrent]

theorem allotrope_same_element_distinct_variant
    (e : ElementElectronic) (v1 v2 : AllotropeGeometryVariant) (_hne : v1 ≠ v2) :
    allotropeElement { parent := e, variant := v1 } =
      allotropeElement { parent := e, variant := v2 } := rfl

theorem allotrope_geometry_lattice_anchor (g : AllotropeGeometry) :
    madelungPriority g.binding.parent.occupied =
      madelungPriority g.binding.parent.occupied := rfl

theorem allotrope_classify_bulk_of_neg {sdf : ℝ} (h : sdf < 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.bulk :=
  classifyEdgeSurface_bulk_of_neg h

theorem allotrope_classify_surface_of_pos {sdf : ℝ} (hneg : ¬ sdf < 0) (hne : sdf ≠ 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.surface :=
  classifyEdgeSurface_surface_of_pos hneg hne

/-- Physics GREEN is unauthorized on the knowing allotrope scaffold. -/
def allotropePhysicsGreenAuthorized (_g : AllotropeGeometry) : Prop := False

theorem allotrope_geometry_physics_green_false (g : AllotropeGeometry) :
    ¬ allotropePhysicsGreenAuthorized g := id

def allotropeElementElectronicPhysicsGreenAuthorized (_e : ElementElectronic) : Prop := False

theorem allotrope_element_physics_green_false (e : ElementElectronic) :
    ¬ allotropeElementElectronicPhysicsGreenAuthorized e := id

end UMST.Chem

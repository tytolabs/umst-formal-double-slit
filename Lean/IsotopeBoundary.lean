-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT

import ElementElectronic
import ChemGeometry

/-!
# IsotopeBoundary — knowing-fiber nuclear vs electronic boundary honesty (Q lattice)

Isotopes are **nuclear variants of the same `ElementElectronic`**, not a parallel chem axiom
or duplicate element row. Pairs `umst-chem` scaffold `CHEM-L0-EDGE-ISOTOPE`.

- The nuclear vs electronic boundary is **named** (`IsotopeBoundaryLeg`), not chem GREEN.
- Reuses `ChemGeometry` SCALE + EDGE-SURFACE modality (Unwired).
- No meso / acting theorems. No new physics `axiom`.
- `physics_green` stays false.
-/

namespace UMST.Chem

/-- Design modality for isotope boundary claims (TYPE-03 preview). -/
inductive IsotopeModality where
  | unwired | assumed | proved | surrogate
  deriving DecidableEq, Repr

def isotopeModalityCurrent : IsotopeModality := .unwired

/-- Named legs of the nuclear vs electronic boundary (Born–Oppenheimer split scaffold). -/
inductive IsotopeBoundaryLeg where
  | electronic | nuclear
  deriving DecidableEq, Repr

/-- Named nuclear mass variants for L0 isotopes (Unwired — no SDF GREEN). -/
inductive IsotopeNuclearVariant where
  | lightStable | heavyStable | radioactiveTrace
  deriving DecidableEq, Repr

/-- Binding of a nuclear variant to its parent `ElementElectronic` row. -/
structure IsotopeBinding where
  parent : ElementElectronic
  variant : IsotopeNuclearVariant
  deriving Repr

/-- Parent atomic number — invariant across isotope variants. -/
def isotopeElement (b : IsotopeBinding) : AtomicNumber := b.parent.Z

theorem isotope_binding_same_element (a b : IsotopeBinding) (h : isotopeElement a = isotopeElement b) :
    a.parent.Z = b.parent.Z := h

theorem isotope_boundary_leg_distinct :
    IsotopeBoundaryLeg.electronic ≠ IsotopeBoundaryLeg.nuclear := by
  decide

theorem isotope_variant_distinct_light_radioactive :
    IsotopeNuclearVariant.lightStable ≠ IsotopeNuclearVariant.radioactiveTrace := by
  decide

/-- Electronic side of the named boundary. -/
def isotopeBoundaryElectronicLeg : IsotopeBoundaryLeg := .electronic

/-- Nuclear side of the named boundary. -/
def isotopeBoundaryNuclearLeg : IsotopeBoundaryLeg := .nuclear

/-- SCALE + EDGE-SURFACE isotope boundary witness indexed by element + nuclear variant (Unwired). -/
structure IsotopeBoundary where
  binding : IsotopeBinding
  scaleModality : ChemGeometryModality
  edgeModality : ChemGeometryModality
  isotopeModality : IsotopeModality
  deriving Repr

/-- Electronic identity on the knowing side of the boundary. -/
def isotopeBoundaryElectronic (b : IsotopeBoundary) : ElementElectronic := b.binding.parent

/-- Nuclear variant on the named nuclear side of the boundary. -/
def isotopeBoundaryNuclear (b : IsotopeBoundary) : IsotopeNuclearVariant := b.binding.variant

def isotopeBoundaryUnwired (e : ElementElectronic) (v : IsotopeNuclearVariant) : IsotopeBoundary :=
  { binding := { parent := e, variant := v }
    scaleModality := chemGeometryModalityCurrent
    edgeModality := chemGeometryModalityCurrent
    isotopeModality := isotopeModalityCurrent }

theorem isotope_boundary_modality_unwired (b : IsotopeBoundary) :
    b.scaleModality = chemGeometryModalityCurrent ∧
    b.edgeModality = chemGeometryModalityCurrent ∧
    b.isotopeModality = isotopeModalityCurrent ↔
      b.scaleModality = .unwired ∧
      b.edgeModality = .unwired ∧
      b.isotopeModality = .unwired := by
  simp [chemGeometryModalityCurrent, isotopeModalityCurrent]

theorem isotope_same_element_distinct_variant
    (e : ElementElectronic) (v1 v2 : IsotopeNuclearVariant) (_hne : v1 ≠ v2) :
    isotopeElement { parent := e, variant := v1 } =
      isotopeElement { parent := e, variant := v2 } := rfl

theorem isotope_boundary_electronic_leg_named :
    isotopeBoundaryElectronicLeg = IsotopeBoundaryLeg.electronic := rfl

theorem isotope_boundary_nuclear_leg_named :
    isotopeBoundaryNuclearLeg = IsotopeBoundaryLeg.nuclear := rfl

theorem isotope_boundary_legs_named_distinct :
    isotopeBoundaryElectronicLeg ≠ isotopeBoundaryNuclearLeg := by
  decide

theorem isotope_boundary_lattice_anchor (b : IsotopeBoundary) :
    madelungPriority b.binding.parent.occupied =
      madelungPriority b.binding.parent.occupied := rfl

theorem isotope_classify_bulk_of_neg {sdf : ℝ} (h : sdf < 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.bulk :=
  classifyEdgeSurface_bulk_of_neg h

theorem isotope_classify_surface_of_pos {sdf : ℝ} (hneg : ¬ sdf < 0) (hne : sdf ≠ 0) :
    classifyEdgeSurface sdf = EdgeSurfaceRegime.surface :=
  classifyEdgeSurface_surface_of_pos hneg hne

/-- Physics GREEN is unauthorized on the knowing isotope boundary scaffold. -/
def isotopePhysicsGreenAuthorized (_b : IsotopeBoundary) : Prop := False

theorem isotope_boundary_physics_green_false (b : IsotopeBoundary) :
    ¬ isotopePhysicsGreenAuthorized b := id

def isotopeElementElectronicPhysicsGreenAuthorized (_e : ElementElectronic) : Prop := False

theorem isotope_element_physics_green_false (e : ElementElectronic) :
    ¬ isotopeElementElectronicPhysicsGreenAuthorized e := id

end UMST.Chem

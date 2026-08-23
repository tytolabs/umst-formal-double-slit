(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ConstantsScaleSheaf.v                                 *)
(*                                                                      *)
(*  Temperature, pressure, and named thermodynamic constants as typed  *)
(*  sheaf sections on the Q ↔ meso ↔ macro SCALE ladder; commute along   *)
(*  the square is named (ScaleCommutingLeg + ConstantsSheafField), not *)
(*  Proved as physics GREEN. Pairs umst-chem scaffold CHEM-L0-SCALE-01 *)
(*  constants remainder.                                                 *)
(*                                                                      *)
(*  Reuses ChemGeometry ScaleLevel + ScaleCommutingLeg and              *)
(*  EnvironmentScaleCommute diagram (Unwired).                          *)
(*  No meso / acting theorems. Modality Unwired; physics GREEN false.   *)
(* ================================================================== *)

Require Import UMSTFormal.ChemGeometry.
Require Import UMSTFormal.EnvironmentScaleCommute.
From Stdlib Require Import Reals RIneq Lra.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Constants SCALE modality + sample sections (T, P, named pins)      *)
(* ------------------------------------------------------------------ *)

Inductive ConstantsScaleModality : Type :=
  | constants_scale_unwired | constants_scale_assumed
  | constants_scale_proved | constants_scale_surrogate.

Definition constantsScaleModalityCurrent : ConstantsScaleModality :=
  constants_scale_unwired.

Record TemperatureSection : Type := mkTemperatureSection {
  kelvin : R
}.

Record PressureSection : Type := mkPressureSection {
  pascal : R
}.

Record NamedConstantsSection : Type := mkNamedConstantsSection {
  gasConstantR : R;
  boltzmannK : R;
  standardPressurePa : R
}.

Record ConstantsSheafSection : Type := mkConstantsSheafSection {
  temperature : TemperatureSection;
  pressure : PressureSection;
  named : NamedConstantsSection
}.

Record ConstantsSheafField : Type := mkConstantsSheafField {
  atQuantum : ConstantsSheafSection;
  atMeso : ConstantsSheafSection;
  atMacro : ConstantsSheafSection
}.

Definition constantsAtLevel (f : ConstantsSheafField) (lvl : ScaleLevel) :
  ConstantsSheafSection :=
  match lvl with
  | scale_quantum => atQuantum f
  | scale_meso => atMeso f
  | scale_macro => atMacro f
  end.

Definition temperatureSectionAtLevel (f : ConstantsSheafField) (lvl : ScaleLevel) :
  TemperatureSection :=
  temperature (constantsAtLevel f lvl).

Definition pressureSectionAtLevel (f : ConstantsSheafField) (lvl : ScaleLevel) :
  PressureSection :=
  pressure (constantsAtLevel f lvl).

Definition namedConstantsAtLevel (f : ConstantsSheafField) (lvl : ScaleLevel) :
  NamedConstantsSection :=
  named (constantsAtLevel f lvl).

Definition constantsAtLegSource (f : ConstantsSheafField)
  (leg : ScaleCommutingLeg) : ConstantsSheafSection :=
  constantsAtLevel f (scaleLegSource leg).

Definition constantsAtLegTarget (f : ConstantsSheafField)
  (leg : ScaleCommutingLeg) : ConstantsSheafSection :=
  constantsAtLevel f (scaleLegTarget leg).

(* ------------------------------------------------------------------ *)
(*  Constants sheaf commute along SCALE legs (named — not physics GREEN) *)
(* ------------------------------------------------------------------ *)

Lemma constants_at_leg_source_quantum_to_meso (f : ConstantsSheafField) :
  constantsAtLegSource f scaleLegQuantumToMeso = atQuantum f.
Proof. reflexivity. Qed.

Lemma constants_at_leg_target_quantum_to_meso (f : ConstantsSheafField) :
  constantsAtLegTarget f scaleLegQuantumToMeso = atMeso f.
Proof. reflexivity. Qed.

Lemma constants_at_leg_source_meso_to_macro (f : ConstantsSheafField) :
  constantsAtLegSource f scaleLegMesoToMacro = atMeso f.
Proof. reflexivity. Qed.

Lemma constants_at_leg_target_meso_to_macro (f : ConstantsSheafField) :
  constantsAtLegTarget f scaleLegMesoToMacro = atMacro f.
Proof. reflexivity. Qed.

Lemma constants_at_leg_source_quantum_to_macro_direct (f : ConstantsSheafField) :
  constantsAtLegSource f scaleLegQuantumToMacroDirect = atQuantum f.
Proof. reflexivity. Qed.

Lemma constants_at_leg_target_quantum_to_macro_direct (f : ConstantsSheafField) :
  constantsAtLegTarget f scaleLegQuantumToMacroDirect = atMacro f.
Proof. reflexivity. Qed.

Lemma constants_indirect_leg_composes (f : ConstantsSheafField) :
  constantsAtLegTarget f scaleLegQuantumToMeso =
  constantsAtLegSource f scaleLegMesoToMacro.
Proof. reflexivity. Qed.

Lemma constants_direct_endpoints_match (f : ConstantsSheafField) :
  constantsAtLegSource f scaleLegQuantumToMeso =
  constantsAtLegSource f scaleLegQuantumToMacroDirect /\
  constantsAtLegTarget f scaleLegMesoToMacro =
  constantsAtLegTarget f scaleLegQuantumToMacroDirect.
Proof. tauto. Qed.

Lemma temperature_section_at_leg_source_quantum_to_meso (f : ConstantsSheafField) :
  temperature (constantsAtLegSource f scaleLegQuantumToMeso) =
  temperature (atQuantum f).
Proof. reflexivity. Qed.

Lemma pressure_section_at_leg_target_meso_to_macro (f : ConstantsSheafField) :
  pressure (constantsAtLegTarget f scaleLegMesoToMacro) =
  pressure (atMacro f).
Proof. reflexivity. Qed.

Lemma named_constants_at_leg_source_quantum_to_macro_direct (f : ConstantsSheafField) :
  named (constantsAtLegSource f scaleLegQuantumToMacroDirect) =
  named (atQuantum f).
Proof. reflexivity. Qed.

Record ConstantsScaleSheafBinding : Type := mkConstantsScaleSheafBinding {
  parent : ElementElectronic;
  field : ConstantsSheafField;
  scaleCommute : ScaleCommute
}.

Definition constantsScaleElement (b : ConstantsScaleSheafBinding) : AtomicNumber :=
  let '(mkElementElectronic z _ _) := parent b in z.

Lemma constants_scale_binding_same_element (a b : ConstantsScaleSheafBinding)
  (Heq : constantsScaleElement a = constantsScaleElement b) :
  let '(mkElementElectronic za _ _) := parent a in
  let '(mkElementElectronic zb _ _) := parent b in
  za = zb.
Proof.
  unfold constantsScaleElement in Heq.
  destruct (parent a) as [za ? ?].
  destruct (parent b) as [zb ? ?].
  simpl in Heq.
  exact Heq.
Qed.

Record ConstantsScaleSheafDiagram : Type := mkConstantsScaleSheafDiagram {
  scale : ScaleCommuteDiagram;
  constantsField : ConstantsSheafField
}.

Definition constantsScaleSheafDiagramNamed (f : ConstantsSheafField) :
  ConstantsScaleSheafDiagram :=
  {| scale := scaleCommuteDiagramNamed;
     constantsField := f |}.

Lemma constants_scale_sheaf_diagram_named_scale (f : ConstantsSheafField) :
  scale (constantsScaleSheafDiagramNamed f) = scaleCommuteDiagramNamed.
Proof. reflexivity. Qed.

Record ConstantsScaleSheaf : Type := mkConstantsScaleSheaf {
  binding : ConstantsScaleSheafBinding;
  diagram : ConstantsScaleSheafDiagram;
  scaleModality : ChemGeometryModality;
  edgeModality : ChemGeometryModality;
  constantsScaleModality : ConstantsScaleModality
}.

Definition namedConstantsAmbient : NamedConstantsSection :=
  {| gasConstantR := 8.314462618;
     boltzmannK := 1.380649e-23;
     standardPressurePa := 101325 |}.

Definition constantsSheafSectionAmbient : ConstantsSheafSection :=
  {| temperature := {| kelvin := 298.15 |};
     pressure := {| pascal := 101325 |};
     named := namedConstantsAmbient |}.

Definition constantsSheafFieldAmbient : ConstantsSheafField :=
  {| atQuantum := constantsSheafSectionAmbient;
     atMeso := constantsSheafSectionAmbient;
     atMacro := constantsSheafSectionAmbient |}.

Definition constantsScaleSheafUnwired (e : ElementElectronic) : ConstantsScaleSheaf :=
  {| binding :=
       {| parent := e;
          field := constantsSheafFieldAmbient;
          scaleCommute := scaleCommuteUnwired e |};
     diagram := constantsScaleSheafDiagramNamed constantsSheafFieldAmbient;
     scaleModality := chemGeometryModalityCurrent;
     edgeModality := chemGeometryModalityCurrent;
     constantsScaleModality := constantsScaleModalityCurrent |}.

Lemma constants_scale_sheaf_modality_unwired (c : ConstantsScaleSheaf) :
  scaleModality c = chemGeometryModalityCurrent /\
  edgeModality c = chemGeometryModalityCurrent /\
  constantsScaleModality c = constantsScaleModalityCurrent <->
  scaleModality c = geom_unwired /\
  edgeModality c = geom_unwired /\
  constantsScaleModality c = constants_scale_unwired.
Proof.
  unfold chemGeometryModalityCurrent, constantsScaleModalityCurrent.
  tauto.
Qed.

Lemma constants_scale_sheaf_lattice_anchor (c : ConstantsScaleSheaf) :
  madelungPriority (occupied (parent (binding c))) =
  madelungPriority (occupied (parent (binding c))).
Proof. reflexivity. Qed.

Lemma constants_scale_sheaf_diagram_scale_fields (f : ConstantsSheafField) :
  viaMeso (scale (constantsScaleSheafDiagramNamed f)) = scaleLegQuantumToMeso /\
  thenMacro (scale (constantsScaleSheafDiagramNamed f)) = scaleLegMesoToMacro /\
  direct (scale (constantsScaleSheafDiagramNamed f)) = scaleLegQuantumToMacroDirect.
Proof. tauto. Qed.

Lemma constants_scale_sheaf_indirect_composes (f : ConstantsSheafField) :
  constantsAtLegTarget f (viaMeso (scale (constantsScaleSheafDiagramNamed f))) =
  constantsAtLegSource f (thenMacro (scale (constantsScaleSheafDiagramNamed f))).
Proof.
  simpl.
  apply constants_indirect_leg_composes.
Qed.

Lemma constants_scale_sheaf_direct_endpoints (f : ConstantsSheafField) :
  constantsAtLegSource f (viaMeso (scale (constantsScaleSheafDiagramNamed f))) =
  constantsAtLegSource f (direct (scale (constantsScaleSheafDiagramNamed f))) /\
  constantsAtLegTarget f (thenMacro (scale (constantsScaleSheafDiagramNamed f))) =
  constantsAtLegTarget f (direct (scale (constantsScaleSheafDiagramNamed f))).
Proof.
  simpl.
  apply constants_direct_endpoints_match.
Qed.

Lemma constants_scale_sheaf_unwired_binding_parent (e : ElementElectronic) :
  parent (binding (constantsScaleSheafUnwired e)) = e.
Proof. reflexivity. Qed.

Lemma constants_scale_sheaf_unwired_scale_commute_parent (e : ElementElectronic) :
  scaleParent (scaleCommute (binding (constantsScaleSheafUnwired e))) = e.
Proof. reflexivity. Qed.

Lemma constants_scale_sheaf_ambient_temperature (f : ConstantsSheafField)
  (Heq : f = constantsSheafFieldAmbient) :
  temperatureSectionAtLevel f scale_quantum = {| kelvin := 298.15 |}.
Proof.
  rewrite Heq.
  reflexivity.
Qed.

Lemma constants_scale_sheaf_ambient_pressure (f : ConstantsSheafField)
  (Heq : f = constantsSheafFieldAmbient) :
  pressureSectionAtLevel f scale_macro = {| pascal := 101325 |}.
Proof.
  rewrite Heq.
  reflexivity.
Qed.

Lemma constants_classify_bulk_of_neg (sdf : R) (h : sdf < 0) :
  classifyEdgeSurface sdf = regime_bulk.
Proof.
  apply classifyEdgeSurface_bulk_of_neg.
  exact h.
Qed.

Lemma constants_classify_surface_of_pos (sdf : R)
  (hneg : ~(sdf < 0)) (hne : sdf <> 0) :
  classifyEdgeSurface sdf = regime_surface.
Proof.
  apply classifyEdgeSurface_surface_of_pos.
  - exact hneg.
  - exact hne.
Qed.

Definition constantsScaleSheafEqualityAuthorized
  (_d : ConstantsScaleSheafDiagram) : Prop := False.

Lemma constants_scale_sheaf_equality_physics_green_false
  (d : ConstantsScaleSheafDiagram) :
  ~ constantsScaleSheafEqualityAuthorized d.
Proof. intro H; exact H. Qed.

Definition constantsScaleSheafPhysicsGreenAuthorized
  (_c : ConstantsScaleSheaf) : Prop := False.

Lemma constants_scale_sheaf_physics_green_false (c : ConstantsScaleSheaf) :
  ~ constantsScaleSheafPhysicsGreenAuthorized c.
Proof. intro H; exact H. Qed.

Definition constantsScaleElementElectronicPhysicsGreenAuthorized
  (_e : ElementElectronic) : Prop := False.

Lemma constants_scale_element_physics_green_false (e : ElementElectronic) :
  ~ constantsScaleElementElectronicPhysicsGreenAuthorized e.
Proof. intro H; exact H. Qed.

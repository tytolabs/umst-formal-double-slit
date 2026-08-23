(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: EnvironmentScaleCommute.v                             *)
(*                                                                      *)
(*  Quantum / knowing fiber preview for environment SCALE sheaf:        *)
(*    - Vacuum / contained / messy as simultaneous sample sections      *)
(*      (not XOR — all three present in each EnvironmentSection)        *)
(*    - Env sheaf sections commute Q ↔ meso ↔ macro as knowing probes   *)
(*    - Reuses ChemGeometry ScaleLevel + ScaleCommutingLeg (Unwired)    *)
(*                                                                      *)
(*  No meso / acting theorems. Modality Unwired; physics GREEN false.   *)
(* ================================================================== *)

Require Import UMSTFormal.ChemGeometry.
From Stdlib Require Import Reals RIneq Lra.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Environment modality + sample sections (not XOR)                     *)
(* ------------------------------------------------------------------ *)

Inductive EnvironmentScaleModality : Type :=
  | env_scale_unwired | env_scale_assumed
  | env_scale_proved | env_scale_surrogate.

Definition environmentScaleModalityCurrent : EnvironmentScaleModality :=
  env_scale_unwired.

Inductive EnvSampleAxis : Type :=
  | env_axis_vacuum | env_axis_contained | env_axis_messy.

Lemma env_sample_axes_distinct_vacuum_contained :
  env_axis_vacuum <> env_axis_contained.
Proof. discriminate. Qed.

Lemma env_sample_axes_distinct_vacuum_messy :
  env_axis_vacuum <> env_axis_messy.
Proof. discriminate. Qed.

Lemma env_sample_axes_distinct_contained_messy :
  env_axis_contained <> env_axis_messy.
Proof. discriminate. Qed.

Record VacuumSample : Type := mkVacuumSample {
  residualPO2Pa : R
}.

Record ContainedSample : Type := mkContainedSample {
  kelvin : R;
  pascal : R
}.

Record MessySample : Type := mkMessySample {
  oreGradeFraction : R;
  impurityFraction : R
}.

(* All three sample sections coexist — not an exclusive env choice. *)
Record EnvironmentSection : Type := mkEnvironmentSection {
  vacuum : VacuumSample;
  contained : ContainedSample;
  messy : MessySample
}.

Lemma environment_section_has_all_samples (s : EnvironmentSection) :
  vacuum s = vacuum s /\
  contained s = contained s /\
  messy s = messy s.
Proof. tauto. Qed.

Record EnvironmentSheafField : Type := mkEnvironmentSheafField {
  atQuantum : EnvironmentSection;
  atMeso : EnvironmentSection;
  atMacro : EnvironmentSection
}.

Definition environmentAtLevel (f : EnvironmentSheafField) (lvl : ScaleLevel) :
  EnvironmentSection :=
  match lvl with
  | scale_quantum => atQuantum f
  | scale_meso => atMeso f
  | scale_macro => atMacro f
  end.

Definition vacuumSampleAtLevel (f : EnvironmentSheafField) (lvl : ScaleLevel) :
  VacuumSample :=
  vacuum (environmentAtLevel f lvl).

Definition containedSampleAtLevel (f : EnvironmentSheafField) (lvl : ScaleLevel) :
  ContainedSample :=
  contained (environmentAtLevel f lvl).

Definition messySampleAtLevel (f : EnvironmentSheafField) (lvl : ScaleLevel) :
  MessySample :=
  messy (environmentAtLevel f lvl).

Definition environmentAtLegSource (f : EnvironmentSheafField)
  (leg : ScaleCommutingLeg) : EnvironmentSection :=
  environmentAtLevel f (scaleLegSource leg).

Definition environmentAtLegTarget (f : EnvironmentSheafField)
  (leg : ScaleCommutingLeg) : EnvironmentSection :=
  environmentAtLevel f (scaleLegTarget leg).

(* ------------------------------------------------------------------ *)
(*  Knowing probes — env sample axis × scale stratum                    *)
(* ------------------------------------------------------------------ *)

Record KnowingProbe : Type := mkKnowingProbe {
  axis : EnvSampleAxis;
  scale : ScaleLevel
}.

Definition probeVacuumAtQuantum : KnowingProbe :=
  {| axis := env_axis_vacuum; scale := scale_quantum |}.

Definition probeContainedAtMeso : KnowingProbe :=
  {| axis := env_axis_contained; scale := scale_meso |}.

Definition probeMessyAtMacro : KnowingProbe :=
  {| axis := env_axis_messy; scale := scale_macro |}.

Definition probeSample (f : EnvironmentSheafField) (p : KnowingProbe) : R :=
  match axis p, scale p with
  | env_axis_vacuum, lvl => residualPO2Pa (vacuumSampleAtLevel f lvl)
  | env_axis_contained, lvl => kelvin (containedSampleAtLevel f lvl)
  | env_axis_messy, lvl => oreGradeFraction (messySampleAtLevel f lvl)
  end.

Lemma probe_vacuum_at_quantum_named (f : EnvironmentSheafField) :
  probeSample f probeVacuumAtQuantum =
  residualPO2Pa (vacuum (atQuantum f)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SCALE commute diagram (named legs — equality not Proved)           *)
(* ------------------------------------------------------------------ *)

Definition scaleLegQuantumToMeso : ScaleCommutingLeg := leg_quantum_to_meso.
Definition scaleLegMesoToMacro : ScaleCommutingLeg := leg_meso_to_macro.
Definition scaleLegQuantumToMacroDirect : ScaleCommutingLeg :=
  leg_quantum_to_macro_direct.

Record ScaleCommuteDiagram : Type := mkScaleCommuteDiagram {
  viaMeso : ScaleCommutingLeg;
  thenMacro : ScaleCommutingLeg;
  direct : ScaleCommutingLeg
}.

Definition scaleCommuteDiagramNamed : ScaleCommuteDiagram :=
  {| viaMeso := scaleLegQuantumToMeso;
     thenMacro := scaleLegMesoToMacro;
     direct := scaleLegQuantumToMacroDirect |}.

Lemma scale_commute_diagram_named_fields :
  viaMeso scaleCommuteDiagramNamed = scaleLegQuantumToMeso /\
  thenMacro scaleCommuteDiagramNamed = scaleLegMesoToMacro /\
  direct scaleCommuteDiagramNamed = scaleLegQuantumToMacroDirect.
Proof. tauto. Qed.

Lemma scale_leg_indirect_composes_levels :
  scaleLegTarget scaleLegQuantumToMeso = scaleLegSource scaleLegMesoToMacro.
Proof. reflexivity. Qed.

Lemma scale_leg_direct_endpoints_match :
  scaleLegSource scaleLegQuantumToMeso = scaleLegSource scaleLegQuantumToMacroDirect /\
  scaleLegTarget scaleLegMesoToMacro = scaleLegTarget scaleLegQuantumToMacroDirect.
Proof. tauto. Qed.

(* ------------------------------------------------------------------ *)
(*  Env sheaf commute along SCALE legs (named — not physics GREEN)      *)
(* ------------------------------------------------------------------ *)

Lemma environment_at_leg_source_quantum_to_meso (f : EnvironmentSheafField) :
  environmentAtLegSource f scaleLegQuantumToMeso = atQuantum f.
Proof. reflexivity. Qed.

Lemma environment_at_leg_target_quantum_to_meso (f : EnvironmentSheafField) :
  environmentAtLegTarget f scaleLegQuantumToMeso = atMeso f.
Proof. reflexivity. Qed.

Lemma environment_at_leg_source_meso_to_macro (f : EnvironmentSheafField) :
  environmentAtLegSource f scaleLegMesoToMacro = atMeso f.
Proof. reflexivity. Qed.

Lemma environment_at_leg_target_meso_to_macro (f : EnvironmentSheafField) :
  environmentAtLegTarget f scaleLegMesoToMacro = atMacro f.
Proof. reflexivity. Qed.

Lemma environment_at_leg_source_quantum_to_macro_direct (f : EnvironmentSheafField) :
  environmentAtLegSource f scaleLegQuantumToMacroDirect = atQuantum f.
Proof. reflexivity. Qed.

Lemma environment_at_leg_target_quantum_to_macro_direct (f : EnvironmentSheafField) :
  environmentAtLegTarget f scaleLegQuantumToMacroDirect = atMacro f.
Proof. reflexivity. Qed.

Lemma environment_indirect_leg_composes (f : EnvironmentSheafField) :
  environmentAtLegTarget f scaleLegQuantumToMeso =
  environmentAtLegSource f scaleLegMesoToMacro.
Proof. reflexivity. Qed.

Lemma environment_direct_endpoints_match (f : EnvironmentSheafField) :
  environmentAtLegSource f scaleLegQuantumToMeso =
  environmentAtLegSource f scaleLegQuantumToMacroDirect /\
  environmentAtLegTarget f scaleLegMesoToMacro =
  environmentAtLegTarget f scaleLegQuantumToMacroDirect.
Proof. tauto. Qed.

Lemma vacuum_sample_at_leg_source_quantum_to_meso (f : EnvironmentSheafField) :
  vacuum (environmentAtLegSource f scaleLegQuantumToMeso) =
  vacuum (atQuantum f).
Proof. reflexivity. Qed.

Lemma contained_sample_at_leg_target_meso_to_macro (f : EnvironmentSheafField) :
  contained (environmentAtLegTarget f scaleLegMesoToMacro) =
  contained (atMacro f).
Proof. reflexivity. Qed.

Lemma messy_sample_at_leg_source_quantum_to_macro_direct (f : EnvironmentSheafField) :
  messy (environmentAtLegSource f scaleLegQuantumToMacroDirect) =
  messy (atQuantum f).
Proof. reflexivity. Qed.

Record ScaleCommute : Type := mkScaleCommute {
  scaleParent : ElementElectronic;
  scaleDiagram : ScaleCommuteDiagram;
  scScaleModality : ChemGeometryModality;
  scEdgeModality : ChemGeometryModality
}.

Definition scaleCommuteUnwired (e : ElementElectronic) : ScaleCommute :=
  {| scaleParent := e;
     scaleDiagram := scaleCommuteDiagramNamed;
     scScaleModality := chemGeometryModalityCurrent;
     scEdgeModality := chemGeometryModalityCurrent |}.

Record EnvironmentScaleSheafDiagram : Type := mkEnvironmentScaleSheafDiagram {
  scaleDiag : ScaleCommuteDiagram;
  envField : EnvironmentSheafField
}.

Definition environmentScaleSheafDiagramNamed (f : EnvironmentSheafField) :
  EnvironmentScaleSheafDiagram :=
  {| scaleDiag := scaleCommuteDiagramNamed;
     envField := f |}.

Lemma environment_scale_sheaf_diagram_named_scale (f : EnvironmentSheafField) :
  scaleDiag (environmentScaleSheafDiagramNamed f) = scaleCommuteDiagramNamed.
Proof. reflexivity. Qed.

Record EnvironmentScaleSheafBinding : Type := mkEnvironmentScaleSheafBinding {
  parent : ElementElectronic;
  field : EnvironmentSheafField;
  scaleCommute : ScaleCommute
}.

Definition environmentScaleElement (b : EnvironmentScaleSheafBinding) : AtomicNumber :=
  let '(mkElementElectronic z _ _) := parent b in z.

Lemma environment_scale_binding_same_element (a b : EnvironmentScaleSheafBinding)
  (Heq : environmentScaleElement a = environmentScaleElement b) :
  let '(mkElementElectronic za _ _) := parent a in
  let '(mkElementElectronic zb _ _) := parent b in
  za = zb.
Proof.
  unfold environmentScaleElement in Heq.
  destruct (parent a) as [za ? ?].
  destruct (parent b) as [zb ? ?].
  simpl in Heq.
  exact Heq.
Qed.

Record EnvironmentScaleCommute : Type := mkEnvironmentScaleCommute {
  escBinding : EnvironmentScaleSheafBinding;
  escDiagram : EnvironmentScaleSheafDiagram;
  escScaleModality : ChemGeometryModality;
  escEdgeModality : ChemGeometryModality;
  environmentScaleModality : EnvironmentScaleModality
}.

Definition vacuumSampleAmbient : VacuumSample := {| residualPO2Pa := 0 |}.
Definition containedSampleAmbient : ContainedSample :=
  {| kelvin := 298.15; pascal := 101325 |}.
Definition messySampleAmbient : MessySample :=
  {| oreGradeFraction := 0; impurityFraction := 0 |}.

Definition environmentSectionAmbient : EnvironmentSection :=
  {| vacuum := vacuumSampleAmbient;
     contained := containedSampleAmbient;
     messy := messySampleAmbient |}.

Definition environmentSheafFieldAmbient : EnvironmentSheafField :=
  {| atQuantum := environmentSectionAmbient;
     atMeso := environmentSectionAmbient;
     atMacro := environmentSectionAmbient |}.

Definition environmentScaleCommuteUnwired (e : ElementElectronic) :
  EnvironmentScaleCommute :=
  {| escBinding :=
       {| parent := e;
          field := environmentSheafFieldAmbient;
          scaleCommute := scaleCommuteUnwired e |};
     escDiagram := environmentScaleSheafDiagramNamed environmentSheafFieldAmbient;
     escScaleModality := chemGeometryModalityCurrent;
     escEdgeModality := chemGeometryModalityCurrent;
     environmentScaleModality := environmentScaleModalityCurrent |}.

Lemma environment_scale_commute_modality_unwired (c : EnvironmentScaleCommute) :
  escScaleModality c = chemGeometryModalityCurrent /\
  escEdgeModality c = chemGeometryModalityCurrent /\
  environmentScaleModality c = environmentScaleModalityCurrent <->
  escScaleModality c = geom_unwired /\
  escEdgeModality c = geom_unwired /\
  environmentScaleModality c = env_scale_unwired.
Proof.
  unfold chemGeometryModalityCurrent, environmentScaleModalityCurrent.
  tauto.
Qed.

Lemma environment_scale_commute_lattice_anchor (c : EnvironmentScaleCommute) :
  madelungPriority (occupied (parent (escBinding c))) =
  madelungPriority (occupied (parent (escBinding c))).
Proof. reflexivity. Qed.

Lemma environment_scale_sheaf_indirect_composes (f : EnvironmentSheafField) :
  environmentAtLegTarget f (viaMeso (scaleDiag (environmentScaleSheafDiagramNamed f))) =
  environmentAtLegSource f (thenMacro (scaleDiag (environmentScaleSheafDiagramNamed f))).
Proof.
  simpl.
  apply environment_indirect_leg_composes.
Qed.

Lemma environment_scale_sheaf_direct_endpoints (f : EnvironmentSheafField) :
  environmentAtLegSource f (viaMeso (scaleDiag (environmentScaleSheafDiagramNamed f))) =
  environmentAtLegSource f (direct (scaleDiag (environmentScaleSheafDiagramNamed f))) /\
  environmentAtLegTarget f (thenMacro (scaleDiag (environmentScaleSheafDiagramNamed f))) =
  environmentAtLegTarget f (direct (scaleDiag (environmentScaleSheafDiagramNamed f))).
Proof.
  simpl.
  apply environment_direct_endpoints_match.
Qed.

Lemma environment_scale_commute_unwired_binding_parent (e : ElementElectronic) :
  parent (escBinding (environmentScaleCommuteUnwired e)) = e.
Proof. reflexivity. Qed.

Lemma environment_scale_commute_ambient_vacuum (f : EnvironmentSheafField)
  (Heq : f = environmentSheafFieldAmbient) :
  vacuumSampleAtLevel f scale_quantum = vacuumSampleAmbient.
Proof.
  rewrite Heq.
  reflexivity.
Qed.

Lemma environment_scale_commute_ambient_contained (f : EnvironmentSheafField)
  (Heq : f = environmentSheafFieldAmbient) :
  containedSampleAtLevel f scale_macro = containedSampleAmbient.
Proof.
  rewrite Heq.
  reflexivity.
Qed.

Definition environmentSectionAllSamples (s : EnvironmentSection) :
  VacuumSample * ContainedSample * MessySample :=
  (vacuum s, contained s, messy s).

Lemma environment_sections_coexist_not_xor (s : EnvironmentSection) :
  environmentSectionAllSamples s = (vacuum s, contained s, messy s).
Proof. reflexivity. Qed.

Lemma environment_classify_bulk_of_neg (sdf : R) (h : sdf < 0) :
  classifyEdgeSurface sdf = regime_bulk.
Proof.
  apply classifyEdgeSurface_bulk_of_neg.
  exact h.
Qed.

Lemma environment_classify_surface_of_pos (sdf : R)
  (hneg : ~(sdf < 0)) (hne : sdf <> 0) :
  classifyEdgeSurface sdf = regime_surface.
Proof.
  apply classifyEdgeSurface_surface_of_pos.
  - exact hneg.
  - exact hne.
Qed.

Definition environmentScaleSheafEqualityAuthorized
  (_d : EnvironmentScaleSheafDiagram) : Prop := False.

Lemma environment_scale_sheaf_equality_physics_green_false
  (d : EnvironmentScaleSheafDiagram) :
  ~ environmentScaleSheafEqualityAuthorized d.
Proof. intro H; exact H. Qed.

Definition environmentScaleCommutePhysicsGreenAuthorized
  (_c : EnvironmentScaleCommute) : Prop := False.

Lemma environment_scale_commute_physics_green_false (c : EnvironmentScaleCommute) :
  ~ environmentScaleCommutePhysicsGreenAuthorized c.
Proof. intro H; exact H. Qed.

Definition environmentScaleElementElectronicPhysicsGreenAuthorized
  (_e : ElementElectronic) : Prop := False.

Lemma environment_scale_element_physics_green_false (e : ElementElectronic) :
  ~ environmentScaleElementElectronicPhysicsGreenAuthorized e.
Proof. intro H; exact H. Qed.

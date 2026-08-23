(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: AllotropeGeometry.v                                  *)
(*                                                                      *)
(*  Quantum / knowing fiber preview for L0 allotrope geometry:          *)
(*    - Same ElementElectronic identity, distinct geometry variants     *)
(*    - SCALE ladder + EDGE-SURFACE sign convention (typed scaffold)  *)
(*    - Madelung / Q-lattice hooks from ChemGeometry                    *)
(*                                                                      *)
(*  No meso / acting theorems. Modality Unwired; physics GREEN false.   *)
(* ================================================================== *)

Require Import UMSTFormal.ChemGeometry.
From Stdlib Require Import Reals RIneq Lra.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Allotrope modality + named geometry variants (knowing fiber)       *)
(* ------------------------------------------------------------------ *)

Inductive AllotropeModality : Type :=
  | allotrope_unwired | allotrope_assumed
  | allotrope_proved | allotrope_surrogate.

Definition allotropeModalityCurrent : AllotropeModality := allotrope_unwired.

Inductive AllotropeGeometryVariant : Type :=
  | variant_crystalline_lattice
  | variant_layered_graphitic
  | variant_amorphous_disordered.

Record AllotropeBinding : Type := mkAllotropeBinding {
  parent : ElementElectronic;
  variant : AllotropeGeometryVariant
}.

Definition allotropeElement (b : AllotropeBinding) : AtomicNumber :=
  let '(mkElementElectronic z _ _) := parent b in z.

Lemma allotrope_binding_same_element (a b : AllotropeBinding) :
  allotropeElement a = allotropeElement b ->
  let '(mkElementElectronic za _ _) := parent a in
  let '(mkElementElectronic zb _ _) := parent b in
  za = zb.
Proof.
  intros H.
  unfold allotropeElement in H.
  destruct (parent a) as [za ? ?].
  destruct (parent b) as [zb ? ?].
  simpl in H.
  exact H.
Qed.

Lemma allotrope_variant_distinct_crystalline_amorphous :
  variant_crystalline_lattice <> variant_amorphous_disordered.
Proof.
  discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Allotrope geometry witness (Unwired scaffold)                        *)
(* ------------------------------------------------------------------ *)

Record AllotropeGeometry : Type := mkAllotropeGeometry {
  binding : AllotropeBinding;
  scaleModality : ChemGeometryModality;
  edgeModality : ChemGeometryModality;
  allotropeModality : AllotropeModality
}.

Definition allotropeGeometryUnwired (e : ElementElectronic)
  (v : AllotropeGeometryVariant) : AllotropeGeometry :=
  {| binding := {| parent := e; variant := v |};
     scaleModality := chemGeometryModalityCurrent;
     edgeModality := chemGeometryModalityCurrent;
     allotropeModality := allotropeModalityCurrent |}.

Lemma allotrope_geometry_modality_unwired (g : AllotropeGeometry) :
  scaleModality g = chemGeometryModalityCurrent /\
  edgeModality g = chemGeometryModalityCurrent /\
  allotropeModality g = allotropeModalityCurrent <->
  scaleModality g = geom_unwired /\
  edgeModality g = geom_unwired /\
  allotropeModality g = allotrope_unwired.
Proof.
  unfold chemGeometryModalityCurrent, allotropeModalityCurrent.
  tauto.
Qed.

Lemma allotrope_same_element_distinct_variant
  (e : ElementElectronic) (v1 v2 : AllotropeGeometryVariant)
  (Hne : v1 <> v2) :
  allotropeElement (mkAllotropeBinding e v1) =
  allotropeElement (mkAllotropeBinding e v2).
Proof.
  reflexivity.
Qed.

Lemma allotrope_geometry_lattice_anchor (g : AllotropeGeometry) :
  madelungPriority (occupied (parent (binding g))) =
  madelungPriority (occupied (parent (binding g))).
Proof.
  reflexivity.
Qed.

(* EDGE-SURFACE regime reuse for allotrope surface vs bulk scaffold. *)

Lemma allotrope_classify_bulk_of_neg (sdf : R) (h : sdf < 0) :
  classifyEdgeSurface sdf = regime_bulk.
Proof.
  apply classifyEdgeSurface_bulk_of_neg.
  exact h.
Qed.

Lemma allotrope_classify_surface_of_pos (sdf : R)
  (hneg : ~(sdf < 0)) (hne : sdf <> 0) :
  classifyEdgeSurface sdf = regime_surface.
Proof.
  apply classifyEdgeSurface_surface_of_pos.
  - exact hneg.
  - exact hne.
Qed.

Definition allotropePhysicsGreenAuthorized (_g : AllotropeGeometry) : Prop := False.

Lemma allotrope_geometry_physics_green_false (g : AllotropeGeometry) :
  ~ allotropePhysicsGreenAuthorized g.
Proof. intro H; exact H. Qed.

Definition allotropeElementElectronicPhysicsGreenAuthorized
  (_e : ElementElectronic) : Prop := False.

Lemma allotrope_element_physics_green_false (e : ElementElectronic) :
  ~ allotropeElementElectronicPhysicsGreenAuthorized e.
Proof. intro H; exact H. Qed.

(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ChemGeometry.v                                       *)
(*                                                                      *)
(*  Quantum / knowing fiber preview for L0 chemistry (CHEM-FORMAL-Q):  *)
(*    - Q-lattice occupied cell (n, ℓ, m_ℓ, m_s) with hydrogenic bounds *)
(*    - SCALE ladder legs (typed; commute not Proved)                   *)
(*    - EDGE-SURFACE SDF sign convention (bulk / interface / surface)   *)
(*                                                                      *)
(*  No meso / acting theorems. Modality Unwired; physics GREEN false.   *)
(* ================================================================== *)

From Stdlib Require Import ZArith Arith Lia Reals RIneq Lra.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Electronic / Q-lattice (knowing primary discrete identity)         *)
(* ------------------------------------------------------------------ *)

Inductive ElectronicModality : Type :=
  | electronic_unwired | electronic_assumed
  | electronic_proved | electronic_surrogate.

Definition electronicModalityCurrent : ElectronicModality := electronic_unwired.

Inductive SpinProjection : Type := spin_down | spin_up.

Inductive OrbitalLetter : Type := orbital_s | orbital_p | orbital_d | orbital_f.

Definition orbitalLetter (ell : nat) : OrbitalLetter :=
  match ell with
  | 0 => orbital_s
  | 1 => orbital_p
  | 2 => orbital_d
  | _ => orbital_f
  end.

Record QLatticeCell : Type := mkQLatticeCell {
  n : nat;
  hn : (0 < n)%nat;
  ell : nat;
  hell : (ell < n)%nat;
  mEll : Z;
  hmEll : (Z.abs mEll <= Z.of_nat ell)%Z;
  spin : SpinProjection
}.

Definition madelungPriority (q : QLatticeCell) : nat := n q + ell q.

Lemma madelungPriority_pos (q : QLatticeCell) : (0 < madelungPriority q)%nat.
Proof.
  unfold madelungPriority.
  apply Nat.lt_lt_add_r.
  exact (hn q).
Qed.

Definition hydrogen1s : QLatticeCell :=
  {| n := 1;
     hn := Nat.lt_0_1;
     ell := 0;
     hell := Nat.lt_0_1;
     mEll := 0;
     hmEll := Z.le_refl 0;
     spin := spin_down |}.

Lemma hydrogen1s_madelung : madelungPriority hydrogen1s = 1%nat.
Proof. reflexivity. Qed.

Record AtomicNumber : Type := mkAtomicNumber {
  z : nat;
  hz_lo : (0 < z)%nat;
  hz_hi : (z <= 118)%nat
}.

Definition atomicNumber (z : nat) (hz_lo : (0 < z)%nat) (hz_hi : (z <= 118)%nat) :
  AtomicNumber := {| z := z; hz_lo := hz_lo; hz_hi := hz_hi |}.

Record ElementElectronic : Type := mkElementElectronic {
  Z : AtomicNumber;
  occupied : QLatticeCell;
  modality : ElectronicModality
}.

Lemma elementElectronic_modality_unwired (e : ElementElectronic) :
  modality e = electronicModalityCurrent <-> modality e = electronic_unwired.
Proof.
  split; intro H.
  - unfold electronicModalityCurrent in H. exact H.
  - rewrite H. reflexivity.
Qed.

Definition physicsGreenAuthorizedElectronic (_e : ElementElectronic) : Prop := False.

Lemma physics_green_false_electronic (e : ElementElectronic) :
  ~ physicsGreenAuthorizedElectronic e.
Proof. intro H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(*  SCALE + EDGE-SURFACE geometry (knowing fiber)                       *)
(* ------------------------------------------------------------------ *)

Inductive ScaleLevel : Type := scale_quantum | scale_meso | scale_macro.

Inductive ScaleCommutingLeg : Type :=
  | leg_quantum_to_meso | leg_meso_to_macro | leg_quantum_to_macro_direct.

Definition scaleLegSource (leg : ScaleCommutingLeg) : ScaleLevel :=
  match leg with
  | leg_quantum_to_meso => scale_quantum
  | leg_meso_to_macro => scale_meso
  | leg_quantum_to_macro_direct => scale_quantum
  end.

Definition scaleLegTarget (leg : ScaleCommutingLeg) : ScaleLevel :=
  match leg with
  | leg_quantum_to_meso => scale_meso
  | leg_meso_to_macro => scale_macro
  | leg_quantum_to_macro_direct => scale_macro
  end.

Lemma scale_leg_source_target_distinct (leg : ScaleCommutingLeg) :
  scaleLegSource leg <> scaleLegTarget leg.
Proof.
  destruct leg; discriminate.
Qed.

Inductive ChemGeometryModality : Type :=
  | geom_unwired | geom_assumed | geom_proved | geom_surrogate.

Definition chemGeometryModalityCurrent : ChemGeometryModality := geom_unwired.

Inductive EdgeSurfaceRegime : Type :=
  | regime_bulk | regime_interface | regime_surface.

Definition classifyEdgeSurface (sdf : R) : EdgeSurfaceRegime :=
  if Rlt_dec sdf 0 then regime_bulk
  else if Rgt_dec sdf 0 then regime_surface
  else regime_interface.

Lemma classifyEdgeSurface_bulk_of_neg (sdf : R) (h : sdf < 0) :
  classifyEdgeSurface sdf = regime_bulk.
Proof.
  unfold classifyEdgeSurface.
  destruct (Rlt_dec sdf 0); [reflexivity | lra].
Qed.

Lemma classifyEdgeSurface_surface_of_pos (sdf : R)
  (hneg : ~(sdf < 0)) (hne : sdf <> 0) :
  classifyEdgeSurface sdf = regime_surface.
Proof.
  assert (Hsdf : sdf > 0) by lra.
  unfold classifyEdgeSurface.
  destruct (Rlt_dec sdf 0); [lra |].
  destruct (Rgt_dec sdf 0); [reflexivity | lra].
Qed.

Record ChemGeometry : Type := mkChemGeometry {
  lattice : QLatticeCell;
  scaleModality : ChemGeometryModality;
  edgeModality : ChemGeometryModality
}.

Definition chemGeometryUnwired (q : QLatticeCell) : ChemGeometry :=
  {| lattice := q;
     scaleModality := chemGeometryModalityCurrent;
     edgeModality := chemGeometryModalityCurrent |}.

Lemma chem_geometry_modality_unwired (g : ChemGeometry) :
  scaleModality g = chemGeometryModalityCurrent /\
  edgeModality g = chemGeometryModalityCurrent <->
  scaleModality g = geom_unwired /\ edgeModality g = geom_unwired.
Proof.
  unfold chemGeometryModalityCurrent.
  tauto.
Qed.

Definition chemGeometryPhysicsGreenAuthorized (_g : ChemGeometry) : Prop := False.

Lemma chem_geometry_physics_green_false (g : ChemGeometry) :
  ~ chemGeometryPhysicsGreenAuthorized g.
Proof. intro H; exact H. Qed.

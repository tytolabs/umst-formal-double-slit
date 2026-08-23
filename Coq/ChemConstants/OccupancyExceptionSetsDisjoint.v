(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: OccupancyExceptionSetsDisjoint.v                       *)
(*                                                                      *)
(*  Knowing-fiber Coq composition of Named / Actinide / DBlock          *)
(*  occupancy exception modules. Proves pairwise disjoint Z-sets,       *)
(*  Pu (94) absent from all three lists, Lr (103) actinide-only pin.   *)
(*                                                                      *)
(*  Cites sibling exception lists — not a second axiom, not GREEN DFT.  *)
(*  Modality Unwired. physics_green = False. Zero Admitted.             *)
(* ================================================================== *)

Require Import UMST.ChemConstants.NamedOccupancyExceptions.
Require Import UMST.ChemConstants.ActinideOccupancyExceptions.
Require Import UMST.ChemConstants.DBlockOccupancyExceptions.
From Stdlib Require Import Arith List Lia String.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Occupancy exception sets modality (TYPE-03 preview — Unwired)      *)
(* ------------------------------------------------------------------ *)

Inductive OccupancyExceptionSetsModality : Type :=
  | occupancy_exception_sets_unwired
  | occupancy_exception_sets_assumed
  | occupancy_exception_sets_proved
  | occupancy_exception_sets_surrogate.

Definition occupancyExceptionSetsModalityCurrent : OccupancyExceptionSetsModality :=
  occupancy_exception_sets_unwired.

(* ------------------------------------------------------------------ *)
(*  Z-set projections from sibling finite exception lists                *)
(* ------------------------------------------------------------------ *)

Definition namedExceptionZList : list nat :=
  map NamedException_z namedExceptionList.

Definition actinideExceptionZList : list nat :=
  map ActinideException_z actinideExceptionList.

Definition dBlockExceptionZList : list nat :=
  map DBlockException_z dBlockExceptionList.

Lemma named_exception_z_le_79 (ex : NamedException) :
  NamedException_z ex <= 79%nat.
Proof.
  destruct ex; simpl; lia.
Qed.

Lemma named_exception_z_ge_57 (ex : NamedException) :
  NamedException_z ex >= 57%nat.
Proof.
  destruct ex; simpl; lia.
Qed.

Lemma actinide_exception_z_ge_89 (ex : ActinideException) :
  ActinideException_z ex >= 89%nat.
Proof.
  destruct ex; simpl; lia.
Qed.

Lemma actinide_exception_z_le_103 (ex : ActinideException) :
  ActinideException_z ex <= 103%nat.
Proof.
  destruct ex; simpl; lia.
Qed.

Lemma d_block_exception_z_le_47 (ex : DBlockException) :
  DBlockException_z ex <= 47%nat.
Proof.
  destruct ex; simpl; lia.
Qed.

Lemma in_named_exception_z_le_79 (z : nat) :
  In z namedExceptionZList -> z <= 79%nat.
Proof.
  intro Hz.
  apply in_map_iff in Hz.
  destruct Hz as [ex [Hin Heq]].
  subst z.
  apply named_exception_z_le_79.
Qed.

Lemma in_named_exception_z_ge_57 (z : nat) :
  In z namedExceptionZList -> z >= 57%nat.
Proof.
  intro Hz.
  apply in_map_iff in Hz.
  destruct Hz as [ex [Hin Heq]].
  subst z.
  apply named_exception_z_ge_57.
Qed.

Lemma in_actinide_exception_z_ge_89 (z : nat) :
  In z actinideExceptionZList -> z >= 89%nat.
Proof.
  intro Hz.
  apply in_map_iff in Hz.
  destruct Hz as [ex [Hin Heq]].
  subst z.
  apply actinide_exception_z_ge_89.
Qed.

Lemma in_actinide_exception_z_le_103 (z : nat) :
  In z actinideExceptionZList -> z <= 103%nat.
Proof.
  intro Hz.
  apply in_map_iff in Hz.
  destruct Hz as [ex [Hin Heq]].
  subst z.
  apply actinide_exception_z_le_103.
Qed.

Lemma in_d_block_exception_z_le_47 (z : nat) :
  In z dBlockExceptionZList -> z <= 47%nat.
Proof.
  intro Hz.
  apply in_map_iff in Hz.
  destruct Hz as [ex [Hin Heq]].
  subst z.
  apply d_block_exception_z_le_47.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pairwise disjoint Z-sets (no shared atomic numbers)                 *)
(* ------------------------------------------------------------------ *)

Definition occupancyExceptionZListsDisjoint : Prop :=
  (forall z : nat,
     In z namedExceptionZList ->
     ~ In z actinideExceptionZList /\
     ~ In z dBlockExceptionZList) /\
  (forall z : nat,
     In z actinideExceptionZList ->
     ~ In z namedExceptionZList /\
     ~ In z dBlockExceptionZList) /\
  (forall z : nat,
     In z dBlockExceptionZList ->
     ~ In z namedExceptionZList /\
     ~ In z actinideExceptionZList).

Lemma named_actinide_z_sets_disjoint :
  forall z : nat,
    In z namedExceptionZList -> ~ In z actinideExceptionZList.
Proof.
  intros z Hnamed Hin.
  apply in_actinide_exception_z_ge_89 in Hin.
  apply in_named_exception_z_le_79 in Hnamed.
  lia.
Qed.

Lemma named_d_block_z_sets_disjoint :
  forall z : nat,
    In z namedExceptionZList -> ~ In z dBlockExceptionZList.
Proof.
  intros z Hnamed Hin.
  apply in_d_block_exception_z_le_47 in Hin.
  apply in_named_exception_z_ge_57 in Hnamed.
  lia.
Qed.

Lemma actinide_named_z_sets_disjoint :
  forall z : nat,
    In z actinideExceptionZList -> ~ In z namedExceptionZList.
Proof.
  intros z Hact Hin.
  apply in_named_exception_z_le_79 in Hin.
  apply in_actinide_exception_z_ge_89 in Hact.
  lia.
Qed.

Lemma actinide_d_block_z_sets_disjoint :
  forall z : nat,
    In z actinideExceptionZList -> ~ In z dBlockExceptionZList.
Proof.
  intros z Hact Hin.
  apply in_d_block_exception_z_le_47 in Hin.
  apply in_actinide_exception_z_ge_89 in Hact.
  lia.
Qed.

Lemma d_block_named_z_sets_disjoint :
  forall z : nat,
    In z dBlockExceptionZList -> ~ In z namedExceptionZList.
Proof.
  intros z Hd Hin.
  apply in_named_exception_z_ge_57 in Hin.
  apply in_d_block_exception_z_le_47 in Hd.
  lia.
Qed.

Lemma d_block_actinide_z_sets_disjoint :
  forall z : nat,
    In z dBlockExceptionZList -> ~ In z actinideExceptionZList.
Proof.
  intros z Hd Hin.
  apply in_actinide_exception_z_ge_89 in Hin.
  apply in_d_block_exception_z_le_47 in Hd.
  lia.
Qed.

Lemma occupancy_exception_z_lists_disjoint :
  occupancyExceptionZListsDisjoint.
Proof.
  split.
  - intros z Hnamed.
    split.
    + apply named_actinide_z_sets_disjoint; exact Hnamed.
    + apply named_d_block_z_sets_disjoint; exact Hnamed.
  - split.
    + intros z Hact.
      split.
      * apply actinide_named_z_sets_disjoint; exact Hact.
      * apply actinide_d_block_z_sets_disjoint; exact Hact.
    + intros z Hd.
      split.
      * apply d_block_named_z_sets_disjoint; exact Hd.
      * apply d_block_actinide_z_sets_disjoint; exact Hd.
Qed.

(* ------------------------------------------------------------------ *)
(*  Pu (Z=94) absent from all three exception Z-lists                    *)
(* ------------------------------------------------------------------ *)

Lemma pu_not_in_named_exception_z_list :
  ~ In 94%nat namedExceptionZList.
Proof.
  intro H.
  apply in_named_exception_z_le_79 in H.
  lia.
Qed.

Lemma pu_not_in_d_block_exception_z_list :
  ~ In 94%nat dBlockExceptionZList.
Proof.
  intro H.
  apply in_d_block_exception_z_le_47 in H.
  lia.
Qed.

Lemma actinide_in_exception_list (ex : ActinideException) :
  In ex actinideExceptionList.
Proof.
  destruct ex; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
  - right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. left. reflexivity.
Qed.

Lemma actinide_exception_z_in_list (ex : ActinideException) :
  In (ActinideException_z ex) actinideExceptionZList.
Proof.
  apply in_map.
  apply actinide_in_exception_list.
Qed.

Lemma actinide_exception_z_one_of (ex : ActinideException) :
  ActinideException_z ex = 89%nat \/
  ActinideException_z ex = 90%nat \/
  ActinideException_z ex = 91%nat \/
  ActinideException_z ex = 92%nat \/
  ActinideException_z ex = 93%nat \/
  ActinideException_z ex = 96%nat \/
  ActinideException_z ex = 103%nat.
Proof.
  destruct ex; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
  - right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. reflexivity.
Qed.

Lemma in_actinide_z_one_of (z : nat) :
  In z actinideExceptionZList ->
  z = 89%nat \/ z = 90%nat \/ z = 91%nat \/ z = 92%nat \/
  z = 93%nat \/ z = 96%nat \/ z = 103%nat.
Proof.
  intro Hz.
  apply in_map_iff in Hz.
  destruct Hz as [ex [Heq Hin]].
  subst z.
  destruct (actinide_exception_z_one_of ex); auto.
Qed.

Lemma pu_not_in_actinide_exception_z_list :
  ~ In 94%nat actinideExceptionZList.
Proof.
  intro H.
  apply in_map_iff in H.
  destruct H as [ex [Heq Hin]].
  subst.
  destruct ex; simpl in Heq |- *; discriminate Heq.
Qed.

Lemma pu_not_in_any_occupancy_exception_z_list :
  ~ In 94%nat namedExceptionZList /\
  ~ In 94%nat actinideExceptionZList /\
  ~ In 94%nat dBlockExceptionZList.
Proof.
  split.
  - apply pu_not_in_named_exception_z_list.
  - split.
    + apply pu_not_in_actinide_exception_z_list.
    + apply pu_not_in_d_block_exception_z_list.
Qed.

(* ------------------------------------------------------------------ *)
(*  Lr (Z=103) actinide list pin — not in NamedException list          *)
(* ------------------------------------------------------------------ *)

Lemma lr_z_in_actinide_exception_z_list :
  In 103%nat actinideExceptionZList.
Proof.
  rewrite <- actinide_exception_lr_z.
  apply (actinide_exception_z_in_list actinide_exception_lr).
Qed.

Lemma lr_not_in_named_exception_z_list :
  ~ In 103%nat namedExceptionZList.
Proof.
  intro H.
  apply in_named_exception_z_le_79 in H.
  lia.
Qed.

Lemma lr_actinide_only_named_absent :
  In 103%nat actinideExceptionZList /\
  ~ In 103%nat namedExceptionZList.
Proof.
  split.
  - apply lr_z_in_actinide_exception_z_list.
  - apply lr_not_in_named_exception_z_list.
Qed.

Lemma lr_z_eq_actinide_exception_lr :
  ActinideException_z actinide_exception_lr = 103%nat.
Proof.
  apply actinide_exception_lr_z.
Qed.

(* ------------------------------------------------------------------ *)
(*  Sibling modality pins (all Unwired — composition witness)          *)
(* ------------------------------------------------------------------ *)

Lemma occupancy_exception_sets_modality_unwired :
  occupancyExceptionSetsModalityCurrent = occupancy_exception_sets_unwired.
Proof. reflexivity. Qed.

Lemma named_occupancy_modality_still_unwired :
  namedOccupancyModalityCurrent = named_occupancy_unwired.
Proof. apply named_occupancy_modality_unwired. Qed.

Lemma actinide_occupancy_modality_still_unwired :
  actinideOccupancyModalityCurrent = actinide_occupancy_unwired.
Proof. apply actinide_occupancy_modality_unwired. Qed.

Lemma d_block_occupancy_modality_still_unwired :
  dBlockOccupancyModalityCurrent = d_block_occupancy_unwired.
Proof. apply d_block_occupancy_modality_unwired. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pins are named here) *)
(* ------------------------------------------------------------------ *)

Definition occupancyExceptionSetsCellId : string :=
  "CHEM-FORMAL-Q-COQ-OCCUPANCY-EXCEPTION-SETS-DISJOINT".

Definition occupancyExceptionSetsNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-OCCUPANCY-EXCEPTION-SETS-DISJOINT knowing-fiber Coq composition Named Actinide DBlock occupancy exception Z-lists pairwise disjoint; Pu 94 absent; Lr 103 actinide-only not NamedException; cites sibling modules not second axiom; not GREEN DFT; not physics GREEN; not production_wired".

Definition occupancyExceptionSetsNamedAuthority : string :=
  namedOccupancyExceptionsCellId.

Definition occupancyExceptionSetsActinideAuthority : string :=
  actinideOccupancyExceptionsCellId.

Definition occupancyExceptionSetsDBlockAuthority : string :=
  dBlockOccupancyExceptionsCellId.

Lemma occupancy_exception_sets_cell_id :
  occupancyExceptionSetsCellId =
  "CHEM-FORMAL-Q-COQ-OCCUPANCY-EXCEPTION-SETS-DISJOINT".
Proof. reflexivity. Qed.

Lemma occupancy_exception_sets_cites_named_cell :
  occupancyExceptionSetsNamedAuthority =
  "CHEM-FORMAL-Q-COQ-NAMED-OCCUPANCY-EXCEPTIONS".
Proof. reflexivity. Qed.

Lemma occupancy_exception_sets_not_second_axiom :
  namedOccupancyMadelungWitnessAuthority <> "".
Proof. apply named_occupancy_not_second_axiom. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition occupancyExceptionSetsPhysicsGreenAuthorized : Prop := False.

Lemma occupancy_exception_sets_physics_green_false :
  ~ occupancyExceptionSetsPhysicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma occupancy_exception_sets_named_physics_green_false :
  ~ namedOccupancyPhysicsGreenAuthorized.
Proof. apply named_occupancy_physics_green_false. Qed.

Lemma occupancy_exception_sets_actinide_physics_green_false :
  ~ actinideOccupancyPhysicsGreenAuthorized.
Proof. apply actinide_occupancy_physics_green_false. Qed.

Lemma occupancy_exception_sets_d_block_physics_green_false :
  ~ dBlockOccupancyPhysicsGreenAuthorized.
Proof. apply d_block_occupancy_physics_green_false. Qed.

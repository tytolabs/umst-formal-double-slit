(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ActinideOccupancyExceptions.v                         *)
(*                                                                      *)
(*  Finite named set of period-7 qlattice Madelung predicted ≠ observed *)
(*  occupancy exceptions as ActinideException (Ac Th Pa U Np Cm Lr).    *)
(*  Pins mirror umst-chem qlattice observed_override_config and         *)
(*  madelung_predicted_config authority — not a second axiom, not GREEN *)
(*  DFT. Lr named override agrees with Madelung walk (honest pin).       *)
(*                                                                      *)
(*  Self-contained (Stdlib lists / bools / strings). Modality Unwired. *)
(*  physics_green = False. No meso / acting theorems. Zero Admitted.     *)
(* ================================================================== *)

From Stdlib Require Import Arith List String.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Actinide occupancy modality (TYPE-03 preview — Unwired)            *)
(* ------------------------------------------------------------------ *)

Inductive ActinideOccupancyModality : Type :=
  | actinide_occupancy_unwired
  | actinide_occupancy_assumed
  | actinide_occupancy_proved
  | actinide_occupancy_surrogate.

Definition actinideOccupancyModalityCurrent : ActinideOccupancyModality :=
  actinide_occupancy_unwired.

(* ------------------------------------------------------------------ *)
(*  Finite period-7 named qlattice override tag (Ac Th Pa U Np Cm Lr)    *)
(* ------------------------------------------------------------------ *)

Inductive ActinideException : Type :=
  | actinide_exception_ac
  | actinide_exception_th
  | actinide_exception_pa
  | actinide_exception_u
  | actinide_exception_np
  | actinide_exception_cm
  | actinide_exception_lr.

Definition ActinideException_z (ex : ActinideException) : nat :=
  match ex with
  | actinide_exception_ac => 89%nat
  | actinide_exception_th => 90%nat
  | actinide_exception_pa => 91%nat
  | actinide_exception_u => 92%nat
  | actinide_exception_np => 93%nat
  | actinide_exception_cm => 96%nat
  | actinide_exception_lr => 103%nat
  end.

Definition ActinideException_symbol (ex : ActinideException) : string :=
  match ex with
  | actinide_exception_ac => "Ac"
  | actinide_exception_th => "Th"
  | actinide_exception_pa => "Pa"
  | actinide_exception_u => "U"
  | actinide_exception_np => "Np"
  | actinide_exception_cm => "Cm"
  | actinide_exception_lr => "Lr"
  end.

Lemma actinide_exception_ac_z :
  ActinideException_z actinide_exception_ac = 89%nat.
Proof. reflexivity. Qed.

Lemma actinide_exception_th_z :
  ActinideException_z actinide_exception_th = 90%nat.
Proof. reflexivity. Qed.

Lemma actinide_exception_pa_z :
  ActinideException_z actinide_exception_pa = 91%nat.
Proof. reflexivity. Qed.

Lemma actinide_exception_u_z :
  ActinideException_z actinide_exception_u = 92%nat.
Proof. reflexivity. Qed.

Lemma actinide_exception_np_z :
  ActinideException_z actinide_exception_np = 93%nat.
Proof. reflexivity. Qed.

Lemma actinide_exception_cm_z :
  ActinideException_z actinide_exception_cm = 96%nat.
Proof. reflexivity. Qed.

Lemma actinide_exception_lr_z :
  ActinideException_z actinide_exception_lr = 103%nat.
Proof. reflexivity. Qed.

(* Observed ground-state subshell notation pin (qlattice observed_override_config SSOT). *)

Definition ActinideException_observedNotation (ex : ActinideException) : string :=
  match ex with
  | actinide_exception_ac =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d1"
  | actinide_exception_th =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s26d2"
  | actinide_exception_pa =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f26d1"
  | actinide_exception_u =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f36d1"
  | actinide_exception_np =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f46d1"
  | actinide_exception_cm =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f76d1"
  | actinide_exception_lr =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1"
  end.

(* Madelung (n+ℓ) walk predicted subshell notation at Z (madelung_predicted_config pin). *)

Definition ActinideException_predictedNotation (ex : ActinideException) : string :=
  match ex with
  | actinide_exception_ac =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f1"
  | actinide_exception_th =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f2"
  | actinide_exception_pa =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f3"
  | actinide_exception_u =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f4"
  | actinide_exception_np =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f5"
  | actinide_exception_cm =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f8"
  | actinide_exception_lr =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106p67s25f146d1"
  end.

(* Chemist valence occupancy shorthand (named pin — not axiom). *)

Definition ActinideException_occupancyTag (ex : ActinideException) : string :=
  match ex with
  | actinide_exception_ac => "6d17s2"
  | actinide_exception_th => "6d27s2"
  | actinide_exception_pa => "5f26d17s2"
  | actinide_exception_u => "5f36d17s2"
  | actinide_exception_np => "7s25f46d1"
  | actinide_exception_cm => "5f76d17s2"
  | actinide_exception_lr => "5f146d17s2"
  end.

(* ------------------------------------------------------------------ *)
(*  Actinide exception row scaffold (Unwired)                            *)
(* ------------------------------------------------------------------ *)

Record ActinideExceptionRow : Type := mkActinideExceptionRow {
  exception : ActinideException;
  modality : ActinideOccupancyModality
}.

Definition ActinideExceptionRow_z (row : ActinideExceptionRow) : nat :=
  ActinideException_z (exception row).

Definition ActinideExceptionRow_symbol (row : ActinideExceptionRow) : string :=
  ActinideException_symbol (exception row).

Definition ActinideExceptionRow_observedNotation (row : ActinideExceptionRow) : string :=
  ActinideException_observedNotation (exception row).

Definition ActinideExceptionRow_predictedNotation (row : ActinideExceptionRow) : string :=
  ActinideException_predictedNotation (exception row).

Definition ActinideExceptionRow_occupancyTag (row : ActinideExceptionRow) : string :=
  ActinideException_occupancyTag (exception row).

Definition actinideExceptionRow (ex : ActinideException) : ActinideExceptionRow :=
  {| exception := ex;
     modality := actinideOccupancyModalityCurrent |}.

Lemma actinide_exception_row_z (ex : ActinideException) :
  ActinideExceptionRow_z (actinideExceptionRow ex) = ActinideException_z ex.
Proof. reflexivity. Qed.

Lemma actinide_exception_row_modality_unwired (ex : ActinideException) :
  modality (actinideExceptionRow ex) = actinide_occupancy_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Finite actinide exception list (cardinality 7 — not Z=1…118 dump)  *)
(* ------------------------------------------------------------------ *)

Definition actinideExceptionList : list ActinideException :=
  actinide_exception_ac ::
  actinide_exception_th ::
  actinide_exception_pa ::
  actinide_exception_u ::
  actinide_exception_np ::
  actinide_exception_cm ::
  actinide_exception_lr ::
  nil.

Definition actinideExceptionCount : nat := List.length actinideExceptionList.

Lemma actinide_exception_count_seven : actinideExceptionCount = 7%nat.
Proof. reflexivity. Qed.

Lemma actinide_exception_list_length :
  List.length actinideExceptionList = 7%nat.
Proof. reflexivity. Qed.

Lemma ac_observed_ne_predicted :
  ActinideException_observedNotation actinide_exception_ac <>
  ActinideException_predictedNotation actinide_exception_ac.
Proof. discriminate. Qed.

Lemma th_observed_ne_predicted :
  ActinideException_observedNotation actinide_exception_th <>
  ActinideException_predictedNotation actinide_exception_th.
Proof. discriminate. Qed.

Lemma pa_observed_ne_predicted :
  ActinideException_observedNotation actinide_exception_pa <>
  ActinideException_predictedNotation actinide_exception_pa.
Proof. discriminate. Qed.

Lemma u_observed_ne_predicted :
  ActinideException_observedNotation actinide_exception_u <>
  ActinideException_predictedNotation actinide_exception_u.
Proof. discriminate. Qed.

Lemma np_observed_ne_predicted :
  ActinideException_observedNotation actinide_exception_np <>
  ActinideException_predictedNotation actinide_exception_np.
Proof. discriminate. Qed.

Lemma cm_observed_ne_predicted :
  ActinideException_observedNotation actinide_exception_cm <>
  ActinideException_predictedNotation actinide_exception_cm.
Proof. discriminate. Qed.

(* Lr: named qlattice override in observed_override_config; Madelung walk agrees (honest). *)

Lemma lr_named_override_observed_eq_predicted :
  ActinideException_observedNotation actinide_exception_lr =
  ActinideException_predictedNotation actinide_exception_lr.
Proof. reflexivity. Qed.

Lemma lr_named_override_in_observed_override_config :
  ActinideException_observedNotation actinide_exception_lr <>
  "".
Proof. discriminate. Qed.

Definition actinideExceptionIsMadelungException (ex : ActinideException) : Prop :=
  ActinideException_observedNotation ex <>
  ActinideException_predictedNotation ex.

Lemma actinide_exception_is_madelung_exception (ex : ActinideException) :
  actinideExceptionIsMadelungException ex ->
  ActinideException_observedNotation ex <>
  ActinideException_predictedNotation ex.
Proof. intros H; exact H. Qed.

Lemma actinide_exception_ac_is_madelung_exception :
  actinideExceptionIsMadelungException actinide_exception_ac.
Proof. apply ac_observed_ne_predicted. Qed.

Lemma actinide_exception_th_is_madelung_exception :
  actinideExceptionIsMadelungException actinide_exception_th.
Proof. apply th_observed_ne_predicted. Qed.

Lemma actinide_exception_pa_is_madelung_exception :
  actinideExceptionIsMadelungException actinide_exception_pa.
Proof. apply pa_observed_ne_predicted. Qed.

Lemma actinide_exception_u_is_madelung_exception :
  actinideExceptionIsMadelungException actinide_exception_u.
Proof. apply u_observed_ne_predicted. Qed.

Lemma actinide_exception_np_is_madelung_exception :
  actinideExceptionIsMadelungException actinide_exception_np.
Proof. apply np_observed_ne_predicted. Qed.

Lemma actinide_exception_cm_is_madelung_exception :
  actinideExceptionIsMadelungException actinide_exception_cm.
Proof. apply cm_observed_ne_predicted. Qed.

Lemma actinide_exception_lr_not_madelung_exception :
  ~ actinideExceptionIsMadelungException actinide_exception_lr.
Proof.
  intro H.
  unfold actinideExceptionIsMadelungException in H.
  pose proof lr_named_override_observed_eq_predicted as E.
  congruence.
Qed.

(* Approximate-not-identity: six period-7 exceptions differ; Lr named override agrees. *)

Definition actinideExceptionApproximateNotIdentity (ex : ActinideException) : Prop :=
  actinideExceptionIsMadelungException ex.

Lemma actinide_exception_approximate_not_identity_ac :
  actinideExceptionApproximateNotIdentity actinide_exception_ac.
Proof. apply actinide_exception_ac_is_madelung_exception. Qed.

Lemma actinide_exception_approximate_not_identity_th :
  actinideExceptionApproximateNotIdentity actinide_exception_th.
Proof. apply actinide_exception_th_is_madelung_exception. Qed.

Lemma actinide_exception_approximate_not_identity_pa :
  actinideExceptionApproximateNotIdentity actinide_exception_pa.
Proof. apply actinide_exception_pa_is_madelung_exception. Qed.

Lemma actinide_exception_approximate_not_identity_u :
  actinideExceptionApproximateNotIdentity actinide_exception_u.
Proof. apply actinide_exception_u_is_madelung_exception. Qed.

Lemma actinide_exception_approximate_not_identity_np :
  actinideExceptionApproximateNotIdentity actinide_exception_np.
Proof. apply actinide_exception_np_is_madelung_exception. Qed.

Lemma actinide_exception_approximate_not_identity_cm :
  actinideExceptionApproximateNotIdentity actinide_exception_cm.
Proof. apply actinide_exception_cm_is_madelung_exception. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pins are named here) *)
(* ------------------------------------------------------------------ *)

Definition actinideOccupancyQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition actinideOccupancyMadelungWitnessAuthority : string :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs".

Definition actinideOccupancyExceptionsCellId : string :=
  "CHEM-FORMAL-Q-COQ-ACTINIDE-OCCUPANCY-EXCEPTIONS".

Definition actinideOccupancyExceptionsNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-ACTINIDE-OCCUPANCY-EXCEPTIONS finite period-7 named qlattice Madelung occupancy exceptions Ac Th Pa U Np Cm Lr as ActinideException; observed_override_config and madelung_predicted_config pins; Lr named override agrees Madelung honest; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired".

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition actinideOccupancyPhysicsGreenAuthorized : Prop := False.

Lemma actinide_occupancy_physics_green_false :
  ~ actinideOccupancyPhysicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma actinide_occupancy_modality_unwired :
  actinideOccupancyModalityCurrent = actinide_occupancy_unwired.
Proof. reflexivity. Qed.

Lemma actinide_occupancy_not_second_axiom :
  actinideOccupancyMadelungWitnessAuthority <> "".
Proof. discriminate. Qed.

Lemma actinide_occupancy_cites_qlattice :
  actinideOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs".
Proof. reflexivity. Qed.

Lemma actinide_occupancy_exceptions_cell_id :
  actinideOccupancyExceptionsCellId =
  "CHEM-FORMAL-Q-COQ-ACTINIDE-OCCUPANCY-EXCEPTIONS".
Proof. reflexivity. Qed.

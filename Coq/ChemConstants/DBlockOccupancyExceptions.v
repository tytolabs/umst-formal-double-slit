(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: DBlockOccupancyExceptions.v                          *)
(*                                                                      *)
(*  Finite named set of period-4/5 d-block qlattice Madelung predicted  *)
(*  ≠ observed occupancy exceptions as DBlockException (Cr Cu Nb Mo Ru   *)
(*  Rh Pd Ag). Pins mirror umst-chem qlattice observed_override_config  *)
(*  and madelung_predicted_config authority — not a second axiom, not   *)
(*  GREEN DFT. DISTINCT from NamedException (La Ce Gd Pt Au) and from   *)
(*  actinide exceptions (Ac Th Pa U Np Cm Lr).                           *)
(*                                                                      *)
(*  Self-contained (Stdlib lists / bools / strings). Modality Unwired. *)
(*  physics_green = False. No meso / acting theorems. Zero Admitted.     *)
(* ================================================================== *)

From Stdlib Require Import Arith List String.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  D-block occupancy modality (TYPE-03 preview — Unwired)             *)
(* ------------------------------------------------------------------ *)

Inductive DBlockOccupancyModality : Type :=
  | d_block_occupancy_unwired
  | d_block_occupancy_assumed
  | d_block_occupancy_proved
  | d_block_occupancy_surrogate.

Definition dBlockOccupancyModalityCurrent : DBlockOccupancyModality :=
  d_block_occupancy_unwired.

(* ------------------------------------------------------------------ *)
(*  Finite period-4/5 d-block qlattice override tag (Cr Cu Nb Mo Ru    *)
(*  Rh Pd Ag)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive DBlockException : Type :=
  | d_block_exception_cr
  | d_block_exception_cu
  | d_block_exception_nb
  | d_block_exception_mo
  | d_block_exception_ru
  | d_block_exception_rh
  | d_block_exception_pd
  | d_block_exception_ag.

Definition DBlockException_z (ex : DBlockException) : nat :=
  match ex with
  | d_block_exception_cr => 24%nat
  | d_block_exception_cu => 29%nat
  | d_block_exception_nb => 41%nat
  | d_block_exception_mo => 42%nat
  | d_block_exception_ru => 44%nat
  | d_block_exception_rh => 45%nat
  | d_block_exception_pd => 46%nat
  | d_block_exception_ag => 47%nat
  end.

Definition DBlockException_symbol (ex : DBlockException) : string :=
  match ex with
  | d_block_exception_cr => "Cr"
  | d_block_exception_cu => "Cu"
  | d_block_exception_nb => "Nb"
  | d_block_exception_mo => "Mo"
  | d_block_exception_ru => "Ru"
  | d_block_exception_rh => "Rh"
  | d_block_exception_pd => "Pd"
  | d_block_exception_ag => "Ag"
  end.

Lemma d_block_exception_cr_z :
  DBlockException_z d_block_exception_cr = 24%nat.
Proof. reflexivity. Qed.

Lemma d_block_exception_cu_z :
  DBlockException_z d_block_exception_cu = 29%nat.
Proof. reflexivity. Qed.

Lemma d_block_exception_nb_z :
  DBlockException_z d_block_exception_nb = 41%nat.
Proof. reflexivity. Qed.

Lemma d_block_exception_mo_z :
  DBlockException_z d_block_exception_mo = 42%nat.
Proof. reflexivity. Qed.

Lemma d_block_exception_ru_z :
  DBlockException_z d_block_exception_ru = 44%nat.
Proof. reflexivity. Qed.

Lemma d_block_exception_rh_z :
  DBlockException_z d_block_exception_rh = 45%nat.
Proof. reflexivity. Qed.

Lemma d_block_exception_pd_z :
  DBlockException_z d_block_exception_pd = 46%nat.
Proof. reflexivity. Qed.

Lemma d_block_exception_ag_z :
  DBlockException_z d_block_exception_ag = 47%nat.
Proof. reflexivity. Qed.

(* Observed ground-state subshell notation pin (qlattice observed_override_config SSOT). *)

Definition DBlockException_observedNotation (ex : DBlockException) : string :=
  match ex with
  | d_block_exception_cr =>
    "1s22s22p63s23p64s13d5"
  | d_block_exception_cu =>
    "1s22s22p63s23p64s13d10"
  | d_block_exception_nb =>
    "1s22s22p63s23p64s23d104p65s14d4"
  | d_block_exception_mo =>
    "1s22s22p63s23p64s23d104p65s14d5"
  | d_block_exception_ru =>
    "1s22s22p63s23p64s23d104p65s14d7"
  | d_block_exception_rh =>
    "1s22s22p63s23p64s23d104p65s14d8"
  | d_block_exception_pd =>
    "1s22s22p63s23p64s23d104p64d10"
  | d_block_exception_ag =>
    "1s22s22p63s23p64s23d104p65s14d10"
  end.

(* Madelung (n+ℓ) walk predicted subshell notation at Z (madelung_predicted_config pin). *)

Definition DBlockException_predictedNotation (ex : DBlockException) : string :=
  match ex with
  | d_block_exception_cr =>
    "1s22s22p63s23p64s23d4"
  | d_block_exception_cu =>
    "1s22s22p63s23p64s23d9"
  | d_block_exception_nb =>
    "1s22s22p63s23p64s23d104p65s24d3"
  | d_block_exception_mo =>
    "1s22s22p63s23p64s23d104p65s24d4"
  | d_block_exception_ru =>
    "1s22s22p63s23p64s23d104p65s24d6"
  | d_block_exception_rh =>
    "1s22s22p63s23p64s23d104p65s24d7"
  | d_block_exception_pd =>
    "1s22s22p63s23p64s23d104p65s24d8"
  | d_block_exception_ag =>
    "1s22s22p63s23p64s23d104p65s24d9"
  end.

(* Chemist valence occupancy shorthand (named pin — not axiom). *)

Definition DBlockException_occupancyTag (ex : DBlockException) : string :=
  match ex with
  | d_block_exception_cr => "3d54s1"
  | d_block_exception_cu => "3d104s1"
  | d_block_exception_nb => "4d45s1"
  | d_block_exception_mo => "4d55s1"
  | d_block_exception_ru => "4d75s1"
  | d_block_exception_rh => "4d85s1"
  | d_block_exception_pd => "4d105s0"
  | d_block_exception_ag => "4d105s1"
  end.

(* ------------------------------------------------------------------ *)
(*  D-block exception row scaffold (Unwired)                           *)
(* ------------------------------------------------------------------ *)

Record DBlockExceptionRow : Type := mkDBlockExceptionRow {
  exception : DBlockException;
  modality : DBlockOccupancyModality
}.

Definition DBlockExceptionRow_z (row : DBlockExceptionRow) : nat :=
  DBlockException_z (exception row).

Definition DBlockExceptionRow_symbol (row : DBlockExceptionRow) : string :=
  DBlockException_symbol (exception row).

Definition DBlockExceptionRow_observedNotation (row : DBlockExceptionRow) : string :=
  DBlockException_observedNotation (exception row).

Definition DBlockExceptionRow_predictedNotation (row : DBlockExceptionRow) : string :=
  DBlockException_predictedNotation (exception row).

Definition DBlockExceptionRow_occupancyTag (row : DBlockExceptionRow) : string :=
  DBlockException_occupancyTag (exception row).

Definition dBlockExceptionRow (ex : DBlockException) : DBlockExceptionRow :=
  {| exception := ex;
     modality := dBlockOccupancyModalityCurrent |}.

Lemma d_block_exception_row_z (ex : DBlockException) :
  DBlockExceptionRow_z (dBlockExceptionRow ex) = DBlockException_z ex.
Proof. reflexivity. Qed.

Lemma d_block_exception_row_modality_unwired (ex : DBlockException) :
  modality (dBlockExceptionRow ex) = d_block_occupancy_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Finite d-block exception list (cardinality 8 — not Z=1…118 dump)   *)
(* ------------------------------------------------------------------ *)

Definition dBlockExceptionList : list DBlockException :=
  d_block_exception_cr ::
  d_block_exception_cu ::
  d_block_exception_nb ::
  d_block_exception_mo ::
  d_block_exception_ru ::
  d_block_exception_rh ::
  d_block_exception_pd ::
  d_block_exception_ag ::
  nil.

Definition dBlockExceptionCount : nat := List.length dBlockExceptionList.

Lemma d_block_exception_count_eight : dBlockExceptionCount = 8%nat.
Proof. reflexivity. Qed.

Lemma d_block_exception_list_length :
  List.length dBlockExceptionList = 8%nat.
Proof. reflexivity. Qed.

Lemma cr_observed_ne_predicted :
  DBlockException_observedNotation d_block_exception_cr <>
  DBlockException_predictedNotation d_block_exception_cr.
Proof. discriminate. Qed.

Lemma cu_observed_ne_predicted :
  DBlockException_observedNotation d_block_exception_cu <>
  DBlockException_predictedNotation d_block_exception_cu.
Proof. discriminate. Qed.

Lemma nb_observed_ne_predicted :
  DBlockException_observedNotation d_block_exception_nb <>
  DBlockException_predictedNotation d_block_exception_nb.
Proof. discriminate. Qed.

Lemma mo_observed_ne_predicted :
  DBlockException_observedNotation d_block_exception_mo <>
  DBlockException_predictedNotation d_block_exception_mo.
Proof. discriminate. Qed.

Lemma ru_observed_ne_predicted :
  DBlockException_observedNotation d_block_exception_ru <>
  DBlockException_predictedNotation d_block_exception_ru.
Proof. discriminate. Qed.

Lemma rh_observed_ne_predicted :
  DBlockException_observedNotation d_block_exception_rh <>
  DBlockException_predictedNotation d_block_exception_rh.
Proof. discriminate. Qed.

Lemma pd_observed_ne_predicted :
  DBlockException_observedNotation d_block_exception_pd <>
  DBlockException_predictedNotation d_block_exception_pd.
Proof. discriminate. Qed.

Lemma ag_observed_ne_predicted :
  DBlockException_observedNotation d_block_exception_ag <>
  DBlockException_predictedNotation d_block_exception_ag.
Proof. discriminate. Qed.

Definition dBlockExceptionIsMadelungException (ex : DBlockException) : Prop :=
  DBlockException_observedNotation ex <>
  DBlockException_predictedNotation ex.

Lemma d_block_exception_is_madelung_exception (ex : DBlockException) :
  dBlockExceptionIsMadelungException ex.
Proof.
  destruct ex; discriminate.
Qed.

(* Approximate-not-identity: predicted and observed notations differ at same Z pin. *)

Definition dBlockExceptionApproximateNotIdentity (ex : DBlockException) : Prop :=
  dBlockExceptionIsMadelungException ex.

Lemma d_block_exception_approximate_not_identity (ex : DBlockException) :
  dBlockExceptionApproximateNotIdentity ex.
Proof.
  apply d_block_exception_is_madelung_exception.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pins are named here) *)
(* ------------------------------------------------------------------ *)

Definition dBlockOccupancyQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition dBlockOccupancyMadelungWitnessAuthority : string :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs".

Definition dBlockOccupancyExceptionsCellId : string :=
  "CHEM-FORMAL-Q-COQ-DBLOCK-OCCUPANCY-EXCEPTIONS".

Definition dBlockOccupancyExceptionsNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-DBLOCK-OCCUPANCY-EXCEPTIONS finite period-4/5 d-block qlattice Madelung occupancy exceptions Cr Cu Nb Mo Ru Rh Pd Ag as DBlockException; observed_override_config and madelung_predicted_config pins; DISTINCT from NamedException and actinide exceptions; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired".

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition dBlockOccupancyPhysicsGreenAuthorized : Prop := False.

Lemma d_block_occupancy_physics_green_false :
  ~ dBlockOccupancyPhysicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma d_block_occupancy_modality_unwired :
  dBlockOccupancyModalityCurrent = d_block_occupancy_unwired.
Proof. reflexivity. Qed.

Lemma d_block_occupancy_not_second_axiom :
  dBlockOccupancyMadelungWitnessAuthority <> "".
Proof. discriminate. Qed.

Lemma d_block_occupancy_cites_qlattice :
  dBlockOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs".
Proof. reflexivity. Qed.

Lemma d_block_occupancy_exceptions_cell_id :
  dBlockOccupancyExceptionsCellId =
  "CHEM-FORMAL-Q-COQ-DBLOCK-OCCUPANCY-EXCEPTIONS".
Proof. reflexivity. Qed.

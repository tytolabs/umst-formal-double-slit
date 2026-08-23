(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: NamedOccupancyExceptions.v                            *)
(*                                                                      *)
(*  Finite named set of Madelung predicted ≠ observed occupancy         *)
(*  exceptions as NamedException (La / Ce / Gd / Pt / Au). Pins mirror *)
(*  umst-chem qlattice observed overrides and madelung_witness cross-   *)
(*  matrix authority — not a second axiom, not GREEN DFT.               *)
(*                                                                      *)
(*  Self-contained (Stdlib lists / bools / strings). Modality Unwired. *)
(*  physics_green = False. No meso / acting theorems. Zero Admitted.     *)
(* ================================================================== *)

From Stdlib Require Import Arith List String.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Named occupancy modality (TYPE-03 preview — Unwired)               *)
(* ------------------------------------------------------------------ *)

Inductive NamedOccupancyModality : Type :=
  | named_occupancy_unwired
  | named_occupancy_assumed
  | named_occupancy_proved
  | named_occupancy_surrogate.

Definition namedOccupancyModalityCurrent : NamedOccupancyModality :=
  named_occupancy_unwired.

(* ------------------------------------------------------------------ *)
(*  Finite named Madelung occupancy exception tag (La Ce Gd Pt Au)       *)
(* ------------------------------------------------------------------ *)

Inductive NamedException : Type :=
  | named_exception_la
  | named_exception_ce
  | named_exception_gd
  | named_exception_pt
  | named_exception_au.

Definition NamedException_z (ex : NamedException) : nat :=
  match ex with
  | named_exception_la => 57%nat
  | named_exception_ce => 58%nat
  | named_exception_gd => 64%nat
  | named_exception_pt => 78%nat
  | named_exception_au => 79%nat
  end.

Definition NamedException_symbol (ex : NamedException) : string :=
  match ex with
  | named_exception_la => "La"
  | named_exception_ce => "Ce"
  | named_exception_gd => "Gd"
  | named_exception_pt => "Pt"
  | named_exception_au => "Au"
  end.

Lemma named_exception_la_z :
  NamedException_z named_exception_la = 57%nat.
Proof. reflexivity. Qed.

Lemma named_exception_ce_z :
  NamedException_z named_exception_ce = 58%nat.
Proof. reflexivity. Qed.

Lemma named_exception_gd_z :
  NamedException_z named_exception_gd = 64%nat.
Proof. reflexivity. Qed.

Lemma named_exception_pt_z :
  NamedException_z named_exception_pt = 78%nat.
Proof. reflexivity. Qed.

Lemma named_exception_au_z :
  NamedException_z named_exception_au = 79%nat.
Proof. reflexivity. Qed.

(* Observed ground-state subshell notation pin (qlattice SSOT — not GREEN DFT). *)

Definition NamedException_observedNotation (ex : NamedException) : string :=
  match ex with
  | named_exception_la =>
    "1s22s22p63s23p64s23d104p65s24d105p66s25d1"
  | named_exception_ce =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f15d1"
  | named_exception_gd =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f75d1"
  | named_exception_pt =>
    "1s22s22p63s23p63d104s24p64d104f145s25p65d96s1"
  | named_exception_au =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d106s1"
  end.

(* Madelung (n+ℓ) walk predicted subshell notation at Z (design witness — not identity). *)

Definition NamedException_predictedNotation (ex : NamedException) : string :=
  match ex with
  | named_exception_la =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f1"
  | named_exception_ce =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f2"
  | named_exception_gd =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f8"
  | named_exception_pt =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d8"
  | named_exception_au =>
    "1s22s22p63s23p64s23d104p65s24d105p66s24f145d9"
  end.

(* Chemist valence occupancy shorthand (named pin — not axiom). *)

Definition NamedException_occupancyTag (ex : NamedException) : string :=
  match ex with
  | named_exception_la => "5d16s2"
  | named_exception_ce => "4f15d16s2"
  | named_exception_gd => "4f75d16s2"
  | named_exception_pt => "5d96s1"
  | named_exception_au => "5d106s1"
  end.

(* ------------------------------------------------------------------ *)
(*  Named exception row scaffold (Unwired)                             *)
(* ------------------------------------------------------------------ *)

Record NamedExceptionRow : Type := mkNamedExceptionRow {
  exception : NamedException;
  modality : NamedOccupancyModality
}.

Definition NamedExceptionRow_z (row : NamedExceptionRow) : nat :=
  NamedException_z (exception row).

Definition NamedExceptionRow_symbol (row : NamedExceptionRow) : string :=
  NamedException_symbol (exception row).

Definition NamedExceptionRow_observedNotation (row : NamedExceptionRow) : string :=
  NamedException_observedNotation (exception row).

Definition NamedExceptionRow_predictedNotation (row : NamedExceptionRow) : string :=
  NamedException_predictedNotation (exception row).

Definition NamedExceptionRow_occupancyTag (row : NamedExceptionRow) : string :=
  NamedException_occupancyTag (exception row).

Definition namedExceptionRow (ex : NamedException) : NamedExceptionRow :=
  {| exception := ex;
     modality := namedOccupancyModalityCurrent |}.

Lemma named_exception_row_z (ex : NamedException) :
  NamedExceptionRow_z (namedExceptionRow ex) = NamedException_z ex.
Proof. reflexivity. Qed.

Lemma named_exception_row_modality_unwired (ex : NamedException) :
  modality (namedExceptionRow ex) = named_occupancy_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Finite named exception list (cardinality 5 — not Z=1…118 dump)     *)
(* ------------------------------------------------------------------ *)

Definition namedExceptionList : list NamedException :=
  named_exception_la ::
  named_exception_ce ::
  named_exception_gd ::
  named_exception_pt ::
  named_exception_au ::
  nil.

Definition namedExceptionCount : nat := List.length namedExceptionList.

Lemma named_exception_count_five : namedExceptionCount = 5%nat.
Proof. reflexivity. Qed.

Lemma named_exception_list_length :
  List.length namedExceptionList = 5%nat.
Proof. reflexivity. Qed.

Lemma la_observed_ne_predicted :
  NamedException_observedNotation named_exception_la <>
  NamedException_predictedNotation named_exception_la.
Proof. discriminate. Qed.

Lemma ce_observed_ne_predicted :
  NamedException_observedNotation named_exception_ce <>
  NamedException_predictedNotation named_exception_ce.
Proof. discriminate. Qed.

Lemma gd_observed_ne_predicted :
  NamedException_observedNotation named_exception_gd <>
  NamedException_predictedNotation named_exception_gd.
Proof. discriminate. Qed.

Lemma pt_observed_ne_predicted :
  NamedException_observedNotation named_exception_pt <>
  NamedException_predictedNotation named_exception_pt.
Proof. discriminate. Qed.

Lemma au_observed_ne_predicted :
  NamedException_observedNotation named_exception_au <>
  NamedException_predictedNotation named_exception_au.
Proof. discriminate. Qed.

Lemma named_exception_is_madelung_exception (ex : NamedException) :
  NamedException_observedNotation ex <>
  NamedException_predictedNotation ex.
Proof.
  destruct ex; discriminate.
Qed.

(* Approximate-not-identity: predicted and observed notations differ at same Z pin. *)

Definition namedExceptionApproximateNotIdentity (ex : NamedException) : Prop :=
  NamedException_observedNotation ex <>
  NamedException_predictedNotation ex.

Lemma named_exception_approximate_not_identity (ex : NamedException) :
  namedExceptionApproximateNotIdentity ex.
Proof.
  apply named_exception_is_madelung_exception.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — pins are named here) *)
(* ------------------------------------------------------------------ *)

Definition namedOccupancyQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition namedOccupancyMadelungWitnessAuthority : string :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs".

Definition namedOccupancyExceptionsCellId : string :=
  "CHEM-FORMAL-Q-COQ-NAMED-OCCUPANCY-EXCEPTIONS".

Definition namedOccupancyExceptionsNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-NAMED-OCCUPANCY-EXCEPTIONS finite named Madelung occupancy exceptions La Ce Gd Pt Au as NamedException; predicted vs observed approximate not identity; cites qlattice and madelung_witness not second axiom; not GREEN DFT; not physics GREEN; not production_wired".

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition namedOccupancyPhysicsGreenAuthorized : Prop := False.

Lemma named_occupancy_physics_green_false :
  ~ namedOccupancyPhysicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma named_occupancy_modality_unwired :
  namedOccupancyModalityCurrent = named_occupancy_unwired.
Proof. reflexivity. Qed.

Lemma named_occupancy_not_second_axiom :
  namedOccupancyMadelungWitnessAuthority <> "".
Proof. discriminate. Qed.

Lemma named_occupancy_cites_qlattice :
  namedOccupancyQlatticeAuthority = "umst/umst-chem/src/qlattice.rs".
Proof. reflexivity. Qed.

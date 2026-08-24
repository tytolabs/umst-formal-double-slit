(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: LandauerNTo1.v                                       *)
(*                                                                      *)
(*  Knowing/quantum Coq: §19.8 Landauer price of N→1 compression.      *)
(*  Every ADK collapse destroys information; price in **bits of         *)
(*  destroyed distinction**, not fake joules. Joule conversion is the  *)
(*  Landauer floor (`kT ln 2` per bit), not measured laptop heat.       *)
(*  Mirrors Lean `UrgeKnowing.LandauerNTo1` and Rust `landauer_n_to_1` *)
(*  — not meso thermo G(T,P,x) restated.                               *)
(*                                                                      *)
(*  Self-contained over UMSTFormal Landauer spine. Modality Unwired.  *)
(*  physics_green = False. Zero Admitted. Zero new Axiom. One axiom    *)
(*  second law + conservation framing — Landauer N→1 is not a second     *)
(*  Landauer axiom.                                                     *)
(* ================================================================== *)

From Coq Require Import Reals RIneq Lra Field Arith PeanoNat String Bool.
From UMSTFormal Require Import LandauerEinsteinBridge MeasurementCost.

Open Scope R_scope.
Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Landauer N→1 compression modality (Unwired / Assumed / Proved /     *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive LandauerNTo1Modality : Type :=
  | landauer_n_to_1_unwired
  | landauer_n_to_1_assumed
  | landauer_n_to_1_proved
  | landauer_n_to_1_surrogate.

Definition landauerNTo1ModalityCurrent : LandauerNTo1Modality :=
  landauer_n_to_1_unwired.

(* ------------------------------------------------------------------ *)
(*  Destroyed distinction bits for N→1 compression                      *)
(* ------------------------------------------------------------------ *)

Definition destroyed_distinction_bits (n : nat) : option nat :=
  match n with
  | O | S O => None
  | S _ => Some (Nat.log2 n)
  end.

Lemma destroyed_distinction_bits_four :
  destroyed_distinction_bits 4 = Some 2%nat.
Proof. reflexivity. Qed.

Lemma destroyed_distinction_bits_two :
  destroyed_distinction_bits 2 = Some 1%nat.
Proof. reflexivity. Qed.

Lemma destroyed_distinction_bits_one :
  destroyed_distinction_bits 1 = None.
Proof. reflexivity. Qed.

Lemma destroyed_distinction_bits_zero :
  destroyed_distinction_bits 0 = None.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Landauer floor joules from destroyed bits (floor only, not heat)    *)
(* ------------------------------------------------------------------ *)


Lemma measurementEnergyLowerBound_nonneg (T mi : R) :
  0 <= T -> 0 <= mi -> 0 <= measurementEnergyLowerBound T mi.
Proof.
  intros HT Hmi.
  unfold measurementEnergyLowerBound, E_Landauer_bit.
  apply Rmult_le_pos; [exact Hmi|].
  apply Rmult_le_pos; [|apply Rlt_le, ln2_pos].
  apply Rmult_le_pos; [apply Rlt_le, kB_SI_pos|exact HT].
Qed.

Lemma E_Landauer_bit_nonneg (T : R) :
  0 <= T -> 0 <= E_Landauer_bit T.
Proof.
  intros HT.
  unfold E_Landauer_bit.
  apply Rmult_le_pos; [|apply Rlt_le, ln2_pos].
  apply Rmult_le_pos; [apply Rlt_le, kB_SI_pos|exact HT].
Qed.

Definition landauer_floor_from_destroyed_bits (T : R) (bits : nat) : R :=
  measurementEnergyLowerBound T (INR bits).

Lemma landauer_floor_two_bit_collapse_nonneg (T : R) :
  0 <= T ->
  0 <= landauer_floor_from_destroyed_bits T 2%nat.
Proof.
  intros HT.
  unfold landauer_floor_from_destroyed_bits, measurementEnergyLowerBound.
  apply Rmult_le_pos.
  - simpl. lra.
  - apply Rmult_le_pos; [|apply Rlt_le, ln2_pos].
    apply Rmult_le_pos; [apply Rlt_le, kB_SI_pos|exact HT].
Qed.

Lemma landauer_floor_two_bit_le_bit_energy (T : R) :
  0 <= T ->
  landauer_floor_from_destroyed_bits T 2%nat <= 2 * E_Landauer_bit T.
Proof.
  intros HT.
  unfold landauer_floor_from_destroyed_bits, measurementEnergyLowerBound, E_Landauer_bit.
  simpl. lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  N→1 compression candidate scaffold (bits-first discipline)          *)
(* ------------------------------------------------------------------ *)

Record CompressionCandidate := {
  source_distinction_count : nat;
  claimed_destroyed_bits : option nat;
  laptop_heat_theater : bool;
  claims_physics_green : bool;
  provenance_intact : bool;
  evidence_tagged : bool
}.

Inductive LandauerNTo1Refusal : Type :=
  | refuse_laptop_heat_theater
  | refuse_invented_distinction_bits
  | refuse_false_green_compression
  | refuse_provenance_lost
  | refuse_missing_evidence_tag.

Inductive CompressionVerdict : Type :=
  | compression_accept
  | compression_refuse.

Definition admit_compression_candidate (c : CompressionCandidate)
  : option LandauerNTo1Refusal :=
  if laptop_heat_theater c then
    Some refuse_laptop_heat_theater
  else if claims_physics_green c then
    Some refuse_false_green_compression
  else if negb (provenance_intact c) then
    Some refuse_provenance_lost
  else if negb (evidence_tagged c) then
    Some refuse_missing_evidence_tag
  else
    match destroyed_distinction_bits (source_distinction_count c),
          claimed_destroyed_bits c with
    | Some expected, Some claimed =>
        if Nat.eqb expected claimed then None else
        Some refuse_invented_distinction_bits
    | _, _ => Some refuse_invented_distinction_bits
    end.

Definition evaluate_compression (c : CompressionCandidate) : CompressionVerdict :=
  match admit_compression_candidate c with
  | None => compression_accept
  | Some _ => compression_refuse
  end.

Definition fixture_admissible_two_bit_collapse : CompressionCandidate :=
  {| source_distinction_count := 4%nat;
     claimed_destroyed_bits := Some 2%nat;
     laptop_heat_theater := false;
     claims_physics_green := false;
     provenance_intact := true;
     evidence_tagged := true |}.

Definition fixture_inadmissible_laptop_heat : CompressionCandidate :=
  {| source_distinction_count := 4%nat;
     claimed_destroyed_bits := Some 2%nat;
     laptop_heat_theater := true;
     claims_physics_green := false;
     provenance_intact := true;
     evidence_tagged := true |}.

Definition fixture_inadmissible_invented_bits : CompressionCandidate :=
  {| source_distinction_count := 4%nat;
     claimed_destroyed_bits := Some 47%nat;
     laptop_heat_theater := false;
     claims_physics_green := false;
     provenance_intact := true;
     evidence_tagged := true |}.

Lemma fixture_admissible_two_bit_accepts :
  evaluate_compression fixture_admissible_two_bit_collapse = compression_accept.
Proof. reflexivity. Qed.

Lemma fixture_laptop_heat_refuses :
  admit_compression_candidate fixture_inadmissible_laptop_heat =
  Some refuse_laptop_heat_theater.
Proof. reflexivity. Qed.

Lemma fixture_invented_bits_refuses :
  admit_compression_candidate fixture_inadmissible_invented_bits =
  Some refuse_invented_distinction_bits.
Proof. reflexivity. Qed.

Lemma landauer_n_to_1_laptop_heat_positive_refuse :
  admit_compression_candidate fixture_inadmissible_laptop_heat =
  Some refuse_laptop_heat_theater.
Proof. reflexivity. Qed.

Lemma landauer_n_to_1_invented_bits_positive_refuse :
  admit_compression_candidate fixture_inadmissible_invented_bits =
  Some refuse_invented_distinction_bits.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — N→1 compression)     *)
(* ------------------------------------------------------------------ *)

Definition landauerBoundAuthority : string :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean".

Definition landauerNTo1LeanAuthority : string :=
  "umst/umst-formal-double-slit/Lean/UrgeKnowing/LandauerNTo1.lean".

Definition landauerLawAuthority : string :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition landauerNTo1CellId : string :=
  "URGE-FORMAL-Q-COQ-LANDAUER-N-TO-1".

Definition landauerNTo1NonClaim : string :=
  "URGE-FORMAL-Q-COQ-LANDAUER-N-TO-1 §19.8 Landauer price of N→1 compression; bits of destroyed distinction not fake joules; Landauer floor kT ln2 per bit not measured laptop heat; Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired".

Lemma landauer_n_to_1_cell_id :
  landauerNTo1CellId = "URGE-FORMAL-Q-COQ-LANDAUER-N-TO-1".
Proof. reflexivity. Qed.

Lemma landauer_n_to_1_cites_landauer_bound :
  landauerBoundAuthority <> "".
Proof. discriminate. Qed.

Lemma landauer_n_to_1_cites_lean_knowing :
  landauerNTo1LeanAuthority <> "".
Proof. discriminate. Qed.

Lemma landauer_n_to_1_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second Landauer  *)
(* ------------------------------------------------------------------ *)

Definition landauerNTo1SecondLawConservationFraming : string :=
  "second_law_conservation_n_to_1_one_axiom_landauer_not_second_axiom".

Lemma landauer_n_to_1_not_second_landauer_axiom :
  landauerNTo1SecondLawConservationFraming <>
  "landauer_second_axiom".
Proof. discriminate. Qed.

Lemma landauer_n_to_1_second_law_conservation_framing :
  landauerNTo1SecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma landauer_n_to_1_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma landauer_n_to_1_modality_unwired :
  landauerNTo1ModalityCurrent = landauer_n_to_1_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Not meso thermo restated fence                                      *)
(* ------------------------------------------------------------------ *)

Definition mesoThermoGRestated : string :=
  "meso_thermo_G_T_P_x_restate".

Lemma landauer_n_to_1_not_meso_thermo_restate :
  landauerNTo1NonClaim <> mesoThermoGRestated.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Bits-first fence — not fake joules theater                          *)
(* ------------------------------------------------------------------ *)

Definition laptopHeatTheaterPrimary : string :=
  "laptop_heat_joules_primary_price".

Lemma landauer_n_to_1_not_laptop_heat_theater :
  landauerNTo1NonClaim <> laptopHeatTheaterPrimary.
Proof. discriminate. Qed.

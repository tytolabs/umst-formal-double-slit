(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: LandauerHistoryLook.v                                 *)
(*                                                                      *)
(*  Knowing/quantum Coq: §5.2 / §22.4 LandauerBound of a look at       *)
(*  history. Cumulative Landauer lower bound when an observer inspects   *)
(*  a finite epistemic history (per-step MI in bit-equivalents).        *)
(*  Mirrors Lean `EpistemicTrajectoryMI.cumulativeEpistemicLandauerCost` *)
(*  and `MeasurementCost.measurementEnergyLowerBound` — not meso         *)
(*  thermo G(T,P,x) restated.                                           *)
(*                                                                      *)
(*  Self-contained over UMSTFormal Landauer spine. Modality Unwired.    *)
(*  physics_green = False. Zero Admitted. One axiom second law +         *)
(*  conservation framing — Landauer history look is not a second axiom.  *)
(* ================================================================== *)

From Coq Require Import Reals RIneq Lra Field List Arith String.
From UMSTFormal Require Import LandauerEinsteinBridge MeasurementCost.
Import ListNotations.

Open Scope R_scope.
Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Landauer history-look modality (Unwired / Assumed / Proved /        *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive LandauerHistoryLookModality : Type :=
  | landauer_history_look_unwired
  | landauer_history_look_assumed
  | landauer_history_look_proved
  | landauer_history_look_surrogate.

Definition landauerHistoryLookModalityCurrent : LandauerHistoryLookModality :=
  landauer_history_look_unwired.

(* ------------------------------------------------------------------ *)
(*  Per-step MI scaffold (bit-equivalents along a history look)         *)
(* ------------------------------------------------------------------ *)

Definition history_step_mi_bounded (mi : R) : Prop :=
  0 <= mi /\ mi <= 1.

Definition history_mi_bounded (history : list R) : Prop :=
  Forall history_step_mi_bounded history.

(* ------------------------------------------------------------------ *)
(*  Cumulative Landauer cost of looking at history                      *)
(* ------------------------------------------------------------------ *)

Fixpoint sum_history_look_landauer (T : R) (history : list R) : R :=
  match history with
  | [] => 0
  | mi :: rest =>
      measurementEnergyLowerBound T mi + sum_history_look_landauer T rest
  end.

Definition historyLookLandauerCost (T : R) (history : list R) : R :=
  sum_history_look_landauer T history.

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

Lemma measurementEnergyLowerBound_le_bit_energy (T mi : R) :
  0 <= T -> 0 <= mi -> mi <= 1 ->
  measurementEnergyLowerBound T mi <= E_Landauer_bit T.
Proof.
  intros HT Hmi Hle.
  unfold measurementEnergyLowerBound.
  rewrite <- Rmult_1_l.
  apply Rmult_le_compat_r.
  - apply E_Landauer_bit_nonneg; exact HT.
  - exact Hle.
Qed.

Lemma historyLookLandauerCost_empty (T : R) :
  historyLookLandauerCost T [] = 0.
Proof. reflexivity. Qed.

Lemma historyLookLandauerCost_zero_mi (T : R) :
  historyLookLandauerCost T [0] = 0.
Proof.
  unfold historyLookLandauerCost, sum_history_look_landauer,
    measurementEnergyLowerBound.
  simpl. ring.
Qed.

Lemma historyLookLandauerCost_nonneg (T : R) (history : list R) :
  0 <= T ->
  Forall (fun mi => 0 <= mi) history ->
  0 <= historyLookLandauerCost T history.
Proof.
  intros HT Hforall.
  induction history as [| mi rest IH].
  - unfold historyLookLandauerCost. simpl. lra.
  - unfold historyLookLandauerCost. simpl.
    apply Rplus_le_le_0_compat.
    + apply measurementEnergyLowerBound_nonneg.
      * exact HT.
      * apply (Forall_inv Hforall).
    + apply IH.
      apply Forall_inv_tail in Hforall.
      exact Hforall.
Qed.

Lemma historyLookLandauerCost_one_step_le (T mi : R) :
  0 <= T ->
  history_step_mi_bounded mi ->
  historyLookLandauerCost T [mi] <= E_Landauer_bit T.
Proof.
  intros HT Hmi.
  unfold historyLookLandauerCost, sum_history_look_landauer.
  simpl.
  destruct Hmi as [Hmi0 Hle].
  rewrite Rplus_0_r.
  apply measurementEnergyLowerBound_le_bit_energy.
  - exact HT.
  - exact Hmi0.
  - exact Hle.
Qed.

Lemma historyLookLandauerCost_two_step_le (T mi1 mi2 : R) :
  0 <= T ->
  history_step_mi_bounded mi1 ->
  history_step_mi_bounded mi2 ->
  historyLookLandauerCost T [mi1; mi2] <= 2 * E_Landauer_bit T.
Proof.
  intros HT Hmi1 Hmi2.
  destruct Hmi1 as [Hmi1a Hmi1b].
  destruct Hmi2 as [Hmi2a Hmi2b].
  unfold historyLookLandauerCost, sum_history_look_landauer, measurementEnergyLowerBound.
  simpl. rewrite Rplus_0_r.
  assert (H2 : (2 : R) * E_Landauer_bit T = E_Landauer_bit T + E_Landauer_bit T).
  { ring. }
  rewrite H2.
  apply Rplus_le_compat.
  - apply measurementEnergyLowerBound_le_bit_energy; lra.
  - apply measurementEnergyLowerBound_le_bit_energy; lra.
Qed.

Lemma historyLookLandauerCost_null_history (T : R) :
  historyLookLandauerCost T (0 :: 0 :: []) = 0.
Proof.
  unfold historyLookLandauerCost, sum_history_look_landauer,
    measurementEnergyLowerBound, E_Landauer_bit.
  simpl. ring.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — history look)        *)
(* ------------------------------------------------------------------ *)

Definition landauerBoundAuthority : string :=
  "umst/umst-formal-double-slit/Lean/LandauerBound.lean".

Definition epistemicTrajectoryMIAuthority : string :=
  "umst/umst-formal-double-slit/Lean/EpistemicTrajectoryMI.lean".

Definition landauerLawAuthority : string :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition landauerHistoryLookCellId : string :=
  "URGE-FORMAL-Q-COQ-LANDAUER-HISTORY-LOOK".

Definition landauerHistoryLookNonClaim : string :=
  "URGE-FORMAL-Q-COQ-LANDAUER-HISTORY-LOOK §5.2 §22.4 LandauerBound history look cumulative epistemic Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired".

Lemma landauer_history_look_cell_id :
  landauerHistoryLookCellId = "URGE-FORMAL-Q-COQ-LANDAUER-HISTORY-LOOK".
Proof. reflexivity. Qed.

Lemma landauer_history_look_cites_landauer_bound :
  landauerBoundAuthority <> "".
Proof. discriminate. Qed.

Lemma landauer_history_look_cites_epistemic_trajectory :
  epistemicTrajectoryMIAuthority <> "".
Proof. discriminate. Qed.

Lemma landauer_history_look_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second Landauer    *)
(* ------------------------------------------------------------------ *)

Definition landauerHistorySecondLawConservationFraming : string :=
  "second_law_conservation_history_look_one_axiom_landauer_not_second_axiom".

Lemma landauer_history_not_second_landauer_axiom :
  landauerHistorySecondLawConservationFraming <>
  "landauer_second_axiom".
Proof. discriminate. Qed.

Lemma landauer_history_second_law_conservation_framing :
  landauerHistorySecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma landauer_history_look_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma landauer_history_look_modality_unwired :
  landauerHistoryLookModalityCurrent = landauer_history_look_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Not meso thermo restated fence                                      *)
(* ------------------------------------------------------------------ *)

Definition mesoThermoGRestated : string :=
  "meso_thermo_G_T_P_x_restate".

Lemma landauer_history_look_not_meso_thermo_restate :
  landauerHistoryLookNonClaim <> mesoThermoGRestated.
Proof. discriminate. Qed.

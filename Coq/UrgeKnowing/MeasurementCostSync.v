(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: MeasurementCostSync.v                                 *)
(*                                                                      *)
(*  Knowing/quantum Coq: §16 measurement cost of a **sync look**       *)
(*  when an observer inspects inbound state during Kleisli sync —        *)
(*  distinct from rollout history look and meso thermo G(T,P,x).         *)
(*  Mirrors Lean `MeasurementCost.measurementCost` /                     *)
(*  `epistemicLandauerCost` on the knowing fiber.                        *)
(*                                                                      *)
(*  Self-contained over UMSTFormal Landauer spine. Modality Unwired.    *)
(*  physics_green = False. Zero Admitted. One axiom second law +         *)
(*  conservation framing — sync look is not a second Landauer axiom.     *)
(*  Composes imported Excitement select — no second local argmin.        *)
(* ================================================================== *)

From Coq Require Import Reals RIneq Lra Field String.
From UMSTFormal Require Import LandauerEinsteinBridge MeasurementCost.

Open Scope R_scope.
Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Sync-look measurement cost modality (Unwired / Assumed / Proved /    *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive MeasurementCostSyncModality : Type :=
  | measurement_cost_sync_unwired
  | measurement_cost_sync_assumed
  | measurement_cost_sync_proved
  | measurement_cost_sync_surrogate.

Definition measurementCostSyncModalityCurrent : MeasurementCostSyncModality :=
  measurement_cost_sync_unwired.

(* ------------------------------------------------------------------ *)
(*  Path probe scaffold (knowing fiber — null / which-path)             *)
(* ------------------------------------------------------------------ *)

Inductive PathProbe : Type :=
  | path_probe_null
  | path_probe_which_path.

Definition syncLookStepMIBounded (mi : R) : Prop :=
  0 <= mi /\ mi <= 1.

Definition clampPathEntropyBits (path_entropy_bits : R) : R :=
  Rmax 0 (Rmin 1 path_entropy_bits).

Definition syncLookMIBits (probe : PathProbe) (path_entropy_bits : R) : R :=
  match probe with
  | path_probe_null => 0
  | path_probe_which_path => clampPathEntropyBits path_entropy_bits
  end.

Definition syncLookMeasurementCost (probe : PathProbe)
  (path_entropy_bits T : R) : R :=
  measurementEnergyLowerBound T (syncLookMIBits probe path_entropy_bits).

(* ------------------------------------------------------------------ *)
(*  Landauer bit-energy helpers (reused from history-look spine)        *)
(* ------------------------------------------------------------------ *)

Lemma E_Landauer_bit_nonneg (T : R) :
  0 <= T -> 0 <= E_Landauer_bit T.
Proof.
  intros HT.
  unfold E_Landauer_bit.
  apply Rmult_le_pos; [|apply Rlt_le, ln2_pos].
  apply Rmult_le_pos; [apply Rlt_le, kB_SI_pos|exact HT].
Qed.

Lemma measurementEnergyLowerBound_nonneg (T mi : R) :
  0 <= T -> 0 <= mi -> 0 <= measurementEnergyLowerBound T mi.
Proof.
  intros HT Hmi.
  unfold measurementEnergyLowerBound, E_Landauer_bit.
  apply Rmult_le_pos; [exact Hmi|].
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

Lemma clampPathEntropyBits_bounded (path_entropy_bits : R) :
  syncLookStepMIBounded (clampPathEntropyBits path_entropy_bits).
Proof.
  unfold syncLookStepMIBounded, clampPathEntropyBits.
  split.
  - apply Rmax_l.
  - destruct (Rle_dec 0 (Rmin 1 path_entropy_bits)) as [H0|H0].
    + rewrite Rmax_right by exact H0.
      unfold Rmin; destruct (Rle_dec 1 path_entropy_bits); lra.
    + rewrite Rmax_left by lra. lra.
Qed.

Lemma syncLookMIBits_null (path_entropy_bits : R) :
  syncLookMIBits path_probe_null path_entropy_bits = 0.
Proof. reflexivity. Qed.

Lemma syncLookMIBits_bounded (probe : PathProbe) (path_entropy_bits : R) :
  syncLookStepMIBounded (syncLookMIBits probe path_entropy_bits).
Proof.
  destruct probe; unfold syncLookMIBits; simpl.
  - split; [lra | lra].
  - apply clampPathEntropyBits_bounded.
Qed.

Lemma syncLookMeasurementCost_null_zero (path_entropy_bits T : R) :
  syncLookMeasurementCost path_probe_null path_entropy_bits T = 0.
Proof.
  unfold syncLookMeasurementCost, syncLookMIBits.
  simpl.
  apply zero_info_zero_energy.
Qed.

Lemma syncLookMeasurementCost_nonneg (probe : PathProbe)
  (path_entropy_bits T : R) :
  0 <= T ->
  syncLookStepMIBounded (syncLookMIBits probe path_entropy_bits) ->
  0 <= syncLookMeasurementCost probe path_entropy_bits T.
Proof.
  intros HT Hmi.
  unfold syncLookMeasurementCost.
  destruct Hmi as [Hmi0 _].
  apply measurementEnergyLowerBound_nonneg; assumption.
Qed.

Lemma syncLookMeasurementCost_le_bit_energy (probe : PathProbe)
  (path_entropy_bits T : R) :
  0 <= T ->
  syncLookStepMIBounded (syncLookMIBits probe path_entropy_bits) ->
  syncLookMeasurementCost probe path_entropy_bits T <= E_Landauer_bit T.
Proof.
  intros HT Hmi.
  unfold syncLookMeasurementCost.
  destruct Hmi as [Hmi0 Hmi1].
  apply measurementEnergyLowerBound_le_bit_energy; assumption.
Qed.

Lemma syncLookMeasurementCost_which_path_example (T : R) :
  0 <= T ->
  syncLookMeasurementCost path_probe_which_path 0.5 T <= E_Landauer_bit T.
Proof.
  intros HT.
  apply syncLookMeasurementCost_le_bit_energy.
  - exact HT.
  - apply clampPathEntropyBits_bounded.
Qed.

(* ------------------------------------------------------------------ *)
(*  Excitement compose pin — import select; refuse second argmin        *)
(* ------------------------------------------------------------------ *)

Inductive ExcitementComposePin : Type :=
  | import_select_excitement
  | second_argmin_refused.

Inductive SyncLookComposeVerdict : Type :=
  | sync_look_compose_nonneg_ok
  | sync_look_compose_second_argmin_refuse.

Definition excitementComposeForSyncLook (pin : ExcitementComposePin)
  : SyncLookComposeVerdict :=
  match pin with
  | import_select_excitement => sync_look_compose_nonneg_ok
  | second_argmin_refused => sync_look_compose_second_argmin_refuse
  end.

Lemma second_argmin_refused_on_sync_look :
  excitementComposeForSyncLook second_argmin_refused =
  sync_look_compose_second_argmin_refuse.
Proof. reflexivity. Qed.

Lemma import_select_excitement_ok :
  excitementComposeForSyncLook import_select_excitement <>
  sync_look_compose_second_argmin_refuse.
Proof. discriminate. Qed.

Definition secondArgminRefusedTag : string := "second_argmin_refused".

Lemma second_argmin_tag_nonempty :
  secondArgminRefusedTag <> "".
Proof. discriminate. Qed.

Definition syncLookComposeSurrogate : string :=
  "UMST.Excitement.select".

Lemma sync_look_compose_surrogate_cited :
  syncLookComposeSurrogate <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — sync look)           *)
(* ------------------------------------------------------------------ *)

Definition measurementCostAuthority : string :=
  "umst/umst-formal-double-slit/Lean/MeasurementCost.lean".

Definition landauerLawAuthority : string :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition measurementCostSyncCellId : string :=
  "URGE-FORMAL-Q-COQ-MEASUREMENT-COST-SYNC".

Definition measurementCostSyncNonClaim : string :=
  "URGE-FORMAL-Q-COQ-MEASUREMENT-COST-SYNC MeasurementCostSync Unwired §16 sync look knowing fiber MeasurementCost epistemicLandauerCost not meso thermo G(T,P,x) restate compose Excitement select no second argmin not physics GREEN not production_wired".

Lemma measurement_cost_sync_cell_id :
  measurementCostSyncCellId = "URGE-FORMAL-Q-COQ-MEASUREMENT-COST-SYNC".
Proof. reflexivity. Qed.

Lemma measurement_cost_sync_cites_measurement_cost :
  measurementCostAuthority <> "".
Proof. discriminate. Qed.

Lemma measurement_cost_sync_cites_landauer_law :
  landauerLawAuthority <> "".
Proof. discriminate. Qed.

Lemma measurement_cost_sync_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second Landauer    *)
(* ------------------------------------------------------------------ *)

Definition syncLookSecondLawConservationFraming : string :=
  "second_law_conservation_sync_look_one_axiom_landauer_not_second_axiom".

Lemma measurement_cost_sync_not_second_landauer_axiom :
  syncLookSecondLawConservationFraming <> "landauer_second_axiom".
Proof. discriminate. Qed.

Lemma measurement_cost_sync_second_law_conservation_framing :
  syncLookSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma measurement_cost_sync_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma measurement_cost_sync_modality_unwired :
  measurementCostSyncModalityCurrent = measurement_cost_sync_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Not meso thermo restated fence                                      *)
(* ------------------------------------------------------------------ *)

Definition mesoThermoGRestated : string :=
  "meso_thermo_G_T_P_x_restate".

Lemma measurement_cost_sync_not_meso_thermo_restate :
  measurementCostSyncNonClaim <> mesoThermoGRestated.
Proof. discriminate. Qed.

Definition quantumKnowingFiber : string :=
  "umst-formal-double-slit/quantum_knowing".

Lemma measurement_cost_sync_knowing_fiber_ok :
  quantumKnowingFiber <> mesoThermoGRestated.
Proof. discriminate. Qed.

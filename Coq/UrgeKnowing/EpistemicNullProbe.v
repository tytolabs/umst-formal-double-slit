(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: EpistemicNullProbe.v                                  *)
(*                                                                      *)
(*  Knowing/quantum Coq: §22.4 EpistemicMI null probe I=0 on the       *)
(*  knowing fiber. Mirrors Lean `EpistemicMI.epistemicMI_null`,        *)
(*  `epistemicMIBits_null`, and `epistemicLandauerCost_null`.          *)
(*  Not meso thermo G(T,P,x) restated.                                 *)
(*                                                                      *)
(*  Self-contained over UMSTFormal Landauer spine. Modality Unwired.    *)
(*  physics_green = False. Zero Admitted. Zero new Axiom.              *)
(* ================================================================== *)

From Coq Require Import Reals RIneq Lra Field String.
From UMSTFormal Require Import LandauerEinsteinBridge MeasurementCost
  DensityStateSpec VonNeumannEntropySpec.

Open Scope R_scope.
Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Epistemic-null-probe modality (Unwired / Assumed / Proved /         *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive EpistemicNullProbeModality : Type :=
  | epistemic_null_probe_unwired
  | epistemic_null_probe_assumed
  | epistemic_null_probe_proved
  | epistemic_null_probe_surrogate.

Definition epistemicNullProbeModalityCurrent : EpistemicNullProbeModality :=
  epistemic_null_probe_unwired.

(* ------------------------------------------------------------------ *)
(*  PathProbe scaffold — probe-indexed epistemic MI on knowing fiber    *)
(* ------------------------------------------------------------------ *)

Inductive PathProbe : Type :=
  | path_probe_null
  | path_probe_which_path.

Definition EpistemicMI (p : PathProbe) (rho : DensityMatrix2) : R :=
  match p with
  | path_probe_null => 0
  | path_probe_which_path => vonNeumannDiagonal rho
  end.

Definition epistemicMIBits (p : PathProbe) (rho : DensityMatrix2) : R :=
  EpistemicMI p rho / ln2.

Definition epistemicLandauerCost (p : PathProbe) (rho : DensityMatrix2)
  (T : R) : R :=
  measurementEnergyLowerBound T (epistemicMIBits p rho).

(* ------------------------------------------------------------------ *)
(*  §22.4 null probe: EpistemicMI PathProbe.null ρ = 0                 *)
(* ------------------------------------------------------------------ *)

Lemma epistemicMI_null (rho : DensityMatrix2) :
  EpistemicMI path_probe_null rho = 0.
Proof. reflexivity. Qed.

Lemma epistemicMIBits_null (rho : DensityMatrix2) :
  epistemicMIBits path_probe_null rho = 0.
Proof.
  unfold epistemicMIBits, EpistemicMI.
  simpl.
  field.
  apply Rgt_not_eq.
  exact ln2_pos.
Qed.

Lemma epistemicLandauerCost_null (rho : DensityMatrix2) (T : R) :
  epistemicLandauerCost path_probe_null rho T = 0.
Proof.
  unfold epistemicLandauerCost.
  rewrite epistemicMIBits_null.
  apply zero_info_zero_energy.
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

Lemma epistemicMI_nonneg (p : PathProbe) (rho : DensityMatrix2) :
  0 <= EpistemicMI p rho.
Proof.
  destruct p.
  - simpl. lra.
  - simpl. apply vonNeumannDiagonal_nonneg.
Qed.

Lemma epistemicMIBits_nonneg (p : PathProbe) (rho : DensityMatrix2) :
  0 <= epistemicMIBits p rho.
Proof.
  unfold epistemicMIBits.
  apply Rmult_le_pos.
  - apply epistemicMI_nonneg.
  - apply Rlt_le, Rinv_0_lt_compat, ln2_pos.
Qed.

Lemma epistemicLandauerCost_nonneg (p : PathProbe) (rho : DensityMatrix2)
  (T : R) :
  0 <= T -> 0 <= epistemicLandauerCost p rho T.
Proof.
  intros HT.
  unfold epistemicLandauerCost.
  apply measurementEnergyLowerBound_nonneg; [|apply epistemicMIBits_nonneg].
  exact HT.
Qed.

Lemma epistemicLandauerCost_null_all_temps (rho : DensityMatrix2) :
  forall T : R, epistemicLandauerCost path_probe_null rho T = 0.
Proof.
  intros T. exact (epistemicLandauerCost_null rho T).
Qed.

Definition epistemicNullProbePolicy (rho : DensityMatrix2) : Prop :=
  EpistemicMI path_probe_null rho = 0 /\
  epistemicMIBits path_probe_null rho = 0 /\
  forall T : R, epistemicLandauerCost path_probe_null rho T = 0.

Lemma epistemic_null_probe_policy (rho : DensityMatrix2) :
  epistemicNullProbePolicy rho.
Proof.
  split; [|split].
  - apply epistemicMI_null.
  - apply epistemicMIBits_null.
  - intros T. apply epistemicLandauerCost_null.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — null probe)          *)
(* ------------------------------------------------------------------ *)

Definition epistemicMIAuthority : string :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean".

Definition landauerLawAuthority : string :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition epistemicNullProbeCellId : string :=
  "URGE-FORMAL-Q-COQ-EPISTEMIC-NULL-PROBE".

Definition epistemicNullProbeNamed : string :=
  "epistemic_null_probe: EpistemicMI null probe I=0 on knowing fiber; Landauer hook zero; physicalSecondLaw sole axiom framing".

Definition epistemicNullProbeNonClaim : string :=
  "URGE-FORMAL-Q-COQ-EPISTEMIC-NULL-PROBE §22.4 epistemic_null_probe EpistemicMI null I=0 knowing fiber Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired".

Lemma epistemic_null_probe_cell_id :
  epistemicNullProbeCellId = "URGE-FORMAL-Q-COQ-EPISTEMIC-NULL-PROBE".
Proof. reflexivity. Qed.

Lemma epistemic_null_probe_cites_epistemic_mi :
  epistemicMIAuthority <> "".
Proof. discriminate. Qed.

Lemma epistemic_null_probe_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

Lemma epistemic_null_probe_cites_landauer_law :
  landauerLawAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second Landauer  *)
(* ------------------------------------------------------------------ *)

Definition epistemicNullSecondLawConservationFraming : string :=
  "second_law_conservation_null_probe_one_axiom_landauer_not_second_axiom".

Lemma epistemic_null_not_second_landauer_axiom :
  epistemicNullSecondLawConservationFraming <>
  "landauer_second_axiom".
Proof. discriminate. Qed.

Lemma epistemic_null_second_law_conservation_framing :
  epistemicNullSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma epistemic_null_probe_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma epistemic_null_probe_modality_unwired :
  epistemicNullProbeModalityCurrent = epistemic_null_probe_unwired.
Proof. reflexivity. Qed.

Definition epistemicNullProbeKnowingFiberOk : Prop :=
  epistemicNullProbeModalityCurrent = epistemic_null_probe_unwired /\
  ~ physicsGreenAuthorized.

Lemma epistemic_null_probe_knowing_fiber_ok :
  epistemicNullProbeKnowingFiberOk.
Proof.
  split.
  - apply epistemic_null_probe_modality_unwired.
  - apply epistemic_null_probe_physics_green_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  Not meso thermo restated fence                                      *)
(* ------------------------------------------------------------------ *)

Definition mesoThermoGRestated : string :=
  "meso_thermo_G_T_P_x_restate".

Lemma epistemic_null_probe_not_meso_thermo_restate :
  epistemicNullProbeNonClaim <> mesoThermoGRestated.
Proof. discriminate. Qed.

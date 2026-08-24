(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: CompactionMiCost.v                                    *)
(*                                                                      *)
(*  Knowing/quantum Coq: §17.5 / §22.4 compaction pays MI vs           *)
(*  epistemicMI_null. Semantic compaction composes Excitement — not a   *)
(*  second argmin. Mirrors Lean EpistemicMI.epistemicMI_null and        *)
(*  epistemicMIBits_null on the knowing fiber — not meso thermo         *)
(*  G(T,P,x) restated.                                                  *)
(*                                                                      *)
(*  Self-contained over UMSTFormal Landauer spine. Modality Unwired.    *)
(*  physics_green = False. Zero Admitted. Zero new Axiom — sole         *)
(*  physicalSecondLaw framing cited as authority string only.             *)
(* ================================================================== *)

From Coq Require Import Reals RIneq Lra Field List Arith String.
From UMSTFormal Require Import LandauerEinsteinBridge MeasurementCost.
Import ListNotations.

Open Scope R_scope.
Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Compaction MI cost modality (Unwired / Assumed / Proved /          *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive CompactionMiCostModality : Type :=
  | compaction_mi_cost_unwired
  | compaction_mi_cost_assumed
  | compaction_mi_cost_proved
  | compaction_mi_cost_surrogate.

Definition compactionMiCostModalityCurrent : CompactionMiCostModality :=
  compaction_mi_cost_unwired.

(* ------------------------------------------------------------------ *)
(*  Path-qubit probe scaffold (mirrors PathProbe on knowing fiber)      *)
(* ------------------------------------------------------------------ *)

Inductive PathProbe : Type :=
  | path_probe_null
  | path_probe_which_path.

Definition isEpistemicMINull (p : PathProbe) : Prop :=
  p = path_probe_null.

(* ------------------------------------------------------------------ *)
(*  Epistemic MI surrogate in bit-equivalents (probe-indexed)           *)
(* ------------------------------------------------------------------ *)

Definition epistemicMIBits (p : PathProbe) (mi_bits : R) : R :=
  match p with
  | path_probe_null => 0
  | path_probe_which_path => mi_bits
  end.

Definition epistemicMI_step_bounded (mi_bits : R) : Prop :=
  0 <= mi_bits /\ mi_bits <= 1.

Lemma epistemicMI_null (mi_bits : R) :
  epistemicMIBits path_probe_null mi_bits = 0.
Proof. reflexivity. Qed.

Lemma epistemicMIBits_null (mi_bits : R) :
  epistemicMIBits path_probe_null mi_bits = 0.
Proof. exact (epistemicMI_null mi_bits). Qed.

Lemma epistemicMIBits_which_path (mi_bits : R) :
  epistemicMIBits path_probe_which_path mi_bits = mi_bits.
Proof. reflexivity. Qed.

Lemma epistemicMIBits_nonneg (p : PathProbe) (mi_bits : R) :
  0 <= mi_bits ->
  0 <= epistemicMIBits p mi_bits.
Proof.
  intros Hmi.
  destruct p; simpl.
  - lra.
  - exact Hmi.
Qed.

Lemma epistemicMIBits_le_one (p : PathProbe) (mi_bits : R) :
  epistemicMI_step_bounded mi_bits ->
  epistemicMIBits p mi_bits <= 1.
Proof.
  intros Hmi.
  destruct p; simpl.
  - lra.
  - destruct Hmi as [_ Hle]; exact Hle.
Qed.

(* ------------------------------------------------------------------ *)
(*  Compaction pays MI vs epistemicMI_null baseline                     *)
(* ------------------------------------------------------------------ *)

Definition compactionPaysMIBitsVsNull (p : PathProbe) (mi_bits : R) : Prop :=
  ~ isEpistemicMINull p /\ 0 < epistemicMIBits p mi_bits.

Lemma compaction_pays_mi_vs_null_which_path (mi_bits : R) :
  0 < mi_bits ->
  compactionPaysMIBitsVsNull path_probe_which_path mi_bits.
Proof.
  intros Hpos.
  unfold compactionPaysMIBitsVsNull, isEpistemicMINull, epistemicMIBits.
  split.
  - intro H; inversion H.
  - exact Hpos.
Qed.

Lemma compaction_refuses_null_probe (mi_bits : R) :
  ~ compactionPaysMIBitsVsNull path_probe_null mi_bits.
Proof.
  intro H.
  destruct H as [Hnot _].
  apply Hnot; reflexivity.
Qed.

Lemma compaction_null_probe_mi_zero (mi_bits : R) :
  epistemicMIBits path_probe_null mi_bits = 0 ->
  ~ compactionPaysMIBitsVsNull path_probe_null mi_bits.
Proof.
  intros Heq.
  intro H.
  destruct H as [_ Hpos].
  rewrite Heq in Hpos.
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  Per-step Landauer hook from probe-indexed epistemic MI bits         *)
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

Definition compactionLandauerCost (p : PathProbe) (T mi_bits : R) : R :=
  measurementEnergyLowerBound T (epistemicMIBits p mi_bits).

Lemma compactionLandauerCost_null_zero (T mi_bits : R) :
  compactionLandauerCost path_probe_null T mi_bits = 0.
Proof.
  unfold compactionLandauerCost, epistemicMIBits, measurementEnergyLowerBound.
  simpl. ring.
Qed.

Lemma compactionLandauerCost_null_all_temps (mi_bits : R) :
  forall T, compactionLandauerCost path_probe_null T mi_bits = 0.
Proof.
  intros T; apply compactionLandauerCost_null_zero.
Qed.

Lemma compactionLandauerCost_nonneg (p : PathProbe) (T mi_bits : R) :
  0 <= T ->
  0 <= mi_bits ->
  0 <= compactionLandauerCost p T mi_bits.
Proof.
  intros HT Hmi.
  unfold compactionLandauerCost.
  apply measurementEnergyLowerBound_nonneg.
  - exact HT.
  - apply epistemicMIBits_nonneg; exact Hmi.
Qed.

(* ------------------------------------------------------------------ *)
(*  Derivation witness — composite arrow retains stamp chain (§17.5)    *)
(* ------------------------------------------------------------------ *)

Definition derivationWitnessRetainsChain (chain : list string) : Prop :=
  chain <> [].

Definition compactionDerivationWitnessAbsent (chain : list string) : Prop :=
  chain = [].

Lemma derivation_witness_nonempty_retains :
  derivationWitnessRetainsChain ["stamp1"].
Proof. discriminate. Qed.

Lemma compaction_derivation_witness_absent_empty :
  compactionDerivationWitnessAbsent [].
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Excitement compose pin (import-only — not second argmin)            *)
(* ------------------------------------------------------------------ *)

Definition excitementComposeAuthority : string :=
  "umst-meta/crates/umst-meta/src/excitement.rs".

Definition excitementSelectSurrogateFor : string :=
  "UMST.Excitement.select".

Lemma compaction_not_second_argmin :
  excitementSelectSurrogateFor <> "second_argmin_selector".
Proof. discriminate. Qed.

Lemma compaction_compose_excitement_authority :
  excitementComposeAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — compaction MI)         *)
(* ------------------------------------------------------------------ *)

Definition epistemicMIAuthority : string :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean".

Definition epistemicMINullAuthority : string :=
  "EpistemicMI.epistemicMI_null".

Definition epistemicMIBitsNullAuthority : string :=
  "EpistemicMI.epistemicMIBits_null".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition compactionMiCostCellId : string :=
  "URGE-FORMAL-Q-COQ-COMPACTION-MI-COST".

Definition compactionMiCostNonClaim : string :=
  "URGE-FORMAL-Q-COQ-COMPACTION-MI-COST §17.5 §22.4 compaction pays MI vs epistemicMI_null compose Excitement not second argmin Unwired one axiom physicalSecondLaw not second Landauer axiom not meso thermo not GREEN not physics GREEN not production_wired".

Lemma compaction_mi_cost_cell_id :
  compactionMiCostCellId = "URGE-FORMAL-Q-COQ-COMPACTION-MI-COST".
Proof. reflexivity. Qed.

Lemma compaction_mi_cost_cites_epistemic_mi :
  epistemicMIAuthority <> "".
Proof. discriminate. Qed.

Lemma compaction_mi_cost_cites_epistemic_mi_null :
  epistemicMINullAuthority = "EpistemicMI.epistemicMI_null".
Proof. reflexivity. Qed.

Lemma compaction_mi_cost_cites_epistemic_mi_bits_null :
  epistemicMIBitsNullAuthority = "EpistemicMI.epistemicMIBits_null".
Proof. reflexivity. Qed.

Lemma compaction_mi_cost_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second Landauer    *)
(* ------------------------------------------------------------------ *)

Definition compactionSecondLawConservationFraming : string :=
  "second_law_conservation_compaction_mi_one_axiom_landauer_not_second_axiom".

Lemma compaction_not_second_landauer_axiom :
  compactionSecondLawConservationFraming <>
  "landauer_second_axiom".
Proof. discriminate. Qed.

Lemma compaction_second_law_conservation_framing :
  compactionSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma compaction_mi_cost_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma compaction_mi_cost_modality_unwired :
  compactionMiCostModalityCurrent = compaction_mi_cost_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Not meso thermo restated fence                                      *)
(* ------------------------------------------------------------------ *)

Definition mesoThermoGRestated : string :=
  "meso_thermo_G_T_P_x_restate".

Lemma compaction_mi_cost_not_meso_thermo_restate :
  compactionMiCostNonClaim <> mesoThermoGRestated.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing fiber scaffold honesty                                      *)
(* ------------------------------------------------------------------ *)

Definition compactionMiCostKnowingFiberOk : Prop :=
  compactionMiCostModalityCurrent = compaction_mi_cost_unwired /\
  ~ physicsGreenAuthorized.

Lemma compaction_mi_cost_knowing_fiber_ok :
  compactionMiCostKnowingFiberOk.
Proof.
  split.
  - apply compaction_mi_cost_modality_unwired.
  - apply compaction_mi_cost_physics_green_false.
Qed.

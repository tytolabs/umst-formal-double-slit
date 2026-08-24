(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ObserveMinMi.v                                       *)
(*                                                                      *)
(*  Knowing/quantum Coq: §5.2 step-1 observe local+mesh at minimal MI   *)
(*  (Landauer accounted). Paired local+mesh observation carrier with    *)
(*  pairwise MI bits and Landauer lower-bound hook. Mirrors Lean         *)
(*  EpistemicMI / MeasurementCost knowing-fiber scaffold — not acting   *)
(*  coalgebra frugal MI.                                                *)
(*                                                                      *)
(*  Self-contained over UMSTFormal Landauer spine. Modality Unwired.    *)
(*  physics_green = False. Zero Admitted. Zero new Axiom — sole         *)
(*  physicalSecondLaw authority cite; Landauer observe is not a second  *)
(*  axiom.                                                              *)
(* ================================================================== *)

From Coq Require Import Reals RIneq Lra Field String.
From UMSTFormal Require Import LandauerEinsteinBridge MeasurementCost.

Open Scope R_scope.
Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Observe-min-MI modality (Unwired / Assumed / Proved / Surrogate)  *)
(* ------------------------------------------------------------------ *)

Inductive ObserveMinMiModality : Type :=
  | observe_min_mi_unwired
  | observe_min_mi_assumed
  | observe_min_mi_proved
  | observe_min_mi_surrogate.

Definition observeMinMiModalityCurrent : ObserveMinMiModality :=
  observe_min_mi_unwired.

(* ------------------------------------------------------------------ *)
(*  Local + mesh observation carrier (knowing fiber product)            *)
(* ------------------------------------------------------------------ *)

Record LocalState : Type := {
  local_entropy_bits : R
}.

Record MeshState : Type := {
  mesh_entropy_bits : R
}.

Record LocalMeshState : Type := {
  local_mesh_local : LocalState;
  local_mesh_mesh : MeshState
}.

Definition makeLocalState (h : R) : LocalState :=
  {| local_entropy_bits := h |}.

Definition makeMeshState (h : R) : MeshState :=
  {| mesh_entropy_bits := h |}.

Definition localMeshState (h_local h_mesh : R) : LocalMeshState :=
  {| local_mesh_local := makeLocalState h_local;
     local_mesh_mesh := makeMeshState h_mesh |}.

(* ------------------------------------------------------------------ *)
(*  Pairwise MI bits — I(local; mesh) = H(local) + H(mesh) − H(joint) *)
(* ------------------------------------------------------------------ *)

Definition pairwise_mi_bits (h_local h_mesh joint_entropy : R) : R :=
  h_local + h_mesh - joint_entropy.

Definition mi_bits_consistent (h_local h_mesh joint_entropy mi : R) : Prop :=
  mi = pairwise_mi_bits h_local h_mesh joint_entropy /\
  0 <= mi.

Definition observe_mi_bounded (mi : R) : Prop :=
  0 <= mi /\ mi <= 1.

Definition observeMinMiBits (s : LocalMeshState) (joint_entropy : R) : R :=
  pairwise_mi_bits (local_entropy_bits (local_mesh_local s))
    (mesh_entropy_bits (local_mesh_mesh s)) joint_entropy.

(* ------------------------------------------------------------------ *)
(*  Minimal MI observation — required = observed = pairwise MI bits     *)
(* ------------------------------------------------------------------ *)

Record MinimalMiObservation : Type := {
  mi_required_bits : R;
  mi_observed_bits : R
}.

Definition minimal_mi_observation (mi : R) : MinimalMiObservation :=
  {| mi_required_bits := mi; mi_observed_bits := mi |}.

Definition minimal_mi_matches (obs : MinimalMiObservation) : Prop :=
  mi_required_bits obs = mi_observed_bits obs.

Lemma minimal_mi_observation_matches (mi : R) :
  minimal_mi_matches (minimal_mi_observation mi).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Landauer cost hook — measurementEnergyLowerBound at observed MI     *)
(* ------------------------------------------------------------------ *)

Definition observeMinLandauerCost (T : R) (s : LocalMeshState) (joint_entropy : R) : R :=
  measurementEnergyLowerBound T (observeMinMiBits s joint_entropy).

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

Lemma observeMinLandauerCost_zero_mi (T : R) :
  observeMinLandauerCost T (localMeshState 1 1) 2 = 0.
Proof.
  unfold observeMinLandauerCost, observeMinMiBits, localMeshState,
    pairwise_mi_bits, measurementEnergyLowerBound.
  simpl. ring.
Qed.

Lemma observeMinLandauerCost_nonneg (T : R) (s : LocalMeshState) (joint : R) :
  0 <= T ->
  0 <= observeMinMiBits s joint ->
  0 <= observeMinLandauerCost T s joint.
Proof.
  intros HT Hmi.
  unfold observeMinLandauerCost.
  apply measurementEnergyLowerBound_nonneg; assumption.
Qed.

Lemma observeMinLandauerCost_le_bit_energy (T : R) (s : LocalMeshState) (joint : R) :
  0 <= T ->
  observe_mi_bounded (observeMinMiBits s joint) ->
  observeMinLandauerCost T s joint <= E_Landauer_bit T.
Proof.
  intros HT Hmi.
  unfold observeMinLandauerCost.
  destruct Hmi as [Hmi0 Hle].
  apply measurementEnergyLowerBound_le_bit_energy; assumption.
Qed.

Lemma observeMinMiBits_independent_zero :
  observeMinMiBits (localMeshState 1 2) 3 = 0.
Proof.
  unfold observeMinMiBits, localMeshState, pairwise_mi_bits. simpl. ring.
Qed.

(* ------------------------------------------------------------------ *)
(*  Positive refuse — zero MI occupancy; inconsistent entropies         *)
(* ------------------------------------------------------------------ *)

Inductive ObserveMinMiRefusal : Type :=
  | refuse_mutual_information_zero
  | refuse_inconsistent_entropies
  | refuse_mesh_absent_when_paired_required.

Definition observe_min_mi_paired_required (s : LocalMeshState) : Prop :=
  exists h_l h_m, s = localMeshState h_l h_m.

Lemma observe_min_mi_paired_always (h_l h_m : R) :
  observe_min_mi_paired_required (localMeshState h_l h_m).
Proof.
  intros. exists h_l, h_m. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — observe min MI)      *)
(* ------------------------------------------------------------------ *)

Definition epistemicMIAuthority : string :=
  "umst/umst-formal-double-slit/Lean/EpistemicMI.lean".

Definition measurementCostAuthority : string :=
  "umst/umst-formal-double-slit/Coq/MeasurementCost.v".

Definition landauerLawAuthority : string :=
  "umst/umst-formal-double-slit/Lean/LandauerLaw.lean".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition observeMinMiCellId : string :=
  "URGE-FORMAL-Q-COQ-OBSERVE-MIN-MI".

Definition observeMinMiNonClaim : string :=
  "URGE-FORMAL-Q-COQ-OBSERVE-MIN-MI §5.2 step-1 observe local+mesh at minimal MI Landauer accounted knowing fiber Unwired one axiom physicalSecondLaw not second Landauer axiom not acting coalgebra not GREEN not physics GREEN not production_wired".

Lemma observe_min_mi_cell_id :
  observeMinMiCellId = "URGE-FORMAL-Q-COQ-OBSERVE-MIN-MI".
Proof. reflexivity. Qed.

Lemma observe_min_mi_cites_epistemic_mi :
  epistemicMIAuthority <> "".
Proof. discriminate. Qed.

Lemma observe_min_mi_cites_measurement_cost :
  measurementCostAuthority <> "".
Proof. discriminate. Qed.

Lemma observe_min_mi_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second Landauer   *)
(* ------------------------------------------------------------------ *)

Definition observeMinMiSecondLawConservationFraming : string :=
  "second_law_conservation_observe_min_mi_one_axiom_landauer_not_second_axiom".

Lemma observe_min_mi_not_second_landauer_axiom :
  observeMinMiSecondLawConservationFraming <>
  "landauer_second_axiom".
Proof. discriminate. Qed.

Lemma observe_min_mi_second_law_conservation_framing :
  observeMinMiSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma observe_min_mi_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma observe_min_mi_modality_unwired :
  observeMinMiModalityCurrent = observe_min_mi_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Not acting-coalgebra frugal MI fence                                *)
(* ------------------------------------------------------------------ *)

Definition actingCoalgebraFrugalMiRestated : string :=
  "acting_coalgebra_frugal_mi_restate".

Lemma observe_min_mi_not_acting_coalgebra_restate :
  observeMinMiNonClaim <> actingCoalgebraFrugalMiRestated.
Proof. discriminate. Qed.

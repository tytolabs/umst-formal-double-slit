(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal-Double-Slit: KnowingFibreLaw.v                         *)
(*                                                                      *)
(*  Twin of Lean/KnowingFibreInstance.lean and Lean/KnowingFibreLaw.lean: *)
(*  the knowing fibre's processes as instances of the erase and        *)
(*  measure-feedback cases of umst-formal's one predicate SecondLaw    *)
(*  (umst-formal Coq/Process.v). The two cases are stated below on     *)
(*  the records of Process.v (HeatBath, ErasureProcess,                 *)
(*  FeedbackProcess), clause for clause; this tree cannot load         *)
(*  Process.v itself while both trees map Constants/SI.v to the one    *)
(*  logical name UMSTFormal.Constants.SI (cell FORMAL-KNOWING-TWIN-    *)
(*  LAW-IMPORT).                                                        *)
(* ================================================================== *)

From Stdlib Require Import Reals Lra RIneq QArith Qreals.
From UMSTFormal Require Import DensityStateSpec ComplementaritySpec VonNeumannEntropySpec.
Require Import UMSTFormal.Constants.SI.

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  The two cases of SecondLaw (umst-formal Coq/Process.v)             *)
(* ------------------------------------------------------------------ *)

(** A heat bath at a positive temperature (kelvin). *)
Record HeatBath : Type := mkHeatBath {
  bathTemp : R;
  bathTemp_pos : 0 < bathTemp
}.

(** An erasure: its bath and the work it dissipates (units of k_B times kelvin). *)
Record ErasureProcess : Type := mkErasure {
  erasureBath : HeatBath;
  work : R
}.

(** Measurement and feedback: external work, free-energy change, bath. *)
Record FeedbackProcess : Type := mkFeedback {
  feedbackBath : HeatBath;
  extWork : R;
  deltaFreeEnergy : R
}.

(** The exact SI Boltzmann constant of Constants/SI.v. *)
Definition kB : R := Q2R boltzmann.

Lemma kB_pos : 0 < kB.
Proof.
  unfold kB, Q2R, boltzmann; simpl.
  apply Rmult_lt_0_compat; [apply IZR_lt; reflexivity | apply Rinv_0_lt_compat; apply IZR_lt; reflexivity].
Qed.

(** The erase case on a binary prior of first weight [p]: S(prior) - S(Dirac) <= W / T. *)
Definition eraseCase (e : ErasureProcess) (p : R) : Prop :=
  shannon_binary p - shannon_binary 1 <= work e / bathTemp (erasureBath e).

(** The measure-feedback case against the mutual information [mi] (nats): W_ext <= -dF + k_B T I. *)
Definition measureFeedbackCase (f : FeedbackProcess) (mi : R) : Prop :=
  extWork f <= - deltaFreeEnergy f + kB * bathTemp (feedbackBath f) * mi.

Lemma shannon_binary_one : shannon_binary 1 = 0.
Proof.
  unfold shannon_binary. replace (1 - 1) with 0 by ring. rewrite negMulLog_one, negMulLog_zero. ring.
Qed.

Lemma ln2_pos : 0 < ln 2.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

(* ------------------------------------------------------------------ *)
(*  Energies of information (twins of DoubleSlitCore, LandauerBound,   *)
(*  EpistemicMI and MeasurementCost)                                    *)
(* ------------------------------------------------------------------ *)

Definition landauerBitEnergy (T : R) : R := kB * T * ln 2.

Definition pathEntropyBits (rho : DensityMatrix2) : R := vonNeumannDiagonal rho / ln 2.

Definition landauerCostDiagonal (rho : DensityMatrix2) (T : R) : R :=
  landauerBitEnergy T * pathEntropyBits rho.

Inductive PathProbe : Type := nullProbe | whichPathProbe.

Definition EpistemicMI (p : PathProbe) (rho : DensityMatrix2) : R :=
  match p with
  | nullProbe => 0
  | whichPathProbe => vonNeumannDiagonal rho
  end.

Definition measurementCost (p : PathProbe) (rho : DensityMatrix2) (T : R) : R :=
  landauerBitEnergy T * (EpistemicMI p rho / ln 2).

Lemma EpistemicMI_le_ln2 (p : PathProbe) (rho : DensityMatrix2) : EpistemicMI p rho <= ln 2.
Proof.
  destruct p; simpl; [pose proof ln2_pos; lra | apply vonNeumannDiagonal_le_ln2].
Qed.

(* ------------------------------------------------------------------ *)
(*  Twins of Lean/KnowingFibreInstance.lean                            *)
(* ------------------------------------------------------------------ *)

(** The Born prior of the path qubit, by its first weight. *)
Definition pathBornDist (rho : DensityMatrix2) : R := p0 rho.

Theorem shannonEntropy_pathBornDist (rho : DensityMatrix2) :
  shannon_binary (pathBornDist rho) - shannon_binary 1 = vonNeumannDiagonal rho.
Proof. unfold pathBornDist, vonNeumannDiagonal. rewrite shannon_binary_one. ring. Qed.

(** The erasure at work T * S of the path prior. *)
Definition pathBornEraseProcess (rho : DensityMatrix2) (b : HeatBath) : ErasureProcess :=
  mkErasure b (bathTemp b * vonNeumannDiagonal rho).

Theorem pathBornErase_secondLaw (rho : DensityMatrix2) (b : HeatBath) :
  eraseCase (pathBornEraseProcess rho b) (pathBornDist rho).
Proof.
  unfold eraseCase. rewrite shannonEntropy_pathBornDist. simpl.
  pose proof (bathTemp_pos b). right. field. lra.
Qed.

(** The same instance, read as the erase case of the process family (Lean: SecondLaw (.erase _) (.erasure _)). *)
Theorem pathBornErase_processFamily (rho : DensityMatrix2) (b : HeatBath) :
  eraseCase (pathBornEraseProcess rho b) (pathBornDist rho) /\ work (pathBornEraseProcess rho b) =
    bathTemp b * vonNeumannDiagonal rho.
Proof. split; [apply pathBornErase_secondLaw | reflexivity]. Qed.

Theorem landauerCostDiagonal_eq_kB_eraseWork (rho : DensityMatrix2) (b : HeatBath) :
  landauerCostDiagonal rho (bathTemp b) = kB * work (pathBornEraseProcess rho b).
Proof.
  unfold landauerCostDiagonal, landauerBitEnergy, pathEntropyBits, pathBornEraseProcess; simpl.
  pose proof ln2_pos. field. lra.
Qed.

(** The erase hypothesis for the path qubit: admissibility in the process family. *)
Record PathEraseHypothesis (rho : DensityMatrix2) (b : HeatBath) : Prop := mkPathEraseHypothesis {
  pathErase_admissible : eraseCase (pathBornEraseProcess rho b) (pathBornDist rho)
}.

Theorem pathEraseHypothesis_default (rho : DensityMatrix2) (b : HeatBath) : PathEraseHypothesis rho b.
Proof. constructor. apply pathBornErase_secondLaw. Qed.

(** The probe's readout as a measurement with feedback: work its cost, no free-energy change. *)
Definition epistemicMeasureFeedback (p : PathProbe) (rho : DensityMatrix2) (b : HeatBath) : FeedbackProcess :=
  mkFeedback b (measurementCost p rho (bathTemp b)) 0.

Theorem measurementCost_eq_kBT_epistemicMI (p : PathProbe) (rho : DensityMatrix2) (T : R) :
  measurementCost p rho T = kB * T * EpistemicMI p rho.
Proof. unfold measurementCost, landauerBitEnergy. pose proof ln2_pos. field. lra. Qed.

(** The measure-feedback hypothesis: a record whose mutual information is the probe's, and admissibility. *)
Record MeasureFeedbackHypothesis (p : PathProbe) (rho : DensityMatrix2) (b : HeatBath) : Type :=
  mkMeasureFeedbackHypothesis {
    hyp_mi : R;
    hyp_miAlign : hyp_mi = EpistemicMI p rho;
    hyp_admissible : measureFeedbackCase (epistemicMeasureFeedback p rho b) hyp_mi
  }.

Theorem measureFeedback_admissible_iff (p : PathProbe) (rho : DensityMatrix2) (b : HeatBath) (mi : R) :
  mi = EpistemicMI p rho ->
  (measureFeedbackCase (epistemicMeasureFeedback p rho b) mi <->
     measurementCost p rho (bathTemp b) <= kB * bathTemp b * EpistemicMI p rho).
Proof.
  intro hmi. subst mi. unfold measureFeedbackCase, epistemicMeasureFeedback; simpl.
  split; intro h; lra.
Qed.

Theorem measureFeedback_null_instance (rho : DensityMatrix2) (b : HeatBath) :
  measureFeedbackCase (epistemicMeasureFeedback nullProbe rho b) 0.
Proof.
  unfold measureFeedbackCase, epistemicMeasureFeedback, measurementCost; simpl.
  replace (0 / ln 2) with 0 by (pose proof ln2_pos; field; lra). lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  Twins of Lean/KnowingFibreLaw.lean                                 *)
(* ------------------------------------------------------------------ *)

(** A joint law of two binary variables, by its four masses. *)
Record JointDist2 : Type := mkJointDist2 { j00 : R; j01 : R; j10 : R; j11 : R }.

Definition jointEntropy (j : JointDist2) : R :=
  negMulLog (j00 j) + negMulLog (j01 j) + negMulLog (j10 j) + negMulLog (j11 j).

Definition marginalX (j : JointDist2) : R := j00 j + j01 j.
Definition marginalY (j : JointDist2) : R := j00 j + j10 j.

Definition mutualInformation (j : JointDist2) : R :=
  shannon_binary (marginalX j) + shannon_binary (marginalY j) - jointEntropy j.

(** The record of a Lüders which-path measurement: the record equals the path. *)
Definition pathRecordJoint (rho : DensityMatrix2) : JointDist2 := mkJointDist2 (p0 rho) 0 0 (p1 rho).

Theorem pathRecordJoint_marginalX (rho : DensityMatrix2) : marginalX (pathRecordJoint rho) = pathBornDist rho.
Proof. unfold marginalX, pathRecordJoint, pathBornDist; simpl. ring. Qed.

Theorem pathRecordJoint_marginalY (rho : DensityMatrix2) : marginalY (pathRecordJoint rho) = pathBornDist rho.
Proof. unfold marginalY, pathRecordJoint, pathBornDist; simpl. ring. Qed.

Theorem pathRecordJoint_jointEntropy (rho : DensityMatrix2) :
  jointEntropy (pathRecordJoint rho) = shannon_binary (pathBornDist rho).
Proof.
  unfold jointEntropy, pathRecordJoint, pathBornDist, shannon_binary; simpl.
  rewrite negMulLog_zero. pose proof (trace_one rho).
  replace (1 - p0 rho) with (p1 rho) by lra. ring.
Qed.

Theorem pathRecordJoint_mutualInformation (rho : DensityMatrix2) :
  mutualInformation (pathRecordJoint rho) = EpistemicMI whichPathProbe rho.
Proof.
  unfold mutualInformation. rewrite pathRecordJoint_marginalX, pathRecordJoint_marginalY, pathRecordJoint_jointEntropy.
  unfold pathBornDist; simpl. unfold vonNeumannDiagonal. ring.
Qed.

Theorem whichPath_measureFeedback_secondLaw (rho : DensityMatrix2) (b : HeatBath) :
  measureFeedbackCase (epistemicMeasureFeedback whichPathProbe rho b) (mutualInformation (pathRecordJoint rho)).
Proof.
  apply (measureFeedback_admissible_iff whichPathProbe rho b _ (pathRecordJoint_mutualInformation rho)).
  rewrite measurementCost_eq_kBT_epistemicMI. lra.
Qed.

Theorem landauerBitEnergy_eq_kB (T : R) : landauerBitEnergy T = kB * T * ln 2.
Proof. reflexivity. Qed.

Theorem measureFeedback_extWork_le_landauerBitEnergy (f : FeedbackProcess) (p : PathProbe) (rho : DensityMatrix2)
  (mi : R) : mi = EpistemicMI p rho -> measureFeedbackCase f mi ->
  extWork f <= - deltaFreeEnergy f + landauerBitEnergy (bathTemp (feedbackBath f)).
Proof.
  intros hmi h. unfold measureFeedbackCase in h. subst mi. unfold landauerBitEnergy.
  pose proof (bathTemp_pos (feedbackBath f)) as hT. pose proof kB_pos as hk.
  pose proof (EpistemicMI_le_ln2 p rho) as hI.
  assert (kB * bathTemp (feedbackBath f) * EpistemicMI p rho <= kB * bathTemp (feedbackBath f) * ln 2).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | exact hI]. }
  lra.
Qed.

(** The readout costs at most one bit, through the law: a probe's readout admissible under the measure-feedback
    case against a record carrying its information costs at most k_B T ln 2. *)
Theorem readoutCost_le_landauerBitEnergy_of_secondLaw (p : PathProbe) (rho : DensityMatrix2) (b : HeatBath) (mi : R) :
  mi = EpistemicMI p rho -> measureFeedbackCase (epistemicMeasureFeedback p rho b) mi ->
  measurementCost p rho (bathTemp b) <= landauerBitEnergy (bathTemp b).
Proof.
  intros hmi h.
  pose proof (measureFeedback_extWork_le_landauerBitEnergy (epistemicMeasureFeedback p rho b) p rho mi hmi h) as H.
  unfold epistemicMeasureFeedback in H; simpl in H. lra.
Qed.

Theorem erase_pathRecord_work (e : ErasureProcess) (rho : DensityMatrix2) :
  eraseCase e (pathBornDist rho) -> vonNeumannDiagonal rho * bathTemp (erasureBath e) <= work e.
Proof.
  unfold eraseCase. rewrite shannonEntropy_pathBornDist. intro h.
  pose proof (bathTemp_pos (erasureBath e)) as hT.
  apply (Rmult_le_compat_r (bathTemp (erasureBath e))) in h; [| lra].
  replace (work e / bathTemp (erasureBath e) * bathTemp (erasureBath e)) with (work e) in h by (field; lra).
  exact h.
Qed.

Theorem erase_pathRecord_cost_ge_bits (e : ErasureProcess) (rho : DensityMatrix2) :
  eraseCase e (pathBornDist rho) ->
  landauerBitEnergy (bathTemp (erasureBath e)) * pathEntropyBits rho <= kB * work e.
Proof.
  intro h. apply erase_pathRecord_work in h.
  unfold landauerBitEnergy, pathEntropyBits. pose proof ln2_pos. pose proof kB_pos.
  replace (kB * bathTemp (erasureBath e) * ln 2 * (vonNeumannDiagonal rho / ln 2))
    with (kB * (vonNeumannDiagonal rho * bathTemp (erasureBath e))) by (field; lra).
  apply Rmult_le_compat_l; lra.
Qed.

Theorem negMulLog_ge_mul_one_sub (x : R) : 0 <= x -> x * (1 - x) <= negMulLog x.
Proof.
  intro hx. unfold negMulLog. destruct (Rle_dec x 0) as [Hle | Hgt].
  - assert (x = 0) by lra. subst x. lra.
  - assert (hx' : 0 < x) by lra. pose proof (ln_le_minus_one x hx') as hl.
    assert (x * ln x <= x * (x - 1)) by (apply Rmult_le_compat_l; lra). lra.
Qed.

Theorem one_sub_distinguishability_sq_le_two_mul_entropy (rho : DensityMatrix2) :
  1 - distinguishability rho * distinguishability rho <= 2 * vonNeumannDiagonal rho.
Proof.
  rewrite vonNeumannDiagonal_alt. unfold distinguishability. rewrite Rabs_sq.
  pose proof (negMulLog_ge_mul_one_sub (p0 rho) (p0_nonneg rho)).
  pose proof (negMulLog_ge_mul_one_sub (p1 rho) (p1_nonneg rho)).
  pose proof (trace_one rho) as htr.
  replace (p1 rho) with (1 - p0 rho) in * by lra.
  nra.
Qed.

Theorem erase_pathRecord_cost_ge_complementarity (e : ErasureProcess) (rho : DensityMatrix2) :
  eraseCase e (pathBornDist rho) ->
  kB * bathTemp (erasureBath e) * (1 - distinguishability rho * distinguishability rho) / 2 <= kB * work e.
Proof.
  intro h. apply erase_pathRecord_work in h.
  pose proof (one_sub_distinguishability_sq_le_two_mul_entropy rho) as hE.
  pose proof (bathTemp_pos (erasureBath e)) as hT. pose proof kB_pos as hk.
  assert (hkT : 0 <= kB * bathTemp (erasureBath e)) by (apply Rmult_le_pos; lra).
  assert (h1 : kB * bathTemp (erasureBath e) * (1 - distinguishability rho * distinguishability rho)
               <= kB * bathTemp (erasureBath e) * (2 * vonNeumannDiagonal rho))
    by (apply Rmult_le_compat_l; lra).
  assert (h2 : kB * (vonNeumannDiagonal rho * bathTemp (erasureBath e)) <= kB * work e)
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Theorem erase_pathRecord_cost_ge_visibility_sq (e : ErasureProcess) (rho : DensityMatrix2) :
  eraseCase e (pathBornDist rho) ->
  kB * bathTemp (erasureBath e) * (visibility rho * visibility rho) / 2 <= kB * work e.
Proof.
  intro h. pose proof (erase_pathRecord_cost_ge_complementarity e rho h) as hc.
  pose proof (englert_complementarity rho) as hE.
  pose proof (bathTemp_pos (erasureBath e)) as hT. pose proof kB_pos as hk.
  assert (hkT : 0 <= kB * bathTemp (erasureBath e)) by (apply Rmult_le_pos; lra).
  assert (kB * bathTemp (erasureBath e) * (visibility rho * visibility rho)
          <= kB * bathTemp (erasureBath e) * (1 - distinguishability rho * distinguishability rho))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Theorem measure_then_erase_no_net_work (rho : DensityMatrix2) (f : FeedbackProcess) (e : ErasureProcess) :
  bathTemp (feedbackBath f) = bathTemp (erasureBath e) -> deltaFreeEnergy f = 0 ->
  measureFeedbackCase f (mutualInformation (pathRecordJoint rho)) -> eraseCase e (pathBornDist rho) ->
  extWork f <= kB * work e.
Proof.
  intros hbath hF hmeas herase. unfold measureFeedbackCase in hmeas.
  rewrite pathRecordJoint_mutualInformation, hF, hbath in hmeas. simpl in hmeas.
  apply erase_pathRecord_work in herase. pose proof kB_pos as hk.
  assert (kB * (vonNeumannDiagonal rho * bathTemp (erasureBath e)) <= kB * work e)
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(** The reset process of LandauerBound: an initial state, a dissipated heat, and its Landauer bound. *)
Record ResetProcess (T : R) : Type := mkResetProcess {
  initial : DensityMatrix2;
  dissipatedHeat : R;
  resetBound : landauerCostDiagonal initial T <= dissipatedHeat
}.

(** The reset whose heat is the erasure work in joules takes its bound from the erase case. *)
Definition resetProcess_of_secondLaw (e : ErasureProcess) (rho : DensityMatrix2)
  (h : eraseCase e (pathBornDist rho)) : ResetProcess (bathTemp (erasureBath e)) :=
  mkResetProcess (bathTemp (erasureBath e)) rho (kB * work e) (erase_pathRecord_cost_ge_bits e rho h).

(* ------------------------------------------------------------------ *)
(*  The measurement channel: the Lüders which-path map                  *)
(* ------------------------------------------------------------------ *)

(** The Lüders which-path channel keeps the Born weights and removes the coherence. *)
Definition whichPathApply (rho : DensityMatrix2) : DensityMatrix2.
Proof.
  refine (mkDensityMatrix2 (p0 rho) (p1 rho) 0 0 (p0_nonneg rho) (p1_nonneg rho) (trace_one rho) _).
  pose proof (p0_p1_nonneg rho). lra.
Defined.

Theorem fringeVisibility_whichPath_apply (rho : DensityMatrix2) : visibility (whichPathApply rho) = 0.
Proof.
  unfold visibility, whichPathApply; simpl. replace (0 * 0 + 0 * 0) with 0 by ring. rewrite sqrt_0. ring.
Qed.

Theorem measurementCost_le_landauerBitEnergy (p : PathProbe) (rho : DensityMatrix2) (T : R) :
  0 <= T -> measurementCost p rho T <= landauerBitEnergy T.
Proof.
  intro hT. rewrite measurementCost_eq_kBT_epistemicMI. unfold landauerBitEnergy.
  pose proof kB_pos. pose proof (EpistemicMI_le_ln2 p rho).
  apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | lra].
Qed.

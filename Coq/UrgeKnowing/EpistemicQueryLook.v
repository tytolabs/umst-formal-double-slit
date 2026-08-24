(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: EpistemicQueryLook.v                                  *)
(*                                                                      *)
(*  Knowing/quantum Coq: §18 query is verification cost                *)
(*  (information-up), not coordination. An epistemic query look on the  *)
(*  quantum knowing fiber pays information-up verification cost — not   *)
(*  multi-agent coordination theater or a second ℚ Excitement argmin.   *)
(*  Mirrors Rust `epistemic_query_look` on the knowing fiber.           *)
(*                                                                      *)
(*  Self-contained over UMSTFormal MeasurementCost spine. Modality       *)
(*  Unwired. physics_green = False. Zero Admitted. Zero new Axiom —      *)
(*  sole axiom framing cites LandauerLaw.physicalSecondLaw only.         *)
(* ================================================================== *)

From Coq Require Import Reals RIneq Lra Field String.
From UMSTFormal Require Import LandauerEinsteinBridge MeasurementCost.
Open Scope R_scope.
Open Scope string.

Lemma measurementEnergyLowerBound_nonneg (T mi : R) :
  0 <= T -> 0 <= mi -> 0 <= measurementEnergyLowerBound T mi.
Proof.
  intros HT Hmi.
  unfold measurementEnergyLowerBound, E_Landauer_bit.
  apply Rmult_le_pos; [exact Hmi|].
  apply Rmult_le_pos; [|apply Rlt_le, ln2_pos].
  apply Rmult_le_pos; [apply Rlt_le, kB_SI_pos|exact HT].
Qed.

(* ------------------------------------------------------------------ *)
(*  Epistemic query look modality (Unwired / Assumed / Proved /         *)
(*  Surrogate)                                                          *)
(* ------------------------------------------------------------------ *)

Inductive EpistemicQueryLookModality : Type :=
  | epistemic_query_look_unwired
  | epistemic_query_look_assumed
  | epistemic_query_look_proved
  | epistemic_query_look_surrogate.

Definition epistemicQueryLookModalityCurrent : EpistemicQueryLookModality :=
  epistemic_query_look_unwired.

(* ------------------------------------------------------------------ *)
(*  Formal fiber — knowing vs meso acting                               *)
(* ------------------------------------------------------------------ *)

Inductive FormalFiber : Type :=
  | formal_fiber_meso_acting
  | formal_fiber_quantum_knowing.

Definition formalFiberQuantumKnowing : FormalFiber :=
  formal_fiber_quantum_knowing.

Definition formalFiberMesoActing : FormalFiber :=
  formal_fiber_meso_acting.

(* ------------------------------------------------------------------ *)
(*  §18 query class — verification cost vs coordination theater         *)
(* ------------------------------------------------------------------ *)

Inductive QueryLookClass : Type :=
  | query_verification_cost (verification_bits : R)
  | query_coordination_theater.

Definition queryLookClassIsVerificationCost (c : QueryLookClass) : Prop :=
  match c with
  | query_verification_cost _ => True
  | query_coordination_theater => False
  end.

Definition queryLookClassIsCoordinationTheater (c : QueryLookClass) : Prop :=
  match c with
  | query_verification_cost _ => False
  | query_coordination_theater => True
  end.

Record EpistemicQueryLook := {
  look_class : QueryLookClass;
  look_fiber : FormalFiber
}.

Definition epistemicQueryLookVerificationCost (verification_bits : R) :
  EpistemicQueryLook :=
  {| look_class := query_verification_cost verification_bits;
     look_fiber := formal_fiber_quantum_knowing |}.

Definition epistemicQueryLookCoordinationTheater : EpistemicQueryLook :=
  {| look_class := query_coordination_theater;
     look_fiber := formal_fiber_quantum_knowing |}.

Definition verificationBitsBounded (bits : R) : Prop :=
  0 < bits /\ bits <= 1.

(* ------------------------------------------------------------------ *)
(*  Typed positive refuse reasons                                       *)
(* ------------------------------------------------------------------ *)

Inductive EpistemicQueryLookRefusal : Type :=
  | refusal_coordination_theater
  | refusal_meso_fiber_misroute
  | refusal_non_positive_verification_bits
  | refusal_second_argmin.

Inductive EpistemicQueryLookOutcome : Type :=
  | outcome_admitted (verification_bits : R)
  | outcome_refused (reason : EpistemicQueryLookRefusal).

Definition admitEpistemicQueryLook (look : EpistemicQueryLook) :
  EpistemicQueryLookOutcome :=
  match look with
  | {| look_class := query_coordination_theater; look_fiber := _ |} =>
      outcome_refused refusal_coordination_theater
  | {| look_class := query_verification_cost bits;
       look_fiber := formal_fiber_meso_acting |} =>
      outcome_refused refusal_meso_fiber_misroute
  | {| look_class := query_verification_cost bits;
       look_fiber := formal_fiber_quantum_knowing |} =>
      if Rlt_dec bits 0 then
        outcome_refused refusal_non_positive_verification_bits
      else
        outcome_admitted bits
  end.

Definition refuseCoordinationTheater :
  option EpistemicQueryLookRefusal :=
  Some refusal_coordination_theater.

Definition refuseSecondArgminSelector :
  option EpistemicQueryLookRefusal :=
  Some refusal_second_argmin.

(* ------------------------------------------------------------------ *)
(*  Verification cost energy hook (information-up via MeasurementCost)  *)
(* ------------------------------------------------------------------ *)

Definition queryLookVerificationEnergy (T verification_bits : R) : R :=
  measurementEnergyLowerBound T verification_bits.

Lemma queryLookVerificationEnergy_nonneg (T verification_bits : R) :
  0 <= T -> 0 <= verification_bits ->
  0 <= queryLookVerificationEnergy T verification_bits.
Proof.
  intros HT Hbits.
  unfold queryLookVerificationEnergy.
  apply measurementEnergyLowerBound_nonneg.
  - exact HT.
  - exact Hbits.
Qed.

Lemma queryLookVerificationEnergy_zero_bits (T : R) :
  queryLookVerificationEnergy T 0 = 0.
Proof.
  unfold queryLookVerificationEnergy.
  apply zero_info_zero_energy.
Qed.

Lemma queryLookVerificationEnergy_positive_bits (T bits : R) :
  0 < T -> verificationBitsBounded bits ->
  0 < queryLookVerificationEnergy T bits.
Proof.
  intros HT [Hpos _].
  unfold queryLookVerificationEnergy, verificationBitsBounded in *.
  unfold measurementEnergyLowerBound, E_Landauer_bit.
  apply Rmult_lt_0_compat; [exact Hpos|].
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; [exact kB_SI_pos| exact HT].
  - exact ln2_pos.
Qed.

(* ------------------------------------------------------------------ *)
(*  Excitement compose pin (import-only — no second argmin)             *)
(* ------------------------------------------------------------------ *)

Definition metaExcitementModule : string :=
  "umst-meta/crates/umst-meta/src/excitement.rs".

Definition composeSurrogateFor : string :=
  "UMST.Excitement.select".

Definition secondArgminSelectorTag : string :=
  "second_Q_argmin_selector".

Lemma epistemic_query_look_compose_surrogate_ok :
  composeSurrogateFor = "UMST.Excitement.select".
Proof. reflexivity. Qed.

Lemma epistemic_query_look_not_second_argmin :
  composeSurrogateFor <> secondArgminSelectorTag.
Proof. discriminate. Qed.

Lemma epistemic_query_look_meta_excitement_cited :
  metaExcitementModule <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Admit / refuse lemmas (positive refuse, not only !physics_green)    *)
(* ------------------------------------------------------------------ *)

Lemma epistemic_query_look_admits_verification_cost (bits : R) :
  0 <= bits ->
  admitEpistemicQueryLook (epistemicQueryLookVerificationCost bits) =
  outcome_admitted bits.
Proof.
  intros Hbits.
  unfold admitEpistemicQueryLook, epistemicQueryLookVerificationCost.
  destruct (Rlt_dec bits 0); [lra|reflexivity].
Qed.

Lemma epistemic_query_look_refuses_coordination_theater :
  admitEpistemicQueryLook epistemicQueryLookCoordinationTheater =
  outcome_refused refusal_coordination_theater.
Proof. reflexivity. Qed.

Lemma epistemic_query_look_refuses_meso_fiber (bits : R) :
  admitEpistemicQueryLook
    {| look_class := query_verification_cost bits;
       look_fiber := formal_fiber_meso_acting |} =
  outcome_refused refusal_meso_fiber_misroute.
Proof. reflexivity. Qed.

Lemma epistemic_query_look_refuses_negative_bits (bits : R) :
  bits < 0 ->
  admitEpistemicQueryLook (epistemicQueryLookVerificationCost bits) =
  outcome_refused refusal_non_positive_verification_bits.
Proof.
  intros Hneg.
  unfold admitEpistemicQueryLook, epistemicQueryLookVerificationCost.
  destruct (Rlt_dec bits 0); [reflexivity|lra].
Qed.

Lemma epistemic_query_look_refuse_coordination_theater_ok :
  refuseCoordinationTheater = Some refusal_coordination_theater.
Proof. reflexivity. Qed.

Lemma epistemic_query_look_refuse_second_argmin_ok :
  refuseSecondArgminSelector = Some refusal_second_argmin.
Proof. reflexivity. Qed.

Lemma epistemic_query_look_knowing_fiber_ok :
  (epistemicQueryLookVerificationCost (1/1)).(look_fiber) =
  formal_fiber_quantum_knowing.
Proof. reflexivity. Qed.

Lemma epistemic_query_look_verification_class_ok (bits : R) :
  queryLookClassIsVerificationCost
    (epistemicQueryLookVerificationCost bits).(look_class).
Proof. simpl. exact I. Qed.

Lemma epistemic_query_look_coordination_class_ok :
  queryLookClassIsCoordinationTheater
    epistemicQueryLookCoordinationTheater.(look_class).
Proof. simpl. exact I. Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — query look)          *)
(* ------------------------------------------------------------------ *)

Definition landauerLawAuthority : string :=
  "umst-formal-double-slit/Lean/LandauerLaw.lean".

Definition physicalSecondLawAuthority : string :=
  "LandauerLaw.physicalSecondLaw".

Definition hsAnchorEpistemicQueryLook : string :=
  "umst-formal-double-slit/Haskell/src/UrgeKnowing/EpistemicQueryLook.hs".

Definition formalFiberQuantumKnowingAuthority : string :=
  "umst-formal-double-slit/quantum_knowing".

Definition epistemicQueryLookCellId : string :=
  "URGE-FORMAL-Q-COQ-EPISTEMIC-QUERY-LOOK".

Definition epistemicQueryLookNonClaim : string :=
  "URGE-FORMAL-Q-COQ-EPISTEMIC-QUERY-LOOK epistemic_query_look Unwired §18 query is verification cost information-up not coordination compose Excitement no second argmin umst-formal-double-slit quantum_knowing physicalSecondLaw sole axiom framing not physics GREEN not production_wired".

Lemma epistemic_query_look_cell_id :
  epistemicQueryLookCellId = "URGE-FORMAL-Q-COQ-EPISTEMIC-QUERY-LOOK".
Proof. reflexivity. Qed.

Lemma epistemic_query_look_cites_physical_second_law :
  physicalSecondLawAuthority = "LandauerLaw.physicalSecondLaw".
Proof. reflexivity. Qed.

Lemma epistemic_query_look_cites_landauer_law :
  landauerLawAuthority <> "".
Proof. discriminate. Qed.

Lemma epistemic_query_look_non_claim_verification_cost :
  epistemicQueryLookNonClaim <> "coordination theater only".
Proof. discriminate. Qed.

Lemma epistemic_query_look_non_claim_not_coordination :
  epistemicQueryLookNonClaim <> "coordination not verification cost".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Sole axiom framing: physicalSecondLaw; not second axiom              *)
(* ------------------------------------------------------------------ *)

Definition epistemicQuerySecondLawFraming : string :=
  "physicalSecondLaw_sole_axiom_framing_not_second_axiom".

Definition secondAxiomTag : string :=
  "epistemic_query_second_axiom".

Lemma epistemic_query_look_not_second_axiom :
  epistemicQuerySecondLawFraming <> secondAxiomTag.
Proof. discriminate. Qed.

Lemma epistemic_query_look_second_law_framing :
  epistemicQuerySecondLawFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Definition productionWiredAuthorized : Prop := False.

Lemma epistemic_query_look_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma epistemic_query_look_production_wired_false :
  ~ productionWiredAuthorized.
Proof. intro H; exact H. Qed.

Lemma epistemic_query_look_modality_unwired :
  epistemicQueryLookModalityCurrent = epistemic_query_look_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Honesty probe aggregate (typed refuse + compose pin)                *)
(* ------------------------------------------------------------------ *)

Definition epistemicQueryLookDeepenHonest : Prop :=
  epistemicQueryLookModalityCurrent = epistemic_query_look_unwired /\
  ~ physicsGreenAuthorized /\
  ~ productionWiredAuthorized /\
  admitEpistemicQueryLook (epistemicQueryLookVerificationCost (3/10)) =
    outcome_admitted (3/10) /\
  admitEpistemicQueryLook epistemicQueryLookCoordinationTheater =
    outcome_refused refusal_coordination_theater /\
  refuseSecondArgminSelector = Some refusal_second_argmin /\
  composeSurrogateFor = "UMST.Excitement.select" /\
  (epistemicQueryLookVerificationCost (1/1)).(look_fiber) =
    formal_fiber_quantum_knowing.

Lemma epistemic_query_look_deepen_honest :
  epistemicQueryLookDeepenHonest.
Proof.
  unfold epistemicQueryLookDeepenHonest.
  split; [reflexivity|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [apply epistemic_query_look_admits_verification_cost; lra|].
  split; [apply epistemic_query_look_refuses_coordination_theater|].
  split; [apply epistemic_query_look_refuse_second_argmin_ok|].
  split; [apply epistemic_query_look_compose_surrogate_ok|].
  apply epistemic_query_look_knowing_fiber_ok.
Qed.

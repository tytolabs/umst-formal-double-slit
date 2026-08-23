(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: PartialConservation.v                                 *)
(*                                                                      *)
(*  Knowing-fiber Coq: TYPE-05 partial Interact conservation.          *)
(*  Interact is partial: admissible pair vs forbidden pair lemmas;       *)
(*  total-claim refuse (no pretend-success total morphism).            *)
(*  Modality Unwired; type05PartialProved Unwired not Proved.           *)
(*  Geometry routes knowing/quantum fiber not meso acting.               *)
(*  Not 118² GREEN table.                                              *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). Modality Unwired.                    *)
(*  physics_green = False. Zero Admitted. One axiom second law +        *)
(*  conservation framing — partial conservation is not a second axiom. *)
(* ================================================================== *)

From Stdlib Require Import Arith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  TYPE-05 partial conservation modality (Unwired / Assumed /        *)
(*  Proved / Surrogate)                                                *)
(* ------------------------------------------------------------------ *)

Inductive PartialConservationModality : Type :=
  | partial_conservation_unwired
  | partial_conservation_assumed
  | partial_conservation_proved
  | partial_conservation_surrogate.

Definition partialConservationModalityCurrent : PartialConservationModality :=
  partial_conservation_unwired.

Definition partial_lattice_cardinality : nat := 4.

Lemma partial_lattice_cardinality_is_four :
  partial_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma partial_lattice_not_118_squared :
  negb (Nat.eqb partial_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold partial_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  L0 element carrier + InteractStep (partial morphism scaffold)       *)
(* ------------------------------------------------------------------ *)

Inductive element_id : Type :=
  | elem_H
  | elem_O
  | elem_Ca
  | elem_Si.

Record interact_step : Type := {
  interact_from : element_id;
  interact_to : element_id;
  interact_tag : nat
}.

Definition element_id_beq (a b : element_id) : bool :=
  match a, b with
  | elem_H, elem_H | elem_O, elem_O | elem_Ca, elem_Ca | elem_Si, elem_Si => true
  | _, _ => false
  end.

Lemma element_id_beq_refl (e : element_id) : element_id_beq e e = true.
Proof. destruct e; reflexivity. Qed.

Definition interact_pair_admissible (left right : interact_step) : bool :=
  element_id_beq left.(interact_to) right.(interact_from).

Definition interact_pair_forbidden (left right : interact_step) : bool :=
  negb (interact_pair_admissible left right).

Definition interact_compose (left right : interact_step) : option interact_step :=
  if interact_pair_admissible left right then
    Some {| interact_from := left.(interact_from);
            interact_to := right.(interact_to);
            interact_tag := left.(interact_tag) + right.(interact_tag) + 1 |}
  else None.

Lemma interact_compose_admissible_some (left right : interact_step)
  (H : interact_pair_admissible left right = true) :
  interact_compose left right =
  Some {| interact_from := left.(interact_from);
          interact_to := right.(interact_to);
          interact_tag := left.(interact_tag) + right.(interact_tag) + 1 |}.
Proof.
  unfold interact_compose. rewrite H. reflexivity.
Qed.

Lemma interact_pair_forbidden_means_not_admissible (left right : interact_step)
  (H : interact_pair_forbidden left right = true) :
  interact_pair_admissible left right = false.
Proof.
  unfold interact_pair_forbidden, interact_pair_admissible in H.
  unfold interact_pair_admissible.
  destruct (element_id_beq left.(interact_to) right.(interact_from)) eqn:Heq.
  - simpl in H. discriminate H.
  - simpl. reflexivity.
Qed.

Lemma interact_compose_forbidden_none (left right : interact_step)
  (H : interact_pair_forbidden left right = true) :
  interact_compose left right = None.
Proof.
  unfold interact_compose.
  rewrite (interact_pair_forbidden_means_not_admissible left right H).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture interact steps — admissible vs forbidden pair witnesses       *)
(* ------------------------------------------------------------------ *)

Definition step_ca_o : interact_step :=
  {| interact_from := elem_Ca; interact_to := elem_O; interact_tag := 1 |}.

Definition step_o_h : interact_step :=
  {| interact_from := elem_O; interact_to := elem_H; interact_tag := 2 |}.

Definition step_h_si : interact_step :=
  {| interact_from := elem_H; interact_to := elem_Si; interact_tag := 3 |}.

Definition step_ca_h : interact_step :=
  {| interact_from := elem_Ca; interact_to := elem_H; interact_tag := 4 |}.

Lemma admissible_pair_ca_o_o_h :
  interact_pair_admissible step_ca_o step_o_h = true.
Proof. reflexivity. Qed.

Theorem partial_interact_admissible_pair_ok :
  interact_pair_admissible step_ca_o step_o_h = true /\
  interact_compose step_ca_o step_o_h <>
  None.
Proof.
  split.
  - apply admissible_pair_ca_o_o_h.
  - intro Hnone.
    rewrite (interact_compose_admissible_some step_ca_o step_o_h admissible_pair_ca_o_o_h) in Hnone.
    discriminate Hnone.
Qed.

Lemma forbidden_pair_ca_o_h_si :
  interact_pair_forbidden step_ca_o step_h_si = true.
Proof. reflexivity. Qed.

Theorem partial_interact_forbidden_pair_refuse :
  interact_pair_forbidden step_ca_o step_h_si = true /\
  interact_compose step_ca_o step_h_si = None.
Proof.
  split.
  - apply forbidden_pair_ca_o_h_si.
  - apply (interact_compose_forbidden_none step_ca_o step_h_si).
    apply forbidden_pair_ca_o_h_si.
Qed.

(* ------------------------------------------------------------------ *)
(*  Partial conservation close verdict — fail-closed lattice              *)
(* ------------------------------------------------------------------ *)

Inductive partial_conservation_verdict : Type :=
  | verdict_unwired_ok
  | verdict_admissible_pair_ok
  | verdict_forbidden_pair_refuse
  | verdict_total_claim_refuse
  | verdict_green_invent_refuse.

Definition partial_conservation_verdict_ok (v : partial_conservation_verdict) : bool :=
  match v with
  | verdict_unwired_ok => true
  | verdict_admissible_pair_ok => true
  | _ => false
  end.

Definition partial_conservation_verdict_beq
  (v1 v2 : partial_conservation_verdict) : bool :=
  match v1, v2 with
  | verdict_unwired_ok, verdict_unwired_ok => true
  | verdict_admissible_pair_ok, verdict_admissible_pair_ok => true
  | verdict_forbidden_pair_refuse, verdict_forbidden_pair_refuse => true
  | verdict_total_claim_refuse, verdict_total_claim_refuse => true
  | verdict_green_invent_refuse, verdict_green_invent_refuse => true
  | _, _ => false
  end.

Definition evaluate_partial_conservation_close
  (m : PartialConservationModality)
  (left right : interact_step)
  (claim_total_morphism : bool)
  (claim_physics_green : bool) : partial_conservation_verdict :=
  if claim_physics_green
  then verdict_green_invent_refuse
  else if claim_total_morphism
  then verdict_total_claim_refuse
  else
    match m with
    | partial_conservation_unwired => verdict_unwired_ok
    | partial_conservation_assumed
    | partial_conservation_proved
    | partial_conservation_surrogate =>
        if interact_pair_admissible left right
        then verdict_admissible_pair_ok
        else verdict_forbidden_pair_refuse
    end.

Definition partial_interact_authorized
  (left right : interact_step)
  (claim_total_morphism : bool)
  (claim_physics_green : bool) : bool :=
  match evaluate_partial_conservation_close
          partial_conservation_proved left right claim_total_morphism claim_physics_green with
  | verdict_admissible_pair_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Partial conservation law cells — four laws, open @ Unwired            *)
(* ------------------------------------------------------------------ *)

Inductive partial_conservation_law : Type :=
  | law_admissible_pair_ok
  | law_forbidden_pair_refuse
  | law_total_claim_refuse
  | law_green_invent_refuse.

Definition partial_conservation_law_count : nat := 4.

Lemma partial_conservation_law_count_is_four :
  partial_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive partial_conservation_law_witness : Type :=
  | law_witness_open
  | law_witness_proved.

Definition evaluate_partial_conservation_law_witness
  (law : partial_conservation_law) (m : PartialConservationModality)
  : partial_conservation_law_witness :=
  match m with
  | partial_conservation_unwired
  | partial_conservation_assumed
  | partial_conservation_surrogate => law_witness_open
  | partial_conservation_proved => law_witness_proved
  end.

Lemma all_partial_conservation_laws_open_at_unwired :
  evaluate_partial_conservation_law_witness law_admissible_pair_ok
    partial_conservation_unwired = law_witness_open /\
  evaluate_partial_conservation_law_witness law_forbidden_pair_refuse
    partial_conservation_unwired = law_witness_open /\
  evaluate_partial_conservation_law_witness law_total_claim_refuse
    partial_conservation_unwired = law_witness_open /\
  evaluate_partial_conservation_law_witness law_green_invent_refuse
    partial_conservation_unwired = law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  TYPE-05 pins (structure witnesses — partial laws not Proved)        *)
(* ------------------------------------------------------------------ *)

Definition type05PartialProved : bool := false.

Lemma type05_partial_proved_false : type05PartialProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without total claim (lemma)                           *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_total_claim :
  evaluate_partial_conservation_close
    partial_conservation_unwired step_ca_o step_h_si false false =
  verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_total_claim :
  evaluate_partial_conservation_close
    partial_conservation_unwired step_ca_o step_h_si false false =
  verdict_unwired_ok.
Proof. apply unwired_close_without_total_claim. Qed.

Lemma unwired_verdict_ok_without_total_claim :
  partial_conservation_verdict_ok
    (evaluate_partial_conservation_close
       partial_conservation_unwired step_ca_o step_h_si false false) =
  true.
Proof.
  unfold partial_conservation_verdict_ok.
  rewrite unwired_close_without_total_claim.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Admissible pair — partial Interact compose succeeds                   *)
(* ------------------------------------------------------------------ *)

Lemma admissible_pair_close_ok :
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_o_h false false =
  verdict_admissible_pair_ok.
Proof. reflexivity. Qed.

Theorem partial_interact_admissible_pair_conservation :
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_o_h false false =
  verdict_admissible_pair_ok /\
  partial_interact_authorized step_ca_o step_o_h false false = true.
Proof.
  split.
  - apply admissible_pair_close_ok.
  - unfold partial_interact_authorized.
    rewrite admissible_pair_close_ok.
    reflexivity.
Qed.

Lemma admissible_pair_verdict_ok :
  partial_conservation_verdict_ok
    (evaluate_partial_conservation_close
       partial_conservation_proved step_ca_o step_o_h false false) =
  true.
Proof.
  unfold partial_conservation_verdict_ok.
  rewrite admissible_pair_close_ok.
  reflexivity.
Qed.

Lemma admissible_pair_still_not_physics_green :
  partial_conservation_verdict_ok
    (evaluate_partial_conservation_close
       partial_conservation_proved step_ca_o step_o_h false false) =
  true /\
  type05PartialProved = false.
Proof.
  split.
  - apply admissible_pair_verdict_ok.
  - apply type05_partial_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  Forbidden pair refuse — partial Interact compose fails              *)
(* ------------------------------------------------------------------ *)

Lemma forbidden_pair_refuse :
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_h_si false false =
  verdict_forbidden_pair_refuse.
Proof. reflexivity. Qed.

Theorem partial_interact_forbidden_pair_conservation_refuse :
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_h_si false false =
  verdict_forbidden_pair_refuse /\
  partial_interact_authorized step_ca_o step_h_si false false = false.
Proof.
  split.
  - apply forbidden_pair_refuse.
  - unfold partial_interact_authorized.
    rewrite forbidden_pair_refuse.
    reflexivity.
Qed.

Theorem forbidden_pair_not_ok :
  partial_conservation_verdict_ok
    (evaluate_partial_conservation_close
       partial_conservation_proved step_ca_o step_h_si false false) =
  false.
Proof.
  unfold partial_conservation_verdict_ok.
  rewrite forbidden_pair_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Total-claim refuse — no pretend-success total morphism              *)
(* ------------------------------------------------------------------ *)

Lemma total_claim_refuse :
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_o_h true false =
  verdict_total_claim_refuse.
Proof. reflexivity. Qed.

Theorem partial_interact_total_claim_refused :
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_o_h true false =
  verdict_total_claim_refuse /\
  partial_interact_authorized step_ca_o step_o_h true false = false.
Proof.
  split.
  - apply total_claim_refuse.
  - unfold partial_interact_authorized.
    rewrite total_claim_refuse.
    reflexivity.
Qed.

Theorem total_claim_not_ok :
  partial_conservation_verdict_ok
    (evaluate_partial_conservation_close
       partial_conservation_proved step_ca_o step_o_h true false) =
  false.
Proof.
  unfold partial_conservation_verdict_ok.
  rewrite total_claim_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_partial_conservation_close
    partial_conservation_unwired step_ca_o step_o_h false true =
  verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  partial_conservation_verdict_ok
    (evaluate_partial_conservation_close
       partial_conservation_unwired step_ca_o step_o_h false true) =
  false.
Proof.
  unfold partial_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Partial conservation coherence scaffold — fixture witnesses           *)
(* ------------------------------------------------------------------ *)

Definition partial_conservation_coherence_scaffold : bool :=
  partial_conservation_verdict_beq
    (evaluate_partial_conservation_close
       partial_conservation_proved step_ca_o step_o_h false false)
    verdict_admissible_pair_ok &&
  partial_conservation_verdict_beq
    (evaluate_partial_conservation_close
       partial_conservation_proved step_ca_o step_h_si false false)
    verdict_forbidden_pair_refuse &&
  partial_conservation_verdict_beq
    (evaluate_partial_conservation_close
       partial_conservation_proved step_ca_o step_o_h true false)
    verdict_total_claim_refuse &&
  partial_conservation_verdict_beq
    (evaluate_partial_conservation_close
       partial_conservation_unwired step_ca_o step_o_h false true)
    verdict_green_invent_refuse.

Lemma partial_conservation_coherence_scaffold_true :
  partial_conservation_coherence_scaffold = true.
Proof.
  unfold partial_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem partial_conservation_coherence_scaffold_theorem :
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_o_h false false =
    verdict_admissible_pair_ok /\
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_h_si false false =
    verdict_forbidden_pair_refuse /\
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_o_h true false =
    verdict_total_claim_refuse /\
  evaluate_partial_conservation_close
    partial_conservation_unwired step_ca_o step_o_h false true =
    verdict_green_invent_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Inductive formal_claim_family : Type :=
  | claim_partial_conservation.

Definition partial_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition partial_conservation_knowing_fiber_ok : bool :=
  partial_conservation_fiber_ok fiber_quantum_knowing.

Definition partial_conservation_meso_acting_ok : bool :=
  partial_conservation_fiber_ok fiber_meso_acting.

Lemma partial_conservation_knowing_fiber_ok_true :
  partial_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma partial_conservation_meso_acting_not_ok :
  partial_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem partial_conservation_routes_knowing_not_meso :
  partial_conservation_knowing_fiber_ok = true /\
  partial_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply partial_conservation_knowing_fiber_ok_true.
  - apply partial_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  partial_conservation_knowing_fiber_ok &&
  negb partial_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, partial_conservation_knowing_fiber_ok,
    partial_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — partial interact + fiber + TYPE-05 pins          *)
(* ------------------------------------------------------------------ *)

Theorem partial_conservation_fixture_scaffold :
  evaluate_partial_conservation_close
    partial_conservation_unwired step_ca_o step_h_si false false =
    verdict_unwired_ok /\
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_o_h false false =
    verdict_admissible_pair_ok /\
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_h_si false false =
    verdict_forbidden_pair_refuse /\
  evaluate_partial_conservation_close
    partial_conservation_proved step_ca_o step_o_h true false =
    verdict_total_claim_refuse /\
  partial_conservation_knowing_fiber_ok = true /\
  partial_conservation_meso_acting_ok = false /\
  type05PartialProved = false.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — partial conservation)  *)
(* ------------------------------------------------------------------ *)

Definition partialConservationAuthority : string :=
  "umst/umst-chem/src/partial_interact.rs".

Definition chemL0Type05Authority : string :=
  "CHEM-L0-TYPE-05".

Definition chemIntProveType05PartialAuthority : string :=
  "CHEM-INT-PROVE-TYPE-05-PARTIAL".

Definition kleisliInteractAuthority : string :=
  "umst/umst-chem/src/kleisli_interact.rs".

Definition partialConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-PARTIAL-CONSERVATION".

Definition partialConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PARTIAL-CONSERVATION TYPE-05 partial Interact conservation admissible pair forbidden pair total claim refuse no pretend success total morphism type05PartialProved false Unwired geometry knowing quantum fiber not meso acting one axiom second law conservation not second partial axiom not GREEN DFT not physics GREEN not production_wired".

Lemma partial_conservation_cell_id :
  partialConservationCellId = "CHEM-FORMAL-Q-COQ-PARTIAL-CONSERVATION".
Proof. reflexivity. Qed.

Lemma partial_conservation_cites_partial_interact_rs :
  partialConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma partial_conservation_cites_l0_type_05 :
  chemL0Type05Authority = "CHEM-L0-TYPE-05".
Proof. reflexivity. Qed.

Lemma partial_conservation_cites_int_prove_type_05_partial :
  chemIntProveType05PartialAuthority <> "".
Proof. discriminate. Qed.

Lemma partial_conservation_cites_kleisli_interact :
  kleisliInteractAuthority <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + conservation; not second partial    *)
(* ------------------------------------------------------------------ *)

Definition partialSecondLawConservationFraming : string :=
  "second_law_conservation_partial_one_axiom_not_second_partial_axiom".

Lemma partial_not_second_partial_axiom :
  partialSecondLawConservationFraming <> "second_partial_axiom".
Proof. discriminate. Qed.

Lemma partial_second_law_conservation_framing :
  partialSecondLawConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)      *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma partial_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma partial_conservation_modality_unwired :
  partialConservationModalityCurrent = partial_conservation_unwired.
Proof. reflexivity. Qed.

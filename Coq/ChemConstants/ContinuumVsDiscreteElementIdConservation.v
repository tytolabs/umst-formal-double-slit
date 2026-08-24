(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ContinuumVsDiscreteElementIdConservation.v                               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 23 **continuum_vs_discrete_element_id** **conservation**.        *)
(*  Continuum vs discrete ElementId is **two presentations of one object** on the same second-law +  *)
(*  conservation object (not a parallel continuum_vs_discrete_element_id axiom / two chemistries).         *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Continuum field vs discrete ElementId boundary; same object two charts not two chemistries.             *)
(*  continuumVsDiscreteElementIdConservationProved false. Modality Unwired.               *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/continuum_discrete_element.rs (read-only cite).     *)
(*  INT: umst/umst-chem/src/l0_tables/continuum_vs_discrete_element_id.rs (read-only cite).   *)
(*  INT: umst/umst-chem/src/element_id.rs (read-only cite).   *)
(*  PatternProductConservation.v cited.                                  *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-23 **continuum_vs_discrete_element_id** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive ContinuumVsDiscreteElementIdConservationModality : Type :=
  | cvdiec_conservation_unwired
  | cvdiec_conservation_assumed
  | cvdiec_conservation_proved
  | cvdiec_conservation_surrogate.

Definition continuumVsDiscreteElementIdConservationModalityCurrent :
  ContinuumVsDiscreteElementIdConservationModality :=
  cvdiec_conservation_unwired.

Definition cvdiec_lattice_cardinality : nat := 4.

Lemma cvdiec_lattice_cardinality_is_four :
  cvdiec_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma cvdiec_lattice_not_118_squared :
  negb (Nat.eqb cvdiec_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold cvdiec_lattice_cardinality.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  §2 PatternBundle class cardinality (north-star pinned — not 118²)   *)
(* ------------------------------------------------------------------ *)

Definition pattern_class_cardinality : nat := 25.

Lemma pattern_class_cardinality_is_25 :
  pattern_class_cardinality = 25.
Proof. reflexivity. Qed.

Lemma pattern_class_not_118_squared :
  negb (Nat.eqb pattern_class_cardinality (118 * 118)) = true.
Proof.
  unfold pattern_class_cardinality.
  reflexivity.
Qed.

Definition pattern_class_index_valid (i : nat) : bool :=
  Nat.ltb i pattern_class_cardinality.

(* North-star §2 class 23 — continuum_vs_discrete_element_id concurrent Π_c factor. *)
Definition pattern_class_continuum_vs_discrete_element_id_idx : nat := 23.

Lemma pattern_class_continuum_vs_discrete_element_id_idx_is_23 :
  pattern_class_continuum_vs_discrete_element_id_idx = 23.
Proof. reflexivity. Qed.

Lemma cvdiec_class_index_valid :
  pattern_class_index_valid pattern_class_continuum_vs_discrete_element_id_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_continuum_vs_discrete_element_id_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierContinuumVsDiscreteElementIdRowId : string := "X23".

Lemma cross_classifier_continuum_vs_discrete_element_id_row_named :
  crossClassifierContinuumVsDiscreteElementIdRowId = "X23".
Proof. reflexivity. Qed.

Definition pattern_class_continuum_vs_discrete_element_id_tag : string :=
  "continuum_vs_discrete_element_id".

Definition north_star_class_23_continuum_vs_discrete_tag : string :=
  "class 23 continuum_vs_discrete_element_id".

Lemma pattern_class_continuum_vs_discrete_element_id_tag_nonempty :
  pattern_class_continuum_vs_discrete_element_id_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_23_continuum_vs_discrete_tag_nonempty :
  north_star_class_23_continuum_vs_discrete_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — carbon Z=6 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition carbon_atomic_number_z : nat := 6.

Lemma carbon_atomic_number_z_is_6 :
  carbon_atomic_number_z = 6.
Proof. reflexivity. Qed.

Definition carbon_z_valid : bool :=
  Nat.ltb 0 carbon_atomic_number_z &&
  Nat.leb carbon_atomic_number_z iupac_table_cardinality.

Lemma carbon_z_valid_true : carbon_z_valid = true.
Proof.
  unfold carbon_z_valid, carbon_atomic_number_z, iupac_table_cardinality.
  reflexivity.
Qed.

Definition forbidden_z119_smuggle : nat := 119.

Definition forbidden_z119_not_in_table : bool :=
  negb (Nat.leb forbidden_z119_smuggle iupac_table_cardinality).

Lemma forbidden_z119_not_in_iupac_table :
  forbidden_z119_not_in_table = true.
Proof.
  unfold forbidden_z119_not_in_table, forbidden_z119_smuggle, iupac_table_cardinality.
  reflexivity.
Qed.

Definition cvdiec_factor_tag : string :=
  "continuum_vs_discrete_element_id".

Definition continuum_field_channel_tag : string := "continuum_field_presentation".

Definition edge_discrete_channel_tag : string := "discrete_element_id_boundary".

Lemma cvdiec_factor_tag_nonempty :
  cvdiec_factor_tag <> "".
Proof. discriminate. Qed.

Lemma continuum_field_channel_tag_nonempty :
  continuum_field_channel_tag <> "".
Proof. discriminate. Qed.

Lemma edge_discrete_channel_tag_nonempty :
  edge_discrete_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Continuum-vs-discrete product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive cvdiec_channel_slot : Type :=
  | cvdiec_slot_unwired
  | cvdiec_slot_absent
  | cvdiec_slot_present.

Definition cvdiec_channel_slot_beq (s1 s2 : cvdiec_channel_slot) : bool :=
  match s1, s2 with
  | cvdiec_slot_unwired, cvdiec_slot_unwired => true
  | cvdiec_slot_absent, cvdiec_slot_absent => true
  | cvdiec_slot_present, cvdiec_slot_present => true
  | _, _ => false
  end.

Definition cvdiec_channel_slot_is_present (s : cvdiec_channel_slot) : bool :=
  match s with
  | cvdiec_slot_present => true
  | _ => false
  end.

Definition cvdiecProductChannelCount : nat := 3.

Lemma cvdiec_product_channel_count_is_three :
  cvdiecProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = Edge discrete boundary, 2 = class 23 continuum_vs_discrete_element_id. *)
Definition cvdiec_channel_continuum_field : nat := 0.
Definition cvdiec_channel_edge_discrete : nat := 1.
Definition cvdiec_channel_class23_continuum_vs_discrete : nat := 2.

Lemma cvdiec_channel_continuum_field_idx_is_0 :
  cvdiec_channel_continuum_field = 0.
Proof. reflexivity. Qed.

Lemma cvdiec_channel_edge_discrete_idx_is_1 :
  cvdiec_channel_edge_discrete = 1.
Proof. reflexivity. Qed.

Lemma cvdiec_channel_class23_continuum_vs_discrete_idx_is_2 :
  cvdiec_channel_class23_continuum_vs_discrete = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Continuum-vs-discrete concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition cvdiec_channel_bundle : Type := nat -> cvdiec_channel_slot.

Definition cvdiecBundleAllUnwired : cvdiec_channel_bundle :=
  fun _ => cvdiec_slot_unwired.

Definition cvdiecBundleAt (b : cvdiec_channel_bundle) (idx : nat)
  (slot : cvdiec_channel_slot) : cvdiec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition cvdiecBundleWithPresent
  (b : cvdiec_channel_bundle) (idx : nat) : cvdiec_channel_bundle :=
  cvdiecBundleAt b idx cvdiec_slot_present.

Fixpoint count_cvdiec_present_up_to (b : cvdiec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if cvdiec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_cvdiec_present_up_to b i + add
  end.

Definition cvdiecBundlePresentCount (b : cvdiec_channel_bundle) : nat :=
  count_cvdiec_present_up_to b cvdiecProductChannelCount.

Definition cvdiecBundleHolds (b : cvdiec_channel_bundle) (idx : nat) : bool :=
  cvdiec_channel_slot_is_present (b idx).

Definition cvdiecBundleIsConcurrentProduct (b : cvdiec_channel_bundle) : bool :=
  Nat.leb 2 (cvdiecBundlePresentCount b).

(* carbon Z=6 interact restriction + G-min + class 23 continuum_vs_discrete_element_id concurrent witness. *)
Definition cvdiecCarbon6Witness : cvdiec_channel_bundle :=
  cvdiecBundleWithPresent
    (cvdiecBundleWithPresent
      (cvdiecBundleWithPresent cvdiecBundleAllUnwired
        cvdiec_channel_continuum_field)
      cvdiec_channel_edge_discrete)
    cvdiec_channel_class23_continuum_vs_discrete.

Definition cvdiecEmptyWitness : cvdiec_channel_bundle :=
  cvdiecBundleAllUnwired.

Definition cvdiecSinglePresent : cvdiec_channel_bundle :=
  cvdiecBundleWithPresent cvdiecBundleAllUnwired
    cvdiec_channel_continuum_field.

Lemma continuum_field_channel_present :
  cvdiecBundleHolds cvdiecCarbon6Witness
    cvdiec_channel_continuum_field = true.
Proof. reflexivity. Qed.

Lemma edge_discrete_channel_present :
  cvdiecBundleHolds cvdiecCarbon6Witness
    cvdiec_channel_edge_discrete = true.
Proof. reflexivity. Qed.

Lemma class23_continuum_vs_discrete_channel_present :
  cvdiecBundleHolds cvdiecCarbon6Witness
    cvdiec_channel_class23_continuum_vs_discrete = true.
Proof. reflexivity. Qed.

Lemma carbon6_witness_present_count_is_three :
  cvdiecBundlePresentCount cvdiecCarbon6Witness = 3.
Proof. reflexivity. Qed.

Lemma carbon6_witness_is_concurrent_product :
  cvdiecBundleIsConcurrentProduct cvdiecCarbon6Witness = true.
Proof.
  unfold cvdiecBundleIsConcurrentProduct.
  rewrite carbon6_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma cvdiec_empty_bundle_present_count_zero :
  cvdiecBundlePresentCount cvdiecEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma cvdiec_empty_bundle_not_concurrent_product :
  cvdiecBundleIsConcurrentProduct cvdiecEmptyWitness = false.
Proof.
  unfold cvdiecBundleIsConcurrentProduct.
  rewrite cvdiec_empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma cvdiec_single_present_count_is_one :
  cvdiecBundlePresentCount cvdiecSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma cvdiec_single_present_not_concurrent_product :
  cvdiecBundleIsConcurrentProduct cvdiecSinglePresent = false.
Proof.
  unfold cvdiecBundleIsConcurrentProduct.
  rewrite cvdiec_single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive cvdiec_xor_posture : Type :=
  | cvdiec_xor_exclusive
  | cvdiec_xor_concurrent_product.

Definition cvdiecXorClassifierMarker : string := "chem_l0_continuum_vs_discrete_xor_classifier_v1".
Definition cvdiecConcurrentProductMarker : string := "chem_int_continuum_vs_discrete_product_v1".

Lemma cvdiec_xor_marker_ne_concurrent_product_marker :
  cvdiecXorClassifierMarker <> cvdiecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition cvdiecXorClassifierIncompatible (claim_xor : bool)
  (b : cvdiec_channel_bundle) : bool :=
  claim_xor && cvdiecBundleIsConcurrentProduct b.

Lemma cvdiec_xor_refuse_on_carbon6_witness :
  cvdiecXorClassifierIncompatible true cvdiecCarbon6Witness = true.
Proof.
  unfold cvdiecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma cvdiec_xor_ok_on_concurrent_product_claim :
  cvdiecXorClassifierIncompatible false cvdiecCarbon6Witness = false.
Proof. reflexivity. Qed.

Definition cvdiecProductNotXor : bool :=
  cvdiecBundleIsConcurrentProduct cvdiecCarbon6Witness &&
  cvdiecXorClassifierIncompatible true cvdiecCarbon6Witness.

Lemma cvdiec_product_not_xor_true : cvdiecProductNotXor = true.
Proof.
  unfold cvdiecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem cvdiec_concurrent_product_not_xor :
  cvdiecProductNotXor = true /\
  Nat.leb 2 (cvdiecBundlePresentCount
    cvdiecCarbon6Witness) = true /\
  cvdiecXorClassifierMarker <> cvdiecConcurrentProductMarker.
Proof.
  split.
  - apply cvdiec_product_not_xor_true.
  - split.
    + rewrite carbon6_witness_present_count_is_three.
      reflexivity.
    + apply cvdiec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Continuum-vs-discrete **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive cvdiec_bar_presence : Type :=
  | cvdiec_bar_absent
  | cvdiec_bar_present.

Record cvdiec_claim_bar : Type := {
  cvdiec_bar_presence_field : cvdiec_bar_presence;
  cvdiec_bar_defect_total : nat
}.

Definition cvdiecClaimBarAbsent : cvdiec_claim_bar :=
  {| cvdiec_bar_presence_field := cvdiec_bar_absent;
     cvdiec_bar_defect_total := 0 |}.

Definition cvdiecClaimBarZeroDefect : cvdiec_claim_bar :=
  {| cvdiec_bar_presence_field := cvdiec_bar_present;
     cvdiec_bar_defect_total := 0 |}.

Definition cvdiec_claim_bar_zero_defect (b : cvdiec_claim_bar) : bool :=
  match cvdiec_bar_presence_field b with
  | cvdiec_bar_absent => false
  | cvdiec_bar_present => Nat.eqb (cvdiec_bar_defect_total b) 0
  end.

Lemma cvdiec_claim_bar_zero_defect_true :
  cvdiec_claim_bar_zero_defect cvdiecClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma cvdiec_claim_bar_absent_not_zero_defect :
  cvdiec_claim_bar_zero_defect cvdiecClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Continuum-vs-discrete **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive cvdiec_conservation_verdict : Type :=
  | cvdiec_verdict_unwired_ok
  | cvdiec_verdict_named_ok
  | cvdiec_verdict_design_ok
  | cvdiec_verdict_trivial_refuse
  | cvdiec_verdict_xor_refuse
  | cvdiec_verdict_green_invent_refuse
  | cvdiec_verdict_proved_without_bar_refuse
  | cvdiec_verdict_production_wired_refuse
  | cvdiec_verdict_parallel_continuum_axiom_refuse
  | cvdiec_verdict_two_chemistries_refuse
  | cvdiec_verdict_cvdiec_extra_element_id_refuse
  | cvdiec_verdict_bare_element_id_refuse
  | cvdiec_verdict_tp_float_pin_refuse.

Definition cvdiec_conservation_verdict_ok (v : cvdiec_conservation_verdict) : bool :=
  match v with
  | cvdiec_verdict_unwired_ok => true
  | cvdiec_verdict_named_ok => true
  | cvdiec_verdict_design_ok => true
  | _ => false
  end.

Definition cvdiecBundleNontrivial (b : cvdiec_channel_bundle) : bool :=
  Nat.ltb 0 (cvdiecBundlePresentCount b).

Definition evaluate_cvdiec_bundle
  (m : ContinuumVsDiscreteElementIdConservationModality)
  (b : cvdiec_channel_bundle)
  (bar : cvdiec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : cvdiec_conservation_verdict :=
  if claim_physics_green
  then cvdiec_verdict_green_invent_refuse
  else if claim_proved
       then cvdiec_verdict_proved_without_bar_refuse
       else if negb (cvdiecBundleNontrivial b)
            then cvdiec_verdict_trivial_refuse
            else if cvdiecXorClassifierIncompatible claim_xor_classifier b
                 then cvdiec_verdict_xor_refuse
                 else
                   match m with
                   | cvdiec_conservation_unwired =>
                       if cvdiecBundleIsConcurrentProduct b
                       then cvdiec_verdict_named_ok
                       else cvdiec_verdict_design_ok
                   | cvdiec_conservation_assumed
                   | cvdiec_conservation_surrogate =>
                       cvdiec_verdict_design_ok
                   | cvdiec_conservation_proved =>
                       cvdiec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_cvdiec_conservation_close
  (m : ContinuumVsDiscreteElementIdConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : cvdiec_conservation_verdict :=
  if claim_physics_green
  then cvdiec_verdict_green_invent_refuse
  else if claim_production_wired
  then cvdiec_verdict_production_wired_refuse
  else
    match m with
    | cvdiec_conservation_unwired => cvdiec_verdict_unwired_ok
    | cvdiec_conservation_assumed
    | cvdiec_conservation_proved
    | cvdiec_conservation_surrogate => cvdiec_verdict_named_ok
    end.

Definition cvdiec_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_cvdiec_conservation_close
          cvdiec_conservation_proved claim_physics_green claim_production_wired with
  | cvdiec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Continuum-vs-discrete **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive cvdiec_conservation_law : Type :=
  | cvdiec_law_conserved
  | cvdiec_law_named_ok
  | cvdiec_law_trivial_refuse
  | cvdiec_law_green_invent_refuse.

Definition cvdiec_conservation_law_count : nat := 4.

Lemma cvdiec_conservation_law_count_is_four :
  cvdiec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive cvdiec_conservation_law_witness : Type :=
  | cvdiec_law_witness_open
  | cvdiec_law_witness_proved.

Definition evaluate_cvdiec_conservation_law_witness
  (law : cvdiec_conservation_law)
  (m : ContinuumVsDiscreteElementIdConservationModality)
  : cvdiec_conservation_law_witness :=
  match m with
  | cvdiec_conservation_unwired
  | cvdiec_conservation_assumed
  | cvdiec_conservation_surrogate => cvdiec_law_witness_open
  | cvdiec_conservation_proved => cvdiec_law_witness_proved
  end.

Lemma all_cvdiec_conservation_laws_open_at_unwired :
  evaluate_cvdiec_conservation_law_witness cvdiec_law_conserved
    cvdiec_conservation_unwired = cvdiec_law_witness_open /\
  evaluate_cvdiec_conservation_law_witness cvdiec_law_named_ok
    cvdiec_conservation_unwired = cvdiec_law_witness_open /\
  evaluate_cvdiec_conservation_law_witness cvdiec_law_trivial_refuse
    cvdiec_conservation_unwired = cvdiec_law_witness_open /\
  evaluate_cvdiec_conservation_law_witness cvdiec_law_green_invent_refuse
    cvdiec_conservation_unwired = cvdiec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-23 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition continuumVsDiscreteElementIdConservationProved : bool := false.

Lemma cvdiec_conservation_proved_false :
  continuumVsDiscreteElementIdConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_unwired false false =
  cvdiec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_unwired false false =
  cvdiec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_conservation_close
       cvdiec_conservation_unwired false false) =
  true.
Proof.
  unfold cvdiec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named carbon Z=6 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma carbon6_witness_named_ok :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent false false false =
  cvdiec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_carbon6_cvdiec_conservation :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent false false false =
  cvdiec_verdict_named_ok /\
  cvdiecBundleIsConcurrentProduct cvdiecCarbon6Witness = true /\
  carbon_atomic_number_z = 6 /\
  pattern_class_continuum_vs_discrete_element_id_idx = 23.
Proof.
  repeat split; reflexivity.
Qed.

Lemma cvdiec_named_close_ok :
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_proved false false =
  cvdiec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_cvdiec_conservation_close :
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_proved false false =
  cvdiec_verdict_named_ok /\
  cvdiec_conservation_authorized false false = true.
Proof.
  split.
  - apply cvdiec_named_close_ok.
  - unfold cvdiec_conservation_authorized.
    rewrite cvdiec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — continuum-vs-discrete refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecEmptyWitness
    cvdiecClaimBarAbsent false false false =
  cvdiec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecEmptyWitness
    cvdiecClaimBarAbsent false false false =
  cvdiec_verdict_trivial_refuse /\
  cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_bundle
       cvdiec_conservation_unwired
       cvdiecEmptyWitness
       cvdiecClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold cvdiec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma cvdiec_xor_classifier_refused :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent true false false =
  cvdiec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem cvdiec_xor_mutually_exclusive_classifier_fail_closed :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent true false false =
  cvdiec_verdict_xor_refuse /\
  cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_bundle
       cvdiec_conservation_unwired
       cvdiecCarbon6Witness
       cvdiecClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply cvdiec_xor_classifier_refused.
  - unfold cvdiec_conservation_verdict_ok.
    rewrite cvdiec_xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_unwired true false =
  cvdiec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_conservation_close
       cvdiec_conservation_unwired true false) =
  false.
Proof.
  unfold cvdiec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_cvdiec_bundle_refuse :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent false true false =
  cvdiec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — continuum-vs-discrete refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent false false true =
  cvdiec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent false false true =
  cvdiec_verdict_proved_without_bar_refuse /\
  cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_bundle
       cvdiec_conservation_unwired
       cvdiecCarbon6Witness
       cvdiecClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold cvdiec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — continuum-vs-discrete lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_proved false true =
  cvdiec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_conservation_close
       cvdiec_conservation_proved false true) =
  false.
Proof.
  unfold cvdiec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition cvdiecConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/continuum_discrete_element.rs".

Definition parallelContinuumAxiomTag : string := "parallel_continuum_vs_discrete_element_id_axiom".

Lemma parallel_continuum_axiom_refuse :
  cvdiecConservationAuthority <>
  parallelContinuumAxiomTag /\
  continuumVsDiscreteElementIdConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply cvdiec_conservation_proved_false.
Qed.

Theorem parallel_continuum_axiom_not_minted :
  cvdiecConservationAuthority =
  "umst/umst-chem/src/l0_tables/continuum_discrete_element.rs" /\
  continuumVsDiscreteElementIdConservationProved = false /\
  cvdiecConservationAuthority <> parallelContinuumAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Two chemistries refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition twoChemistriesFraming : string :=
  "two_independent_chemistries_not_one_object".

Definition cvdiecConservationFraming : string :=
  "second_law_conservation_continuum_vs_discrete_two_presentations_one_object_one_axiom".

Lemma two_chemistries_refuse :
  cvdiecConservationFraming <>
  twoChemistriesFraming /\
  carbon_atomic_number_z = 6 /\
  pattern_class_continuum_vs_discrete_element_id_idx = 23.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem continuum_vs_discrete_not_two_chemistries :
  cvdiecConservationFraming <>
  twoChemistriesFraming /\
  carbon_atomic_number_z = 6 /\
  pattern_class_continuum_vs_discrete_element_id_idx = 23 /\
  continuumVsDiscreteElementIdConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — continuum-vs-discrete ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "catalyst_consumed_in_net_reaction".

Lemma cvdiec_extra_element_id_refuse :
  cvdiecConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem cvdiec_not_extra_element_id :
  cvdiecConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  carbon_atomic_number_z = 6.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Bare ElementId refuse — continuum field ≠ bare discrete row    *)
(* ------------------------------------------------------------------ *)

Definition bareElementIdFraming : string :=
  "bare_discrete_element_id_without_witness".

Definition continuumDiscreteElementAuthority : string :=
  "umst/umst-chem/src/continuum_discrete_element.rs".

Lemma bare_element_id_refuse :
  cvdiecConservationFraming <>
  bareElementIdFraming /\
  continuumDiscreteElementAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem cvdiec_not_bare_element_id :
  cvdiecConservationFraming <>
  bareElementIdFraming /\
  continuumDiscreteElementAuthority =
  "umst/umst-chem/src/continuum_discrete_element.rs" /\
  continuumVsDiscreteElementIdConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_continuum_vs_discrete_scaffold".

Lemma tp_float_pin_refuse :
  cvdiecConservationFraming <>
  tpFloatPinFraming /\
  continuum_field_channel_tag = "continuum_field_presentation".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  cvdiecConservationFraming <>
  tpFloatPinFraming /\
  edge_discrete_channel_tag = "discrete_element_id_boundary" /\
  carbon_atomic_number_z = 6.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  ContinuumVsDiscreteElementId **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition cvdiec_conservation_coherence_scaffold : bool :=
  cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_conservation_close
       cvdiec_conservation_proved false false) &&
  negb (cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_conservation_close
       cvdiec_conservation_unwired true false)) &&
  negb (cvdiec_conservation_verdict_ok
    (evaluate_cvdiec_conservation_close
       cvdiec_conservation_proved false true)).

Lemma cvdiec_conservation_coherence_scaffold_true :
  cvdiec_conservation_coherence_scaffold = true.
Proof.
  unfold cvdiec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem cvdiec_conservation_coherence_scaffold_theorem :
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_proved false false =
    cvdiec_verdict_named_ok /\
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_unwired true false =
    cvdiec_verdict_green_invent_refuse /\
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_proved false true =
    cvdiec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition cvdiec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition cvdiec_conservation_knowing_fiber_ok : bool :=
  cvdiec_conservation_fiber_ok fiber_quantum_knowing.

Definition cvdiec_conservation_meso_acting_ok : bool :=
  cvdiec_conservation_fiber_ok fiber_meso_acting.

Lemma cvdiec_conservation_knowing_fiber_ok_true :
  cvdiec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma cvdiec_conservation_meso_acting_not_ok :
  cvdiec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem cvdiec_conservation_routes_knowing_not_meso :
  cvdiec_conservation_knowing_fiber_ok = true /\
  cvdiec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply cvdiec_conservation_knowing_fiber_ok_true.
  - apply cvdiec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  cvdiec_conservation_knowing_fiber_ok &&
  negb cvdiec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, cvdiec_conservation_knowing_fiber_ok,
    cvdiec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-23 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem cvdiec_conservation_fixture_scaffold :
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent false false false =
    cvdiec_verdict_named_ok /\
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecEmptyWitness
    cvdiecClaimBarAbsent false false false =
    cvdiec_verdict_trivial_refuse /\
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent true false false =
    cvdiec_verdict_xor_refuse /\
  evaluate_cvdiec_bundle
    cvdiec_conservation_unwired
    cvdiecCarbon6Witness
    cvdiecClaimBarAbsent false false true =
    cvdiec_verdict_proved_without_bar_refuse /\
  evaluate_cvdiec_conservation_close
    cvdiec_conservation_unwired false false =
    cvdiec_verdict_unwired_ok /\
  cvdiec_conservation_knowing_fiber_ok = true /\
  cvdiec_conservation_meso_acting_ok = false /\
  continuumVsDiscreteElementIdConservationProved = false /\
  cvdiecProductNotXor = true /\
  carbon_atomic_number_z = 6.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — continuum vs discrete) *)
(* ------------------------------------------------------------------ *)

Definition chemContinuumDiscreteElementAuthority : string :=
  "umst/umst-chem/src/continuum_discrete_element.rs".

Definition chemL0ContinuumVsDiscreteTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/continuum_discrete_element.rs".

Definition elementIdAuthority : string :=
  "umst/umst-chem/src/element_id.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0EdgeDiscreteCellId : string := "CHEM-L0-EDGE-DISCRETE".


Definition temperatureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/temperature_is_graph_function.rs".

Definition pressureGraphFunctionAuthority : string :=
  "umst/umst-chem/src/pressure_is_graph_function.rs".

Definition chemIntNuanceContinuumDiscreteCellId : string :=
  "CHEM-INT-NUANCE-CONTINUUM_DISCRETE".

Definition chemIntZ118ElementIdCellId : string :=
  "CHEM-INT-Z118-ELEMENT-ID".

Definition wave100NoLibRsMarker : string :=
  "WAVE100 no lib.rs continuum_vs_discrete_element_id not wired".

Lemma wave100_no_lib_rs_marker_nonempty :
  wave100NoLibRsMarker <> "".
Proof. discriminate. Qed.

Lemma cvdiec_conservation_cites_temperature_graph :
  temperatureGraphFunctionAuthority <> "".
Proof. discriminate. Qed.

Lemma cvdiec_conservation_cites_pressure_graph :
  pressureGraphFunctionAuthority <> "".
Proof. discriminate. Qed.

Lemma cvdiec_conservation_cites_nuance_cell :
  chemIntNuanceContinuumDiscreteCellId = "CHEM-INT-NUANCE-CONTINUUM_DISCRETE".
Proof. reflexivity. Qed.

Lemma cvdiec_conservation_cites_element_id_cell :
  chemIntZ118ElementIdCellId = "CHEM-INT-Z118-ELEMENT-ID".
Proof. reflexivity. Qed.

Definition continuumVsDiscreteElementIdConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-CONTINUUM-VS-DISCRETE-ELEMENT-ID-CONSERVATION".

Definition continuumVsDiscreteElementIdConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-CONTINUUM-VS-DISCRETE-ELEMENT-ID-CONSERVATION ContinuumVsDiscreteElementIdConservationModality Unwired Assumed Proved Surrogate four-step lattice continuumVsDiscreteElementIdConservationProved false evaluateCvdiecBundle evaluateCvdiecConservation named class 23 continuum vs discrete ElementId carbon Z=6 continuum field discrete ElementId boundary second law two presentations one object not two chemistries concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel continuum axiom refuse two chemistries refuse extra element id Z=119 refuse bare discrete ElementId without witness refuse Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired WAVE100 no lib.rs T P graph functions v14 not float pins".

Lemma cvdiec_conservation_cell_id :
  continuumVsDiscreteElementIdConservationCellId =
  "CHEM-FORMAL-Q-COQ-CONTINUUM-VS-DISCRETE-ELEMENT-ID-CONSERVATION".
Proof. reflexivity. Qed.

Lemma cvdiec_conservation_cites_l0_table :
  chemL0ContinuumVsDiscreteTableAuthority <> "".
Proof. discriminate. Qed.

Lemma cvdiec_conservation_authority_path :
  cvdiecConservationAuthority =
  "umst/umst-chem/src/l0_tables/continuum_discrete_element.rs".
Proof. reflexivity. Qed.

Lemma cvdiec_conservation_cites_continuum_discrete :
  chemContinuumDiscreteElementAuthority <> "".
Proof. discriminate. Qed.

Lemma cvdiec_conservation_cites_marker :
  cvdiecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma cvdiec_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma cvdiec_conservation_cites_edge_discrete_cell :
  chemL0EdgeDiscreteCellId = "CHEM-L0-EDGE-DISCRETE".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma cvdiec_not_parallel_axiom :
  cvdiecConservationFraming <> parallelContinuumAxiomTag.
Proof. discriminate. Qed.

Lemma cvdiec_second_law_conservation_framing :
  cvdiecConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Edge discrete boundary — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition edgeDiscreteBoundaryFraming : string :=
  "transition_state_theory_prior_art_not_named_object".

Definition twoPresentationsOneObject : string :=
  "two_presentations_one_object_continuum_vs_discrete_morphism".

Lemma two_independent_chemistries_not_one_object :
  twoPresentationsOneObject <>
  edgeDiscreteBoundaryFraming /\
  edge_discrete_channel_tag = "discrete_element_id_boundary".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem two_presentations_one_object_not_two_chemistries :
  twoPresentationsOneObject <>
  edgeDiscreteBoundaryFraming /\
  continuum_field_channel_tag = "continuum_field_presentation" /\
  continuumVsDiscreteElementIdConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Two presentations refuse — not continuum_vs_discrete_element_id axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition twoPresentationsFraming : string :=
  "two_presentations_not_two_chemistries".

Lemma two_presentations_not_two_chemistries_refuse :
  twoPresentationsFraming <>
  bareElementIdFraming /\
  continuum_field_channel_tag = "continuum_field_presentation".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem continuum_vs_discrete_element_id_two_presentations_not_two_chemistries :
  twoPresentationsFraming <>
  bareElementIdFraming /\
  continuumDiscreteElementAuthority =
  "umst/umst-chem/src/continuum_discrete_element.rs" /\
  continuumVsDiscreteElementIdConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma cvdiec_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma cvdiec_conservation_modality_unwired :
  continuumVsDiscreteElementIdConservationModalityCurrent =
  cvdiec_conservation_unwired.
Proof. reflexivity. Qed.

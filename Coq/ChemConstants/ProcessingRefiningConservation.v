(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: ProcessingRefiningConservation.v               *)
(*                                                                      *)
(*  Knowing-fiber Coq: class 9 **processing_refining**             *)
(*  **conservation**. Processing/refining is a concurrent PatternBundle factor on *)
(*  the same second-law + conservation object (not a 26th axiom). Concurrent Π_c   *)
(*  PatternBundle factor — **product** not XOR. processingRefiningConservationProved *)
(*  false. Modality Unwired.                                           *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/refine_process.rs (read-only cite).       *)
(*  INT: umst/umst-chem/src/l0_tables/processing_refining.rs             *)
(*  (read-only cite). GRAPH cuts cited. PatternProductConservation.v   *)
(* ================================================================== *)

From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-9 **processing_refining** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive ProcessingRefiningConservationModality : Type :=
  | processing_refining_conservation_unwired
  | processing_refining_conservation_assumed
  | processing_refining_conservation_proved
  | processing_refining_conservation_surrogate.

Definition processingRefiningConservationModalityCurrent :
  ProcessingRefiningConservationModality :=
  processing_refining_conservation_unwired.

Definition processing_refining_lattice_cardinality : nat := 4.

Lemma processing_refining_lattice_cardinality_is_four :
  processing_refining_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma processing_refining_lattice_not_118_squared :
  negb (Nat.eqb processing_refining_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold processing_refining_lattice_cardinality.
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

(* North-star §2 class 9 — processing_refining concurrent Π_c factor. *)
Definition pattern_class_processing_refining_idx : nat := 9.

Lemma pattern_class_processing_refining_idx_is_9 :
  pattern_class_processing_refining_idx = 9.
Proof. reflexivity. Qed.

Lemma processing_refining_class_index_valid :
  pattern_class_index_valid pattern_class_processing_refining_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_processing_refining_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierProcessingRefiningRowId : string := "X09".

Lemma cross_classifier_processing_refining_row_named :
  crossClassifierProcessingRefiningRowId = "X09".
Proof. reflexivity. Qed.

Definition pattern_class_processing_refining_tag : string :=
  "processing_refining".

Definition north_star_class_9_processing_refining_tag : string :=
  "class 9 processing refining".

Lemma pattern_class_processing_refining_tag_nonempty :
  pattern_class_processing_refining_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_9_processing_refining_tag_nonempty :
  north_star_class_9_processing_refining_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Fe Z=26 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition iron_atomic_number_z : nat := 26.

Lemma iron_atomic_number_z_is_26 :
  iron_atomic_number_z = 26.
Proof. reflexivity. Qed.

Definition iron_z_valid : bool :=
  Nat.ltb 0 iron_atomic_number_z &&
  Nat.leb iron_atomic_number_z iupac_table_cardinality.

Lemma iron_z_valid_true : iron_z_valid = true.
Proof.
  unfold iron_z_valid, iron_atomic_number_z, iupac_table_cardinality.
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

Definition processing_refining_factor_tag : string :=
  "processing_refining".

Definition dissipative_refine_channel_tag : string := "dissipative_refine".

Definition second_law_gmin_channel_tag : string := "second_law_presentation".

Lemma processing_refining_factor_tag_nonempty :
  processing_refining_factor_tag <> "".
Proof. discriminate. Qed.

Lemma dissipative_refine_channel_tag_nonempty :
  dissipative_refine_channel_tag <> "".
Proof. discriminate. Qed.

Lemma second_law_gmin_channel_tag_nonempty :
  second_law_gmin_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Processing-refining product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive prc_channel_slot : Type :=
  | prc_slot_unwired
  | prc_slot_absent
  | prc_slot_present.

Definition prc_channel_slot_beq (s1 s2 : prc_channel_slot) : bool :=
  match s1, s2 with
  | prc_slot_unwired, prc_slot_unwired => true
  | prc_slot_absent, prc_slot_absent => true
  | prc_slot_present, prc_slot_present => true
  | _, _ => false
  end.

Definition prc_channel_slot_is_present (s : prc_channel_slot) : bool :=
  match s with
  | prc_slot_present => true
  | _ => false
  end.

Definition processingRefiningProductChannelCount : nat := 3.

Lemma processing_refining_product_channel_count_is_three :
  processingRefiningProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = dissipative refine, 1 = G-min second law, 2 = class 9. *)
Definition prc_channel_dissipative_refine : nat := 0.
Definition prc_channel_second_law_gmin : nat := 1.
Definition prc_channel_class9_processing_refining : nat := 2.

Lemma prc_channel_dissipative_refine_idx_is_0 :
  prc_channel_dissipative_refine = 0.
Proof. reflexivity. Qed.

Lemma prc_channel_second_law_gmin_idx_is_1 :
  prc_channel_second_law_gmin = 1.
Proof. reflexivity. Qed.

Lemma prc_channel_class9_processing_refining_idx_is_2 :
  prc_channel_class9_processing_refining = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Processing-refining concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition prc_channel_bundle : Type := nat -> prc_channel_slot.

Definition processingRefiningBundleAllUnwired : prc_channel_bundle :=
  fun _ => prc_slot_unwired.

Definition processingRefiningBundleAt (b : prc_channel_bundle) (idx : nat)
  (slot : prc_channel_slot) : prc_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition processingRefiningBundleWithPresent
  (b : prc_channel_bundle) (idx : nat) : prc_channel_bundle :=
  processingRefiningBundleAt b idx prc_slot_present.

Fixpoint count_prc_present_up_to (b : prc_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if prc_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_prc_present_up_to b i + add
  end.

Definition processingRefiningBundlePresentCount (b : prc_channel_bundle) : nat :=
  count_prc_present_up_to b processingRefiningProductChannelCount.

Definition processingRefiningBundleHolds (b : prc_channel_bundle) (idx : nat) : bool :=
  prc_channel_slot_is_present (b idx).

Definition processingRefiningBundleIsConcurrentProduct (b : prc_channel_bundle) : bool :=
  Nat.leb 2 (processingRefiningBundlePresentCount b).

(* Fe Z=26 dissipative refine + G-min + class-9 processing refining concurrent witness. *)
Definition processingRefiningFe26Witness : prc_channel_bundle :=
  processingRefiningBundleWithPresent
    (processingRefiningBundleWithPresent
      (processingRefiningBundleWithPresent processingRefiningBundleAllUnwired
        prc_channel_dissipative_refine)
      prc_channel_second_law_gmin)
    prc_channel_class9_processing_refining.

Definition processingRefiningEmptyWitness : prc_channel_bundle :=
  processingRefiningBundleAllUnwired.

Definition processingRefiningSinglePresent : prc_channel_bundle :=
  processingRefiningBundleWithPresent processingRefiningBundleAllUnwired
    prc_channel_dissipative_refine.

Lemma dissipative_refine_channel_present :
  processingRefiningBundleHolds processingRefiningFe26Witness
    prc_channel_dissipative_refine = true.
Proof. reflexivity. Qed.

Lemma second_law_gmin_channel_present :
  processingRefiningBundleHolds processingRefiningFe26Witness
    prc_channel_second_law_gmin = true.
Proof. reflexivity. Qed.

Lemma class9_processing_refining_channel_present :
  processingRefiningBundleHolds processingRefiningFe26Witness
    prc_channel_class9_processing_refining = true.
Proof. reflexivity. Qed.

Lemma fe26_witness_present_count_is_three :
  processingRefiningBundlePresentCount processingRefiningFe26Witness = 3.
Proof. reflexivity. Qed.

Lemma fe26_witness_is_concurrent_product :
  processingRefiningBundleIsConcurrentProduct processingRefiningFe26Witness = true.
Proof.
  unfold processingRefiningBundleIsConcurrentProduct.
  rewrite fe26_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  processingRefiningBundlePresentCount processingRefiningEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  processingRefiningBundleIsConcurrentProduct processingRefiningEmptyWitness = false.
Proof.
  unfold processingRefiningBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  processingRefiningBundlePresentCount processingRefiningSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  processingRefiningBundleIsConcurrentProduct processingRefiningSinglePresent = false.
Proof.
  unfold processingRefiningBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive prc_xor_posture : Type :=
  | prc_xor_exclusive
  | prc_xor_concurrent_product.

Definition prcXorClassifierMarker : string := "chem_l0_processing_refining_xor_classifier_v1".
Definition prcConcurrentProductMarker : string := "chem_int_processing_refining_product_v1".

Lemma prc_xor_marker_ne_concurrent_product_marker :
  prcXorClassifierMarker <> prcConcurrentProductMarker.
Proof. discriminate. Qed.

Definition prcXorClassifierIncompatible (claim_xor : bool)
  (b : prc_channel_bundle) : bool :=
  claim_xor && processingRefiningBundleIsConcurrentProduct b.

Lemma prc_xor_refuse_on_fe26_witness :
  prcXorClassifierIncompatible true processingRefiningFe26Witness = true.
Proof.
  unfold prcXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma prc_xor_ok_on_concurrent_product_claim :
  prcXorClassifierIncompatible false processingRefiningFe26Witness = false.
Proof. reflexivity. Qed.

Definition prcProductNotXor : bool :=
  processingRefiningBundleIsConcurrentProduct processingRefiningFe26Witness &&
  prcXorClassifierIncompatible true processingRefiningFe26Witness.

Lemma prc_product_not_xor_true : prcProductNotXor = true.
Proof.
  unfold prcProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  prcProductNotXor = true /\
  Nat.leb 2 (processingRefiningBundlePresentCount
    processingRefiningFe26Witness) = true /\
  prcXorClassifierMarker <> prcConcurrentProductMarker.
Proof.
  split.
  - apply prc_product_not_xor_true.
  - split.
    + rewrite fe26_witness_present_count_is_three.
      reflexivity.
    + apply prc_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  Processing-refining **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive prc_bar_presence : Type :=
  | prc_bar_absent
  | prc_bar_present.

Record prc_claim_bar : Type := {
  prc_bar_presence_field : prc_bar_presence;
  prc_bar_defect_total : nat
}.

Definition processingRefiningClaimBarAbsent : prc_claim_bar :=
  {| prc_bar_presence_field := prc_bar_absent;
     prc_bar_defect_total := 0 |}.

Definition processingRefiningClaimBarZeroDefect : prc_claim_bar :=
  {| prc_bar_presence_field := prc_bar_present;
     prc_bar_defect_total := 0 |}.

Definition prc_claim_bar_zero_defect (b : prc_claim_bar) : bool :=
  match prc_bar_presence_field b with
  | prc_bar_absent => false
  | prc_bar_present => Nat.eqb (prc_bar_defect_total b) 0
  end.

Lemma prc_claim_bar_zero_defect_true :
  prc_claim_bar_zero_defect processingRefiningClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma prc_claim_bar_absent_not_zero_defect :
  prc_claim_bar_zero_defect processingRefiningClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Processing-refining **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive prc_conservation_verdict : Type :=
  | prc_verdict_unwired_ok
  | prc_verdict_named_ok
  | prc_verdict_design_ok
  | prc_verdict_trivial_refuse
  | prc_verdict_xor_refuse
  | prc_verdict_green_invent_refuse
  | prc_verdict_proved_without_bar_refuse
  | prc_verdict_production_wired_refuse
  | prc_verdict_parallel_processing_refining_axiom_refuse
  | prc_verdict_species_id_smuggle_refuse
  | prc_verdict_extra_element_id_refuse
  | prc_verdict_free_purification_refuse
  | prc_verdict_tp_float_pin_refuse.

Definition prc_conservation_verdict_ok (v : prc_conservation_verdict) : bool :=
  match v with
  | prc_verdict_unwired_ok => true
  | prc_verdict_named_ok => true
  | prc_verdict_design_ok => true
  | _ => false
  end.

Definition processingRefiningBundleNontrivial (b : prc_channel_bundle) : bool :=
  Nat.ltb 0 (processingRefiningBundlePresentCount b).

Definition evaluate_processing_refining_bundle
  (m : ProcessingRefiningConservationModality)
  (b : prc_channel_bundle)
  (bar : prc_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : prc_conservation_verdict :=
  if claim_physics_green
  then prc_verdict_green_invent_refuse
  else if claim_proved
       then prc_verdict_proved_without_bar_refuse
       else if negb (processingRefiningBundleNontrivial b)
            then prc_verdict_trivial_refuse
            else if prcXorClassifierIncompatible claim_xor_classifier b
                 then prc_verdict_xor_refuse
                 else
                   match m with
                   | processing_refining_conservation_unwired =>
                       if processingRefiningBundleIsConcurrentProduct b
                       then prc_verdict_named_ok
                       else prc_verdict_design_ok
                   | processing_refining_conservation_assumed
                   | processing_refining_conservation_surrogate =>
                       prc_verdict_design_ok
                   | processing_refining_conservation_proved =>
                       prc_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_processing_refining_conservation_close
  (m : ProcessingRefiningConservationModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : prc_conservation_verdict :=
  if claim_physics_green
  then prc_verdict_green_invent_refuse
  else if claim_production_wired
  then prc_verdict_production_wired_refuse
  else
    match m with
    | processing_refining_conservation_unwired => prc_verdict_unwired_ok
    | processing_refining_conservation_assumed
    | processing_refining_conservation_proved
    | processing_refining_conservation_surrogate => prc_verdict_named_ok
    end.

Definition processing_refining_conservation_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_processing_refining_conservation_close
          processing_refining_conservation_proved claim_physics_green claim_production_wired with
  | prc_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Processing-refining **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive prc_conservation_law : Type :=
  | prc_law_conserved
  | prc_law_named_ok
  | prc_law_trivial_refuse
  | prc_law_green_invent_refuse.

Definition prc_conservation_law_count : nat := 4.

Lemma prc_conservation_law_count_is_four :
  prc_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive prc_conservation_law_witness : Type :=
  | prc_law_witness_open
  | prc_law_witness_proved.

Definition evaluate_prc_conservation_law_witness
  (law : prc_conservation_law)
  (m : ProcessingRefiningConservationModality)
  : prc_conservation_law_witness :=
  match m with
  | processing_refining_conservation_unwired
  | processing_refining_conservation_assumed
  | processing_refining_conservation_surrogate => prc_law_witness_open
  | processing_refining_conservation_proved => prc_law_witness_proved
  end.

Lemma all_prc_conservation_laws_open_at_unwired :
  evaluate_prc_conservation_law_witness prc_law_conserved
    processing_refining_conservation_unwired = prc_law_witness_open /\
  evaluate_prc_conservation_law_witness prc_law_named_ok
    processing_refining_conservation_unwired = prc_law_witness_open /\
  evaluate_prc_conservation_law_witness prc_law_trivial_refuse
    processing_refining_conservation_unwired = prc_law_witness_open /\
  evaluate_prc_conservation_law_witness prc_law_green_invent_refuse
    processing_refining_conservation_unwired = prc_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-9 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition processingRefiningConservationProved : bool := false.

Lemma processing_refining_conservation_proved_false :
  processingRefiningConservationProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_unwired false false =
  prc_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_unwired false false =
  prc_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  prc_conservation_verdict_ok
    (evaluate_processing_refining_conservation_close
       processing_refining_conservation_unwired false false) =
  true.
Proof.
  unfold prc_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Fe Z=26 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma fe26_witness_named_ok :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent false false false =
  prc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_fe26_processing_refining_conservation :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent false false false =
  prc_verdict_named_ok /\
  processingRefiningBundleIsConcurrentProduct processingRefiningFe26Witness = true /\
  iron_atomic_number_z = 26 /\
  pattern_class_processing_refining_idx = 9.
Proof.
  repeat split; reflexivity.
Qed.

Lemma prc_named_close_ok :
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_proved false false =
  prc_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_processing_refining_conservation_close :
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_proved false false =
  prc_verdict_named_ok /\
  processing_refining_conservation_authorized false false = true.
Proof.
  split.
  - apply prc_named_close_ok.
  - unfold processing_refining_conservation_authorized.
    rewrite prc_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — processing-refining refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningEmptyWitness
    processingRefiningClaimBarAbsent false false false =
  prc_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningEmptyWitness
    processingRefiningClaimBarAbsent false false false =
  prc_verdict_trivial_refuse /\
  prc_conservation_verdict_ok
    (evaluate_processing_refining_bundle
       processing_refining_conservation_unwired
       processingRefiningEmptyWitness
       processingRefiningClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold prc_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent true false false =
  prc_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent true false false =
  prc_verdict_xor_refuse /\
  prc_conservation_verdict_ok
    (evaluate_processing_refining_bundle
       processing_refining_conservation_unwired
       processingRefiningFe26Witness
       processingRefiningClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold prc_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_unwired true false =
  prc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  prc_conservation_verdict_ok
    (evaluate_processing_refining_conservation_close
       processing_refining_conservation_unwired true false) =
  false.
Proof.
  unfold prc_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_prc_bundle_refuse :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent false true false =
  prc_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — processing-refining refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent false false true =
  prc_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent false false true =
  prc_verdict_proved_without_bar_refuse /\
  prc_conservation_verdict_ok
    (evaluate_processing_refining_bundle
       processing_refining_conservation_unwired
       processingRefiningFe26Witness
       processingRefiningClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold prc_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — processing-refining lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_proved false true =
  prc_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  prc_conservation_verdict_ok
    (evaluate_processing_refining_conservation_close
       processing_refining_conservation_proved false true) =
  false.
Proof.
  unfold prc_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel processing-refining axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition processingRefiningConservationAuthority : string :=
  "umst/umst-chem/src/l0_tables/processing_refining.rs".

Definition parallelProcessingRefiningAxiomTag : string := "26th_chemistry_axiom".

Lemma parallel_processing_refining_axiom_refuse :
  processingRefiningConservationAuthority <>
  parallelProcessingRefiningAxiomTag /\
  processingRefiningConservationProved = false.
Proof.
  split.
  - discriminate.
  - apply processing_refining_conservation_proved_false.
Qed.

Theorem parallel_processing_refining_axiom_not_minted :
  processingRefiningConservationAuthority =
  "umst/umst-chem/src/l0_tables/processing_refining.rs" /\
  processingRefiningConservationProved = false /\
  processingRefiningConservationAuthority <> parallelProcessingRefiningAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — dissipative refine ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition speciesIdSmuggleFraming : string :=
  "l1_species_id_cement_occupancy_tag".

Definition processingRefiningConservationFraming : string :=
  "second_law_conservation_processing_refining_one_axiom".

Lemma species_id_smuggle_refuse :
  processingRefiningConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_processing_refining_idx = 9.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem dissipative_refine_not_species_id_smuggle :
  processingRefiningConservationFraming <>
  speciesIdSmuggleFraming /\
  iron_atomic_number_z = 26 /\
  pattern_class_processing_refining_idx = 9 /\
  processingRefiningConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — processing refining ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "vacancy_or_impurity_as_z119_element_row".

Lemma extra_element_id_refuse :
  processingRefiningConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  processingRefiningConservationFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — processing refining ≠ CAT-03 adjunction    *)
(* ------------------------------------------------------------------ *)

Definition freePurificationFraming : string :=
  "free_purification_reverse_refine_cat03_adjunction".

Definition refineProcessAuthority : string :=
  "umst/umst-chem/src/refine_process.rs".

Lemma free_purification_refuse :
  processingRefiningConservationFraming <>
  freePurificationFraming /\
  refineProcessAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem processing_refining_not_free_purification :
  processingRefiningConservationFraming <>
  freePurificationFraming /\
  refineProcessAuthority =
  "umst/umst-chem/src/refine_process.rs" /\
  processingRefiningConservationProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_processing_refining_scaffold".

Lemma tp_float_pin_refuse :
  processingRefiningConservationFraming <>
  tpFloatPinFraming /\
  dissipative_refine_channel_tag = "dissipative_refine".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  processingRefiningConservationFraming <>
  tpFloatPinFraming /\
  second_law_gmin_channel_tag = "second_law_presentation" /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Processing-refining **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition prc_conservation_coherence_scaffold : bool :=
  prc_conservation_verdict_ok
    (evaluate_processing_refining_conservation_close
       processing_refining_conservation_proved false false) &&
  negb (prc_conservation_verdict_ok
    (evaluate_processing_refining_conservation_close
       processing_refining_conservation_unwired true false)) &&
  negb (prc_conservation_verdict_ok
    (evaluate_processing_refining_conservation_close
       processing_refining_conservation_proved false true)).

Lemma prc_conservation_coherence_scaffold_true :
  prc_conservation_coherence_scaffold = true.
Proof.
  unfold prc_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem prc_conservation_coherence_scaffold_theorem :
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_proved false false =
    prc_verdict_named_ok /\
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_unwired true false =
    prc_verdict_green_invent_refuse /\
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_proved false true =
    prc_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition prc_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition prc_conservation_knowing_fiber_ok : bool :=
  prc_conservation_fiber_ok fiber_quantum_knowing.

Definition prc_conservation_meso_acting_ok : bool :=
  prc_conservation_fiber_ok fiber_meso_acting.

Lemma prc_conservation_knowing_fiber_ok_true :
  prc_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma prc_conservation_meso_acting_not_ok :
  prc_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem prc_conservation_routes_knowing_not_meso :
  prc_conservation_knowing_fiber_ok = true /\
  prc_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply prc_conservation_knowing_fiber_ok_true.
  - apply prc_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  prc_conservation_knowing_fiber_ok &&
  negb prc_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, prc_conservation_knowing_fiber_ok,
    prc_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-9 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem processing_refining_conservation_fixture_scaffold :
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent false false false =
    prc_verdict_named_ok /\
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningEmptyWitness
    processingRefiningClaimBarAbsent false false false =
    prc_verdict_trivial_refuse /\
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent true false false =
    prc_verdict_xor_refuse /\
  evaluate_processing_refining_bundle
    processing_refining_conservation_unwired
    processingRefiningFe26Witness
    processingRefiningClaimBarAbsent false false true =
    prc_verdict_proved_without_bar_refuse /\
  evaluate_processing_refining_conservation_close
    processing_refining_conservation_unwired false false =
    prc_verdict_unwired_ok /\
  prc_conservation_knowing_fiber_ok = true /\
  prc_conservation_meso_acting_ok = false /\
  processingRefiningConservationProved = false /\
  prcProductNotXor = true /\
  iron_atomic_number_z = 26.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — processing refining) *)
(* ------------------------------------------------------------------ *)

Definition chemL0ProcessingRefiningAuthority : string :=
  "umst/umst-chem/src/processing_refining.rs".

Definition chemL0ProcessingRefiningTableAuthority : string :=
  "umst/umst-chem/src/l0_tables/processing_refining.rs".

Definition refiningGraphCutsAuthority : string :=
  "umst/umst-chem/src/refining_graph_cuts.rs".

Definition patternProductConservationAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/PatternProductConservation.v".

Definition chemL0Graph02CellId : string := "CHEM-L0-GRAPH-02".

Definition processingRefiningConservationCellId : string :=
  "CHEM-FORMAL-Q-COQ-PROCESSING-REFINING-CONSERVATION".

Definition processingRefiningConservationNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-PROCESSING-REFINING-CONSERVATION ProcessingRefiningConservationModality Unwired Assumed Proved Surrogate four-step lattice processingRefiningConservationProved false evaluateProcessingRefiningBundle evaluateProcessingRefiningConservation named class 9 processing_refining Fe Z=26 dissipative refine second law G-min presentation concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel processing refining axiom refuse species id smuggle refuse extra element id Z=119 refuse free purification CAT-03 refuse processing refining ne SpeciesId Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma processing_refining_conservation_cell_id :
  processingRefiningConservationCellId =
  "CHEM-FORMAL-Q-COQ-PROCESSING-REFINING-CONSERVATION".
Proof. reflexivity. Qed.

Lemma processing_refining_conservation_cites_l0_table :
  chemL0ProcessingRefiningTableAuthority <> "".
Proof. discriminate. Qed.

Lemma processing_refining_conservation_authority_path :
  processingRefiningConservationAuthority =
  "umst/umst-chem/src/l0_tables/processing_refining.rs".
Proof. reflexivity. Qed.

Lemma processing_refining_conservation_cites_l0_ore02 :
  chemL0ProcessingRefiningAuthority <> "".
Proof. discriminate. Qed.

Lemma processing_refining_conservation_cites_marker :
  prcConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma processing_refining_conservation_cites_pattern_product :
  patternProductConservationAuthority <> "".
Proof. discriminate. Qed.

Lemma processing_refining_conservation_cites_ore02_cell :
  chemL0Graph02CellId = "CHEM-L0-GRAPH-02".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma processing_refining_not_26th_axiom :
  processingRefiningConservationFraming <> parallelProcessingRefiningAxiomTag.
Proof. discriminate. Qed.

Lemma processing_refining_second_law_conservation_framing :
  processingRefiningConservationFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma processing_refining_conservation_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma processing_refining_conservation_modality_unwired :
  processingRefiningConservationModalityCurrent =
  processing_refining_conservation_unwired.
Proof. reflexivity. Qed.

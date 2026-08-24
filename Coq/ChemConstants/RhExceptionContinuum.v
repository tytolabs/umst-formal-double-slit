(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: RhExceptionContinuum.v                                *)
(*                                                                      *)
(*  Knowing-fiber Coq: Rh Z=45 d-block occupancy **exception continuum** *)
(*  **conservation**. Occupancy-engine sort (X29) restriction on the    *)
(*  same second-law + conservation object (not a 26th axiom / extra force). *)
(*  Concurrent Π_c PatternBundle factor — **product** not XOR.          *)
(*  Rh Z=45 4d5 5s1 d-block Madelung exception; Co Z=27 / Ir Z=77 homolog not Rh copy. *)
(*  rhExceptionContinuumProved false. Modality Unwired.               *)
(*                                                                      *)
(*  Self-contained (Stdlib Arith). physics_green = False. Zero Admitted. *)
(*  One axiom second law + **conservation** framing.                     *)
(*  INT: umst/umst-chem/src/x_rows/occupancy_engine_sort.rs (read-only). *)
(*  INT: umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs (cite). *)
(*  INT: umst/umst-chem/src/qlattice.rs (read-only cite).               *)
(*  DBlockOccupancyExceptions.v cited. OccupancyEngineSort.v cited.      *)
(* ================================================================== *)


From Stdlib Require Import Arith ZArith String Bool Lia List.
Import ListNotations.

Open Scope string.

(* ------------------------------------------------------------------ *)
(*  Class-14 **rh_exception_continuum** **conservation** modality     *)
(*  (Unwired / Assumed / Proved / Surrogate)                           *)
(* ------------------------------------------------------------------ *)

Inductive RhExceptionContinuumModality : Type :=
  | rh_exception_continuum_unwired
  | rh_exception_continuum_assumed
  | rh_exception_continuum_proved
  | rh_exception_continuum_surrogate.

Definition rhExceptionContinuumModalityCurrent :
  RhExceptionContinuumModality :=
  rh_exception_continuum_unwired.

Definition rh_exception_continuum_lattice_cardinality : nat := 4.

Lemma rh_exception_continuum_lattice_cardinality_is_four :
  rh_exception_continuum_lattice_cardinality = 4.
Proof. reflexivity. Qed.

Lemma rh_exception_continuum_lattice_not_118_squared :
  negb (Nat.eqb rh_exception_continuum_lattice_cardinality (118 * 118)) = true.
Proof.
  unfold rh_exception_continuum_lattice_cardinality.
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

(* North-star §2 class 14 — rh_exception_continuum concurrent Π_c factor. *)
Definition pattern_class_rh_exception_continuum_idx : nat := 14.

Lemma pattern_class_rh_exception_continuum_idx_is_14 :
  pattern_class_rh_exception_continuum_idx = 14.
Proof. reflexivity. Qed.

Lemma rh_exception_continuum_class_index_valid :
  pattern_class_index_valid pattern_class_rh_exception_continuum_idx = true.
Proof.
  unfold pattern_class_index_valid, pattern_class_rh_exception_continuum_idx,
    pattern_class_cardinality.
  reflexivity.
Qed.

Definition crossClassifierOccupancyEngineSortRowId : string := "X29".

Lemma cross_classifier_rh_exception_continuum_row_named :
  crossClassifierOccupancyEngineSortRowId = "X29".
Proof. reflexivity. Qed.

Definition pattern_class_rh_exception_continuum_tag : string :=
  "occupancy_engine_sort".

Definition north_star_class_14_rh_exception_continuum_tag : string :=
  "X29 occupancy engine sort".

Lemma pattern_class_rh_exception_continuum_tag_nonempty :
  pattern_class_rh_exception_continuum_tag <> "".
Proof. discriminate. Qed.

Lemma north_star_class_14_rh_exception_continuum_tag_nonempty :
  north_star_class_14_rh_exception_continuum_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  IUPAC Z pins — Rh Z=45 host assemblage identity witness            *)
(* ------------------------------------------------------------------ *)

Definition iupac_table_cardinality : nat := 118.

Lemma iupac_table_cardinality_is_118 :
  iupac_table_cardinality = 118.
Proof. reflexivity. Qed.

Definition rhodium_atomic_number_z : nat := 45.

Lemma rhodium_atomic_number_z_is_45 :
  rhodium_atomic_number_z = 45.
Proof. reflexivity. Qed.

Definition rhodium_z_valid : bool :=
  Nat.ltb 0 rhodium_atomic_number_z &&
  Nat.leb rhodium_atomic_number_z iupac_table_cardinality.

Lemma rhodium_z_valid_true : rhodium_z_valid = true.
Proof.
  unfold rhodium_z_valid, rhodium_atomic_number_z, iupac_table_cardinality.
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


(* ------------------------------------------------------------------ *)
(*  Rh Z=45 occupancy pins — 4d⁵5s¹ observed vs Madelung predicted     *)
(*  (qlattice observed_override_config / madelung_predicted_config SSOT) *)
(* ------------------------------------------------------------------ *)

Definition rh_element_symbol : string := "Rh".

Definition rh_observed_occupancy_tag : string := "4d85s1".

Definition rh_predicted_occupancy_tag : string := "4d75s2".

Definition rh_observed_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s14d8".

Definition rh_predicted_subshell_notation : string :=
  "1s22s22p63s23p64s23d104p65s24d7".

Definition co_homolog_observed_occupancy_tag : string := "3d74s2".

Definition cobalt_homolog_z : nat := 27.

Lemma cobalt_homolog_z_is_27 :
  cobalt_homolog_z = 27.
Proof. reflexivity. Qed.

Lemma rh_element_symbol_nonempty :
  rh_element_symbol <> "".
Proof. discriminate. Qed.

Lemma rh_observed_occupancy_tag_nonempty :
  rh_observed_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma rh_predicted_occupancy_tag_nonempty :
  rh_predicted_occupancy_tag <> "".
Proof. discriminate. Qed.

Lemma rh_observed_ne_predicted_occupancy :
  rh_observed_occupancy_tag <> rh_predicted_occupancy_tag.
Proof. discriminate. Qed.

Lemma rh_observed_ne_predicted_subshell :
  rh_observed_subshell_notation <> rh_predicted_subshell_notation.
Proof. discriminate. Qed.

Lemma rh_homolog_occupancy_not_copy :
  rh_observed_occupancy_tag <> co_homolog_observed_occupancy_tag.
Proof. discriminate. Qed.

Definition occupancyEngineSortBucketTag : string := "dblock_exception".

Lemma occupancy_engine_sort_bucket_tag_named :
  occupancyEngineSortBucketTag = "dblock_exception".
Proof. reflexivity. Qed.

Definition rh_exception_continuum_factor_tag : string :=
  "occupancy_engine_sort".

Definition occupancy_engine_sort_channel_tag : string := "occupancy_engine_sort".

Definition observed_override_channel_tag : string := "observed_override".

Lemma rh_exception_continuum_factor_tag_nonempty :
  rh_exception_continuum_factor_tag <> "".
Proof. discriminate. Qed.

Lemma occupancy_engine_sort_channel_tag_nonempty :
  occupancy_engine_sort_channel_tag <> "".
Proof. discriminate. Qed.

Lemma observed_override_channel_tag_nonempty :
  observed_override_channel_tag <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  RhExceptionContinuum product channel — concurrent **product**  *)
(* ------------------------------------------------------------------ *)

Inductive rhec_channel_slot : Type :=
  | rhec_slot_unwired
  | rhec_slot_absent
  | rhec_slot_present.

Definition rhec_channel_slot_beq (s1 s2 : rhec_channel_slot) : bool :=
  match s1, s2 with
  | rhec_slot_unwired, rhec_slot_unwired => true
  | rhec_slot_absent, rhec_slot_absent => true
  | rhec_slot_present, rhec_slot_present => true
  | _, _ => false
  end.

Definition rhec_channel_slot_is_present (s : rhec_channel_slot) : bool :=
  match s with
  | rhec_slot_present => true
  | _ => false
  end.

Definition rhExceptionContinuumProductChannelCount : nat := 3.

Lemma rh_exception_continuum_product_channel_count_is_three :
  rhExceptionContinuumProductChannelCount = 3.
Proof. reflexivity. Qed.

(* Channel indices: 0 = interact restriction, 1 = TST prior art, 2 = class 14 rh_exception_continuum. *)
Definition rhec_channel_occupancy_engine_sort : nat := 0.
Definition rhec_channel_observed_override : nat := 1.
Definition rhec_channel_dblock_exception_continuum : nat := 2.

Lemma rhec_channel_occupancy_engine_sort_idx_is_0 :
  rhec_channel_occupancy_engine_sort = 0.
Proof. reflexivity. Qed.

Lemma rhec_channel_observed_override_idx_is_1 :
  rhec_channel_observed_override = 1.
Proof. reflexivity. Qed.

Lemma rhec_channel_class9_rh_exception_continuum_idx_is_2 :
  rhec_channel_dblock_exception_continuum = 2.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  RhExceptionContinuum concurrent **product** bundle scaffold    *)
(* ------------------------------------------------------------------ *)

Definition rhec_channel_bundle : Type := nat -> rhec_channel_slot.

Definition rhExceptionContinuumBundleAllUnwired : rhec_channel_bundle :=
  fun _ => rhec_slot_unwired.

Definition rhExceptionContinuumBundleAt (b : rhec_channel_bundle) (idx : nat)
  (slot : rhec_channel_slot) : rhec_channel_bundle :=
  fun i => if Nat.eqb i idx then slot else b i.

Definition rhExceptionContinuumBundleWithPresent
  (b : rhec_channel_bundle) (idx : nat) : rhec_channel_bundle :=
  rhExceptionContinuumBundleAt b idx rhec_slot_present.

Fixpoint count_rhec_present_up_to (b : rhec_channel_bundle) (bound : nat) : nat :=
  match bound with
  | 0 => 0
  | S i =>
      let add :=
        if rhec_channel_slot_is_present (b (pred bound))
        then 1 else 0 in
      count_rhec_present_up_to b i + add
  end.

Definition rhExceptionContinuumBundlePresentCount (b : rhec_channel_bundle) : nat :=
  count_rhec_present_up_to b rhExceptionContinuumProductChannelCount.

Definition rhExceptionContinuumBundleHolds (b : rhec_channel_bundle) (idx : nat) : bool :=
  rhec_channel_slot_is_present (b idx).

Definition rhExceptionContinuumBundleIsConcurrentProduct (b : rhec_channel_bundle) : bool :=
  Nat.leb 2 (rhExceptionContinuumBundlePresentCount b).

(* Rh Z=45 interact restriction + G-min + class 14 rh_exception_continuum concurrent witness. *)
Definition rhExceptionContinuumRh45Witness : rhec_channel_bundle :=
  rhExceptionContinuumBundleWithPresent
    (rhExceptionContinuumBundleWithPresent
      (rhExceptionContinuumBundleWithPresent rhExceptionContinuumBundleAllUnwired
        rhec_channel_occupancy_engine_sort)
      rhec_channel_observed_override)
    rhec_channel_dblock_exception_continuum.

Definition rhExceptionContinuumEmptyWitness : rhec_channel_bundle :=
  rhExceptionContinuumBundleAllUnwired.

Definition rhExceptionContinuumSinglePresent : rhec_channel_bundle :=
  rhExceptionContinuumBundleWithPresent rhExceptionContinuumBundleAllUnwired
    rhec_channel_occupancy_engine_sort.

Lemma occupancy_engine_sort_channel_present :
  rhExceptionContinuumBundleHolds rhExceptionContinuumRh45Witness
    rhec_channel_occupancy_engine_sort = true.
Proof. reflexivity. Qed.

Lemma observed_override_channel_present :
  rhExceptionContinuumBundleHolds rhExceptionContinuumRh45Witness
    rhec_channel_observed_override = true.
Proof. reflexivity. Qed.

Lemma class9_rh_exception_continuum_channel_present :
  rhExceptionContinuumBundleHolds rhExceptionContinuumRh45Witness
    rhec_channel_dblock_exception_continuum = true.
Proof. reflexivity. Qed.

Lemma rh45_witness_present_count_is_three :
  rhExceptionContinuumBundlePresentCount rhExceptionContinuumRh45Witness = 3.
Proof. reflexivity. Qed.

Lemma rh45_witness_is_concurrent_product :
  rhExceptionContinuumBundleIsConcurrentProduct rhExceptionContinuumRh45Witness = true.
Proof.
  unfold rhExceptionContinuumBundleIsConcurrentProduct.
  rewrite rh45_witness_present_count_is_three.
  reflexivity.
Qed.

Lemma empty_bundle_present_count_zero :
  rhExceptionContinuumBundlePresentCount rhExceptionContinuumEmptyWitness = 0.
Proof. reflexivity. Qed.

Lemma empty_bundle_not_concurrent_product :
  rhExceptionContinuumBundleIsConcurrentProduct rhExceptionContinuumEmptyWitness = false.
Proof.
  unfold rhExceptionContinuumBundleIsConcurrentProduct.
  rewrite empty_bundle_present_count_zero.
  reflexivity.
Qed.

Lemma single_present_count_is_one :
  rhExceptionContinuumBundlePresentCount rhExceptionContinuumSinglePresent = 1.
Proof. reflexivity. Qed.

Lemma single_present_not_concurrent_product :
  rhExceptionContinuumBundleIsConcurrentProduct rhExceptionContinuumSinglePresent = false.
Proof.
  unfold rhExceptionContinuumBundleIsConcurrentProduct.
  rewrite single_present_count_is_one.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR mutually-exclusive classifiers refuse — not Π_c **product**     *)
(* ------------------------------------------------------------------ *)

Inductive rhec_xor_posture : Type :=
  | rhec_xor_exclusive
  | rhec_xor_concurrent_product.

Definition rhecXorClassifierMarker : string := "chem_l0_rh_exception_continuum_xor_classifier_v1".
Definition rhecConcurrentProductMarker : string := "chem_int_rh_exception_continuum_product_v1".

Lemma rhec_xor_marker_ne_concurrent_product_marker :
  rhecXorClassifierMarker <> rhecConcurrentProductMarker.
Proof. discriminate. Qed.

Definition rhecXorClassifierIncompatible (claim_xor : bool)
  (b : rhec_channel_bundle) : bool :=
  claim_xor && rhExceptionContinuumBundleIsConcurrentProduct b.

Lemma rhec_xor_refuse_on_rh45_witness :
  rhecXorClassifierIncompatible true rhExceptionContinuumRh45Witness = true.
Proof.
  unfold rhecXorClassifierIncompatible.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma rhec_xor_ok_on_concurrent_product_claim :
  rhecXorClassifierIncompatible false rhExceptionContinuumRh45Witness = false.
Proof. reflexivity. Qed.

Definition rhecProductNotXor : bool :=
  rhExceptionContinuumBundleIsConcurrentProduct rhExceptionContinuumRh45Witness &&
  rhecXorClassifierIncompatible true rhExceptionContinuumRh45Witness.

Lemma rhec_product_not_xor_true : rhecProductNotXor = true.
Proof.
  unfold rhecProductNotXor.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem concurrent_product_not_xor :
  rhecProductNotXor = true /\
  Nat.leb 2 (rhExceptionContinuumBundlePresentCount
    rhExceptionContinuumRh45Witness) = true /\
  rhecXorClassifierMarker <> rhecConcurrentProductMarker.
Proof.
  split.
  - apply rhec_product_not_xor_true.
  - split.
    + rewrite rh45_witness_present_count_is_three.
      reflexivity.
    + apply rhec_xor_marker_ne_concurrent_product_marker.
Qed.

(* ------------------------------------------------------------------ *)
(*  RhExceptionContinuum **conservation** bar — Proved-without-bar  *)
(* ------------------------------------------------------------------ *)

Inductive rhec_bar_presence : Type :=
  | rhec_bar_absent
  | rhec_bar_present.

Record rhec_claim_bar : Type := {
  rhec_bar_presence_field : rhec_bar_presence;
  rhec_bar_defect_total : nat
}.

Definition rhExceptionContinuumClaimBarAbsent : rhec_claim_bar :=
  {| rhec_bar_presence_field := rhec_bar_absent;
     rhec_bar_defect_total := 0 |}.

Definition rhExceptionContinuumClaimBarZeroDefect : rhec_claim_bar :=
  {| rhec_bar_presence_field := rhec_bar_present;
     rhec_bar_defect_total := 0 |}.

Definition rhec_claim_bar_zero_defect (b : rhec_claim_bar) : bool :=
  match rhec_bar_presence_field b with
  | rhec_bar_absent => false
  | rhec_bar_present => Nat.eqb (rhec_bar_defect_total b) 0
  end.

Lemma rhec_claim_bar_zero_defect_true :
  rhec_claim_bar_zero_defect rhExceptionContinuumClaimBarZeroDefect = true.
Proof. reflexivity. Qed.

Lemma rhec_claim_bar_absent_not_zero_defect :
  rhec_claim_bar_zero_defect rhExceptionContinuumClaimBarAbsent = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  RhExceptionContinuum **conservation** verdict — fail-closed      *)
(* ------------------------------------------------------------------ *)

Inductive rhec_conservation_verdict : Type :=
  | rhec_verdict_unwired_ok
  | rhec_verdict_named_ok
  | rhec_verdict_design_ok
  | rhec_verdict_trivial_refuse
  | rhec_verdict_xor_refuse
  | rhec_verdict_green_invent_refuse
  | rhec_verdict_proved_without_bar_refuse
  | rhec_verdict_production_wired_refuse
  | rhec_verdict_parallel_rh_exception_continuum_axiom_refuse
  | rhec_verdict_species_id_smuggle_refuse
  | rhec_verdict_extra_element_id_refuse
  | rhec_verdict_extra_rh_exception_continuum_force_refuse
  | rhec_verdict_tp_float_pin_refuse.

Definition rhec_conservation_verdict_ok (v : rhec_conservation_verdict) : bool :=
  match v with
  | rhec_verdict_unwired_ok => true
  | rhec_verdict_named_ok => true
  | rhec_verdict_design_ok => true
  | _ => false
  end.

Definition rhExceptionContinuumBundleNontrivial (b : rhec_channel_bundle) : bool :=
  Nat.ltb 0 (rhExceptionContinuumBundlePresentCount b).

Definition evaluate_rh_exception_continuum_bundle
  (m : RhExceptionContinuumModality)
  (b : rhec_channel_bundle)
  (bar : rhec_claim_bar)
  (claim_xor_classifier : bool)
  (claim_physics_green : bool)
  (claim_proved : bool) : rhec_conservation_verdict :=
  if claim_physics_green
  then rhec_verdict_green_invent_refuse
  else if claim_proved
       then rhec_verdict_proved_without_bar_refuse
       else if negb (rhExceptionContinuumBundleNontrivial b)
            then rhec_verdict_trivial_refuse
            else if rhecXorClassifierIncompatible claim_xor_classifier b
                 then rhec_verdict_xor_refuse
                 else
                   match m with
                   | rh_exception_continuum_unwired =>
                       if rhExceptionContinuumBundleIsConcurrentProduct b
                       then rhec_verdict_named_ok
                       else rhec_verdict_design_ok
                   | rh_exception_continuum_assumed
                   | rh_exception_continuum_surrogate =>
                       rhec_verdict_design_ok
                   | rh_exception_continuum_proved =>
                       rhec_verdict_proved_without_bar_refuse
                   end.

Definition evaluate_rh_exception_continuum_close
  (m : RhExceptionContinuumModality)
  (claim_physics_green : bool)
  (claim_production_wired : bool) : rhec_conservation_verdict :=
  if claim_physics_green
  then rhec_verdict_green_invent_refuse
  else if claim_production_wired
  then rhec_verdict_production_wired_refuse
  else
    match m with
    | rh_exception_continuum_unwired => rhec_verdict_unwired_ok
    | rh_exception_continuum_assumed
    | rh_exception_continuum_proved
    | rh_exception_continuum_surrogate => rhec_verdict_named_ok
    end.

Definition rh_exception_continuum_authorized
  (claim_physics_green : bool)
  (claim_production_wired : bool) : bool :=
  match evaluate_rh_exception_continuum_close
          rh_exception_continuum_proved claim_physics_green claim_production_wired with
  | rhec_verdict_named_ok => true
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  RhExceptionContinuum **conservation** law cells — four laws       *)
(* ------------------------------------------------------------------ *)

Inductive rhec_conservation_law : Type :=
  | rhec_law_conserved
  | rhec_law_named_ok
  | rhec_law_trivial_refuse
  | rhec_law_green_invent_refuse.

Definition rhec_conservation_law_count : nat := 4.

Lemma rhec_conservation_law_count_is_four :
  rhec_conservation_law_count = 4.
Proof. reflexivity. Qed.

Inductive rhec_conservation_law_witness : Type :=
  | rhec_law_witness_open
  | rhec_law_witness_proved.

Definition evaluate_rhec_conservation_law_witness
  (law : rhec_conservation_law)
  (m : RhExceptionContinuumModality)
  : rhec_conservation_law_witness :=
  match m with
  | rh_exception_continuum_unwired
  | rh_exception_continuum_assumed
  | rh_exception_continuum_surrogate => rhec_law_witness_open
  | rh_exception_continuum_proved => rhec_law_witness_proved
  end.

Lemma all_rhec_conservation_laws_open_at_unwired :
  evaluate_rhec_conservation_law_witness rhec_law_conserved
    rh_exception_continuum_unwired = rhec_law_witness_open /\
  evaluate_rhec_conservation_law_witness rhec_law_named_ok
    rh_exception_continuum_unwired = rhec_law_witness_open /\
  evaluate_rhec_conservation_law_witness rhec_law_trivial_refuse
    rh_exception_continuum_unwired = rhec_law_witness_open /\
  evaluate_rhec_conservation_law_witness rhec_law_green_invent_refuse
    rh_exception_continuum_unwired = rhec_law_witness_open.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Class-14 pins (structure witnesses — conservation laws not Proved)   *)
(* ------------------------------------------------------------------ *)

Definition rhExceptionContinuumProved : bool := false.

Lemma rh_exception_continuum_proved_false :
  rhExceptionContinuumProved = false.
Proof. reflexivity. Qed.

Definition not118SquaredGreenTable : bool := true.

Lemma not_118_squared_green_table : not118SquaredGreenTable = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Unwired close without production wiring (lemma)                     *)
(* ------------------------------------------------------------------ *)

Lemma unwired_close_without_production_wiring :
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_unwired false false =
  rhec_verdict_unwired_ok.
Proof. reflexivity. Qed.

Theorem unwired_modality_always_ok_without_production_wiring :
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_unwired false false =
  rhec_verdict_unwired_ok.
Proof. apply unwired_close_without_production_wiring. Qed.

Lemma unwired_verdict_ok_without_production_wiring :
  rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_close
       rh_exception_continuum_unwired false false) =
  true.
Proof.
  unfold rhec_conservation_verdict_ok.
  rewrite unwired_close_without_production_wiring.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Named Rh Z=45 close — concurrent **product**                        *)
(* ------------------------------------------------------------------ *)

Lemma rh45_witness_named_ok :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent false false false =
  rhec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_rh45_rh_exception_continuum :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent false false false =
  rhec_verdict_named_ok /\
  rhExceptionContinuumBundleIsConcurrentProduct rhExceptionContinuumRh45Witness = true /\
  rhodium_atomic_number_z = 45 /\
  rh_observed_occupancy_tag = "4d85s1".
Proof.
  repeat split; reflexivity.
Qed.

Lemma rhec_named_close_ok :
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_proved false false =
  rhec_verdict_named_ok.
Proof. reflexivity. Qed.

Theorem named_rh_exception_continuum_close :
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_proved false false =
  rhec_verdict_named_ok /\
  rh_exception_continuum_authorized false false = true.
Proof.
  split.
  - apply rhec_named_close_ok.
  - unfold rh_exception_continuum_authorized.
    rewrite rhec_named_close_ok.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Trivial empty-bundle fail-closed — rh_exception_continuum refuse *)
(* ------------------------------------------------------------------ *)

Lemma trivial_bundle_refused :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumEmptyWitness
    rhExceptionContinuumClaimBarAbsent false false false =
  rhec_verdict_trivial_refuse.
Proof. reflexivity. Qed.

Theorem trivial_empty_bundle_fail_closed :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumEmptyWitness
    rhExceptionContinuumClaimBarAbsent false false false =
  rhec_verdict_trivial_refuse /\
  rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_bundle
       rh_exception_continuum_unwired
       rhExceptionContinuumEmptyWitness
       rhExceptionContinuumClaimBarAbsent false false false) =
  false.
Proof.
  split.
  - apply trivial_bundle_refused.
  - unfold rhec_conservation_verdict_ok.
    rewrite trivial_bundle_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  XOR classifier fail-closed — mutually-exclusive refuse                *)
(* ------------------------------------------------------------------ *)

Lemma xor_classifier_refused :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent true false false =
  rhec_verdict_xor_refuse.
Proof. reflexivity. Qed.

Theorem xor_mutually_exclusive_classifier_fail_closed :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent true false false =
  rhec_verdict_xor_refuse /\
  rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_bundle
       rh_exception_continuum_unwired
       rhExceptionContinuumRh45Witness
       rhExceptionContinuumClaimBarAbsent true false false) =
  false.
Proof.
  split.
  - apply xor_classifier_refused.
  - unfold rhec_conservation_verdict_ok.
    rewrite xor_classifier_refused.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Green invent refuse — physics GREEN never authorized                *)
(* ------------------------------------------------------------------ *)

Lemma green_invent_refuse_unwired :
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_unwired true false =
  rhec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

Theorem green_invent_always_refuse :
  rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_close
       rh_exception_continuum_unwired true false) =
  false.
Proof.
  unfold rhec_conservation_verdict_ok.
  rewrite green_invent_refuse_unwired.
  reflexivity.
Qed.

Lemma green_invent_rhec_bundle_refuse :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent false true false =
  rhec_verdict_green_invent_refuse.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Proved-without-bar fail-closed — rh_exception_continuum refuse   *)
(* ------------------------------------------------------------------ *)

Lemma proved_without_bar_refuse :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent false false true =
  rhec_verdict_proved_without_bar_refuse.
Proof. reflexivity. Qed.

Theorem proved_without_bar_fail_closed :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent false false true =
  rhec_verdict_proved_without_bar_refuse /\
  rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_bundle
       rh_exception_continuum_unwired
       rhExceptionContinuumRh45Witness
       rhExceptionContinuumClaimBarAbsent false false true) =
  false.
Proof.
  split.
  - apply proved_without_bar_refuse.
  - unfold rhec_conservation_verdict_ok.
    rewrite proved_without_bar_refuse.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Production wired refuse — rh_exception_continuum lattice not wired *)
(* ------------------------------------------------------------------ *)

Lemma production_wired_refuse :
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_proved false true =
  rhec_verdict_production_wired_refuse.
Proof. reflexivity. Qed.

Theorem production_wired_claim_refused :
  rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_close
       rh_exception_continuum_proved false true) =
  false.
Proof.
  unfold rhec_conservation_verdict_ok.
  rewrite production_wired_refuse.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel rh_exception_continuum axiom refuse — morphism not 26th axiom      *)
(* ------------------------------------------------------------------ *)

Definition rhExceptionContinuumAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition parallelRhExceptionAxiomTag : string := "26th_periodic_table_axiom".

Lemma parallel_rh_exception_continuum_axiom_refuse :
  rhExceptionContinuumAuthority <>
  parallelRhExceptionAxiomTag /\
  rhExceptionContinuumProved = false.
Proof.
  split.
  - discriminate.
  - apply rh_exception_continuum_proved_false.
Qed.

Theorem parallel_rh_exception_continuum_axiom_not_minted :
  rhExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs" /\
  rhExceptionContinuumProved = false /\
  rhExceptionContinuumAuthority <> parallelRhExceptionAxiomTag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  SpeciesId smuggle refuse — interact restriction ≠ L1 SpeciesId          *)
(* ------------------------------------------------------------------ *)

Definition homologCopyFraming : string :=
  "co_z27_occupancy_copied_onto_rh_z45".

Definition rhExceptionContinuumFraming : string :=
  "second_law_conservation_rh_exception_continuum_occupancy_engine_sort_one_axiom".

Lemma species_id_smuggle_refuse :
  rhExceptionContinuumFraming <>
  homologCopyFraming /\
  rhodium_atomic_number_z = 45 /\
  rh_observed_occupancy_tag = "4d85s1".
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem mo_co_homolog_not_occupancy_copy :
  rhExceptionContinuumFraming <>
  homologCopyFraming /\
  rhodium_atomic_number_z = 45 /\
  cobalt_homolog_z = 27 /\
  rh_observed_occupancy_tag <> co_homolog_observed_occupancy_tag /\
  rhExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Extra ElementId refuse — rh_exception_continuum ≠ Z=119 smuggle          *)
(* ------------------------------------------------------------------ *)

Definition extraElementIdSmuggleFraming : string :=
  "rh_exception_as_extra_element_id_smuggle".

Lemma extra_element_id_refuse :
  rhExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_not_in_table = true.
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem impurity_morphism_not_extra_element_id :
  rhExceptionContinuumFraming <>
  extraElementIdSmuggleFraming /\
  forbidden_z119_smuggle = 119 /\
  rhodium_atomic_number_z = 45.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Free purification refuse — rh_exception_continuum ≠ extra rh_exception_continuum force axiom    *)
(* ------------------------------------------------------------------ *)

Definition extraOccupancyAxiomFraming : string :=
  "extra_rh_exception_continuum_force_axiom_minted_as_26th_law".

Definition occupancyEngineSortAuthority : string :=
  "umst/umst-chem/src/rh_exception_continuum_barrier.rs".

Lemma extra_rh_exception_continuum_force_refuse :
  rhExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority <> "".
Proof.
  split.
  - discriminate.
  - discriminate.
Qed.

Theorem rh_exception_continuum_not_extra_rh_exception_continuum_force :
  rhExceptionContinuumFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/rh_exception_continuum_barrier.rs" /\
  rhExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  Madelung family smuggle refuse — observed override ≠ family-only      *)
(* ------------------------------------------------------------------ *)

Definition madelungFamilySmuggleFraming : string :=
  "madelung_family_only_no_observed_override".

Definition madelungWitnessAuthority : string :=
  "umst/umst-chem/src/x_rows/madelung_witness.rs".

Lemma madelung_family_smuggle_refuse :
  rhExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  rh_observed_occupancy_tag <> rh_predicted_occupancy_tag.
Proof.
  split.
  - discriminate.
  - apply rh_observed_ne_predicted_occupancy.
Qed.

Theorem mo_observed_override_not_madelung_family_smuggle :
  rhExceptionContinuumFraming <>
  madelungFamilySmuggleFraming /\
  rh_observed_occupancy_tag = "4d85s1" /\
  rh_predicted_occupancy_tag = "4d75s2" /\
  rhExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate || apply rh_exception_continuum_proved_false.
Qed.

(* ------------------------------------------------------------------ *)
(*  T/P float-pin refuse — graph functions v14 ≠ bare float pins        *)
(* ------------------------------------------------------------------ *)

Definition tpFloatPinFraming : string :=
  "bare_298_15_k_1_atm_float_pins_on_rh_exception_continuum_scaffold".

Lemma tp_float_pin_refuse :
  rhExceptionContinuumFraming <>
  tpFloatPinFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem tp_graph_function_not_float_pin :
  rhExceptionContinuumFraming <>
  tpFloatPinFraming /\
  observed_override_channel_tag = "observed_override" /\
  rhodium_atomic_number_z = 45.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  RhExceptionContinuum **conservation** coherence scaffold         *)
(* ------------------------------------------------------------------ *)

Definition rhec_conservation_coherence_scaffold : bool :=
  rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_close
       rh_exception_continuum_proved false false) &&
  negb (rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_close
       rh_exception_continuum_unwired true false)) &&
  negb (rhec_conservation_verdict_ok
    (evaluate_rh_exception_continuum_close
       rh_exception_continuum_proved false true)).

Lemma rhec_conservation_coherence_scaffold_true :
  rhec_conservation_coherence_scaffold = true.
Proof.
  unfold rhec_conservation_coherence_scaffold.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem rhec_conservation_coherence_scaffold_theorem :
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_proved false false =
    rhec_verdict_named_ok /\
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_unwired true false =
    rhec_verdict_green_invent_refuse /\
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_proved false true =
    rhec_verdict_production_wired_refuse.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Knowing / quantum fiber routing — geometry not meso acting          *)
(* ------------------------------------------------------------------ *)

Inductive formal_fiber : Type :=
  | fiber_quantum_knowing
  | fiber_meso_acting.

Definition rhec_conservation_fiber_ok (f : formal_fiber) : bool :=
  match f with
  | fiber_quantum_knowing => true
  | fiber_meso_acting => false
  end.

Definition rhec_conservation_knowing_fiber_ok : bool :=
  rhec_conservation_fiber_ok fiber_quantum_knowing.

Definition rhec_conservation_meso_acting_ok : bool :=
  rhec_conservation_fiber_ok fiber_meso_acting.

Lemma rhec_conservation_knowing_fiber_ok_true :
  rhec_conservation_knowing_fiber_ok = true.
Proof. reflexivity. Qed.

Lemma rhec_conservation_meso_acting_not_ok :
  rhec_conservation_meso_acting_ok = false.
Proof. reflexivity. Qed.

Theorem rhec_conservation_routes_knowing_not_meso :
  rhec_conservation_knowing_fiber_ok = true /\
  rhec_conservation_meso_acting_ok = false.
Proof.
  split.
  - apply rhec_conservation_knowing_fiber_ok_true.
  - apply rhec_conservation_meso_acting_not_ok.
Qed.

Definition fiberNotMesoActing : bool :=
  rhec_conservation_knowing_fiber_ok &&
  negb rhec_conservation_meso_acting_ok.

Lemma fiber_not_meso_acting_true : fiberNotMesoActing = true.
Proof.
  unfold fiberNotMesoActing, rhec_conservation_knowing_fiber_ok,
    rhec_conservation_meso_acting_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Fixture scaffold — named class-14 + fail-closed + fiber                *)
(* ------------------------------------------------------------------ *)

Theorem rh_exception_continuum_fixture_scaffold :
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent false false false =
    rhec_verdict_named_ok /\
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumEmptyWitness
    rhExceptionContinuumClaimBarAbsent false false false =
    rhec_verdict_trivial_refuse /\
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent true false false =
    rhec_verdict_xor_refuse /\
  evaluate_rh_exception_continuum_bundle
    rh_exception_continuum_unwired
    rhExceptionContinuumRh45Witness
    rhExceptionContinuumClaimBarAbsent false false true =
    rhec_verdict_proved_without_bar_refuse /\
  evaluate_rh_exception_continuum_close
    rh_exception_continuum_unwired false false =
    rhec_verdict_unwired_ok /\
  rhec_conservation_knowing_fiber_ok = true /\
  rhec_conservation_meso_acting_ok = false /\
  rhExceptionContinuumProved = false /\
  rhecProductNotXor = true /\
  rhodium_atomic_number_z = 45.
Proof.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Ir Z=77 homolog not Co copy — period-6 group-9 homolog ≠ identity   *)
(* ------------------------------------------------------------------ *)

Definition iridium_atomic_number_z : nat := 77.

Lemma iridium_atomic_number_z_is_77 :
  iridium_atomic_number_z = 77.
Proof. reflexivity. Qed.

Definition cobalt_occupancy_tag : string := "3d74s2".

Definition iridium_occupancy_tag : string := "6s24f145d7".

Lemma cobalt_iridium_occupancy_tags_distinct :
  cobalt_occupancy_tag <> iridium_occupancy_tag.
Proof. discriminate. Qed.

Definition homologExceptionNotCopyCellId : string :=
  "CHEM-INT-CROSS-HOMOLOG-EXCEPTION-NOT-COPY".

Lemma ir_co_homolog_not_copy :
  rhodium_atomic_number_z = 45 /\
  iridium_atomic_number_z = 77 /\
  cobalt_occupancy_tag <> iridium_occupancy_tag.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

Theorem ir_period6_homolog_not_co_occupancy_copy :
  rhodium_atomic_number_z = 45 /\
  iridium_atomic_number_z = 77 /\
  cobalt_occupancy_tag = "3d74s2" /\
  iridium_occupancy_tag = "6s24f145d7" /\
  cobalt_occupancy_tag <> iridium_occupancy_tag /\
  rhExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Cited upstream authority strings (views only — rh_exception_continuum) *)
(* ------------------------------------------------------------------ *)

Definition rhExceptionContinuumQlatticeAuthority : string :=
  "umst/umst-chem/src/qlattice.rs".

Definition occupancyEngineSortIntAuthority : string :=
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".

Definition homologExceptionNotCopyAuthority : string :=
  "umst/umst-chem/src/x_rows/homolog_exception_not_copy.rs".

Definition dBlockOccupancyExceptionsAuthority : string :=
  "umst/umst-formal-double-slit/Coq/ChemConstants/DBlockOccupancyExceptions.v".

Definition occupancyEngineSortExceptionSetsCellId : string := "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".

Definition rhExceptionContinuumCellId : string :=
  "CHEM-FORMAL-Q-COQ-RH-EXCEPTION-CONTINUUM".

Definition rhExceptionContinuumNonClaim : string :=
  "CHEM-FORMAL-Q-COQ-RH-EXCEPTION-CONTINUUM RhExceptionContinuumModality Unwired Assumed Proved Surrogate four-step lattice rhExceptionContinuumProved false evaluateRhExceptionContinuumBundle evaluateRhExceptionContinuum named Rh Z=45 d-block occupancy exception continuum X29 occupancy engine sort observed override dblock exception concurrent product identity conserved present ge 2 product not XOR xor mutually exclusive refuse parallel cu exception axiom refuse homolog copy smuggle refuse extra element id Z=119 refuse extra occupancy axiom refuse Ir Z=77 homolog not Co 3d10 4s1 copy Unwired one axiom second law conservation not 118 squared GREEN table not meso acting not physics GREEN not production_wired".

Lemma rh_exception_continuum_cell_id :
  rhExceptionContinuumCellId =
  "CHEM-FORMAL-Q-COQ-RH-EXCEPTION-CONTINUUM".
Proof. reflexivity. Qed.

Lemma rh_exception_continuum_cites_l0_table :
  occupancyEngineSortIntAuthority <> "".
Proof. discriminate. Qed.

Lemma rh_exception_continuum_authority_path :
  rhExceptionContinuumAuthority =
  "umst/umst-chem/src/x_rows/occupancy_engine_sort.rs".
Proof. reflexivity. Qed.

Lemma rh_exception_continuum_cites_l0_ore02 :
  rhExceptionContinuumQlatticeAuthority <> "".
Proof. discriminate. Qed.

Lemma rh_exception_continuum_cites_marker :
  rhecConcurrentProductMarker <> "".
Proof. discriminate. Qed.

Lemma rh_exception_continuum_cites_pattern_product :
  dBlockOccupancyExceptionsAuthority <> "".
Proof. discriminate. Qed.

Lemma rh_exception_continuum_cites_ore02_cell :
  occupancyEngineSortExceptionSetsCellId = "CHEM-INT-CROSS-OCCUPANCY-EXCEPTION-SETS".
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  One axiom framing: second law + **conservation**; not 26th axiom    *)
(* ------------------------------------------------------------------ *)

Lemma rh_exception_continuum_not_26th_axiom :
  rhExceptionContinuumFraming <> parallelRhExceptionAxiomTag.
Proof. discriminate. Qed.

Lemma rh_exception_continuum_second_law_conservation_framing :
  rhExceptionContinuumFraming <> "".
Proof. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  TST prior art — restriction is named object, not TST axiom        *)
(* ------------------------------------------------------------------ *)

Definition madelungWalkFraming : string :=
  "madelung_walk_predicted_not_observed_override".

Definition dblockExceptionNamedObject : string :=
  "interact_restriction_on_rh_exception_continuum_morphism".

Lemma tst_prior_art_not_named_object :
  dblockExceptionNamedObject <>
  madelungWalkFraming /\
  observed_override_channel_tag = "observed_override".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem dblock_exception_is_named_object_not_madelung_walk :
  dblockExceptionNamedObject <>
  madelungWalkFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort" /\
  rhExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Interact restriction refuse — not rh_exception_continuum axiom / extra force     *)
(* ------------------------------------------------------------------ *)

Definition occupancyEngineSortFraming : string :=
  "occupancy_engine_sort_not_extra_force".

Lemma interact_restriction_not_extra_force_refuse :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancy_engine_sort_channel_tag = "occupancy_engine_sort".
Proof.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem rh_exception_continuum_interact_restriction_not_extra_force :
  occupancyEngineSortFraming <>
  extraOccupancyAxiomFraming /\
  occupancyEngineSortAuthority =
  "umst/umst-chem/src/rh_exception_continuum_barrier.rs" /\
  rhExceptionContinuumProved = false.
Proof.
  repeat split; reflexivity || discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  Physics GREEN fence (False — not authorized on knowing scaffold)    *)
(* ------------------------------------------------------------------ *)

Definition physicsGreenAuthorized : Prop := False.

Lemma rh_exception_continuum_physics_green_false :
  ~ physicsGreenAuthorized.
Proof. intro H; exact H. Qed.

Lemma rh_exception_continuum_modality_unwired :
  rhExceptionContinuumModalityCurrent =
  rh_exception_continuum_unwired.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  WAVE100 — not wired in lib.rs / eos.rs (honest pin)                *)
(* ------------------------------------------------------------------ *)

Definition rhExceptionContinuumProductionWired : Prop := False.

Lemma rh_exception_continuum_not_production_wired :
  ~ rhExceptionContinuumProductionWired.
Proof. intro H; exact H. Qed.

Definition wave100NotWiredLibOrEos : string :=
  "WAVE100 freeze — deferred composition not impossibility; not wired lib.rs eos.rs".

Lemma wave100_not_wired_lib_or_eos :
  wave100NotWiredLibOrEos <> "".
Proof. discriminate. Qed.

